-- Prove2me | solution 1 for StochApproxDyn.LimitSet.chainRecurrentSet_isInternallyChainRecurrent
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:52:25.616087+00:00
-- url     : https://prove2.me/submissions/ddd36125-1e2a-4963-937a-e309d194f75f

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence

open scoped NNReal


namespace StochApproxDyn.LimitSet

theorem d45k_unif {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (K : Set M) (hK : IsCompact K)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ τ : ℝ≥0, τ ≤ T → ∀ x ∈ K, ∀ y ∈ K, dist x y < η →
      dist (Φ τ x) (Φ τ y) < ε := by
  have hc : IsCompact (Set.Icc (0:ℝ≥0) T ×ˢ K) := isCompact_Icc.prod hK
  have hu := hc.uniformContinuousOn_of_continuous
    (f := fun p : ℝ≥0 × M => Φ p.1 p.2) (Φ.continuous continuous_fst continuous_snd).continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨η, hη, h⟩ := hu ε hε
  refine ⟨η, hη, fun τ hτ x hx y hy hxy => ?_⟩
  have := h (τ, x) ⟨⟨zero_le, hτ⟩, hx⟩ (τ, y) ⟨⟨zero_le, hτ⟩, hy⟩ (by
    rw [Prod.dist_eq]; simp [hxy])
  simpa using this

theorem d45k_split_time (T s : ℝ≥0) (hT : 0 < T) (hs : T ≤ s) :
    ∃ n : ℕ, 1 ≤ n ∧ T ≤ s / n ∧ s / n ≤ 2 * T ∧ (n : ℝ≥0) * (s / n) = s := by
  set n := Nat.floor (s / T) with hndef
  have hn1 : 1 ≤ n := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hT, one_mul]
    exact hs
  have hnpos : (0 : ℝ≥0) < n := by exact_mod_cast hn1
  have hnT : (n : ℝ≥0) * T ≤ s := by
    rw [← le_div_iff₀ hT]
    exact Nat.floor_le zero_le
  have hnT2 : s < ((n : ℝ≥0) + 1) * T := by
    rw [← div_lt_iff₀ hT]
    exact Nat.lt_floor_add_one _
  refine ⟨n, hn1, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hnpos, mul_comm]; exact hnT
  · rw [div_le_iff₀ hnpos]
    have : (1 : ℝ≥0) ≤ n := by exact_mod_cast hn1
    calc s ≤ ((n : ℝ≥0) + 1) * T := hnT2.le
      _ ≤ ((n : ℝ≥0) + n) * T := mul_le_mul_of_nonneg_right (add_le_add le_rfl this) zero_le
      _ = 2 * T * n := by ring
  · exact mul_div_cancel₀ _ hnpos.ne'

/-- normalized chain data -/
def d45kG {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (δ : ℝ) (T : ℝ≥0) (k : ℕ)
    (y : ℕ → M) (t : ℕ → ℝ≥0) : Prop :=
  (∀ i < k, T ≤ t i ∧ t i ≤ 2 * T) ∧ ∀ j < k, dist (Φ (t j) (y j)) (y (j + 1)) < δ

theorem d45k_split {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (δ : ℝ) (T : ℝ≥0)
    (hT : 0 < T) (y0 b : M) (s : ℝ≥0) (hs : T ≤ s) (hb : dist (Φ s y0) b < δ) :
    ∃ k y t, d45kG Φ δ T k y t ∧ 1 ≤ k ∧ y 0 = y0 ∧ y k = b := by
  obtain ⟨n, hn1, hτ1, hτ2, hns⟩ := d45k_split_time T s hT hs
  have hδ : 0 < δ := lt_of_le_of_lt dist_nonneg hb
  refine ⟨n, fun i => if i < n then Φ ((i : ℝ≥0) * (s / n)) y0 else b, fun _ => s / n,
    ⟨fun i _ => ⟨hτ1, hτ2⟩, ?_⟩, hn1, ?_, ?_⟩
  · intro j hj
    have hstep : Φ (s / n) (Φ ((j : ℝ≥0) * (s / n)) y0) =
        Φ (((j + 1 : ℕ) : ℝ≥0) * (s / n)) y0 := by
      rw [← Flow.map_add]; congr 1; push_cast; ring
    dsimp only
    rw [if_pos hj]
    by_cases hj1 : j + 1 < n
    · rw [if_pos hj1, hstep, dist_self]; exact hδ
    · have : j + 1 = n := by omega
      rw [if_neg hj1, hstep, this, hns]; exact hb
  · dsimp only
    rw [if_pos (by omega), Nat.cast_zero, zero_mul, Flow.map_zero_apply]
  · dsimp only
    rw [if_neg (lt_irrefl n)]

theorem d45k_concat {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (δ : ℝ) (T : ℝ≥0)
    (k1 : ℕ) (y1 : ℕ → M) (t1 : ℕ → ℝ≥0) (k2 : ℕ) (y2 : ℕ → M) (t2 : ℕ → ℝ≥0)
    (h1 : d45kG Φ δ T k1 y1 t1) (h2 : d45kG Φ δ T k2 y2 t2) (hj : y2 0 = y1 k1) :
    d45kG Φ δ T (k1 + k2) (fun i => if i < k1 then y1 i else y2 (i - k1))
      (fun i => if i < k1 then t1 i else t2 (i - k1)) ∧
    (fun i => if i < k1 then y1 i else y2 (i - k1)) 0 = y1 0 ∧
    (fun i => if i < k1 then y1 i else y2 (i - k1)) (k1 + k2) = y2 k2 := by
  refine ⟨⟨fun i hi => ?_, fun j hj' => ?_⟩, ?_, ?_⟩
  · dsimp only
    by_cases h : i < k1
    · rw [if_pos h]; exact h1.1 i h
    · rw [if_neg h]; exact h2.1 (i - k1) (by omega)
  · dsimp only
    by_cases h : j < k1
    · rw [if_pos h, if_pos h]
      by_cases h' : j + 1 < k1
      · rw [if_pos h']; exact h1.2 j h
      · have e : j + 1 = k1 := by omega
        rw [if_neg h', show j + 1 - k1 = 0 by omega, hj, ← e]; exact h1.2 j h
    · rw [if_neg h, if_neg h, if_neg (by omega)]
      have e : j + 1 - k1 = (j - k1) + 1 := by omega
      rw [e]; exact h2.2 (j - k1) (by omega)
  · dsimp only
    by_cases h : 0 < k1
    · rw [if_pos h]
    · have e : k1 = 0 := by omega
      rw [if_neg h, Nat.zero_sub, hj, e]
  · dsimp only
    rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem d45k_norm_aux {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (δ : ℝ) (T : ℝ≥0)
    (hT : 0 < T) :
    ∀ (k : ℕ) (y : ℕ → M) (t : ℕ → ℝ≥0), (∀ i < k, T ≤ t i) →
      (∀ j < k, dist (Φ (t j) (y j)) (y (j + 1)) < δ) →
      ∃ k' y' t', d45kG Φ δ T k' y' t' ∧ y' 0 = y 0 ∧ y' k' = y k ∧ (1 ≤ k → 1 ≤ k') := by
  intro k
  induction k with
  | zero =>
    intro y t _ _
    exact ⟨0, y, t, ⟨fun i hi => absurd hi (Nat.not_lt_zero _),
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩, rfl, rfl, fun h => absurd h (by norm_num)⟩
  | succ k ih =>
    intro y t ht hd
    obtain ⟨k1, y1, t1, hG1, h10, h1k, _⟩ :=
      ih y t (fun i hi => ht i (by omega)) (fun j hj => hd j (by omega))
    obtain ⟨k2, y2, t2, hG2, hk2, h20, h2k⟩ :=
      d45k_split Φ δ T hT (y k) (y (k+1)) (t k) (ht k (by omega)) (hd k (by omega))
    obtain ⟨hG, h0, hend⟩ := d45k_concat Φ δ T k1 y1 t1 k2 y2 t2 hG1 hG2 (by rw [h20, h1k])
    exact ⟨k1 + k2, _, _, hG, h0.trans h10, hend.trans h2k, fun _ => by omega⟩

theorem d45k_norm {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (δ : ℝ) (T : ℝ≥0) (a b : M)
    (h : PseudoOrbitTo Φ δ T a b) (hT : 0 < T) :
    ∃ k y t, IsPseudoOrbit Φ δ T a b k y t ∧ ∀ i < k, t i ≤ 2 * T := by
  obtain ⟨k, y, t, hk, ht, h0, hd, hb⟩ := h
  obtain ⟨k', y', t', hG, h0', hk', h1⟩ := d45k_norm_aux Φ δ T hT k y t ht hd
  exact ⟨k', y', t', ⟨h1 hk, fun i hi => (hG.1 i hi).1, by rw [h0']; exact h0, hG.2,
    by rw [hk', hb]⟩, fun i hi => (hG.1 i hi).2⟩

theorem d45k_shadow {M : Type*} [MetricSpace M] [CompactSpace M] (Φ : Flow ℝ≥0 M)
    (T : ℝ≥0) :
    ∀ m : ℕ, ∀ δ : ℝ, 0 < δ → ∃ ε > 0, ∀ (w : ℕ → M) (τ : ℕ → ℝ≥0),
      (∀ r < m, τ r ≤ 2 * T) → (∀ r < m, dist (Φ (τ r) (w r)) (w (r + 1)) < ε) →
      dist (Φ (∑ r ∈ Finset.range m, τ r) (w 0)) (w m) < δ := by
  intro m
  induction m with
  | zero =>
    intro δ hδ
    refine ⟨1, one_pos, fun w τ _ _ => ?_⟩
    simp [Flow.map_zero_apply, hδ]
  | succ m ih =>
    intro δ hδ
    obtain ⟨ω, hω, hu⟩ := d45k_unif Φ Set.univ isCompact_univ (2 * T) (δ / 2) (by linarith)
    obtain ⟨ε', hε', h'⟩ := ih ω hω
    refine ⟨min ε' (δ / 2), lt_min hε' (by linarith), fun w τ hτ hd => ?_⟩
    have hA := h' w τ (fun r hr => hτ r (by omega))
      (fun r hr => lt_of_lt_of_le (hd r (by omega)) (min_le_left _ _))
    rw [Finset.sum_range_succ, add_comm, Flow.map_add]
    have hB := hu (τ m) (hτ m (by omega)) _ (Set.mem_univ _) _ (Set.mem_univ _) hA
    have hC := lt_of_lt_of_le (hd m (by omega)) (min_le_right _ _)
    calc dist (Φ (τ m) (Φ (∑ r ∈ Finset.range m, τ r) (w 0))) (w (m + 1))
        ≤ dist (Φ (τ m) (Φ (∑ r ∈ Finset.range m, τ r) (w 0))) (Φ (τ m) (w m)) +
          dist (Φ (τ m) (w m)) (w (m+1)) := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add hB hC
      _ = δ := by ring

theorem d45k_mod_succ (k i : ℕ) (hk : 0 < k) :
    (i + 1) % k = if i % k + 1 < k then i % k + 1 else 0 := by
  have h1 := Nat.mod_lt i hk
  rcases Nat.lt_or_ge 1 k with hk1 | hk1
  · rw [Nat.add_mod, Nat.mod_eq_of_lt hk1]
    split_ifs with hc
    · exact Nat.mod_eq_of_lt hc
    · have : i % k + 1 = k := by omega
      rw [this, Nat.mod_self]
  · have : k = 1 := by omega
    subst this
    simp [Nat.mod_one]

theorem d45k_merge {M : Type*} [MetricSpace M] [CompactSpace M] (Φ : Flow ℝ≥0 M) (T : ℝ≥0)
    (hT : 0 < T) (x : M) (h : ∀ ε : ℝ, 0 < ε → PseudoOrbitTo Φ ε T x x) : ChainTo Φ x x := by
  intro δ hδ T'' hT''
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.ceil (T'' / T) := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by
    rw [hm]; exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (div_pos hT'' hT)).ne'
  have hmT : T'' ≤ m * T := by
    have := Nat.le_ceil (T'' / T)
    rw [← hm, div_le_iff₀ hT] at this
    exact this
  obtain ⟨ε1, hε1, hS⟩ := d45k_shadow Φ T m δ hδ
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min ε1 δ / 2 := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; exact half_pos (lt_min hε1 hδ)
  have h2ε : 2 * ε ≤ ε1 := by rw [hε]; linarith [min_le_left ε1 δ]
  have hεδ : 2 * ε ≤ δ := by rw [hε]; linarith [min_le_right ε1 δ]
  obtain ⟨k, y, t, ⟨hk, ht, h0, hd, hyk⟩, ht2⟩ := d45k_norm Φ ε T x x (h ε hεpos) hT
  have hkpos : 0 < k := hk
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → M, ∀ i, Y i = if i = k * m then x else y (i % k) :=
    ⟨_, fun _ => rfl⟩
  have hτ : ∀ i, T ≤ t (i % k) ∧ t (i % k) ≤ 2 * T :=
    fun i => ⟨ht _ (Nat.mod_lt _ hkpos), ht2 _ (Nat.mod_lt _ hkpos)⟩
  have hjump : ∀ i < k * m, dist (Φ (t (i % k)) (Y i)) (Y (i + 1)) < ε1 := by
    intro i hi
    rw [hY i, if_neg (by omega)]
    have hr := Nat.mod_lt i hkpos
    have hjr := hd (i % k) hr
    have hms := d45k_mod_succ k i hkpos
    by_cases hlast : i + 1 = k * m
    · rw [hY (i+1), if_pos hlast]
      rw [hlast, Nat.mul_mod_right] at hms
      have hr1 : i % k + 1 = k := by
        split_ifs at hms with hc <;> omega
      rw [hr1, hyk] at hjr
      linarith
    · rw [hY (i+1), if_neg hlast, hms]
      split_ifs with hc
      · linarith
      · have hr1 : i % k + 1 = k := by omega
        rw [hr1, hyk] at hjr
        calc dist (Φ (t (i % k)) (y (i % k))) (y 0)
            ≤ dist (Φ (t (i % k)) (y (i % k))) x + dist x (y 0) := dist_triangle _ _ _
          _ < ε + ε := add_lt_add hjr (by rw [dist_comm]; exact h0)
          _ ≤ ε1 := by linarith
  refine ⟨k, fun j => Y (j * m), fun j => ∑ r ∈ Finset.range m, t ((j * m + r) % k), hk,
    ?_, ?_, ?_, ?_⟩
  · intro j _
    calc T'' ≤ m * T := hmT
      _ = ∑ r ∈ Finset.range m, T := by simp [Finset.sum_const, Finset.card_range]
      _ ≤ ∑ r ∈ Finset.range m, t ((j * m + r) % k) :=
          Finset.sum_le_sum fun r _ => (hτ _).1
  · show dist (Y (0 * m)) x < δ
    rw [zero_mul, hY, if_neg (by positivity), Nat.zero_mod]
    linarith
  · intro j hj
    have hlt : ∀ r < m, j * m + r < k * m := by
      intro r hr
      calc j * m + r < j * m + m := by omega
        _ = (j + 1) * m := by ring
        _ ≤ k * m := Nat.mul_le_mul_right m hj
    have := hS (fun r => Y (j * m + r)) (fun r => t ((j * m + r) % k))
      (fun r _ => (hτ _).2) (fun r hr => by
        have h' := hjump (j * m + r) (hlt r hr)
        simpa [add_assoc] using h')
    simp only [add_zero] at this
    show dist (Φ (∑ r ∈ Finset.range m, t ((j * m + r) % k)) (Y (j * m))) (Y ((j + 1) * m)) < δ
    rw [show (j + 1) * m = j * m + m by ring]
    exact this
  · show Y (k * m) = x
    rw [hY, if_pos rfl]

theorem d45k_rot {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (ε : ℝ) (T : ℝ≥0) (p : M)
    (k : ℕ) (y : ℕ → M) (t : ℕ → ℝ≥0) (h : IsPseudoOrbit Φ ε T p p k y t) (j : ℕ)
    (hj : j < k) : PseudoOrbitTo Φ (2 * ε) T (y j) (y j) := by
  obtain ⟨hk, ht, h0, hd, hyk⟩ := h
  have hkpos : 0 < k := by omega
  have hε : 0 < ε := lt_of_le_of_lt dist_nonneg h0
  refine ⟨k, fun i => y ((j + i) % k), fun i => t ((j + i) % k), hk,
    fun i _ => ht _ (Nat.mod_lt _ hkpos), ?_, ?_, ?_⟩
  · show dist (y ((j + 0) % k)) (y j) < 2 * ε
    rw [add_zero, Nat.mod_eq_of_lt hj, dist_self]; linarith
  · intro i _
    show dist (Φ (t ((j + i) % k)) (y ((j + i) % k))) (y ((j + (i + 1)) % k)) < 2 * ε
    have hr := Nat.mod_lt (j + i) hkpos
    have hjr := hd _ hr
    rw [← add_assoc, d45k_mod_succ k (j + i) hkpos]
    split_ifs with hc
    · linarith
    · have hr1 : (j + i) % k + 1 = k := by omega
      rw [hr1, hyk] at hjr
      calc dist (Φ (t ((j + i) % k)) (y ((j + i) % k))) (y 0)
          ≤ dist (Φ (t ((j + i) % k)) (y ((j + i) % k))) p + dist p (y 0) :=
            dist_triangle _ _ _
        _ < ε + ε := add_lt_add hjr (by rw [dist_comm]; exact h0)
        _ = 2 * ε := by ring
  · show y ((j + k) % k) = y j
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hj]

theorem d45k_L1 {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (δ : ℝ) (T : ℝ≥0) (x z : M)
    (hxz : dist x z < δ / 2) (h : PseudoOrbitTo Φ (δ / 2) T x x) : PseudoOrbitTo Φ δ T z z := by
  obtain ⟨k, y, t, hk, ht, h0, hd, hyk⟩ := h
  refine ⟨k, fun i => if i = k then z else y i, t, hk, ht, ?_, ?_, ?_⟩
  · show dist (if 0 = k then z else y 0) z < δ
    rw [if_neg (by omega)]
    calc dist (y 0) z ≤ dist (y 0) x + dist x z := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add h0 hxz
      _ = δ := by ring
  · intro j hj
    show dist (Φ (t j) (if j = k then z else y j)) (if j + 1 = k then z else y (j + 1)) < δ
    rw [if_neg (by omega)]
    have hdj := hd j hj
    have hδ : 0 < δ := by linarith [dist_nonneg (x := x) (y := z)]
    split_ifs with h1
    · rw [h1, hyk] at hdj
      calc dist (Φ (t j) (y j)) z ≤ dist (Φ (t j) (y j)) x + dist x z := dist_triangle _ _ _
        _ < δ / 2 + δ / 2 := add_lt_add hdj hxz
        _ = δ := by ring
    · linarith
  · show (if k = k then z else y k) = z
    rw [if_pos rfl]

theorem d45k_mono {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (δ δ' : ℝ) (T : ℝ≥0) (a b : M)
    (h : δ ≤ δ') : PseudoOrbitTo Φ δ T a b → PseudoOrbitTo Φ δ' T a b := by
  rintro ⟨k, y, t, hk, ht, h0, hd, hyk⟩
  exact ⟨k, y, t, hk, ht, lt_of_lt_of_le h0 h, fun j hj => lt_of_lt_of_le (hd j hj) h, hyk⟩

theorem d45k_seq {M : Type*} [MetricSpace M] [CompactSpace M] (Φ : Flow ℝ≥0 M) (T : ℝ≥0)
    (hT : 0 < T) (x : ℕ → M)
    (hx : ∀ n : ℕ, PseudoOrbitTo Φ (1 / ((n:ℝ) + 1)) T (x n) (x n))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (z : M)
    (hz : Filter.Tendsto (x ∘ φ) Filter.atTop (nhds z)) : z ∈ chainRecurrentSet Φ := by
  apply d45k_merge Φ T hT z
  intro ε hε
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hz (ε/2) (by linarith)
  obtain ⟨N2, hN2⟩ := exists_nat_one_div_lt (show 0 < ε/2 by linarith)
  refine d45k_L1 Φ ε T (x (φ (max N1 N2))) z (hN1 _ (le_max_left _ _))
    (d45k_mono Φ _ _ T _ _ ?_ (hx (φ (max N1 N2))))
  have : (N2:ℝ) ≤ φ (max N1 N2) := by
    exact_mod_cast le_trans (le_max_right _ _) (hφ.id_le _)
  calc 1 / ((φ (max N1 N2) : ℝ) + 1) ≤ 1 / ((N2:ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
    _ ≤ ε / 2 := hN2.le

theorem d45k_U {M : Type*} [MetricSpace M] [CompactSpace M] (Φ : Flow ℝ≥0 M) (T : ℝ≥0)
    (hT : 0 < T) (η : ℝ) (hη : 0 < η) :
    ∃ ε > 0, ∀ x, PseudoOrbitTo Φ ε T x x → ∃ r ∈ chainRecurrentSet Φ, dist x r < η := by
  by_contra hcon
  push_neg at hcon
  choose x hx1 hx2 using fun n : ℕ => hcon (1 / ((n:ℝ) + 1)) (by positivity)
  obtain ⟨z, _, φ, hφ, hz⟩ := isCompact_univ.tendsto_subseq (x := x) (fun n => Set.mem_univ _)
  have hzR := d45k_seq Φ T hT x hx1 φ hφ z hz
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hz η hη
  have h1 := hx2 (φ N) z hzR
  have h2 := hN N le_rfl
  simp only [Function.comp_apply] at h2
  linarith

theorem d45k_fwd {M : Type*} [MetricSpace M] [CompactSpace M] (Φ : Flow ℝ≥0 M) (t : ℝ≥0)
    (p : M) (hp : p ∈ chainRecurrentSet Φ) : Φ t p ∈ chainRecurrentSet Φ := by
  intro δ hδ T hT
  obtain ⟨ω, hω, hu⟩ := d45k_unif Φ Set.univ isCompact_univ t (δ/2) (by linarith)
  obtain ⟨k, y, s, hk, hs, h0, hd, hyk⟩ := hp (min ω δ) (lt_min hω hδ) T hT
  refine ⟨k, fun i => Φ t (y i), s, hk, hs, ?_, ?_, ?_⟩
  · have := hu t le_rfl _ (Set.mem_univ _) _ (Set.mem_univ _)
      (lt_of_lt_of_le h0 (min_le_left _ _))
    show dist (Φ t (y 0)) (Φ t p) < δ
    linarith
  · intro j hj
    show dist (Φ (s j) (Φ t (y j))) (Φ t (y (j+1))) < δ
    have e : Φ (s j) (Φ t (y j)) = Φ t (Φ (s j) (y j)) := by
      rw [← Flow.map_add, ← Flow.map_add, add_comm]
    rw [e]
    have := hu t le_rfl _ (Set.mem_univ _) _ (Set.mem_univ _)
      (lt_of_lt_of_le (hd j hj) (min_le_left _ _))
    linarith
  · show Φ t (y k) = Φ t p
    rw [hyk]

theorem d45k_bwd {M : Type*} [MetricSpace M] [CompactSpace M] (Φ : Flow ℝ≥0 M) (t : ℝ≥0)
    (p : M) (hp : p ∈ chainRecurrentSet Φ) : p ∈ Φ t '' chainRecurrentSet Φ := by
  rcases eq_or_ne t 0 with h0 | h0
  · subst h0; exact ⟨p, hp, Flow.map_zero_apply _ _⟩
  have ht : 0 < t := pos_iff_ne_zero.mpr h0
  have hloop : ∀ n : ℕ, ∃ q : M, ∃ s : ℝ≥0, t ≤ s ∧ s ≤ 2 * t ∧
      dist (Φ s q) p < 1 / ((n:ℝ) + 1) ∧ PseudoOrbitTo Φ (1 / ((n:ℝ) + 1)) t q q := by
    intro n
    have hpos : (0:ℝ) < 1 / (2 * ((n:ℝ) + 1)) := by positivity
    obtain ⟨k, y, s, hPO, hs2⟩ := d45k_norm Φ (1 / (2 * ((n:ℝ) + 1))) t p p (hp _ hpos t ht) ht
    have hPO' := hPO
    obtain ⟨hk, hs, h0', hd, hyk⟩ := hPO
    have hhalf : 1 / (2 * ((n:ℝ) + 1)) < 1 / ((n:ℝ) + 1) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    refine ⟨y (k-1), s (k-1), hs _ (by omega), hs2 _ (by omega), ?_, ?_⟩
    · have := hd (k-1) (by omega)
      rw [Nat.sub_add_cancel hk, hyk] at this
      linarith
    · have := d45k_rot Φ _ t p k y s hPO' (k-1) (by omega)
      have e : 2 * (1 / (2 * ((n:ℝ) + 1))) = 1 / ((n:ℝ) + 1) := by field_simp
      rw [e] at this
      exact this
  choose q s hs1 hs2 hd hPO using hloop
  obtain ⟨q0, _, φ, hφ, hq⟩ := isCompact_univ.tendsto_subseq (x := q) (fun n => Set.mem_univ _)
  obtain ⟨s0, hs0, ψ, hψ, hsc⟩ := (isCompact_Icc (a := t) (b := 2 * t)).tendsto_subseq
    (x := fun n => s (φ n)) (fun n => ⟨hs1 _, hs2 _⟩)
  have hq0 : q0 ∈ chainRecurrentSet Φ := d45k_seq Φ t ht q hPO φ hφ q0 hq
  have hconv : Filter.Tendsto (fun n => Φ (s (φ (ψ n))) (q (φ (ψ n)))) Filter.atTop
      (nhds (Φ s0 q0)) :=
    ((Φ.continuous continuous_fst continuous_snd).tendsto (s0, q0)).comp
      (hsc.prodMk_nhds (hq.comp hψ.tendsto_atTop))
  have hconv2 : Filter.Tendsto (fun n => Φ (s (φ (ψ n))) (q (φ (ψ n)))) Filter.atTop
      (nhds p) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => lt_of_lt_of_le (hd _) ?_⟩
    have : (N:ℝ) ≤ φ (ψ n) := by exact_mod_cast le_trans hn ((hφ.comp hψ).id_le n)
    calc 1 / ((φ (ψ n) : ℝ) + 1) ≤ 1 / ((N:ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
      _ ≤ ε := hN.le
  have heq : Φ s0 q0 = p := tendsto_nhds_unique hconv hconv2
  refine ⟨Φ (s0 - t) q0, d45k_fwd Φ (s0 - t) q0 hq0, ?_⟩
  show Φ t (Φ (s0 - t) q0) = p
  rw [← Flow.map_add, add_tsub_cancel_of_le hs0.1, heq]

theorem d45k_nonempty {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
    (Φ : Flow ℝ≥0 M) : (chainRecurrentSet Φ).Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty M›
  obtain ⟨z, _, φ, hφ, hz⟩ := isCompact_univ.tendsto_subseq
    (x := fun n : ℕ => Φ (n : ℝ≥0) x) (fun n => Set.mem_univ _)
  refine ⟨z, fun δ hδ T _ => ?_⟩
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hz δ hδ
  obtain ⟨b, hb⟩ : ∃ b, b = φ N + Nat.ceil T := ⟨_, rfl⟩
  have hbN : N ≤ b := by have h' : N ≤ φ N := hφ.id_le N; omega
  have hφb : ((φ N : ℕ) : ℝ≥0) + T ≤ ((φ b : ℕ) : ℝ≥0) := by
    have h1 : b ≤ φ b := hφ.id_le b
    have h2 : (b : ℝ≥0) = (φ N : ℝ≥0) + (Nat.ceil T : ℝ≥0) := by rw [hb]; push_cast; rfl
    calc ((φ N : ℕ) : ℝ≥0) + T ≤ (φ N : ℝ≥0) + (Nat.ceil T : ℝ≥0) :=
          add_le_add le_rfl (Nat.le_ceil T)
      _ = (b : ℝ≥0) := h2.symm
      _ ≤ (φ b : ℝ≥0) := by exact_mod_cast h1
  have hle : ((φ N : ℕ) : ℝ≥0) ≤ ((φ b : ℕ) : ℝ≥0) := le_trans le_self_add hφb
  refine ⟨1, fun i => if i = 0 then Φ ((φ N : ℕ) : ℝ≥0) x else z,
    fun _ => ((φ b : ℕ) : ℝ≥0) - ((φ N : ℕ) : ℝ≥0), le_rfl,
    fun i _ => le_tsub_of_add_le_left hφb, ?_, ?_, ?_⟩
  · show dist (if (0:ℕ) = 0 then Φ ((φ N : ℕ) : ℝ≥0) x else z) z < δ
    rw [if_pos rfl]
    exact hN N le_rfl
  · intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    show dist (Φ (((φ b : ℕ) : ℝ≥0) - ((φ N : ℕ) : ℝ≥0))
      (if (0:ℕ) = 0 then Φ ((φ N : ℕ) : ℝ≥0) x else z)) (if 0 + 1 = 0 then _ else z) < δ
    rw [if_pos rfl, if_neg (by omega), ← Flow.map_add, tsub_add_cancel_of_le hle]
    exact hN b hbN
  · show (if 1 = 0 then Φ ((φ N : ℕ) : ℝ≥0) x else z) = z
    rw [if_neg (by omega)]

theorem d45k_closed {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) :
    IsClosed (chainRecurrentSet Φ) := by
  apply isClosed_of_closure_subset
  intro z hz δ hδ T hT
  obtain ⟨x, hx, hxz⟩ := Metric.mem_closure_iff.mp hz (δ/2) (by linarith)
  exact d45k_L1 Φ δ T x z (by rw [dist_comm]; exact hxz) (hx (δ/2) (by linarith) T hT)

theorem d45k_core {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
    (Φ : Flow ℝ≥0 M) : IsInternallyChainRecurrent Φ (chainRecurrentSet Φ) := by
  have hinv : IsInvariantSet Φ (chainRecurrentSet Φ) := fun t =>
    Set.Subset.antisymm (by rintro _ ⟨p, hp, rfl⟩; exact d45k_fwd Φ t p hp)
      (fun p hp => d45k_bwd Φ t p hp)
  refine ⟨d45k_nonempty Φ, (d45k_closed Φ).isCompact, hinv, ?_⟩
  intro p δ hδ T hT
  obtain ⟨ω, hω, hu⟩ := d45k_unif Φ Set.univ isCompact_univ (2 * T) (δ/3) (by linarith)
  have hη : 0 < min ω (δ/3) := lt_min hω (by linarith)
  obtain ⟨ε, hε, hU⟩ := d45k_U Φ T hT _ hη
  have hε' : 0 < min ε (δ/3) / 2 := half_pos (lt_min hε (by linarith))
  have hmin1 := min_le_left ε (δ/3)
  have hmin2 := min_le_right ε (δ/3)
  have hmin3 := min_le_left ω (δ/3)
  have hmin4 := min_le_right ω (δ/3)
  have hpR : ChainTo Φ (p : M) (p : M) := p.2
  obtain ⟨k, y, t, hPO, ht2⟩ := d45k_norm Φ (min ε (δ/3) / 2) T p p (hpR _ hε' T hT) hT
  have hPO' := hPO
  obtain ⟨hk, ht, h0, hd, hyk⟩ := hPO
  have hproj : ∀ j, ∃ r ∈ chainRecurrentSet Φ, j < k → dist (y j) r < min ω (δ/3) := by
    intro j
    by_cases hj : j < k
    · obtain ⟨r, hr, hdr⟩ := hU (y j) (d45k_mono Φ _ _ T _ _ (by linarith)
        (d45k_rot Φ _ T p k y t hPO' j hj))
      exact ⟨r, hr, fun _ => hdr⟩
    · exact ⟨p, p.2, fun h => absurd h hj⟩
  choose r hr1 hr2 using hproj
  obtain ⟨z, hz⟩ : ∃ z : ℕ → chainRecurrentSet Φ,
      ∀ j, z j = if j < k then ⟨r j, hr1 j⟩ else p := ⟨_, fun _ => rfl⟩
  refine ⟨k, z, t, hk, ht, ?_, ?_, ?_⟩
  · rw [Subtype.dist_eq, hz 0, if_pos (by omega)]
    have := hr2 0 (by omega)
    calc dist (r 0) (p : M) ≤ dist (r 0) (y 0) + dist (y 0) p := dist_triangle _ _ _
      _ < min ω (δ/3) + min ε (δ/3) / 2 := by
          rw [dist_comm]; exact add_lt_add this h0
      _ ≤ δ := by linarith
  · intro j hj
    rw [Subtype.dist_eq]
    have e1 : ((restrictSemiflow Φ hinv) (t j) (z j) : M) = Φ (t j) (z j : M) := rfl
    rw [e1]
    have hzj : (z j : M) = r j := by rw [hz j, if_pos hj]
    rw [hzj]
    have hA : dist (Φ (t j) (r j)) (Φ (t j) (y j)) < δ/3 :=
      hu (t j) (ht2 j hj) _ (Set.mem_univ _) _ (Set.mem_univ _)
        (by rw [dist_comm]; exact lt_of_lt_of_le (hr2 j hj) hmin3)
    have hB := hd j hj
    have hC : dist (y (j+1)) (z (j+1) : M) < δ/3 := by
      by_cases hj1 : j + 1 < k
      · have e : (z (j+1) : M) = r (j+1) := by rw [hz (j+1), if_pos hj1]
        rw [e]; exact lt_of_lt_of_le (hr2 (j+1) hj1) hmin4
      · have e2 : j + 1 = k := by omega
        have e : (z (j+1) : M) = p := by rw [hz (j+1), if_neg hj1]
        rw [e, e2, hyk, dist_self]; linarith
    calc dist (Φ (t j) (r j)) (z (j+1) : M)
        ≤ dist (Φ (t j) (r j)) (Φ (t j) (y j)) + dist (Φ (t j) (y j)) (y (j+1)) +
          dist (y (j+1)) (z (j+1) : M) := dist_triangle4 _ _ _ _
      _ < δ/3 + δ/3 + δ/3 := by
          have : dist (Φ (t j) (y j)) (y (j+1)) < δ/3 := by linarith
          linarith
      _ = δ := by ring
  · rw [hz k, if_neg (lt_irrefl k)]

end StochApproxDyn.LimitSet

open StochApproxDyn.LimitSet


theorem solution {M : Type*} [MetricSpace M]
    [CompactSpace M] [Nonempty M] (Φ : Flow ℝ≥0 M) :
    IsInternallyChainRecurrent Φ (chainRecurrentSet Φ) := by
  exact d45k_core Φ

-- Prove2me | solution 1 for TaoBR.exists_sparse_cover
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:15:49.013842+00:00
-- url     : https://prove2.me/submissions/4c121d95-565b-4403-af81-4fac986f6a02

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory Metric

namespace TaoBR

/-- The lattice point `k ∈ ℤⁿ` as a point of `E n`. -/
noncomputable def latt {n : ℕ} (k : Fin n → ℤ) : E n := WithLp.toLp 2 (fun i => (k i : ℝ))

lemma latt_apply {n : ℕ} (k : Fin n → ℤ) (i : Fin n) : latt k i = (k i : ℝ) := rfl

lemma latt_injective {n : ℕ} : Function.Injective (latt (n := n)) := by
  intro k k' h
  funext i
  have := congrArg (fun x : E n => x i) h
  simp only [latt_apply] at this
  exact_mod_cast this

lemma cCube_subset_closedBall {n : ℕ} {c : ℝ} (hc : 0 < c) (k : Fin n → ℤ) :
    cCube c k ⊆ closedBall (latt k) (c * Real.sqrt n / 2) := by
  intro x hx
  rw [mem_closedBall, EuclideanSpace.dist_eq]
  have h1 : ∑ i, dist (x i) (latt k i) ^ 2 ≤ ∑ _i : Fin n, (c / 2) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    rw [Real.dist_eq, latt_apply, sq_abs]
    have := hx i
    have h0 : 0 ≤ |x i - k i| := abs_nonneg _
    nlinarith [sq_abs (x i - k i)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  calc Real.sqrt (∑ i, dist (x i) (latt k i) ^ 2) ≤ Real.sqrt (n * (c / 2) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = c * Real.sqrt n / 2 := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]; ring

lemma cCube_eq_preimage {n : ℕ} (b : ℝ) (k : Fin n → ℤ) :
    cCube b k = (WithLp.ofLp (p := 2)) ⁻¹'
      Set.Icc (fun i => (k i : ℝ) - b / 2) (fun i => (k i : ℝ) + b / 2) := by
  ext x
  simp only [cCube, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Pi.le_def, abs_le]
  constructor
  · intro h; exact ⟨fun i => by have := h i; linarith, fun i => by have := h i; linarith⟩
  · intro h i; exact ⟨by have := h.1 i; linarith, by have := h.2 i; linarith⟩

lemma volume_cCube {n : ℕ} {b : ℝ} (hb : 0 ≤ b) (k : Fin n → ℤ) :
    volume (cCube b k) = ENNReal.ofReal (b ^ n) := by
  rw [cCube_eq_preimage, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp only [add_sub_sub_cancel, add_halves, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [ENNReal.ofReal_pow hb]

lemma measurableSet_cCube {n : ℕ} (b : ℝ) (k : Fin n → ℤ) : MeasurableSet (cCube b k) := by
  rw [cCube_eq_preimage]
  exact measurableSet_Icc.preimage (PiLp.volume_preserving_ofLp (Fin n)).measurable

lemma cCube_mono {n : ℕ} {b c : ℝ} (h : b ≤ c) (k : Fin n → ℤ) : cCube b k ⊆ cCube c k := by
  intro x hx i; have := hx i; simp only [cCube, Set.mem_ofPred_eq] at *; linarith [hx i]

lemma cCube_disjoint {n : ℕ} {b : ℝ} (hb : b ≤ 1 / 2) {k k' : Fin n → ℤ} (h : k ≠ k') :
    Disjoint (cCube b k) (cCube b k') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  apply h
  funext i
  have h1 := hx i
  have h2 := hx' i
  have h3 : |((k i - k' i : ℤ) : ℝ)| < 1 := by
    push_cast
    calc |(k i : ℝ) - k' i| = |(x i - k' i) - (x i - k i)| := by ring_nf
      _ ≤ |x i - k' i| + |x i - k i| := abs_sub _ _
      _ < 1 := by linarith
  have h4 : |k i - k' i| < 1 := by exact_mod_cast h3
  have : k i - k' i = 0 := by rw [abs_lt] at h4; omega
  omega

/-- Volume facts about a finite union of `c`-cubes. -/
lemma volume_cubeUnion {n : ℕ} {c : ℝ} (hc : 0 < c) (s : Finset (Fin n → ℤ)) :
    volume (⋃ k ∈ s, cCube c k) < ⊤ ∧
    (s.card : ℝ) * (min c (1 / 2)) ^ n ≤ (volume (⋃ k ∈ s, cCube c k)).toReal := by
  set b := min c (1 / 2)
  have hb0 : 0 ≤ b := le_min hc.le (by norm_num)
  have hfin : volume (⋃ k ∈ s, cCube c k) < ⊤ := by
    calc volume (⋃ k ∈ s, cCube c k) ≤ ∑ k ∈ s, volume (cCube c k) := measure_biUnion_finset_le _ _
      _ < ⊤ := by
        rw [ENNReal.sum_lt_top]; intro k _; rw [volume_cCube hc.le]; exact ENNReal.ofReal_lt_top
  refine ⟨hfin, ?_⟩
  have h1 : volume (⋃ k ∈ s, cCube b k) = ∑ k ∈ s, volume (cCube b k) := by
    apply measure_biUnion_finset
    · intro k _ k' _ hkk'; exact cCube_disjoint (min_le_right _ _) hkk'
    · intro k _; exact measurableSet_cCube _ _
  have h2 : volume (⋃ k ∈ s, cCube b k) ≤ volume (⋃ k ∈ s, cCube c k) := by
    apply measure_mono
    exact Set.biUnion_mono subset_rfl (fun k _ => cCube_mono (min_le_left _ _) k)
  rw [h1] at h2
  simp only [volume_cCube hb0, Finset.sum_const, nsmul_eq_mul] at h2
  have := ENNReal.toReal_mono hfin.ne h2
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast] at this

section Generic

variable {X : Type*} [MetricSpace X]

/-- A maximal `d`-separated subset of a finite set: every point is `< d` from it. -/
lemma exists_net (F : Finset X) {d : ℝ} (hd : 0 < d) :
    ∃ Q ⊆ F, (∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → d ≤ dist q q') ∧ ∀ x ∈ F, ∃ q ∈ Q, dist x q < d := by
  classical
  let G := F.powerset.filter (fun Q => ∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → d ≤ dist q q')
  have hG : G.Nonempty := ⟨∅, by simp [G]⟩
  obtain ⟨Q, hQG, hmax⟩ := G.exists_max_image Finset.card hG
  simp only [G, Finset.mem_filter, Finset.mem_powerset] at hQG
  refine ⟨Q, hQG.1, hQG.2, ?_⟩
  intro x hx
  by_contra hcon
  push Not at hcon
  have hxQ : x ∉ Q := by
    intro h; have := hcon x h; rw [dist_self] at this; linarith
  have hmem : insert x Q ∈ G := by
    simp only [G, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset hx hQG.1, ?_⟩
    intro q hq q' hq' hne
    rw [Finset.mem_insert] at hq hq'
    rcases hq with rfl | hq <;> rcases hq' with rfl | hq'
    · exact absurd rfl hne
    · exact hcon _ hq'
    · rw [dist_comm]; exact hcon _ hq
    · exact hQG.2 q hq q' hq' hne
  have := hmax _ hmem
  rw [Finset.card_insert_of_notMem hxQ] at this
  omega

/-- Greedy colouring: if every point has at most `T` points (itself included) at distance `< d`,
the set splits into `T` classes, each `d`-separated. -/
lemma exists_colouring {d : ℝ} (hd : 0 < d) (T : ℕ) (Q : Finset X)
    (hdeg : ∀ q ∈ Q, (Q.filter (fun q' => dist q q' < d)).card ≤ T) :
    ∃ col : X → ℕ, (∀ q ∈ Q, col q < T) ∧
      ∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → col q = col q' → d ≤ dist q q' := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | @insert a Q haQ ih =>
    have hdeg' : ∀ q ∈ Q, (Q.filter (fun q' => dist q q' < d)).card ≤ T := by
      intro q hq
      refine le_trans (Finset.card_le_card ?_) (hdeg q (Finset.mem_insert_of_mem hq))
      exact Finset.filter_subset_filter _ (Finset.subset_insert _ _)
    obtain ⟨col, hcolT, hcol⟩ := ih hdeg'
    set nb := Q.filter (fun q' => dist a q' < d)
    have hanb : a ∉ nb := fun h => haQ (Finset.mem_filter.1 h).1
    have hnb : nb.card + 1 ≤ T := by
      have h1 := hdeg a (Finset.mem_insert_self _ _)
      have h2 : (insert a Q).filter (fun q' => dist a q' < d) = insert a nb := by
        rw [Finset.filter_insert, if_pos (by rw [dist_self]; exact hd)]
      rw [h2, Finset.card_insert_of_notMem hanb] at h1
      exact h1
    have himg : (nb.image col).card < (Finset.range T).card := by
      rw [Finset.card_range]
      exact lt_of_le_of_lt Finset.card_image_le (by omega)
    obtain ⟨t, htT, htn⟩ := Finset.exists_mem_notMem_of_card_lt_card himg
    rw [Finset.mem_range] at htT
    refine ⟨Function.update col a t, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · simpa using htT
      · have : q ≠ a := fun h => haQ (h ▸ hq)
        rw [Function.update_of_ne this]; exact hcolT q hq
    · have key : ∀ q ∈ Q, col q = t → d ≤ dist a q := by
        intro q hq hqt
        by_contra hlt
        push Not at hlt
        exact htn (Finset.mem_image.2 ⟨q, Finset.mem_filter.2 ⟨hq, hlt⟩, hqt⟩)
      intro q hq q' hq' hne heq
      have hqa : ∀ {y}, y ∈ Q → y ≠ a := fun hy h => haQ (h ▸ hy)
      by_cases ha : q = a <;> by_cases ha' : q' = a
      · exact absurd (ha.trans ha'.symm) hne
      · subst ha
        have hq'Q : q' ∈ Q := (Finset.mem_insert.1 hq').resolve_left ha'
        rw [Function.update_self, Function.update_of_ne ha'] at heq
        exact key q' hq'Q heq.symm
      · subst ha'
        have hqQ : q ∈ Q := (Finset.mem_insert.1 hq).resolve_left ha
        rw [Function.update_self, Function.update_of_ne ha] at heq
        rw [dist_comm]; exact key q hqQ heq
      · have hqQ : q ∈ Q := (Finset.mem_insert.1 hq).resolve_left ha
        have hq'Q : q' ∈ Q := (Finset.mem_insert.1 hq').resolve_left ha'
        rw [Function.update_of_ne ha, Function.update_of_ne ha'] at heq
        exact hcol q hqQ q' hq'Q hne heq

lemma deg_bound (P Q : Finset X) {r R a b : ℝ} (hrR : r + R / 2 ≤ R)
    (hsep : ∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → 2 * r ≤ dist q q') (q : X)
    (hup : ((P.filter (fun y => dist q y < R)).card : ℝ) ≤ b)
    (hlow : ∀ q' ∈ Q, a ≤ ((P.filter (fun y => dist q' y < r)).card : ℝ)) :
    ((Q.filter (fun q' => dist q q' < R / 2)).card : ℝ) * a ≤ b := by
  classical
  set nb := Q.filter (fun q' => dist q q' < R / 2)
  have hdisj : (nb : Set X).PairwiseDisjoint (fun q' => P.filter (fun y => dist q' y < r)) := by
    intro q₁ h₁ q₂ h₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy1 hy2
    have h1 := (Finset.mem_filter.1 hy1).2
    have h2 := (Finset.mem_filter.1 hy2).2
    have := hsep q₁ (Finset.mem_filter.1 h₁).1 q₂ (Finset.mem_filter.1 h₂).1 hne
    have := dist_triangle q₁ y q₂
    rw [dist_comm y q₂] at this
    linarith
  have hsub : nb.biUnion (fun q' => P.filter (fun y => dist q' y < r)) ⊆
      P.filter (fun y => dist q y < R) := by
    intro y hy
    rw [Finset.mem_biUnion] at hy
    obtain ⟨q', hq', hy⟩ := hy
    rw [Finset.mem_filter] at hy hq' ⊢
    refine ⟨hy.1, ?_⟩
    have := dist_triangle q q' y
    linarith [hq'.2, hy.2]
  calc (nb.card : ℝ) * a = ∑ _q' ∈ nb, a := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ q' ∈ nb, ((P.filter (fun y => dist q' y < r)).card : ℝ) :=
        Finset.sum_le_sum (fun q' hq' => hlow q' (Finset.mem_filter.1 hq').1)
    _ = ((nb.biUnion (fun q' => P.filter (fun y => dist q' y < r))).card : ℝ) := by
        rw [Finset.card_biUnion hdisj]; push_cast; rfl
    _ ≤ ((P.filter (fun y => dist q y < R)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ b := hup

/-- Pigeonhole over the scales. -/
lemma exists_level {g : ℕ → ℝ} {θ : ℝ} {N : ℕ} (hN : 1 ≤ N) (hg0 : 1 ≤ g 0)
    (hgN : g N ≤ θ ^ N) : ∃ ℓ < N, g (ℓ + 1) ≤ θ ^ (ℓ + 1) ∧ θ ^ ℓ ≤ g ℓ := by
  by_contra hcon
  push Not at hcon
  have key : ∀ j, j ≤ N - 1 → g (N - j) ≤ θ ^ (N - j) := by
    intro j
    induction j with
    | zero => intro _; simpa using hgN
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 : N - j = (N - (j + 1)) + 1 := by omega
      rw [h2] at h1
      exact (hcon _ (by omega) h1).le
  have h1 := key (N - 1) le_rfl
  have h2 : N - (N - 1) = 0 + 1 := by omega
  rw [h2] at h1
  have := hcon 0 (by omega) h1
  simp at this
  linarith

/-- The multi-scale decomposition (Tao, Lemma 3.3). -/
lemma multiscale (P : Finset X) {N : ℕ} (hN : 1 ≤ N) (hP : P.Nonempty) (ρ : ℕ → ℝ)
    (hρ0 : ∀ k, 0 < ρ k) (hρ2 : ∀ k, 2 * ρ k ≤ ρ (k + 1)) :
    ∃ T : ℕ, (T : ℝ) ≤ (P.card : ℝ) ^ (1 / (N : ℝ)) ∧ ∃ F : ℕ → ℕ → Finset X,
      (∀ ℓ t, F ℓ t ⊆ P) ∧
      (∀ ℓ t, ∀ q ∈ F ℓ t, ∀ q' ∈ F ℓ t, q ≠ q' → ρ (ℓ + 1) / 2 ≤ dist q q') ∧
      ∀ p ∈ P, ∃ ℓ < N, ∃ t < T, ∃ q ∈ F ℓ t, dist p q < 2 * ρ ℓ := by
  classical
  set m : ℝ := (P.card : ℝ)
  have hm1 : 1 ≤ m := by simp only [m]; exact_mod_cast hP.card_pos
  set θ : ℝ := m ^ (1 / (N : ℝ))
  have hθ1 : 1 ≤ θ := Real.one_le_rpow hm1 (by positivity)
  have hθN : θ ^ N = m := by
    simp only [θ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    have : (1 / (N : ℝ)) * N = 1 := by field_simp
    rw [this, Real.rpow_one]
  set g : ℕ → X → ℝ := fun ℓ x => ((P.filter (fun y => dist x y < ρ ℓ)).card : ℝ)
  set Eset : ℕ → Finset X := fun ℓ => P.filter (fun x => g (ℓ + 1) x ≤ θ ^ (ℓ + 1) ∧ θ ^ ℓ ≤ g ℓ x)
  have hnet : ∀ ℓ, ∃ Q ⊆ Eset ℓ, (∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → 2 * ρ ℓ ≤ dist q q') ∧
      ∀ x ∈ Eset ℓ, ∃ q ∈ Q, dist x q < 2 * ρ ℓ := fun ℓ => exists_net _ (by linarith [hρ0 ℓ])
  choose Q hQE hQsep hQcov using hnet
  set T : ℕ := ⌊θ⌋₊
  have hdeg : ∀ ℓ, ∀ q ∈ Q ℓ, ((Q ℓ).filter (fun q' => dist q q' < ρ (ℓ + 1) / 2)).card ≤ T := by
    intro ℓ q hq
    have hqE := (Finset.mem_filter.1 (hQE ℓ hq)).2
    have h := deg_bound P (Q ℓ) (r := ρ ℓ) (R := ρ (ℓ + 1)) (a := θ ^ ℓ) (b := θ ^ (ℓ + 1))
      (by linarith [hρ2 ℓ]) (hQsep ℓ) q hqE.1
      (fun q' hq' => (Finset.mem_filter.1 (hQE ℓ hq')).2.2)
    rw [pow_succ] at h
    have hpos : 0 < θ ^ ℓ := by positivity
    have : (((Q ℓ).filter (fun q' => dist q q' < ρ (ℓ + 1) / 2)).card : ℝ) ≤ θ := by
      nlinarith
    exact Nat.le_floor this
  have hcol : ∀ ℓ, ∃ col : X → ℕ, (∀ q ∈ Q ℓ, col q < T) ∧
      ∀ q ∈ Q ℓ, ∀ q' ∈ Q ℓ, q ≠ q' → col q = col q' → ρ (ℓ + 1) / 2 ≤ dist q q' :=
    fun ℓ => exists_colouring (by linarith [hρ0 (ℓ + 1)]) T (Q ℓ) (hdeg ℓ)
  choose col hcolT hcolsep using hcol
  refine ⟨T, Nat.floor_le (by linarith), fun ℓ t => (Q ℓ).filter (fun q => col ℓ q = t), ?_, ?_, ?_⟩
  · intro ℓ t q hq
    exact (Finset.mem_filter.1 (hQE ℓ (Finset.mem_filter.1 hq).1)).1
  · intro ℓ t q hq q' hq' hne
    rw [Finset.mem_filter] at hq hq'
    exact hcolsep ℓ q hq.1 q' hq'.1 hne (hq.2.trans hq'.2.symm)
  · intro p hp
    have hg0 : 1 ≤ g 0 p := by
      simp only [g]
      have : p ∈ P.filter (fun y => dist p y < ρ 0) := by
        rw [Finset.mem_filter, dist_self]; exact ⟨hp, hρ0 0⟩
      exact_mod_cast Finset.card_pos.2 ⟨p, this⟩
    have hgN : g N p ≤ θ ^ N := by
      rw [hθN]; simp only [g, m]; exact_mod_cast Finset.card_filter_le _ _
    obtain ⟨ℓ, hℓN, hℓ⟩ := exists_level (g := fun k => g k p) hN hg0 hgN
    have hpE : p ∈ Eset ℓ := Finset.mem_filter.2 ⟨hp, hℓ⟩
    obtain ⟨q, hqQ, hpq⟩ := hQcov ℓ p hpE
    exact ⟨ℓ, hℓN, col ℓ q, hcolT ℓ q hqQ, q, Finset.mem_filter.2 ⟨hqQ, rfl⟩, hpq⟩

end Generic

lemma sparse_sep {R M m C₀ C d : ℝ} (hR : 1 ≤ R) (hM : 1 ≤ M) (hMm : M ≤ m) (hC : C₀ ≤ C)
    (hC1 : 0 ≤ C) (hd : (R * m) ^ C ≤ d) : R ^ C₀ * M ^ C₀ ≤ d := by
  rw [← Real.mul_rpow (by linarith) (by linarith)]
  calc (R * M) ^ C₀ ≤ (R * M) ^ C := Real.rpow_le_rpow_of_exponent_le (by nlinarith) hC
    _ ≤ (R * m) ^ C := Real.rpow_le_rpow (by nlinarith) (by nlinarith) hC1
    _ ≤ d := hd

lemma pack {n : ℕ} (C₀ : ℝ) (J : ℕ) (R : Fin J → ℝ) (F : Fin J → Finset (E n))
    (hsep : ∀ j, ∀ q ∈ F j, ∀ q' ∈ F j, q ≠ q' →
      R j ^ C₀ * ((F j).card : ℝ) ^ C₀ ≤ dist q q') :
    ∃ (M : Fin J → ℕ) (x : (j : Fin J) → Fin (M j) → E n), (∀ j, IsSparse C₀ (R j) (x j)) ∧
      (⋃ j, ⋃ y ∈ F j, closedBall y (R j)) ⊆ ⋃ (j) (i), closedBall (x j i) (R j) := by
  refine ⟨fun j => (F j).card, fun j i => ((F j).equivFin.symm i : E n), ?_, ?_⟩
  · intro j i i' hii'
    apply hsep j _ ((F j).equivFin.symm i).2 _ ((F j).equivFin.symm i').2
    intro h
    exact hii' ((F j).equivFin.symm.injective (Subtype.ext h))
  · intro z hz
    simp only [Set.mem_iUnion] at hz ⊢
    obtain ⟨j, y, hy, hz⟩ := hz
    refine ⟨j, (F j).equivFin ⟨y, hy⟩, ?_⟩
    simpa using hz

/-- The scale sequence. -/
noncomputable def scale (r₀ m C : ℝ) : ℕ → ℝ
  | 0 => r₀
  | k + 1 => 2 * (3 * scale r₀ m C k * m) ^ C

lemma scale_props {r₀ m C : ℝ} (hr₀ : 1 ≤ r₀) (hm : 1 ≤ m) (hC : 1 ≤ C) (k : ℕ) :
    1 ≤ scale r₀ m C k ∧ 2 * scale r₀ m C k ≤ scale r₀ m C (k + 1) := by
  induction k with
  | zero =>
    refine ⟨hr₀, ?_⟩
    simp only [scale]
    have h1 : 1 ≤ 3 * r₀ * m := by nlinarith
    have := Real.rpow_le_rpow_of_exponent_le h1 hC
    rw [Real.rpow_one] at this
    nlinarith
  | succ k ih =>
    have h1 : 1 ≤ scale r₀ m C (k + 1) := by linarith [ih.1, ih.2]
    refine ⟨h1, ?_⟩
    show 2 * scale r₀ m C (k + 1) ≤ 2 * (3 * scale r₀ m C (k + 1) * m) ^ C
    have h2 : 1 ≤ 3 * scale r₀ m C (k + 1) * m := by nlinarith
    have := Real.rpow_le_rpow_of_exponent_le h2 hC
    rw [Real.rpow_one] at this
    nlinarith

lemma scale_ge {r₀ m C : ℝ} (hr₀ : 1 ≤ r₀) (hm : 1 ≤ m) (hC : 1 ≤ C) (k : ℕ) :
    r₀ ≤ scale r₀ m C k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have := scale_props hr₀ hm hC k
    linarith

lemma scale_le {r₀ m C D u : ℝ} (hr₀ : 1 ≤ r₀) (hm : 1 ≤ m) (hC : 1 ≤ C) (_hD : 0 ≤ D)
    (hmu : m ≤ D * u) (hu : 6 * D ≤ u) (hu1 : 1 ≤ u) (hr₀u : r₀ ≤ u) (k : ℕ) :
    scale r₀ m C k ≤ u ^ (2 * (2 * C) ^ k) := by
  induction k with
  | zero =>
    simp only [scale, pow_zero, mul_one]
    calc r₀ ≤ u := hr₀u
      _ = u ^ (1 : ℝ) := (Real.rpow_one u).symm
      _ ≤ u ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
  | succ k ih =>
    set e : ℝ := 2 * (2 * C) ^ k
    have he : 2 ≤ e := by
      have : 1 ≤ (2 * C) ^ k := one_le_pow₀ (by linarith)
      simp only [e]; linarith
    have hs1 := (scale_props hr₀ hm hC k).1
    show 2 * (3 * scale r₀ m C k * m) ^ C ≤ u ^ (2 * (2 * C) ^ (k + 1))
    have hupos : 0 < u := by linarith
    have hue : 0 < u ^ e := Real.rpow_pos_of_pos hupos e
    have h1 : 3 * scale r₀ m C k * m ≤ u ^ (e + 2) / 2 := by
      rw [Real.rpow_add hupos, Real.rpow_two]
      have : 3 * scale r₀ m C k * m ≤ 3 * u ^ e * (D * u) := by
        apply mul_le_mul (by linarith) hmu (by linarith) (by positivity)
      have h3 : 3 * u ^ e * (D * u) ≤ u ^ e * (u * u) / 2 := by
        have : u ^ e * u * (6 * D) ≤ u ^ e * u * u :=
          mul_le_mul_of_nonneg_left hu (by positivity)
        nlinarith
      linarith
    have h2 : (3 * scale r₀ m C k * m) ^ C ≤ (u ^ (e + 2) / 2) ^ C :=
      Real.rpow_le_rpow (by positivity) h1 (by linarith)
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hupos.le] at h2
    have h2C : 2 ≤ (2 : ℝ) ^ C := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hC
      rwa [Real.rpow_one] at this
    have hpos : 0 < u ^ ((e + 2) * C) := Real.rpow_pos_of_pos hupos _
    have h3 : 2 * (u ^ ((e + 2) * C) / 2 ^ C) ≤ u ^ ((e + 2) * C) := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have h4 : u ^ ((e + 2) * C) ≤ u ^ (2 * (2 * C) ^ (k + 1)) := by
      apply Real.rpow_le_rpow_of_exponent_le hu1
      have : 2 * (2 * C) ^ (k + 1) = e * (2 * C) := by simp only [e]; ring
      rw [this]
      nlinarith
    linarith

theorem exists_sparse_cover_dev (n : ℕ) (hn : 2 ≤ n) (c : ℝ) (hc : 0 < c) (C₀ : ℝ) :
    ∃ A C₁ : ℝ, ∀ S : Set (E n), IsCubeUnion c S → ∀ N : ℕ, 1 ≤ N →
      ∃ (J : ℕ) (R : Fin J → ℝ) (M : Fin J → ℕ) (x : (j : Fin J) → Fin (M j) → E n),
        (J : ℝ) ≤ A * N * (volume S).toReal ^ (1 / (N : ℝ)) ∧
        (∀ j, 1 ≤ R j ∧ R j ≤ A * (max 1 (volume S).toReal) ^ (C₁ ^ N) ∧ IsSparse C₀ (R j) (x j)) ∧
        S ⊆ ⋃ (j) (i), closedBall (x j i) (R j) := by
  classical
  set b : ℝ := min c (1 / 2) with hb
  have hb0 : 0 < b := lt_min hc (by norm_num)
  have hb1 : b ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  set D : ℝ := (b ^ n)⁻¹ with hD
  have hbn0 : 0 < b ^ n := pow_pos hb0 n
  have hbn1 : b ^ n ≤ 1 := pow_le_one₀ hb0.le hb1
  have hD1 : 1 ≤ D := one_le_inv₀ hbn0 |>.2 hbn1
  set r₀ : ℝ := max 1 (c * Real.sqrt n) with hr₀
  have hr₀1 : 1 ≤ r₀ := le_max_left _ _
  set B : ℝ := max 6 r₀ with hB
  have hB6 : 6 ≤ B := le_max_left _ _
  have hBr : r₀ ≤ B := le_max_right _ _
  set C : ℝ := max C₀ 1 with hC
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCC : C₀ ≤ C := le_max_left _ _
  set A : ℝ := max (max 3 D) (B * D ^ 3) with hA
  have hA3 : 3 ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hAD : D ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
  have hABD : B * D ^ 3 ≤ A := le_max_right _ _
  refine ⟨A, 4 * C, ?_⟩
  rintro S ⟨s, rfl⟩ N hN
  obtain ⟨hfin, hvol⟩ := volume_cubeUnion hc s
  set V : ℝ := (volume (⋃ k ∈ s, cCube c k)).toReal with hV
  set u : ℝ := max 1 V with hu
  have hu1 : 1 ≤ u := le_max_left _ _
  have hVu : V ≤ u := le_max_right _ _
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hVN0 : 0 ≤ V ^ (1 / (N : ℝ)) := Real.rpow_nonneg hV0 _
  have hcover0 : ∀ k ∈ s, ∀ z ∈ cCube c k, dist z (latt k) ≤ r₀ / 2 := by
    intro k _ z hz
    have := cCube_subset_closedBall hc k hz
    rw [mem_closedBall] at this
    have : c * Real.sqrt n ≤ r₀ := le_max_right _ _
    linarith
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs
    refine ⟨0, Fin.elim0, Fin.elim0, fun j => Fin.elim0 j, ?_, fun j => Fin.elim0 j, ?_⟩
    · simp only [Nat.cast_zero]; positivity
    · simp
  have hm1 : (1 : ℝ) ≤ s.card := by exact_mod_cast hs.card_pos
  have hmV : (s.card : ℝ) ≤ D * V := by
    rw [hD, inv_mul_eq_div, le_div_iff₀ hbn0]; exact hvol
  have hmu : (s.card : ℝ) ≤ D * u := le_trans hmV (mul_le_mul_of_nonneg_left hVu (by linarith))
  by_cases hsmall : u < B * D
  · -- few cubes: one ball per cube
    refine ⟨s.card, ?_⟩
    obtain ⟨M, x, hsp, hcov⟩ := pack C₀ s.card (fun _ => r₀)
      (fun j => {latt (s.equivFin.symm j : Fin n → ℤ)}) (by
        intro j q hq q' hq' hne
        rw [Finset.mem_singleton] at hq hq'
        exact absurd (hq.trans hq'.symm) hne)
    refine ⟨fun _ => r₀, M, x, ?_, ?_, ?_⟩
    · -- counting
      have hVlow : D⁻¹ ≤ V := by
        rw [hD, inv_inv]; nlinarith
      have hVN : D⁻¹ ≤ V ^ (1 / (N : ℝ)) := by
        rcases le_or_gt 1 V with h | h
        · have : 1 ≤ V ^ (1 / (N : ℝ)) := Real.one_le_rpow h (by positivity)
          have : D⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD1
          linarith
        · have h1N : 1 / (N : ℝ) ≤ 1 := by
            rw [div_le_one hNpos]; exact_mod_cast hN
          have := Real.rpow_le_rpow_of_exponent_ge
            (lt_of_lt_of_le (inv_pos.2 (by linarith)) hVlow) h.le h1N
          rw [Real.rpow_one] at this
          linarith
      have hmBD : (s.card : ℝ) ≤ B * D ^ 2 := by
        have : D * u ≤ D * (B * D) := mul_le_mul_of_nonneg_left hsmall.le (by linarith)
        nlinarith
      have hDpos : 0 < D := by linarith
      calc (s.card : ℝ) ≤ B * D ^ 3 * D⁻¹ := by
            rw [pow_succ, mul_assoc B, mul_assoc, mul_inv_cancel₀ hDpos.ne', mul_one]; exact hmBD
        _ ≤ A * 1 * V ^ (1 / (N : ℝ)) := by
            rw [mul_one]
            exact mul_le_mul hABD hVN (by positivity) (by linarith)
        _ ≤ A * N * V ^ (1 / (N : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ hVN0
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            exact_mod_cast hN
    · intro j
      refine ⟨hr₀1, ?_, hsp j⟩
      have h1 : 1 ≤ u ^ ((4 * C) ^ N) := Real.one_le_rpow hu1 (by positivity)
      have h2 : r₀ ≤ A := by
        have : B ≤ B * D ^ 3 := le_mul_of_one_le_right (by linarith) (one_le_pow₀ hD1)
        linarith
      nlinarith
    · intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨k, hk, hz⟩ := hz
      apply hcov
      simp only [Set.mem_iUnion]
      refine ⟨s.equivFin ⟨k, hk⟩, latt k, ?_, ?_⟩
      · simp
      · rw [mem_closedBall]
        have := hcover0 k hk z hz
        linarith
  · -- many cubes: the multi-scale argument
    push Not at hsmall
    set m : ℝ := (s.card : ℝ) with hm
    set P : Finset (E n) := s.image latt with hP
    have hPcard : P.card = s.card := Finset.card_image_of_injective _ latt_injective
    have hPne : P.Nonempty := hs.image _
    set ρ : ℕ → ℝ := scale r₀ m C with hρ
    have hρ1 : ∀ k, 1 ≤ ρ k := fun k => (scale_props hr₀1 hm1 hC1 k).1
    have hρr : ∀ k, r₀ ≤ ρ k := fun k => scale_ge hr₀1 hm1 hC1 k
    obtain ⟨T, hT, F, hFP, hFsep, hFcov⟩ := multiscale P hN hPne ρ
      (fun k => by linarith [hρ1 k]) (fun k => (scale_props hr₀1 hm1 hC1 k).2)
    rw [hPcard] at hT
    let e : Fin (N * T) ≃ Fin N × Fin T := finProdFinEquiv.symm
    obtain ⟨M, x, hsp, hcov⟩ := pack C₀ (N * T) (fun j => 3 * ρ (e j).1)
      (fun j => F (e j).1 (e j).2) (by
        intro j q hq q' hq' hne
        have hcard1 : (1 : ℝ) ≤ (F (e j).1 (e j).2).card := by
          exact_mod_cast Finset.card_pos.2 ⟨q, hq⟩
        have hcardm : ((F (e j).1 (e j).2).card : ℝ) ≤ m := by
          rw [hm, ← hPcard]; exact_mod_cast Finset.card_le_card (hFP _ _)
        apply sparse_sep (C := C) (m := m) (by linarith [hρ1 (e j).1]) hcard1 hcardm hCC
          (by linarith)
        have := hFsep (e j).1 (e j).2 q hq q' hq' hne
        have h2 : ρ ((e j).1 + 1) / 2 = (3 * ρ (e j).1 * m) ^ C := by
          simp only [hρ, scale]; ring
        linarith)
    refine ⟨N * T, fun j => 3 * ρ (e j).1, M, x, ?_, ?_, ?_⟩
    · -- counting
      have h1N : 1 / (N : ℝ) ≤ 1 := by
        rw [div_le_one hNpos]; exact_mod_cast hN
      have h1 : m ^ (1 / (N : ℝ)) ≤ (D * V) ^ (1 / (N : ℝ)) :=
        Real.rpow_le_rpow (by linarith) hmV (by positivity)
      rw [Real.mul_rpow (by linarith) hV0] at h1
      have h2 : D ^ (1 / (N : ℝ)) ≤ D := by
        have := Real.rpow_le_rpow_of_exponent_le hD1 h1N
        rwa [Real.rpow_one] at this
      have h3 : (T : ℝ) ≤ A * V ^ (1 / (N : ℝ)) := by
        calc (T : ℝ) ≤ D ^ (1 / (N : ℝ)) * V ^ (1 / (N : ℝ)) := le_trans hT h1
          _ ≤ A * V ^ (1 / (N : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_trans h2 hAD) hVN0
      push_cast
      calc (N : ℝ) * T ≤ N * (A * V ^ (1 / (N : ℝ))) :=
            mul_le_mul_of_nonneg_left h3 hNpos.le
        _ = A * N * V ^ (1 / (N : ℝ)) := by ring
    · intro j
      refine ⟨by linarith [hρ1 (e j).1], ?_, hsp j⟩
      have h6D : 6 * D ≤ u := by nlinarith
      have hr₀u : r₀ ≤ u := by nlinarith
      have h1 := scale_le hr₀1 hm1 hC1 (by linarith) hmu h6D hu1 hr₀u (e j).1
      have hℓ : ((e j).1 : ℕ) ≤ N := (e j).1.2.le
      have h2 : u ^ (2 * (2 * C) ^ ((e j).1 : ℕ)) ≤ u ^ ((4 * C) ^ N) := by
        apply Real.rpow_le_rpow_of_exponent_le hu1
        have ha : (2 * C) ^ ((e j).1 : ℕ) ≤ (2 * C) ^ N := pow_le_pow_right₀ (by linarith) hℓ
        have hb2 : (2 : ℝ) ≤ 2 ^ N := by
          calc (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
        have : (4 * C) ^ N = 2 ^ N * (2 * C) ^ N := by rw [← mul_pow]; ring
        rw [this]
        have : 0 ≤ (2 * C) ^ N := by positivity
        nlinarith
      have h3 : 0 ≤ u ^ ((4 * C) ^ N) := by positivity
      show 3 * scale r₀ m C ((e j).1 : ℕ) ≤ A * u ^ ((4 * C) ^ N)
      have h4 : scale r₀ m C ((e j).1 : ℕ) ≤ u ^ ((4 * C) ^ N) := le_trans h1 h2
      calc 3 * scale r₀ m C ((e j).1 : ℕ) ≤ 3 * u ^ ((4 * C) ^ N) := by linarith
        _ ≤ A * u ^ ((4 * C) ^ N) := mul_le_mul_of_nonneg_right hA3 h3
    · intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨k, hk, hz⟩ := hz
      have hkP : latt k ∈ P := Finset.mem_image_of_mem _ hk
      obtain ⟨ℓ, hℓN, t, htT, q, hq, hdq⟩ := hFcov _ hkP
      apply hcov
      simp only [Set.mem_iUnion]
      refine ⟨e.symm (⟨ℓ, hℓN⟩, ⟨t, htT⟩), q, ?_, ?_⟩
      · simpa using hq
      · rw [mem_closedBall]
        have h1 := hcover0 k hk z hz
        have h2 := dist_triangle z (latt k) q
        have h3 := hρr ℓ
        simp only [Equiv.apply_symm_apply]
        linarith

end TaoBR

theorem solution : type_of% @TaoBR.exists_sparse_cover_dev := @TaoBR.exists_sparse_cover_dev

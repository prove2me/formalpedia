-- Prove2me | solution 1 for RiskUncSets.Distortion.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:19:42.928493+00:00
-- url     : https://prove2.me/submissions/4e904d0e-ddde-4e80-a57c-25cddfd1cfb7

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

open RiskUncSets.Distortion Finset MeasureTheory



/-- rearrangement: antitone weights, sorted (monotone) arrangement is maximal for `∑ q_i (-X_i)`. -/
theorem ru83_rearr {N : ℕ} (q X : Fin N → ℝ) (hq : Antitone q) (π σ : Equiv.Perm (Fin N))
    (hπ : Monotone (X ∘ π)) :
    ∑ i, q i * (-X (σ i)) ≤ ∑ i, q i * (-X (π i)) := by
  have hg : Antitone (fun i => -X (π i)) := fun a b hab => by
    have := hπ hab; simp only [Function.comp] at this; linarith
  have hmv : Monovary q (fun i => -X (π i)) := hq.monovary hg
  have := hmv.sum_mul_comp_perm_le_sum_mul (σ := σ.trans π.symm)
  simpa using this

theorem ru83_reindex {N : ℕ} (f h : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    ∑ i, f (σ i) * h i = ∑ j, f j * h (σ.symm j) := by
  rw [← Equiv.sum_comp σ.symm]; simp

theorem ru83_muQ_generates {N : ℕ} (q : Fin N → ℝ) (hq : q ∈ restrictedSimplex N) :
    Generates (Set.range fun σ : Equiv.Perm (Fin N) => q ∘ σ) (muQ q) := by
  obtain ⟨⟨hq0, hq1⟩, hqa⟩ := hq
  refine ⟨?_, fun X => ?_⟩
  · rintro _ ⟨σ, rfl⟩
    refine ⟨fun i => hq0 _, ?_⟩
    simp only [Function.comp]
    rw [Equiv.sum_comp σ q, hq1]
  · have hτ : Monotone (X ∘ Tuple.sort X) := Tuple.monotone_sort X
    have hS : muQ q X = ∑ i, q i * (-X (Tuple.sort X i)) := by
      simp [muQ, mul_neg, sum_neg_distrib]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
      simp only [Function.comp]
      rw [ru83_reindex q (fun i => -X i) σ, hS]
      exact ru83_rearr q X hqa _ _ hτ
    · intro b hb
      apply hb
      refine ⟨q ∘ (Tuple.sort X).symm, ⟨(Tuple.sort X).symm, rfl⟩, ?_⟩
      simp only [Function.comp]
      rw [ru83_reindex q (fun i => -X i) (Tuple.sort X).symm, hS]
      simp



theorem ru83_gen_le {N : ℕ} {Q : Set (Fin N → ℝ)} {μ : (Fin N → ℝ) → ℝ} (h : Generates Q μ)
    (X : Fin N → ℝ) {q : Fin N → ℝ} (hq : q ∈ Q) : ∑ i, q i * (-X i) ≤ μ X :=
  (h.2 X).1 ⟨q, hq, rfl⟩

theorem ru83_gen_ub {N : ℕ} {Q : Set (Fin N → ℝ)} {μ : (Fin N → ℝ) → ℝ} (h : Generates Q μ)
    (X : Fin N → ℝ) (c : ℝ) (hc : ∀ q ∈ Q, ∑ i, q i * (-X i) ≤ c) : μ X ≤ c :=
  (h.2 X).2 (by rintro _ ⟨q, hq, rfl⟩; exact hc q hq)

theorem ru83_gen_nonempty {N : ℕ} {Q : Set (Fin N → ℝ)} {μ : (Fin N → ℝ) → ℝ}
    (h : Generates Q μ) : Q.Nonempty := by
  by_contra hQ
  rw [Set.not_nonempty_iff_eq_empty] at hQ
  have := ru83_gen_ub h 0 (μ 0 - 1) (by simp [hQ])
  linarith

theorem ru83_gen_coherent {N : ℕ} {Q : Set (Fin N → ℝ)} {μ : (Fin N → ℝ) → ℝ}
    (h : Generates Q μ) : IsCoherent μ := by
  obtain ⟨q0, hq0⟩ := ru83_gen_nonempty h
  have hsum : ∀ q ∈ Q, ∑ i, q i = 1 := fun q hq => (h.1 hq).2
  have hnn : ∀ q ∈ Q, ∀ i, 0 ≤ q i := fun q hq => (h.1 hq).1
  refine ⟨⟨fun X Y hXY => ?_, fun X c => ?_⟩, fun X Y t ht0 ht1 => ?_, fun X t ht => ?_⟩
  · refine ru83_gen_ub h X _ fun q hq => le_trans ?_ (ru83_gen_le h Y hq)
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by linarith [hXY i]) (hnn q hq i)
  · have hv : ∀ q ∈ Q, ∑ i, q i * (-(X i + c)) = ∑ i, q i * (-X i) - c := fun q hq => by
      simp only [neg_add, mul_add, sum_add_distrib, ← sum_mul, hsum q hq]; ring
    apply le_antisymm
    · refine ru83_gen_ub h _ _ fun q hq => ?_
      rw [hv q hq]; linarith [ru83_gen_le h X hq]
    · have : μ X ≤ μ (fun i => X i + c) + c := ru83_gen_ub h X _ fun q hq => by
        have := ru83_gen_le h (fun i => X i + c) hq
        rw [hv q hq] at this; linarith
      linarith
  · refine ru83_gen_ub h _ _ fun q hq => ?_
    have e : ∑ i, q i * (-(t • X + (1 - t) • Y) i) =
        t * ∑ i, q i * (-X i) + (1 - t) * ∑ i, q i * (-Y i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => by ring
    rw [e]
    have h1 := ru83_gen_le h X hq
    have h2 := ru83_gen_le h Y hq
    nlinarith
  · have e : ∀ q : Fin N → ℝ, ∑ i, q i * (-(t • X) i) = t * ∑ i, q i * (-X i) := fun q => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      refine sum_congr rfl fun i _ => by ring
    rcases ht.eq_or_lt with rfl | htp
    · simp only [zero_mul]
      apply le_antisymm
      · exact ru83_gen_ub h _ _ fun q hq => by rw [e]; simp
      · have := ru83_gen_le h ((0:ℝ) • X) hq0; rw [e] at this; simpa using this
    · apply le_antisymm
      · exact ru83_gen_ub h _ _ fun q hq => by
          rw [e]; exact mul_le_mul_of_nonneg_left (ru83_gen_le h X hq) ht
      · have : μ X ≤ (1 / t) * μ (t • X) := ru83_gen_ub h X _ fun q hq => by
          have := ru83_gen_le h (t • X) hq
          rw [e] at this
          rw [one_div, ← div_eq_inv_mul, le_div_iff₀ htp]; linarith
        have h2 := mul_le_mul_of_nonneg_left this ht
        rw [← mul_assoc, mul_one_div_cancel htp.ne', one_mul] at h2
        exact h2



theorem ru83_count_perm {N : ℕ} (X : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (t : ℝ) :
    (univ.filter (fun i => X (σ i) ≤ t)).card = (univ.filter (fun i => X i ≤ t)).card := by
  rw [card_filter, card_filter]
  exact Equiv.sum_comp σ (fun i => if X i ≤ t then 1 else 0)

theorem ru83_sameDist_iff {N : ℕ} (hN : 0 < N) (X Y : Fin N → ℝ) :
    SameDistribution (uniform N) X Y ↔ ∀ t, (univ.filter (fun i => X i ≤ t)).card =
      (univ.filter (fun i => Y i ≤ t)).card := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [SameDistribution, uniform, sum_const, nsmul_eq_mul]
  constructor
  · intro h t; have := h t
    have h2 := mul_right_cancel₀ (one_div_ne_zero hNr) this
    exact_mod_cast h2
  · intro h t; rw [h t]

theorem ru83_law_perm {N : ℕ} (hN : 0 < N) {μ : (Fin N → ℝ) → ℝ}
    (h : IsLawInvariant (uniform N) μ) (X : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    μ (X ∘ σ) = μ X :=
  h _ _ ((ru83_sameDist_iff hN _ _).2 fun t => ru83_count_perm X σ t)

/-- two monotone tuples with equal counting functions are equal -/
theorem ru83_mono_eq_aux {N : ℕ} (a b : Fin N → ℝ) (ha : Monotone a) (hb : Monotone b)
    (k : Fin N) (hlt : ∀ i < k, a i = b i) (hk : a k < b k) :
    (univ.filter (fun i => a i ≤ a k)).card ≠ (univ.filter (fun i => b i ≤ a k)).card := by
  have h1 : Iic k ⊆ univ.filter (fun i => a i ≤ a k) := fun i hi => by
    simp only [mem_Iic] at hi; simp [ha hi]
  have h2 : univ.filter (fun i => b i ≤ a k) ⊆ Iio k := fun i hi => by
    simp only [mem_filter, mem_univ, true_and] at hi
    simp only [mem_Iio]
    by_contra hc; push_neg at hc
    have := hb hc; linarith
  have c1 := card_le_card h1
  have c2 := card_le_card h2
  rw [Fin.card_Iic] at c1; rw [Fin.card_Iio] at c2
  omega

theorem ru83_mono_eq {N : ℕ} (a b : Fin N → ℝ) (ha : Monotone a) (hb : Monotone b)
    (h : ∀ t, (univ.filter (fun i => a i ≤ t)).card = (univ.filter (fun i => b i ≤ t)).card) :
    a = b := by
  by_contra hne
  have hs : (univ.filter (fun i => a i ≠ b i)).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne; exact ⟨i, by simp [hi]⟩
  set k := (univ.filter (fun i => a i ≠ b i)).min' hs
  have hkm : a k ≠ b k := by
    have := min'_mem _ hs; simpa using this
  have hlt : ∀ i < k, a i = b i := fun i hi => by
    by_contra hc
    have := min'_le (univ.filter (fun i => a i ≠ b i)) i (by simp [hc])
    exact absurd hi (not_lt.2 this)
  rcases lt_or_gt_of_ne hkm with hk | hk
  · exact ru83_mono_eq_aux a b ha hb k hlt hk (h _)
  · exact ru83_mono_eq_aux b a hb ha k (fun i hi => (hlt i hi).symm) hk (h _).symm

theorem ru83_muQ_eq_of_mono {N : ℕ} (q X : Fin N → ℝ) (π : Equiv.Perm (Fin N))
    (hπ : Monotone (X ∘ π)) : muQ q X = -∑ i, q i * X (π i) := by
  have := Tuple.comp_sort_eq_comp_iff_monotone.2 hπ
  simp only [muQ]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  have := congrFun this i
  simp only [Function.comp] at this
  rw [this]

theorem ru83_muQ_law {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ) : IsLawInvariant (uniform N) (muQ q) := by
  intro X Y hXY
  have hc := (ru83_sameDist_iff hN X Y).1 hXY
  have heq : X ∘ Tuple.sort X = Y ∘ Tuple.sort Y := by
    refine ru83_mono_eq _ _ (Tuple.monotone_sort X) (Tuple.monotone_sort Y) fun t => ?_
    have := ru83_count_perm X (Tuple.sort X) t
    have := ru83_count_perm Y (Tuple.sort Y) t
    simp only [Function.comp]
    rw [ru83_count_perm X, ru83_count_perm Y, hc t]
  simp only [muQ]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  have := congrFun heq i
  simp only [Function.comp] at this
  rw [this]

theorem ru83_common_sort {N : ℕ} (X Y : Fin N → ℝ) (h : Comonotone X Y) :
    ∃ π : Equiv.Perm (Fin N), Monotone (X ∘ π) ∧ Monotone (Y ∘ π) := by
  set f : Fin N → ℝ ×ₗ ℝ := fun i => toLex (X i, Y i)
  refine ⟨Tuple.sort f, fun i j hij => ?_, fun i j hij => ?_⟩
  · have := Prod.Lex.monotone_fst _ _ (Tuple.monotone_sort f hij)
    simpa [f] using this
  · have := Prod.Lex.le_iff.1 (Tuple.monotone_sort f hij)
    simp only [Function.comp, f, ofLex_toLex] at this ⊢
    rcases this with h1 | ⟨_, h2⟩
    · have := h (Tuple.sort f i) (Tuple.sort f j)
      by_contra hc; push_neg at hc
      nlinarith
    · exact h2

theorem ru83_muQ_comon {N : ℕ} (q : Fin N → ℝ) : IsComonotonic (muQ q) := by
  intro X Y h
  obtain ⟨π, hX, hY⟩ := ru83_common_sort X Y h
  have hXY : Monotone ((X + Y) ∘ π) := fun i j hij => by
    have := hX hij; have := hY hij; simp only [Function.comp, Pi.add_apply] at *; linarith
  rw [ru83_muQ_eq_of_mono q X π hX, ru83_muQ_eq_of_mono q Y π hY, ru83_muQ_eq_of_mono q _ π hXY]
  simp only [Pi.add_apply, mul_add, sum_add_distrib]; ring

theorem ru83_muQ_distortion {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ) (hq : q ∈ restrictedSimplex N) :
    IsDistortion (uniform N) (muQ q) :=
  ⟨ru83_gen_coherent (ru83_muQ_generates q hq), ru83_muQ_comon q, ru83_muQ_law hN q⟩



theorem ru83_mono_comon {N : ℕ} (A B : Fin N → ℝ) (hA : Monotone A) (hB : Monotone B) :
    Comonotone A B := by
  intro ω ω'
  rcases le_total ω ω' with h | h
  · have := hA h; have := hB h; nlinarith
  · have := hA h; have := hB h; nlinarith

/-- indicator of the index-upper set `{j | k ≤ j}` -/
noncomputable def ru83E (N k : ℕ) : Fin N → ℝ := fun j => if k ≤ (j : ℕ) then 1 else 0

theorem ru83E_mono (N k : ℕ) : Monotone (ru83E N k) := fun i j hij => by
  have : (i : ℕ) ≤ j := hij
  simp only [ru83E]; split_ifs <;> first | omega | norm_num

theorem ru83_distortion_muQ {N : ℕ} (hN : 0 < N) (μ : (Fin N → ℝ) → ℝ)
    (hD : IsDistortion (uniform N) μ) : ∃ q ∈ restrictedSimplex N, ∀ X, μ X = muQ q X := by
  obtain ⟨⟨⟨hmono, htrans⟩, hconv, hhom⟩, hcom, hlaw⟩ := hD
  have μ0 : μ 0 = 0 := by
    have := hhom 0 0 le_rfl; simpa using this
  have μc : ∀ c : ℝ, μ (fun _ => c) = -c := fun c => by
    have := htrans 0 c; simp only [Pi.zero_apply, zero_add] at this; rw [this, μ0]; ring
  have hsum_mono : ∀ (W : ℕ → Fin N → ℝ) (n : ℕ), (∀ k < n, Monotone (W k)) →
      Monotone (∑ k ∈ range n, W k) := by
    intro W n hW i j hij
    simp only [Finset.sum_apply]
    exact sum_le_sum fun k hk => hW k (mem_range.1 hk) hij
  have hadd : ∀ (W : ℕ → Fin N → ℝ) (n : ℕ), (∀ k < n, Monotone (W k)) →
      μ (∑ k ∈ range n, W k) = ∑ k ∈ range n, μ (W k) := by
    intro W n hW
    induction n with
    | zero => simp [μ0]
    | succ n ih =>
      rw [sum_range_succ, sum_range_succ,
        hcom _ _ (ru83_mono_comon _ _ (hsum_mono W n fun k hk => hW k (by omega)) (hW n (by omega))),
        ih fun k hk => hW k (by omega)]
  set φ : ℕ → ℝ := fun k => -μ (ru83E N k) with hφ
  set Q : ℕ → ℝ := fun n => φ n - φ (n + 1) with hQ
  have hE0 : ru83E N 0 = fun _ => 1 := by funext j; simp [ru83E]
  have hEN : ru83E N N = 0 := by funext j; simp [ru83E, j.2]
  have φ0 : φ 0 = 1 := by simp [hφ, hE0, μc]
  have φN : φ N = 0 := by simp [hφ, hEN, μ0]
  have hφanti : ∀ n, φ (n + 1) ≤ φ n := fun n => by
    simp only [hφ, neg_le_neg_iff]
    exact hmono _ _ fun i => by simp only [ru83E]; split_ifs <;> first | omega | norm_num
  -- formula for monotone Z
  have hmain : ∀ Z : Fin N → ℝ, Monotone Z → μ Z = -∑ i : Fin N, Q i * Z i := by
    intro Z hZ
    set Z' : ℕ → ℝ := fun n => if h : n < N then Z ⟨n, h⟩ else 0 with hZ'
    set d : ℕ → ℝ := fun k => Z' k - (if k = 0 then 0 else Z' (k - 1)) with hd
    set W : ℕ → Fin N → ℝ := fun k j => d k * ru83E N k j with hW
    have hdecomp : Z = ∑ k ∈ range N, W k := by
      funext j
      simp only [Finset.sum_apply, hW, ru83E, mul_ite, mul_one, mul_zero]
      rw [← sum_filter]
      have hf : (range N).filter (fun k => k ≤ (j : ℕ)) = range ((j : ℕ) + 1) := by
        ext k; simp only [mem_filter, mem_range]; have := j.2; omega
      rw [hf]
      have tele : ∀ m, m < N → ∑ x ∈ range (m + 1), d x = Z' m := by
        intro m
        induction m with
        | zero => intro _; simp [hd]
        | succ m ih =>
          intro hm
          rw [sum_range_succ, ih (by omega)]
          simp [hd]
      rw [tele j j.2]
      simp [hZ', j.2]
    have hdpos : ∀ k, 0 < k → k < N → 0 ≤ d k := by
      intro k hkpos hk
      simp only [hd, if_neg hkpos.ne', hZ', dif_pos hk, dif_pos (show k - 1 < N by omega)]
      have := hZ (show (⟨k - 1, by omega⟩ : Fin N) ≤ ⟨k, hk⟩ from by
        show k - 1 ≤ k; omega)
      linarith
    have hWmono : ∀ k < N, Monotone (W k) := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · intro i j _; simp [hW, hE0]
      · intro i j hij
        exact mul_le_mul_of_nonneg_left (ru83E_mono N k hij) (hdpos k hkpos hk)
    have hWval : ∀ k < N, μ (W k) = -(d k * φ k) := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · have : W 0 = fun _ => d 0 := by funext j; simp [hW, hE0]
        rw [this, μc, φ0]; ring
      · have : W k = d k • ru83E N k := by funext j; simp [hW]
        rw [this, hhom _ _ (hdpos k hkpos hk)]; simp [hφ]
    have hμZ : μ Z = -∑ k ∈ range N, d k * φ k := by
      conv_lhs => rw [hdecomp]
      rw [hadd W N hWmono, ← sum_neg_distrib]
      exact sum_congr rfl fun k hk => hWval k (mem_range.1 hk)
    have abel : ∀ n, ∑ k ∈ range n, d k * φ k =
        ∑ i ∈ range n, Q i * Z' i + φ n * (if n = 0 then 0 else Z' (n - 1)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [sum_range_succ, ih, sum_range_succ]
        simp only [hd, hQ, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
        ring
    have hfin : ∑ i : Fin N, Q i * Z i = ∑ i ∈ range N, Q i * Z' i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => Q i * Z' i) N]
      exact sum_congr rfl fun i _ => by simp [hZ', i.2]
    rw [hμZ, abel N, φN, hfin]; simp
  have hsubadd : ∀ A B : Fin N → ℝ, μ (A + B) ≤ μ A + μ B := by
    intro A B
    have h1 := hconv A B (1/2) (by norm_num) (by norm_num)
    have h2 := hhom ((1/2:ℝ) • A + (1 - 1/2 : ℝ) • B) 2 (by norm_num)
    have : (2:ℝ) • ((1/2:ℝ) • A + (1 - 1/2 : ℝ) • B) = A + B := by
      funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this] at h2; linarith
  have hQstep : ∀ n, n + 2 ≤ N → Q (n + 1) ≤ Q n := by
    intro n hn
    set A := ru83E N (n + 1) with hA
    set σ := Equiv.swap (⟨n, by omega⟩ : Fin N) ⟨n + 1, by omega⟩ with hσ
    have hAB : A + A ∘ σ = ru83E N n + ru83E N (n + 2) := by
      funext j
      simp only [Pi.add_apply, Function.comp, hA, ru83E]
      by_cases h1 : (j : ℕ) = n
      · have : j = ⟨n, by omega⟩ := Fin.ext h1
        rw [this, hσ, Equiv.swap_apply_left]; simp
      · by_cases h2 : (j : ℕ) = n + 1
        · have : j = ⟨n + 1, by omega⟩ := Fin.ext h2
          rw [this, hσ, Equiv.swap_apply_right]; simp
        · rw [hσ, Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))]
          split_ifs <;> first | omega | norm_num
    have hc : μ (ru83E N n + ru83E N (n + 2)) = μ (ru83E N n) + μ (ru83E N (n + 2)) :=
      hcom _ _ (ru83_mono_comon _ _ (ru83E_mono _ _) (ru83E_mono _ _))
    have hs := hsubadd A (A ∘ σ)
    have hp : μ (A ∘ σ) = μ A := ru83_law_perm hN hlaw A σ
    rw [hAB, hc, hp] at hs
    simp only [hQ, hφ]
    linarith
  refine ⟨fun i => Q i, ⟨⟨fun i => ?_, ?_⟩, ?_⟩, fun X => ?_⟩
  · simp only [hQ]; linarith [hφanti i]
  · rw [Fin.sum_univ_eq_sum_range Q N]
    simp only [hQ]
    rw [sum_range_sub', φ0, φN]; ring
  · intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    have key : ∀ d m, m + d < N → Q (m + d) ≤ Q m := by
      intro d
      induction d with
      | zero => intro m _; simp
      | succ d ih =>
        intro m hm
        have := hQstep (m + d) (by omega)
        have := ih m (by omega)
        rw [← add_assoc]; linarith
    have := key ((j : ℕ) - i) i (by have := j.2; omega)
    rw [show (i : ℕ) + ((j : ℕ) - i) = j by omega] at this
    exact this
  · rw [← ru83_law_perm hN hlaw X (Tuple.sort X), hmain _ (Tuple.monotone_sort X),
      ru83_muQ_eq_of_mono _ X _ (Tuple.monotone_sort X)]
    rfl



theorem ru83_hmain_gen {N : ℕ} (μ : (Fin N → ℝ) → ℝ)
    (hcomM : ∀ A B : Fin N → ℝ, Monotone A → Monotone B → μ (A + B) = μ A + μ B)
    (htrans : ∀ (X : Fin N → ℝ) (c : ℝ), μ (fun i => X i + c) = μ X - c)
    (hhom : ∀ (X : Fin N → ℝ) (t : ℝ), 0 ≤ t → μ (t • X) = t * μ X) :
    ∀ Z : Fin N → ℝ, Monotone Z →
      μ Z = -∑ i : Fin N, (-μ (ru83E N i) - -μ (ru83E N (i + 1))) * Z i := by
  have μ0 : μ 0 = 0 := by
    have := hhom 0 0 le_rfl; simpa using this
  have μc : ∀ c : ℝ, μ (fun _ => c) = -c := fun c => by
    have := htrans 0 c; simp only [Pi.zero_apply, zero_add] at this; rw [this, μ0]; ring
  have hsum_mono : ∀ (W : ℕ → Fin N → ℝ) (n : ℕ), (∀ k < n, Monotone (W k)) →
      Monotone (∑ k ∈ range n, W k) := by
    intro W n hW i j hij
    simp only [Finset.sum_apply]
    exact sum_le_sum fun k hk => hW k (mem_range.1 hk) hij
  have hadd : ∀ (W : ℕ → Fin N → ℝ) (n : ℕ), (∀ k < n, Monotone (W k)) →
      μ (∑ k ∈ range n, W k) = ∑ k ∈ range n, μ (W k) := by
    intro W n hW
    induction n with
    | zero => simp [μ0]
    | succ n ih =>
      rw [sum_range_succ, sum_range_succ,
        hcomM _ _ (hsum_mono W n fun k hk => hW k (by omega)) (hW n (by omega)),
        ih fun k hk => hW k (by omega)]
  set φ : ℕ → ℝ := fun k => -μ (ru83E N k) with hφ
  set Q : ℕ → ℝ := fun n => φ n - φ (n + 1) with hQ
  have hE0 : ru83E N 0 = fun _ => 1 := by funext j; simp [ru83E]
  have hEN : ru83E N N = 0 := by funext j; simp [ru83E, j.2]
  have φ0 : φ 0 = 1 := by simp [hφ, hE0, μc]
  have φN : φ N = 0 := by simp [hφ, hEN, μ0]
  intro Z hZ
  set Z' : ℕ → ℝ := fun n => if h : n < N then Z ⟨n, h⟩ else 0 with hZ'
  set d : ℕ → ℝ := fun k => Z' k - (if k = 0 then 0 else Z' (k - 1)) with hd
  set W : ℕ → Fin N → ℝ := fun k j => d k * ru83E N k j with hW
  have hdecomp : Z = ∑ k ∈ range N, W k := by
    funext j
    simp only [Finset.sum_apply, hW, ru83E, mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    have hf : (range N).filter (fun k => k ≤ (j : ℕ)) = range ((j : ℕ) + 1) := by
      ext k; simp only [mem_filter, mem_range]; have := j.2; omega
    rw [hf]
    have tele : ∀ m, m < N → ∑ x ∈ range (m + 1), d x = Z' m := by
      intro m
      induction m with
      | zero => intro _; simp [hd]
      | succ m ih =>
        intro hm
        rw [sum_range_succ, ih (by omega)]
        simp [hd]
    rw [tele j j.2]
    simp [hZ', j.2]
  have hdpos : ∀ k, 0 < k → k < N → 0 ≤ d k := by
    intro k hkpos hk
    simp only [hd, if_neg hkpos.ne', hZ', dif_pos hk, dif_pos (show k - 1 < N by omega)]
    have := hZ (show (⟨k - 1, by omega⟩ : Fin N) ≤ ⟨k, hk⟩ from by
      show k - 1 ≤ k; omega)
    linarith
  have hWmono : ∀ k < N, Monotone (W k) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · intro i j _; simp [hW, hE0]
    · intro i j hij
      exact mul_le_mul_of_nonneg_left (ru83E_mono N k hij) (hdpos k hkpos hk)
  have hWval : ∀ k < N, μ (W k) = -(d k * φ k) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have : W 0 = fun _ => d 0 := by funext j; simp [hW, hE0]
      rw [this, μc, φ0]; ring
    · have : W k = d k • ru83E N k := by funext j; simp [hW]
      rw [this, hhom _ _ (hdpos k hkpos hk)]; simp [hφ]
  have hμZ : μ Z = -∑ k ∈ range N, d k * φ k := by
    conv_lhs => rw [hdecomp]
    rw [hadd W N hWmono, ← sum_neg_distrib]
    exact sum_congr rfl fun k hk => hWval k (mem_range.1 hk)
  have abel : ∀ n, ∑ k ∈ range n, d k * φ k =
      ∑ i ∈ range n, Q i * Z' i + φ n * (if n = 0 then 0 else Z' (n - 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih, sum_range_succ]
      simp only [hd, hQ, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      ring
  have hfin : ∑ i : Fin N, Q i * Z i = ∑ i ∈ range N, Q i * Z' i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => Q i * Z' i) N]
    exact sum_congr rfl fun i _ => by simp [hZ', i.2]
  rw [hμZ, abel N, φN, hfin]; simp



theorem ru83_ind_int (c : ℝ) {s t : Set ℝ} (hs : MeasurableSet s) (hfin : volume (s ∩ t) ≠ ⊤) :
    Integrable (fun x => c * s.indicator 1 x) (volume.restrict t) ∧
      ∫ x in t, c * s.indicator 1 x = c * volume.real (s ∩ t) := by
  have hI : Integrable (s.indicator (1 : ℝ → ℝ)) (volume.restrict t) := by
    rw [integrable_indicator_iff hs]
    refine integrableOn_const ?_ (by simp)
    rw [Measure.restrict_apply hs]; exact hfin
  refine ⟨hI.const_mul c, ?_⟩
  rw [integral_const_mul, integral_indicator_one hs, measureReal_restrict_apply hs]

theorem ru83_choquet_formula {N : ℕ} (g : Set (Fin N) → ℝ) (hg0 : g ∅ = 0) (hg1 : g Set.univ = 1)
    (Y : Fin N → ℝ) (π : Equiv.Perm (Fin N)) (hπ : Monotone (Y ∘ π)) :
    choquet g Y = ∑ i : Fin N, (g {ω | (i : ℕ) ≤ (π.symm ω : ℕ)} -
      g {ω | (i : ℕ) + 1 ≤ (π.symm ω : ℕ)}) * Y (π i) := by
  set z : ℕ → ℝ := fun k => if h : k < N then Y (π ⟨k, h⟩) else 0 with hz
  set G : ℕ → ℝ := fun k => g {ω | k ≤ (π.symm ω : ℕ)} with hG
  have hG0 : G 0 = 1 := by simp [hG, hg1]
  have hGN : G N = 0 := by
    simp only [hG]
    have : {ω : Fin N | N ≤ (π.symm ω : ℕ)} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact (π.symm ω).2
    rw [this, hg0]
  set Δ : ℕ → ℝ := fun k => G (k + 1) - G k with hΔ
  have hΔsum : ∑ k ∈ range N, Δ k = -1 := by
    simp only [hΔ]; rw [sum_range_sub (f := G), hGN, hG0]; ring
  -- pointwise identity
  have hA : ∀ x, g {ω | x < Y ω} = 1 + ∑ k ∈ range N, Δ k * (Set.Ici (z k)).indicator 1 x := by
    intro x
    set m := (univ.filter (fun j : Fin N => Y (π j) ≤ x)).card with hmdef
    have hm : ∀ j : Fin N, Y (π j) ≤ x ↔ (j : ℕ) < m := by
      intro j
      constructor
      · intro hj
        have : Iic j ⊆ univ.filter (fun j : Fin N => Y (π j) ≤ x) := fun i hi => by
          simp only [mem_Iic] at hi
          have := hπ hi; simp only [Function.comp] at this
          simp only [mem_filter, mem_univ, true_and]; linarith
        have := card_le_card this
        rw [Fin.card_Iic] at this; omega
      · intro hj
        by_contra hc; push_neg at hc
        have : univ.filter (fun j : Fin N => Y (π j) ≤ x) ⊆ Iio j := fun i hi => by
          simp only [mem_filter, mem_univ, true_and] at hi
          simp only [mem_Iio]
          by_contra hc2; push_neg at hc2
          have := hπ hc2; simp only [Function.comp] at this; linarith
        have := card_le_card this
        rw [Fin.card_Iio] at this; omega
    have hmN : m ≤ N := by
      have := card_le_univ (univ.filter (fun j : Fin N => Y (π j) ≤ x))
      simpa using this
    have hL : {ω | x < Y ω} = {ω | m ≤ (π.symm ω : ℕ)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      have := hm (π.symm ω)
      rw [Equiv.apply_symm_apply] at this
      constructor
      · intro h; by_contra h2; push_neg at h2; linarith [this.2 h2]
      · intro h; by_contra h2; push_neg at h2; have := this.1 h2; omega
    rw [hL]
    have hR : ∑ k ∈ range N, Δ k * (Set.Ici (z k)).indicator 1 x =
        ∑ k ∈ range N, (if k < m then Δ k else 0) := by
      refine sum_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      have := hm ⟨k, hk⟩
      simp only [Set.indicator, Set.mem_Ici, hz, dif_pos hk, Pi.one_apply]
      by_cases h : k < m
      · rw [if_pos (this.2 h), if_pos h]; ring
      · rw [if_neg (fun h' => h (this.1 h')), if_neg h]; ring
    rw [hR, ← sum_filter]
    have : (range N).filter (fun k => k < m) = range m := by
      ext k; simp only [mem_filter, mem_range]; omega
    rw [this]
    simp only [hΔ]; rw [sum_range_sub (f := G), hG0]; simp [hG]
  have hB : ∀ x, g {ω | x < Y ω} = -∑ k ∈ range N, Δ k * (Set.Iio (z k)).indicator 1 x := by
    intro x
    rw [hA x]
    have : ∀ k, (Set.Ici (z k)).indicator (1 : ℝ → ℝ) x = 1 - (Set.Iio (z k)).indicator 1 x := by
      intro k
      simp only [Set.indicator, Set.mem_Ici, Set.mem_Iio, Pi.one_apply]
      split_ifs <;> first | linarith | norm_num
    simp only [this, mul_sub, mul_one, sum_sub_distrib, hΔsum]; ring
  -- integrals
  have hD : ∫ x in Set.Iic (0 : ℝ), (g {ω | x < Y ω} - 1) =
      ∑ k ∈ range N, Δ k * max (0 - z k) 0 := by
    simp_rw [hA, add_sub_cancel_left]
    rw [integral_finset_sum _ fun k _ =>
      (ru83_ind_int (Δ k) measurableSet_Ici (by rw [Set.Ici_inter_Iic]; simp)).1]
    refine sum_congr rfl fun k _ => ?_
    rw [(ru83_ind_int (Δ k) measurableSet_Ici (by rw [Set.Ici_inter_Iic]; simp)).2,
      Set.Ici_inter_Iic, Real.volume_real_Icc]
  have hE : ∫ x in Set.Ioi (0 : ℝ), g {ω | x < Y ω} =
      -∑ k ∈ range N, Δ k * max (z k - 0) 0 := by
    simp_rw [hB]
    rw [integral_neg, integral_finset_sum _ fun k _ =>
      (ru83_ind_int (Δ k) measurableSet_Iio (by rw [Set.Iio_inter_Ioi]; simp)).1]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [(ru83_ind_int (Δ k) measurableSet_Iio (by rw [Set.Iio_inter_Ioi]; simp)).2,
      Set.Iio_inter_Ioi, Real.volume_real_Ioo]
  rw [choquet, hD, hE, ← sub_eq_add_neg, ← sum_sub_distrib]
  rw [← Fin.sum_univ_eq_sum_range (fun k => Δ k * max (0 - z k) 0 - Δ k * max (z k - 0) 0) N]
  refine sum_congr rfl fun i _ => ?_
  have hzi : z i = Y (π i) := by simp [hz, i.2]
  rw [hzi]
  simp only [hΔ, hG]
  rcases le_total (Y (π i)) 0 with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring



theorem ru83_thm41 {N : ℕ} (μ : (Fin N → ℝ) → ℝ) (hμ : IsCoherent μ) :
    IsComonotonic μ ↔
      ∃ g : Set (Fin N) → ℝ, (∀ A, g A ∈ Set.Icc (0 : ℝ) 1) ∧ IsMonotoneSF g ∧
        IsNormalizedSF g ∧ IsSubmodularSF g ∧ ∀ X, μ X = choquet g (-X) := by
  constructor
  · intro hcom
    obtain ⟨⟨hmono, htrans⟩, hconv, hhom⟩ := hμ
    have μ0 : μ 0 = 0 := by
      have := hhom 0 0 le_rfl; simpa using this
    have μc : ∀ c : ℝ, μ (fun _ => c) = -c := fun c => by
      have := htrans 0 c; simp only [Pi.zero_apply, zero_add] at this; rw [this, μ0]; ring
    have hsubadd : ∀ A B : Fin N → ℝ, μ (A + B) ≤ μ A + μ B := by
      intro A B
      have h1 := hconv A B (1/2) (by norm_num) (by norm_num)
      have h2 := hhom ((1/2:ℝ) • A + (1 - 1/2 : ℝ) • B) 2 (by norm_num)
      have : (2:ℝ) • ((1/2:ℝ) • A + (1 - 1/2 : ℝ) • B) = A + B := by
        funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this] at h2; linarith
    set g : Set (Fin N) → ℝ := fun A => μ (A.indicator (fun _ => (-1 : ℝ))) with hg
    have hg0 : g ∅ = 0 := by simp only [hg, Set.indicator_empty]; rw [μc]; simp
    have hg1 : g Set.univ = 1 := by simp only [hg, Set.indicator_univ]; rw [μc]; simp
    refine ⟨g, fun A => ⟨?_, ?_⟩, fun A B hAB => ?_, ⟨hg0, hg1⟩, fun A B => ?_, fun X => ?_⟩
    · rw [← μ0]
      exact hmono _ _ fun i => by
        simp only [Set.indicator, Pi.zero_apply]; split_ifs <;> norm_num
    · rw [← hg1]
      exact hmono _ _ fun i => by
        simp only [Set.indicator, Set.mem_univ, if_true]; split_ifs <;> norm_num
    · exact hmono _ _ fun i => by
        simp only [Set.indicator]
        by_cases h1 : i ∈ A
        · rw [if_pos h1, if_pos (hAB h1)]
        · rw [if_neg h1]; split_ifs <;> norm_num
    · have hsum : (A ∪ B).indicator (fun _ => (-1 : ℝ)) + (A ∩ B).indicator (fun _ => (-1 : ℝ)) =
          A.indicator (fun _ => (-1 : ℝ)) + B.indicator (fun _ => (-1 : ℝ)) := by
        funext ω
        by_cases a1 : ω ∈ A <;> by_cases b1 : ω ∈ B <;> simp [Set.indicator, a1, b1]
      have hc : Comonotone ((A ∪ B).indicator (fun _ => (-1 : ℝ)))
          ((A ∩ B).indicator (fun _ => (-1 : ℝ))) := by
        intro ω ω'
        by_cases a1 : ω ∈ A <;> by_cases b1 : ω ∈ B <;> by_cases a2 : ω' ∈ A <;>
          by_cases b2 : ω' ∈ B <;> simp [Set.indicator, a1, b1, a2, b2]
      have := hcom _ _ hc
      rw [hsum] at this
      simp only [hg]
      linarith [hsubadd (A.indicator (fun _ => (-1 : ℝ))) (B.indicator (fun _ => (-1 : ℝ)))]
    · set Y := -X with hY
      set π := Tuple.sort Y with hπdef
      have hπ : Monotone (Y ∘ π) := Tuple.monotone_sort Y
      rw [ru83_choquet_formula g hg0 hg1 Y π hπ]
      set μ' : (Fin N → ℝ) → ℝ := fun Z => -μ (-(Z ∘ π.symm)) with hμ'
      have hcomM : ∀ A B : Fin N → ℝ, Monotone A → Monotone B → μ' (A + B) = μ' A + μ' B := by
        intro A B hA hB
        have hc0 := ru83_mono_comon A B hA hB
        have hc : Comonotone (-(A ∘ π.symm)) (-(B ∘ π.symm)) := by
          intro ω ω'
          have := hc0 (π.symm ω) (π.symm ω')
          simp only [Pi.neg_apply, Function.comp]; nlinarith
        simp only [hμ']
        have e : -((A + B) ∘ π.symm) = -(A ∘ π.symm) + -(B ∘ π.symm) := by
          funext ω; simp; ring
        rw [e, hcom _ _ hc]; ring
      have htrans' : ∀ (Z : Fin N → ℝ) (c : ℝ), μ' (fun i => Z i + c) = μ' Z - c := by
        intro Z c
        simp only [hμ']
        have e : -((fun i => Z i + c) ∘ π.symm) = fun i => (-(Z ∘ π.symm)) i + -c := by
          funext ω; simp; ring
        rw [e, htrans]; ring
      have hhom' : ∀ (Z : Fin N → ℝ) (t : ℝ), 0 ≤ t → μ' (t • Z) = t * μ' Z := by
        intro Z t ht
        simp only [hμ']
        have e : -((t • Z) ∘ π.symm) = t • (-(Z ∘ π.symm)) := by
          funext ω; simp
        rw [e, hhom _ _ ht]; ring
      have hm := ru83_hmain_gen μ' hcomM htrans' hhom' (Y ∘ π) hπ
      have hYX : μ' (Y ∘ π) = -μ X := by
        simp only [hμ']
        have : -((Y ∘ π) ∘ π.symm) = X := by funext ω; simp [hY]
        rw [this]
      have hE : ∀ k : ℕ, -μ' (ru83E N k) = g {ω | k ≤ (π.symm ω : ℕ)} := by
        intro k
        simp only [hμ', hg, neg_neg]
        congr 1
        funext ω
        simp only [Pi.neg_apply, Function.comp, ru83E, Set.indicator, Set.mem_setOf_eq]
        split_ifs <;> norm_num
      rw [hYX] at hm
      have : μ X = ∑ i : Fin N, (-μ' (ru83E N i) - -μ' (ru83E N (i + 1))) * (Y ∘ π) i := by
        linarith
      rw [this]
      refine sum_congr rfl fun i _ => ?_
      rw [hE, hE]; rfl
  · rintro ⟨g, -, -, ⟨hg0, hg1⟩, -, hcho⟩ X Y hXY
    have hc : Comonotone (-X) (-Y) := fun ω ω' => by
      have := hXY ω ω'; simp only [Pi.neg_apply]; nlinarith
    obtain ⟨π, h1, h2⟩ := ru83_common_sort (-X) (-Y) hc
    have h3 : Monotone ((-(X + Y)) ∘ π) := fun i j hij => by
      have := h1 hij; have := h2 hij
      simp only [Function.comp, Pi.neg_apply, Pi.add_apply] at *; linarith
    rw [hcho, hcho, hcho, ru83_choquet_formula g hg0 hg1 _ π h3,
      ru83_choquet_formula g hg0 hg1 _ π h1, ru83_choquet_formula g hg0 hg1 _ π h2,
      ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [Pi.neg_apply, Pi.add_apply]; ring


theorem solution {N : ℕ} (μ : (Fin N → ℝ) → ℝ) (hμ : IsCoherent μ) :
    IsComonotonic μ ↔
      ∃ g : Set (Fin N) → ℝ, (∀ A, g A ∈ Set.Icc (0 : ℝ) 1) ∧ IsMonotoneSF g ∧
        IsNormalizedSF g ∧ IsSubmodularSF g ∧ ∀ X, μ X = choquet g (-X) := by


  exact ru83_thm41 μ hμ

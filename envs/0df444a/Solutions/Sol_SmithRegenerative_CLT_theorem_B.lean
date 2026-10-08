-- Prove2me | solution 1 for SmithRegenerative.CLT.theorem_B
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:55:55.479991+00:00
-- url     : https://prove2.me/submissions/cf9baa98-0bdf-4e1c-8eb8-c6b4ca2f3c40

import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology


namespace SmithRegenerative.CLT

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Partial sums `S_k = Σ_{i<k} X_i`. -/
def psum (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range k, X i ω

theorem psum_measurable {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (k : ℕ) :
    Measurable (psum X k) := by
  unfold psum
  exact Finset.measurable_sum _ (fun i _ => hX i)

theorem psum_memLp {X : ℕ → Ω → ℝ} (hL2 : ∀ i, MemLp (X i) 2 P) (k : ℕ) :
    MemLp (psum X k) 2 P := by
  have := memLp_finsetSum' (Finset.range k) (fun i _ => hL2 i) (p := 2) (μ := P)
  convert this using 1
  ext ω; simp [psum]

theorem psum_sub {X : ℕ → Ω → ℝ} {k n : ℕ} (hkn : k ≤ n) (ω : Ω) :
    psum X n ω - psum X k ω = ∑ i ∈ Finset.Ico k n, X i ω := by
  unfold psum
  rw [← Finset.sum_range_add_sum_Ico _ hkn]
  ring

/-- Functions of disjoint blocks of an independent family are independent. -/
theorem indepFun_of_finset {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (S T : Finset ℕ) (hST : Disjoint S T) (G H : (ℕ → ℝ) → ℝ) (hG : Measurable G)
    (hH : Measurable H)
    (hGS : ∀ x y : ℕ → ℝ, (∀ i ∈ S, x i = y i) → G x = G y)
    (hHT : ∀ x y : ℕ → ℝ, (∀ i ∈ T, x i = y i) → H x = H y) :
    IndepFun (fun ω => G (fun i => X i ω)) (fun ω => H (fun i => X i ω)) P := by
  classical
  have h := hind.indepFun_finset S T hST hX
  let φ : (S → ℝ) → ℝ := fun v => G (fun i => if h : i ∈ S then v ⟨i, h⟩ else 0)
  let χ : (T → ℝ) → ℝ := fun v => H (fun i => if h : i ∈ T then v ⟨i, h⟩ else 0)
  have hφ : Measurable φ := by
    refine hG.comp (measurable_pi_lambda _ fun i => ?_)
    by_cases hi : i ∈ S
    · simp only [hi, dite_true]; exact measurable_pi_apply _
    · simp only [hi, dite_false]; exact measurable_const
  have hχ : Measurable χ := by
    refine hH.comp (measurable_pi_lambda _ fun i => ?_)
    by_cases hi : i ∈ T
    · simp only [hi, dite_true]; exact measurable_pi_apply _
    · simp only [hi, dite_false]; exact measurable_const
  have := h.comp hφ hχ
  convert this using 1
  · ext ω
    simp only [Function.comp, φ]
    apply hGS
    intro i hi
    simp [hi]
  · ext ω
    simp only [Function.comp, χ]
    apply hHT
    intro i hi
    simp [hi]

/-- The stopping sets `A k`: first `k` with `a ≤ |S_k|`. -/
def stopSet (X : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) : Set Ω :=
  {ω | a ≤ |psum X k ω| ∧ ∀ j < k, |psum X j ω| < a}

theorem stopSet_measurable {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (a : ℝ) (k : ℕ) :
    MeasurableSet (stopSet X a k) := by
  unfold stopSet
  simp only [Set.setOf_and, Set.setOf_forall]
  refine MeasurableSet.inter (measurableSet_le measurable_const (psum_measurable hX k).abs) ?_
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_lt (psum_measurable hX j).abs measurable_const

theorem stopSet_disjoint (X : ℕ → Ω → ℝ) (a : ℝ) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (stopSet X a k) (stopSet X a l) := by
  rw [Set.disjoint_left]
  intro ω hk hl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact absurd hk.1 (not_le.2 (hl.2 k h))
  · exact absurd hl.1 (not_le.2 (hk.2 l h))

theorem subset_iUnion_stopSet (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) :
    {ω | ∃ k ≤ n, a ≤ |psum X k ω|} ⊆ ⋃ k ∈ Finset.range (n + 1), stopSet X a k := by
  classical
  intro ω hω
  obtain ⟨k, hkn, hk⟩ := hω
  have hex : ∃ k, a ≤ |psum X k ω| := ⟨k, hk⟩
  simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
  refine ⟨Nat.find hex, by have := Nat.find_min' hex hk; omega, Nat.find_spec hex, ?_⟩
  intro j hj
  exact not_le.1 (Nat.find_min hex hj)

/-- **Kolmogorov's inequality.** -/
theorem kolmogorov_ineq {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (h0 : ∀ i, ∫ ω, X i ω ∂P = 0) (n : ℕ) {a : ℝ} (ha : 0 < a) :
    a ^ 2 * P.real {ω | ∃ k ≤ n, a ≤ |psum X k ω|} ≤ ∫ ω, psum X n ω ^ 2 ∂P := by
  classical
  have hSn : MemLp (psum X n) 2 P := psum_memLp hL2 n
  have hSn2 : Integrable (fun ω => psum X n ω ^ 2) P := hSn.integrable_sq
  -- key estimate on each stopping set
  have key : ∀ k ∈ Finset.range (n + 1),
      a ^ 2 * P.real (stopSet X a k) ≤ ∫ ω in stopSet X a k, psum X n ω ^ 2 ∂P := by
    intro k hk
    have hkn : k ≤ n := by simp at hk; omega
    set A := stopSet X a k with hA
    have hAm : MeasurableSet A := stopSet_measurable hX a k
    have hSk : MemLp (psum X k) 2 P := psum_memLp hL2 k
    set D : Ω → ℝ := fun ω => ∑ i ∈ Finset.Ico k n, X i ω with hD
    have hDL2 : MemLp D 2 P := by
      have := memLp_finsetSum' (Finset.Ico k n) (fun i _ => hL2 i) (p := 2) (μ := P)
      convert this using 1
      ext ω; simp [hD]
    have hDint : ∫ ω, D ω ∂P = 0 := by
      simp only [hD]
      rw [integral_finset_sum _ (fun i _ => (hL2 i).integrable one_le_two)]
      simp [h0]
    have hdecomp : ∀ ω, psum X n ω = psum X k ω + D ω := by
      intro ω
      have := psum_sub (X := X) hkn ω
      simp only [hD]; linarith
    -- the indicator-weighted S_k
    set F : Ω → ℝ := A.indicator (psum X k) with hF
    have hFL2 : MemLp F 2 P := hSk.indicator hAm
    -- independence of F and D
    have hFD : IndepFun F D P := by
      let G : (ℕ → ℝ) → ℝ := fun x =>
        if a ≤ |∑ i ∈ Finset.range k, x i| ∧ ∀ j < k, |∑ i ∈ Finset.range j, x i| < a
        then ∑ i ∈ Finset.range k, x i else 0
      let H : (ℕ → ℝ) → ℝ := fun x => ∑ i ∈ Finset.Ico k n, x i
      have hsum_meas : ∀ j, Measurable (fun x : ℕ → ℝ => ∑ i ∈ Finset.range j, x i) :=
        fun j => Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
      have hG : Measurable G := by
        refine Measurable.ite ?_ (hsum_meas k) measurable_const
        simp only [Set.setOf_and, Set.setOf_forall]
        refine MeasurableSet.inter (measurableSet_le measurable_const (hsum_meas k).abs) ?_
        refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
        exact measurableSet_lt (hsum_meas j).abs measurable_const
      have hH : Measurable H := Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
      have h := indepFun_of_finset hX hind (Finset.range k) (Finset.Ico k n)
        (by
          rw [Finset.disjoint_left]
          intro i hi hi'
          simp at hi hi'; omega) G H hG hH
        (by
          intro x y hxy
          have e : ∀ j ≤ k, ∑ i ∈ Finset.range j, x i = ∑ i ∈ Finset.range j, y i := by
            intro j hj
            apply Finset.sum_congr rfl
            intro i hi
            apply hxy
            simp at hi ⊢; omega
          simp only [G]
          rw [e k le_rfl]
          congr 1
          apply propext
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun j hj => by rw [← e j hj.le]; exact h2 j hj⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun j hj => by rw [e j hj.le]; exact h2 j hj⟩)
        (by
          intro x y hxy
          simp only [H]
          exact Finset.sum_congr rfl (fun i hi => hxy i hi))
      convert h using 1
      ext ω
      simp only [hF, G, Set.indicator, hA, stopSet, Set.mem_setOf_eq, psum]
    have hFDint : ∫ ω, F ω * D ω ∂P = 0 := by
      rw [hFD.integral_fun_mul_eq_mul_integral hFL2.aestronglyMeasurable hDL2.aestronglyMeasurable,
        hDint, mul_zero]
    -- expand
    have hexp : ∫ ω in A, psum X n ω ^ 2 ∂P =
        (∫ ω in A, psum X k ω ^ 2 ∂P) + 2 * (∫ ω, F ω * D ω ∂P) + ∫ ω in A, D ω ^ 2 ∂P := by
      have e1 : ∫ ω in A, psum X n ω ^ 2 ∂P =
          ∫ ω in A, (psum X k ω ^ 2 + 2 * (psum X k ω * D ω) + D ω ^ 2) ∂P := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [hdecomp ω]; ring
      rw [e1]
      have i1 : IntegrableOn (fun ω => psum X k ω ^ 2) A P := hSk.integrable_sq.integrableOn
      have i2 : IntegrableOn (fun ω => psum X k ω * D ω) A P :=
        (hSk.integrable_mul hDL2).integrableOn
      have i3 : IntegrableOn (fun ω => D ω ^ 2) A P := hDL2.integrable_sq.integrableOn
      have i2' : IntegrableOn (fun ω => 2 * (psum X k ω * D ω)) A P := i2.const_mul 2
      have i12 : IntegrableOn (fun ω => psum X k ω ^ 2 + 2 * (psum X k ω * D ω)) A P :=
        i1.add i2'
      rw [integral_add i12 i3, integral_add i1 i2', integral_const_mul]
      have e2 : ∫ ω in A, psum X k ω * D ω ∂P = ∫ ω, F ω * D ω ∂P := by
        rw [← integral_indicator hAm]
        apply integral_congr_ae
        filter_upwards with ω
        simp only [hF, Set.indicator]
        split_ifs <;> simp
      rw [e2]
    have hD2 : 0 ≤ ∫ ω in A, D ω ^ 2 ∂P := integral_nonneg fun ω => by positivity
    have hSk2 : a ^ 2 * P.real A ≤ ∫ ω in A, psum X k ω ^ 2 ∂P := by
      refine setIntegral_ge_of_const_le_real hAm (measure_ne_top _ _) ?_
        hSk.integrable_sq.integrableOn
      intro ω hω
      have h1 : a ≤ |psum X k ω| := hω.1
      calc a ^ 2 ≤ |psum X k ω| ^ 2 := by gcongr
        _ = psum X k ω ^ 2 := sq_abs _
    rw [hexp, hFDint]
    linarith
  -- sum up
  have hsub := subset_iUnion_stopSet X a n
  have hmeasE : P.real {ω | ∃ k ≤ n, a ≤ |psum X k ω|} ≤
      ∑ k ∈ Finset.range (n + 1), P.real (stopSet X a k) := by
    calc P.real {ω | ∃ k ≤ n, a ≤ |psum X k ω|}
        ≤ P.real (⋃ k ∈ Finset.range (n + 1), stopSet X a k) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ k ∈ Finset.range (n + 1), P.real (stopSet X a k) :=
          measureReal_biUnion_finset_le _ _
  have hint : ∑ k ∈ Finset.range (n + 1), ∫ ω in stopSet X a k, psum X n ω ^ 2 ∂P ≤
      ∫ ω, psum X n ω ^ 2 ∂P := by
    rw [← integral_biUnion_finset _ (fun k _ => stopSet_measurable hX a k)
      (fun k _ l _ hkl => stopSet_disjoint X a hkl) (fun k _ => hSn2.integrableOn)]
    exact setIntegral_le_integral hSn2 (Eventually.of_forall fun ω => by positivity)
  calc a ^ 2 * P.real {ω | ∃ k ≤ n, a ≤ |psum X k ω|}
      ≤ a ^ 2 * ∑ k ∈ Finset.range (n + 1), P.real (stopSet X a k) := by gcongr
    _ = ∑ k ∈ Finset.range (n + 1), a ^ 2 * P.real (stopSet X a k) := Finset.mul_sum _ _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), ∫ ω in stopSet X a k, psum X n ω ^ 2 ∂P :=
        Finset.sum_le_sum key
    _ ≤ _ := hint

theorem psum_shift (X : ℕ → Ω → ℝ) (b k : ℕ) (ω : Ω) :
    psum (fun j => X (b + j)) k ω = psum X (b + k) ω - psum X b ω := by
  induction k with
  | zero => simp [psum]
  | succ k ih =>
    unfold psum at ih ⊢
    rw [Finset.sum_range_succ, ← add_assoc, Finset.sum_range_succ _ (b + k)]
    linarith

/-- Kolmogorov's inequality for a block of `d` summands starting at `b`, for an i.i.d. centred
sequence. -/
theorem kolmogorov_shift {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hL2 : MemLp (X 0) 2 P)
    (h0 : ∫ ω, X 0 ω ∂P = 0) (b d : ℕ) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ k ≤ d, a ≤ |psum X (b + k) ω - psum X b ω|} ≤
      d * (∫ ω, X 0 ω ^ 2 ∂P) / a ^ 2 := by
  set X' : ℕ → Ω → ℝ := fun j => X (b + j) with hX'
  have hX'm : ∀ j, Measurable (X' j) := fun j => hX _
  have hind' : iIndepFun X' P := hind.precomp (g := fun j => b + j) (add_right_injective b)
  have hL2' : ∀ j, MemLp (X' j) 2 P := fun j => (hident _).memLp_iff.2 hL2
  have h0' : ∀ j, ∫ ω, X' j ω ∂P = 0 := fun j => by
    simp only [hX']; rw [(hident _).integral_eq, h0]
  have hk := kolmogorov_ineq hX'm hind' hL2' h0' d ha
  have hvar : ∫ ω, psum X' d ω ^ 2 ∂P = d * ∫ ω, X 0 ω ^ 2 ∂P := by
    have hm : Measurable (psum X' d) := psum_measurable hX'm d
    have hmean : ∫ ω, psum X' d ω ∂P = 0 := by
      unfold psum
      rw [integral_finsetSum _ (fun i _ => (hL2' i).integrable one_le_two)]
      simp [h0']
    rw [← variance_of_integral_eq_zero hm.aemeasurable hmean]
    have e : psum X' d = ∑ i ∈ Finset.range d, X' i := by ext ω; simp [psum]
    rw [e, IndepFun.variance_sum (fun i _ => hL2' i)
      (fun i _ j _ hij => hind'.indepFun hij)]
    have : ∀ i ∈ Finset.range d, variance (X' i) P = ∫ ω, X 0 ω ^ 2 ∂P := by
      intro i _
      rw [(hident _).variance_eq, variance_of_integral_eq_zero (hident 0).aemeasurable_fst h0]
    rw [Finset.sum_congr rfl this]
    simp
  rw [hvar] at hk
  have hset : {ω | ∃ k ≤ d, a ≤ |psum X (b + k) ω - psum X b ω|} =
      {ω | ∃ k ≤ d, a ≤ |psum X' k ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, h⟩; exact ⟨k, hk, by rw [psum_shift]; exact h⟩
    · rintro ⟨k, hk, h⟩; exact ⟨k, hk, by rw [psum_shift] at h; exact h⟩
  rw [hset, le_div_iff₀ (by positivity), mul_comm]
  exact hk

/-- A real number `r ∈ (0, 1]` below a positive `η : ℝ≥0∞`. -/
theorem exists_real_le_ennreal {η : ENNReal} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ η := by
  refine ⟨(min η 1).toReal, ?_, ?_⟩
  · apply ENNReal.toReal_pos
    · exact (lt_min hη zero_lt_one).ne'
    · exact ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  · rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
    exact min_le_left _ _

/-- **Anscombe's fluctuation estimate**: `(S_{m_t} − S_{⌊ψ t⌋})/(c √ψ(t)) → 0` in probability. -/
theorem anscombe_fluct {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hL2 : MemLp (X 0) 2 P)
    (h0 : ∫ ω, X 0 ω ∂P = 0) (ψ : ℝ → ℝ) (hψ : Tendsto ψ atTop atTop)
    (m : ℝ → Ω → ℕ)
    (hm_ratio : TendstoInMeasure P (fun t ω => (m t ω : ℝ) / ψ t) atTop (fun _ => 1))
    {c : ℝ} (hc : 0 < c) :
    TendstoInMeasure P
      (fun t ω => (psum X (m t ω) ω - psum X ⌊ψ t⌋₊ ω) / (c * Real.sqrt (ψ t))) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨r, hr, hrη⟩ := exists_real_le_ennreal hη
  set v := ∫ ω, X 0 ω ^ 2 ∂P with hv
  have hv0 : 0 ≤ v := integral_nonneg fun ω => by positivity
  set δ : ℝ := r * ε ^ 2 * c ^ 2 / (20 * (v + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hbound : 10 * δ * v / (ε ^ 2 * c ^ 2) ≤ r / 2 := by
    rw [hδ]
    rw [div_le_iff₀ (by positivity)]
    have : 10 * (r * ε ^ 2 * c ^ 2 / (20 * (v + 1))) * v = r / 2 * (ε ^ 2 * c ^ 2) * (v / (v + 1)) := by
      field_simp
      ring
    rw [this]
    have h1 : v / (v + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h2 : 0 ≤ r / 2 * (ε ^ 2 * c ^ 2) := by positivity
    calc r / 2 * (ε ^ 2 * c ^ 2) * (v / (v + 1)) ≤ r / 2 * (ε ^ 2 * c ^ 2) * 1 := by gcongr
      _ = r / 2 * (ε ^ 2 * c ^ 2) := by ring
  -- the three eventual facts
  have hG : ∀ᶠ t in atTop, P {ω | δ ≤ ‖(m t ω : ℝ) / ψ t - 1‖} ≤ ENNReal.ofReal (r / 2) := by
    have := (tendstoInMeasure_iff_norm.1 hm_ratio) δ hδpos
    rw [ENNReal.tendsto_nhds_zero] at this
    exact this _ (by simp [hr])
  have hψ1 : ∀ᶠ t in atTop, 2 / δ ≤ ψ t ∧ 1 ≤ ψ t := by
    filter_upwards [hψ.eventually_ge_atTop (2 / δ), hψ.eventually_ge_atTop 1] with t h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hG, hψ1] with t hGt hψt
  obtain ⟨hψ2, hψ1'⟩ := hψt
  have hψpos : 0 < ψ t := by linarith
  set n : ℕ := ⌊ψ t⌋₊ with hn
  set d : ℕ := ⌈δ * ψ t⌉₊ + 1 with hd
  set a : ℝ := ε * (c * Real.sqrt (ψ t)) with ha
  have hsq : 0 < Real.sqrt (ψ t) := Real.sqrt_pos.2 hψpos
  have hapos : 0 < a := by positivity
  have ha2 : a ^ 2 = ε ^ 2 * c ^ 2 * ψ t := by
    rw [ha, mul_pow, mul_pow, Real.sq_sqrt hψpos.le]; ring
  have hnle : (n : ℝ) ≤ ψ t := Nat.floor_le hψpos.le
  have hnlt : ψ t < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdlt : (d : ℝ) < δ * ψ t + 2 := by
    rw [hd]; push_cast
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ δ * ψ t)
    linarith
  have hdle : (d : ℝ) ≤ 2 * δ * ψ t := by
    have : 2 ≤ δ * ψ t := by
      rw [div_le_iff₀ hδpos] at hψ2; linarith
    linarith
  set b : ℕ := n - d with hb
  -- the three bad events
  set G' := {ω | δ ≤ ‖(m t ω : ℝ) / ψ t - 1‖} with hG'
  set U := {ω | ∃ k ≤ d, a ≤ |psum X (n + k) ω - psum X n ω|} with hU
  set L := {ω | ∃ k ≤ d, a / 2 ≤ |psum X (b + k) ω - psum X b ω|} with hL
  have hincl : {ω | ε ≤ ‖(psum X (m t ω) ω - psum X n ω) / (c * Real.sqrt (ψ t)) - 0‖} ⊆
      G' ∪ U ∪ L := by
    intro ω hω
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : 0 < c * Real.sqrt (ψ t)), le_div_iff₀ (by positivity : 0 < c * Real.sqrt (ψ t))] at hω
    -- hω : a ≤ |S m - S n|
    by_cases hGω : ω ∈ G'
    · exact Or.inl (Or.inl hGω)
    have hlt : |(m t ω : ℝ) / ψ t - 1| < δ := by
      simp only [hG', Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at hGω; exact hGω
    have hmψ : |(m t ω : ℝ) - ψ t| < δ * ψ t := by
      have : (m t ω : ℝ) / ψ t - 1 = ((m t ω : ℝ) - ψ t) / ψ t := by field_simp
      rw [this, abs_div, abs_of_pos hψpos, div_lt_iff₀ hψpos] at hlt
      exact hlt
    rw [abs_lt] at hmψ
    have hceil : δ * ψ t ≤ (⌈δ * ψ t⌉₊ : ℝ) := Nat.le_ceil _
    have hm_le : m t ω ≤ n + d := by
      have : (m t ω : ℝ) < (n : ℝ) + d := by
        rw [hd]; push_cast; linarith
      exact_mod_cast this.le
    have hn_le : n ≤ m t ω + d := by
      have : (n : ℝ) < (m t ω : ℝ) + d := by
        rw [hd]; push_cast; linarith
      exact_mod_cast this.le
    rcases le_or_gt n (m t ω) with hnm | hnm
    · -- upper fluctuation
      refine Or.inl (Or.inr ⟨m t ω - n, by omega, ?_⟩)
      rw [Nat.add_sub_cancel' hnm]
      exact hω
    · -- lower fluctuation
      refine Or.inr ?_
      have hbm : b ≤ m t ω := by omega
      have hbn : b ≤ n := Nat.sub_le _ _
      by_contra hcon
      simp only [hL, Set.mem_setOf_eq, not_exists, not_and, not_le] at hcon
      have h1 := hcon (n - b) (by omega)
      have h2 := hcon (m t ω - b) (by omega)
      rw [Nat.add_sub_cancel' hbn] at h1
      rw [Nat.add_sub_cancel' hbm] at h2
      have : |psum X (m t ω) ω - psum X n ω| ≤
          |psum X (n + 0) ω - psum X b ω| + |psum X (m t ω) ω - psum X b ω| := by
        rw [add_zero]
        calc |psum X (m t ω) ω - psum X n ω|
            = |(psum X n ω - psum X b ω) - (psum X (m t ω) ω - psum X b ω)| := by
              rw [abs_sub_comm]; ring_nf
          _ ≤ _ := abs_sub _ _
      rw [add_zero] at this
      linarith
  have hU_bound : P U ≤ ENNReal.ofReal (d * v / a ^ 2) := by
    rw [← ofReal_measureReal (s := U)]
    exact ENNReal.ofReal_le_ofReal (kolmogorov_shift hX hind hident hL2 h0 n d hapos)
  have hL_bound : P L ≤ ENNReal.ofReal (d * v / (a / 2) ^ 2) := by
    rw [← ofReal_measureReal (s := L)]
    exact ENNReal.ofReal_le_ofReal (kolmogorov_shift hX hind hident hL2 h0 b d (by positivity))
  have hsum : d * v / a ^ 2 + d * v / (a / 2) ^ 2 ≤ r / 2 := by
    have e : d * v / a ^ 2 + d * v / (a / 2) ^ 2 = 5 * d * v / a ^ 2 := by
      field_simp
      ring
    rw [e, ha2]
    calc 5 * d * v / (ε ^ 2 * c ^ 2 * ψ t) ≤ 5 * (2 * δ * ψ t) * v / (ε ^ 2 * c ^ 2 * ψ t) := by
          gcongr
      _ = 10 * δ * v / (ε ^ 2 * c ^ 2) := by
          field_simp
          ring
      _ ≤ r / 2 := hbound
  calc P {ω | ε ≤ ‖(psum X (m t ω) ω - psum X n ω) / (c * Real.sqrt (ψ t)) - 0‖}
      ≤ P (G' ∪ U ∪ L) := measure_mono hincl
    _ ≤ P G' + P U + P L := by
        calc P (G' ∪ U ∪ L) ≤ P (G' ∪ U) + P L := measure_union_le _ _
          _ ≤ P G' + P U + P L := by gcongr; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal (d * v / a ^ 2) +
        ENNReal.ofReal (d * v / (a / 2) ^ 2) := by gcongr
    _ = ENNReal.ofReal (r / 2) + ENNReal.ofReal (d * v / a ^ 2 + d * v / (a / 2) ^ 2) := by
        rw [add_assoc, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) := by gcongr
    _ = ENNReal.ofReal r := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ η := hrη


/-! ### Assembling Theorem B -/

theorem tendstoInDistribution_comp {ι κ : Type*} {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ι → Ω → ℝ} {Z : Ω' → ℝ} {l : Filter ι}
    (h : TendstoInDistribution X l Z (fun _ => P) P') {l' : Filter κ} {g : κ → ι}
    (hg : Tendsto g l' l) :
    TendstoInDistribution (fun k => X (g k)) l' Z (fun _ => P) P' where
  forall_aemeasurable k := h.forall_aemeasurable (g k)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hg

theorem tendstoInMeasure_const_of_tendsto {c : ℝ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀)) :
    TendstoInMeasure P (fun t (_ : Ω) => c t) atTop (fun _ => c₀) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have h := (Metric.tendsto_nhds.1 hc) ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h] with t ht
  have : {x : Ω | ε ≤ ‖c t - c₀‖} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    rw [dist_eq_norm] at ht; exact ht
  rw [this, measure_empty]

theorem psum_random_measurable {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    {N : Ω → ℕ} (hN : Measurable N) : Measurable (fun ω => psum X (N ω) ω) := by
  have h : Measurable (fun p : Ω × ℕ => psum X p.2 p.1) :=
    measurable_from_prod_countable_left (fun k => psum_measurable hX k)
  exact h.comp (measurable_id.prodMk hN)

/-- Theorem B for a measurable i.i.d. sequence `X`, with `S_m = Σ_{i<m} X_i`. -/
theorem theorem_B_meas {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hL2 : MemLp (X 0) 2 P)
    (h0 : ∫ ω, X 0 ω ∂P = 0) (σ : ℝ) (hσ : 0 < σ) (hvar : variance (X 0) P = σ ^ 2)
    (ψ : ℝ → ℝ) (hψ : Tendsto ψ atTop atTop) (m : ℝ → Ω → ℕ) (hm_meas : ∀ t, Measurable (m t))
    (hm_ratio : TendstoInMeasure P (fun t ω => (m t ω : ℝ) / ψ t) atTop (fun _ => 1)) :
    ∀ α : ℝ, Tendsto
      (fun t : ℝ => P.real {ω | psum X (m t ω) ω / (σ * Real.sqrt (ψ t)) ≤ α})
      atTop (𝓝 (cdf (gaussianReal 0 1) α)) := by
  -- normalised sequence
  set X' : ℕ → Ω → ℝ := fun k ω => X k ω / σ with hX'
  have hind' : iIndepFun X' P := hind.comp (fun _ x => x / σ) (fun _ => by fun_prop)
  have hident' : ∀ i, IdentDistrib (X' i) (X' 0) P P :=
    fun i => (hident i).comp (u := fun x => x / σ) (by fun_prop)
  have h0' : P[X' 0] = 0 := by
    simp only [hX']
    rw [integral_div, h0, zero_div]
  have h1' : P[X' 0 ^ 2] = 1 := by
    have : (X' 0 ^ 2) = fun ω => X 0 ω ^ 2 / σ ^ 2 := by
      ext ω; simp [hX', div_pow]
    rw [this, integral_div, ← variance_of_integral_eq_zero (hident 0).aemeasurable_fst h0, hvar,
      div_self (by positivity)]
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum (P := P) (P' := gaussianReal 0 1)
    (Y := id) HasLaw.id h0' h1' hind' hident'
  -- along `n t = ⌊ψ t⌋₊`
  have hn : Tendsto (fun t : ℝ => ⌊ψ t⌋₊) atTop atTop := tendsto_nat_floor_atTop.comp hψ
  have hclt2 := tendstoInDistribution_comp hclt hn
  -- rescale by `√n/√ψ → 1`
  set c : ℝ → ℝ := fun t => Real.sqrt (⌊ψ t⌋₊ : ℝ) / Real.sqrt (ψ t) with hc
  have hc1 : Tendsto c atTop (𝓝 1) := by
    have h1 : Tendsto (fun t => (⌊ψ t⌋₊ : ℝ) / ψ t) atTop (𝓝 1) := by
      have hψpos : ∀ᶠ t in atTop, 0 < ψ t := hψ.eventually_gt_atTop 0
      have hlow : Tendsto (fun t => (ψ t - 1) / ψ t) atTop (𝓝 1) := by
        have : Tendsto (fun t => 1 - 1 / ψ t) atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hψ)
        rw [sub_zero] at this
        refine this.congr' ?_
        filter_upwards [hψpos] with t ht
        field_simp
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
      · filter_upwards [hψpos] with t ht
        apply div_le_div_of_nonneg_right _ ht.le
        have := Nat.lt_floor_add_one (ψ t); linarith
      · filter_upwards [hψpos] with t ht
        rw [div_le_one ht]; exact Nat.floor_le ht.le
    have h2 := (Real.continuous_sqrt.tendsto 1).comp h1
    rw [Real.sqrt_one] at h2
    refine h2.congr' ?_
    filter_upwards [hψ.eventually_gt_atTop 0] with t ht
    simp only [Function.comp, hc]
    rw [Real.sqrt_div (Nat.cast_nonneg _)]
  have hslut := hclt2.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop) (tendstoInMeasure_const_of_tendsto hc1)
    (fun _ => aemeasurable_const)
  -- target variable
  set V : ℝ → Ω → ℝ := fun t ω => psum X (m t ω) ω / (σ * Real.sqrt (ψ t)) with hV
  have hVm : ∀ t, Measurable (V t) := fun t =>
    (psum_random_measurable hX (hm_meas t)).div_const _
  have hfl := anscombe_fluct hX hind hident hL2 h0 ψ hψ m hm_ratio hσ
  dsimp only at hslut
  have hdiff : TendstoInMeasure P
      (V - fun t ω => ((Real.sqrt (⌊ψ t⌋₊ : ℝ))⁻¹ * ∑ k ∈ Finset.range ⌊ψ t⌋₊, X' k ω) * c t)
      atTop 0 := by
    refine hfl.congr' ?_ (by rfl)
    filter_upwards [hψ.eventually_ge_atTop 1] with t ht
    filter_upwards with ω
    have hψpos : 0 < ψ t := by linarith
    have hn1 : (1 : ℝ) ≤ (⌊ψ t⌋₊ : ℝ) := by
      have : 1 ≤ ⌊ψ t⌋₊ := Nat.le_floor (by simpa using ht)
      exact_mod_cast this
    have hsn : 0 < Real.sqrt (⌊ψ t⌋₊ : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hsψ : 0 < Real.sqrt (ψ t) := Real.sqrt_pos.2 hψpos
    simp only [Pi.sub_apply, hV, hc, hX', psum]
    rw [← Finset.sum_div]
    field_simp
  have hB : TendstoInDistribution V atTop id (fun _ => P) (gaussianReal 0 1) := by
    have h := tendstoInDistribution_of_tendstoInMeasure_sub V (fun ω : ℝ => id ω * 1) hslut
      hdiff (fun t => (hVm t).aemeasurable)
    have e : (fun ω : ℝ => id ω * 1) = id := by ext; simp
    rw [e] at h
    exact h
  -- pass to distribution functions
  intro α
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hB.tendsto
    (E := Set.Iic α) (by
      rw [frontier_Iic]
      change ((Measure.map id (gaussianReal 0 1)) {α}).toNNReal = 0
      rw [Measure.map_id]
      haveI := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
      rw [measure_singleton]
      rfl)
  have hlim' := (NNReal.continuous_coe.tendsto _).comp hlim
  convert hlim' using 2 with t
  · change P.real {ω | V t ω ≤ α} = (((P.map (V t)) (Set.Iic α)).toNNReal : ℝ)
    rw [ENNReal.coe_toNNReal_eq_toReal, Measure.map_apply (hVm t) measurableSet_Iic,
      measureReal_def]
    rfl
  · change cdf (gaussianReal 0 1) α = (((Measure.map id (gaussianReal 0 1)) (Set.Iic α)).toNNReal : ℝ)
    rw [ENNReal.coe_toNNReal_eq_toReal, Measure.map_id, cdf_eq_real, measureReal_def]

theorem sum_Icc_one_eq (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, f i = ∑ i ∈ Finset.range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_Icc_succ_top (by omega)]

theorem theorem_B_core (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : ℝ → ℝ) (hψ_mono : Monotone ψ) (hψ_unbdd : ¬ BddAbove (Set.range ψ))
    (m : ℝ → Ω → ℕ) (hm_meas : ∀ t, Measurable (m t)) (hm_pos : ∀ t ω, 1 ≤ m t ω)
    (hm_ratio : TendstoInMeasure P (fun t ω => (m t ω : ℝ) / ψ t) atTop (fun _ => 1))
    (y : ℕ → Ω → ℝ) (hy_indep : iIndepFun (fun i => y (i + 1)) P)
    (hy_ident : ∀ i, IdentDistrib (y (i + 1)) (y 1) P P)
    (hy_L2 : MemLp (y 1) 2 P) (hy_mean : ∫ ω, y 1 ω ∂P = 0)
    (σ : ℝ) (hσ_pos : 0 < σ) (hy_var : variance (y 1) P = σ ^ 2) :
    ∀ α : ℝ, Tendsto
      (fun t : ℝ => P.real {ω | (∑ i ∈ Finset.Icc 1 (m t ω), y i ω) / (σ * Real.sqrt (ψ t)) ≤ α})
      atTop (𝓝 (cdf (gaussianReal 0 1) α)) := by
  have hyae : ∀ i, AEMeasurable (y (i + 1)) P := fun i => (hy_ident i).aemeasurable_fst
  set X : ℕ → Ω → ℝ := fun i => (hyae i).mk (y (i + 1)) with hXdef
  have hXm : ∀ i, Measurable (X i) := fun i => (hyae i).measurable_mk
  have hXeq : ∀ i, y (i + 1) =ᵐ[P] X i := fun i => (hyae i).ae_eq_mk
  have hind : iIndepFun X P := (iIndepFun_congr hXeq).1 hy_indep
  have hX0 : y 1 =ᵐ[P] X 0 := hXeq 0
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ((IdentDistrib.of_ae_eq (hyae i) (hXeq i)).symm.trans (hy_ident i)).trans
      (IdentDistrib.of_ae_eq (hyae 0) hX0)
  have hL2 : MemLp (X 0) 2 P := hy_L2.ae_eq hX0
  have h0 : ∫ ω, X 0 ω ∂P = 0 := by rw [← integral_congr_ae hX0]; exact hy_mean
  have hvar : variance (X 0) P = σ ^ 2 := by rw [← variance_congr hX0]; exact hy_var
  have hψ : Tendsto ψ atTop atTop := tendsto_atTop_atTop_of_monotone' hψ_mono hψ_unbdd
  have hmain := theorem_B_meas hXm hind hident hL2 h0 σ hσ_pos hvar ψ hψ m hm_meas hm_ratio
  intro α
  refine (hmain α).congr fun t => ?_
  apply measureReal_congr
  have hall : ∀ᵐ ω ∂P, ∀ i, y (i + 1) ω = X i ω := ae_all_iff.2 hXeq
  filter_upwards [hall] with ω hω
  change (psum X (m t ω) ω / (σ * Real.sqrt (ψ t)) ≤ α) =
    ((∑ i ∈ Finset.Icc 1 (m t ω), y i ω) / (σ * Real.sqrt (ψ t)) ≤ α)
  rw [sum_Icc_one_eq]
  simp only [psum, hω]


end SmithRegenerative.CLT

open SmithRegenerative.CLT


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : ℝ → ℝ) (hψ_mono : Monotone ψ) (hψ_unbdd : ¬ BddAbove (Set.range ψ))
    (m : ℝ → Ω → ℕ) (hm_meas : ∀ t, Measurable (m t)) (hm_pos : ∀ t ω, 1 ≤ m t ω)
    (hm_ratio : TendstoInMeasure P (fun t ω => (m t ω : ℝ) / ψ t) atTop (fun _ => 1))
    (y : ℕ → Ω → ℝ) (hy_indep : iIndepFun (fun i => y (i + 1)) P)
    (hy_ident : ∀ i, IdentDistrib (y (i + 1)) (y 1) P P)
    (hy_L2 : MemLp (y 1) 2 P) (hy_mean : ∫ ω, y 1 ω ∂P = 0)
    (σ : ℝ) (hσ_pos : 0 < σ) (hy_var : variance (y 1) P = σ ^ 2) :
    ∀ α : ℝ, Tendsto
      (fun t : ℝ => P.real {ω | (∑ i ∈ Finset.Icc 1 (m t ω), y i ω) / (σ * Real.sqrt (ψ t)) ≤ α})
      atTop (𝓝 (cdf (gaussianReal 0 1) α)) := by
  exact theorem_B_core P ψ hψ_mono hψ_unbdd m hm_meas hm_pos hm_ratio y hy_indep hy_ident hy_L2 hy_mean σ hσ_pos hy_var

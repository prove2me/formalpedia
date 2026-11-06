-- Prove2me | solution 1 for StochSchedPrec.CMNS.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:42:35.875904+00:00
-- url     : https://prove2.me/submissions/3823445e-699d-4c7b-8559-ace2e88ff578

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

theorem SSP_indep_of_invariant {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (P : V → Ω → ℝ) (hPm : ∀ k, Measurable (P k)) (hP0 : ∀ k ω, 0 ≤ P k ω)
    (hind : iIndepFun P Pr) (j : V) (F : (V → ℝ) → ℝ)
    (hF : AEMeasurable F (Pr.map (fun ω k => P k ω)))
    (hinv : ∀ p : V → ℝ, (∀ k, 0 ≤ p k) → F p = F (Function.update p j 1)) :
    IndepFun (P j) (fun ω => F (fun k => P k ω)) Pr := by
  classical
  set T : Finset V := Finset.univ.erase j with hT
  have hST : Disjoint ({j} : Finset V) T := by simp [hT]
  have h1 := hind.indepFun_finset {j} T hST hPm
  set Y : Ω → (T → ℝ) := fun ω i => P i ω with hYdef
  have hYm : Measurable Y := measurable_pi_lambda _ (fun i => hPm i)
  have hindY : IndepFun (P j) Y Pr := by
    have := h1.comp (measurable_pi_apply (⟨j, Finset.mem_singleton_self j⟩ : ({j} : Finset V)))
      measurable_id
    exact this
  let combine : ℝ × (T → ℝ) → (V → ℝ) := fun z k =>
    if h : k = j then z.1 else z.2 ⟨k, Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩⟩
  have hcomb : Measurable combine := by
    refine measurable_pi_lambda _ (fun k => ?_)
    by_cases h : k = j
    · simp only [combine, h, dite_true]
      exact measurable_fst
    · simp only [combine, h, dite_false]
      exact (measurable_pi_apply _).comp measurable_snd
  set Z : Ω → ℝ × (T → ℝ) := fun ω => (P j ω, Y ω) with hZdef
  have hZm : Measurable Z := (hPm j).prodMk hYm
  have hXZ : (fun ω k => P k ω) = combine ∘ Z := by
    funext ω k
    by_cases h : k = j
    · subst h; simp [combine, Z]
    · simp [combine, Z, Y, h]
  have hmapprod : Pr.map Z = (Pr.map (P j)).prod (Pr.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map (hPm j).aemeasurable hYm.aemeasurable).1 hindY
  have hF' : AEMeasurable (F ∘ combine) (Pr.map Z) := by
    have : Pr.map (fun ω k => P k ω) = (Pr.map Z).map combine := by
      rw [Measure.map_map hcomb hZm, hXZ]
    rw [this] at hF
    exact hF.comp_measurable hcomb
  set H : (T → ℝ) → ℝ := fun y => F (combine (1, y)) with hHdef
  have hGm : MeasurableSet {z : ℝ × (T → ℝ) | 0 ≤ z.1 ∧ ∀ k, 0 ≤ z.2 k} := by
    have : {z : ℝ × (T → ℝ) | 0 ≤ z.1 ∧ ∀ k, 0 ≤ z.2 k}
        = (Set.Ici (0 : ℝ)) ×ˢ (Set.univ.pi fun _ => Set.Ici (0 : ℝ)) := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ici, Set.mem_pi, Set.mem_univ, true_implies, forall_const]
    rw [this]
    exact measurableSet_Ici.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ici)
  have hG : ∀ᵐ z ∂(Pr.map Z), 0 ≤ z.1 ∧ ∀ k, 0 ≤ z.2 k :=
    (ae_map_iff hZm.aemeasurable hGm).2
      (Filter.Eventually.of_forall fun ω => ⟨hP0 j ω, fun k => hP0 k ω⟩)
  have heq : F ∘ combine =ᵐ[Pr.map Z] H ∘ Prod.snd := by
    filter_upwards [hG] with z hz
    have hnn : ∀ k, 0 ≤ combine z k := by
      intro k
      by_cases h : k = j
      · simp only [combine, h, dite_true]; exact hz.1
      · simp only [combine, h, dite_false]; exact hz.2 _
    simp only [Function.comp, H]
    rw [hinv _ hnn]
    congr 1
    funext k
    by_cases h : k = j
    · subst h; simp [combine]
    · simp [combine, h]
  have hH2 : AEMeasurable (H ∘ Prod.snd) ((Pr.map (P j)).prod (Pr.map Y)) := by
    rw [← hmapprod]
    exact hF'.congr heq
  have : IsProbabilityMeasure (Pr.map (P j)) := Measure.isProbabilityMeasure_map (hPm j).aemeasurable
  have : IsProbabilityMeasure (Pr.map Y) := Measure.isProbabilityMeasure_map hYm.aemeasurable
  have hae := Measure.ae_ae_of_ae_prod hH2.ae_eq_mk
  obtain ⟨a, ha⟩ := hae.exists
  have hHρ : AEMeasurable H (Pr.map Y) :=
    ⟨fun y => hH2.mk _ (a, y), hH2.measurable_mk.comp measurable_prodMk_left, ha⟩
  have hfin := hindY.comp₀ (hPm j).aemeasurable hYm.aemeasurable aemeasurable_id hHρ
  have hFY : (fun ω => F (fun k => P k ω)) = H ∘ Y := by
    funext ω
    simp only [Function.comp, H]
    rw [hinv _ (fun k => hP0 k ω)]
    congr 1
    funext k
    by_cases h : k = j
    · subst h; simp [combine]
    · simp [combine, h, Y]
  rw [hFY]
  exact hfin

open StochSchedPrec.CMNS in
theorem SSP_det_load {V : Type*} [Fintype V] [DecidableEq V] (W : Finset V) (m : ℕ) (hm : 0 < m)
    (p S : V → ℝ) (hp : ∀ j, 0 ≤ p j) (hS : ∀ j, 0 ≤ S j) (hbusy : ∀ t, busy p S t ≤ m) :
    (∑ j ∈ W, p j) ^ 2 / (2 * m) ≤ ∑ j ∈ W, p j * (S j + p j / 2) := by
  classical
  set T := ∑ j ∈ W, p j with hTdef
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set a : ℝ := T / m with ha
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun j _ => hp j)
  have ha0 : 0 ≤ a := div_nonneg hT0 hmR.le
  -- interval integrals of affine functions
  have hInt : ∀ c d : ℝ, Integrable ((Set.Ico c d).indicator (fun t => t - a)) := by
    intro c d
    rw [integrable_indicator_iff measurableSet_Ico]
    exact ((continuous_id.sub continuous_const).integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
  have hI : ∀ c d : ℝ, c ≤ d →
      ∫ t, (Set.Ico c d).indicator (fun t => t - a) t = (d ^ 2 - c ^ 2) / 2 - a * (d - c) := by
    intro c d hcd
    rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hcd, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
        intervalIntegrable_const, integral_id, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  set b : ℝ → ℝ := fun t => ∑ j ∈ W, (Set.Ico (S j) (S j + p j)).indicator (fun _ => (1 : ℝ)) t
    with hb
  have hb_le : ∀ t, b t ≤ m := by
    intro t
    have h1 : b t = ((W.filter fun j => S j ≤ t ∧ t < S j + p j).card : ℝ) := by
      simp only [hb, Set.indicator_apply, Set.mem_Ico]
      rw [Finset.sum_boole]
    rw [h1]
    have h2 : (W.filter fun j => S j ≤ t ∧ t < S j + p j).card ≤ busy p S t := by
      unfold busy
      exact Finset.card_le_card (Finset.monotone_filter_left _ (Finset.subset_univ W))
    exact_mod_cast le_trans h2 (hbusy t)
  have hb_nn : ∀ t, 0 ≤ b t := fun t =>
    Finset.sum_nonneg (fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) t)
  have hb_neg : ∀ t, t < 0 → b t = 0 := by
    intro t ht
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [Set.indicator_of_notMem]
    simp only [Set.mem_Ico, not_and, not_lt]
    intro h
    linarith [hS j]
  -- pointwise comparison with the "bathtub" profile
  have hpt : ∀ t, (m : ℝ) * (Set.Ico 0 a).indicator (fun t => t - a) t
      ≤ ∑ j ∈ W, (Set.Ico (S j) (S j + p j)).indicator (fun t => t - a) t := by
    intro t
    have hsum : ∑ j ∈ W, (Set.Ico (S j) (S j + p j)).indicator (fun t => t - a) t
        = (t - a) * b t := by
      simp only [hb, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases h : t ∈ Set.Ico (S j) (S j + p j)
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [hsum]
    rcases lt_or_ge t 0 with h0 | h0
    · rw [hb_neg t h0, Set.indicator_of_notMem (by simp only [Set.mem_Ico, not_and]; intro h; linarith)]
      simp
    rcases lt_or_ge t a with h1 | h1
    · rw [Set.indicator_of_mem (by exact ⟨h0, h1⟩)]
      have := hb_le t
      nlinarith
    · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ico, not_and, not_lt]; intro _; exact h1)]
      have := hb_nn t
      nlinarith
  have hmono := integral_mono ((hInt 0 a).const_mul (m : ℝ))
    (integrable_finsetSum _ (fun j _ => hInt (S j) (S j + p j))) hpt
  rw [integral_const_mul, hI 0 a ha0, integral_finsetSum _ (fun j _ => hInt (S j) (S j + p j))] at hmono
  have hR : ∑ j ∈ W, ∫ t, (Set.Ico (S j) (S j + p j)).indicator (fun t => t - a) t
      = ∑ j ∈ W, p j * (S j + p j / 2) - a * T := by
    rw [hTdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hI _ _ (by linarith [hp j])]
    ring
  rw [hR] at hmono
  have hfin : T ^ 2 / (2 * m) = a * T - m * (a ^ 2 / 2) := by
    rw [ha]
    field_simp
    ring
  rw [hfin]
  have : (m : ℝ) * ((a ^ 2 - 0 ^ 2) / 2 - a * (a - 0)) = -(m * (a ^ 2 / 2)) := by ring
  linarith

open StochSchedPrec.CMNS in
theorem SSP_start_invariant {V : Type*} [Fintype V] [DecidableEq V]
    (pol : (V → ℝ) → V → ℝ) (hna : IsNonanticipatory pol) (j : V) (p p' : V → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hp' : ∀ k, 0 ≤ p' k) (hagree : ∀ i, i ≠ j → p' i = p i) :
    pol p j = pol p' j := by
  -- the realization in which `j` starts later is used as the base of the nonanticipation property,
  -- at the earlier start time
  have key : ∀ q q' : V → ℝ, (∀ k, 0 ≤ q k) → (∀ k, 0 ≤ q' k) → (∀ i, i ≠ j → q' i = q i) →
      ¬ pol q j < pol q' j := by
    intro q q' hq hq' hqq hlt
    have h := hna (pol q j) q' q hq' hq ?_ j
    · have := h.1.2 le_rfl
      linarith
    · intro i hi
      have hij : i ≠ j := by
        rintro rfl
        linarith
      have he : q' i = q i := hqq i hij
      refine ⟨fun _ => he.symm, fun h2 => ?_⟩
      rw [← he]; exact h2
  rcases lt_trichotomy (pol p j) (pol p' j) with h | h | h
  · exact absurd h (key p p' hp hp' hagree)
  · exact h
  · exact absurd h (key p' p hp' hp (fun i hi => (hagree i hi).symm))

open StochSchedPrec.CMNS in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j)
    (P : V → Ω → ℝ) (hP : IsStochModel Pr P) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hCV : HasCVBound Pr P Δ)
    (pol : (V → ℝ) → V → ℝ) (hpol : IsAdmissiblePolicy m A r Pr P pol)
    (hpolm : AEMeasurable pol (Pr.map (fun ω k => P k ω))) (W : Finset V) :
    loadFn m Δ (fun j => ∫ ω, P j ω ∂Pr) W
      ≤ ∑ j ∈ W, (∫ ω, P j ω ∂Pr) * ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr := by
  set μ : V → ℝ := fun j => ∫ ω, P j ω ∂Pr with hμdef
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hPi : ∀ j, Integrable (P j) Pr := hP.2.2.1
  have hP0 : ∀ j ω, 0 ≤ P j ω := hP.2.1
  have hX0 : ∀ ω, ∀ k, 0 ≤ (fun k => P k ω) k := fun ω k => hP0 k ω
  set Sf : V → Ω → ℝ := fun j ω => pol (fun k => P k ω) j with hSf
  have hSi : ∀ j, Integrable (Sf j) Pr := by
    intro j
    have := (hpol.2.2 j).sub (hPi j)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [Sf]
  -- independence of `P j` and the start time of `j`
  have hind : ∀ j, IndepFun (P j) (Sf j) Pr := by
    intro j
    refine SSP_indep_of_invariant P hP.1 hP0 hP.2.2.2 j (fun p => pol p j)
      ((measurable_pi_apply j).comp_aemeasurable hpolm) ?_
    intro p hp
    refine SSP_start_invariant pol hpol.2.1 j p _ hp ?_ ?_
    · intro k
      by_cases h : k = j
      · subst h; simp
      · simp [h, hp k]
    · intro i hi
      simp [hi]
  have hPS : ∀ j, ∫ ω, P j ω * Sf j ω ∂Pr = μ j * ∫ ω, Sf j ω ∂Pr := fun j =>
    (hind j).integral_fun_mul_eq_mul_integral (hPi j).aestronglyMeasurable
      (hSi j).aestronglyMeasurable
  have hPSi : ∀ j, Integrable (fun ω => P j ω * Sf j ω) Pr := fun j =>
    (hind j).integrable_mul (hPi j) (hSi j)
  have hsq : ∀ j, Integrable (fun ω => P j ω ^ 2) Pr := fun j => (hCV j).1.integrable_sq
  -- second moments of the sum
  have hprod : ∀ i k, Integrable (fun ω => P i ω * P k ω) Pr := by
    intro i k
    by_cases h : i = k
    · subst h
      exact (hsq i).congr (Filter.Eventually.of_forall fun ω => by simp [sq])
    · exact (hP.2.2.2.indepFun h).integrable_mul (hPi i) (hPi k)
  have hEprod : ∀ i k, ∫ ω, P i ω * P k ω ∂Pr
      = μ i * μ k + if i = k then (∫ ω, P i ω ^ 2 ∂Pr - μ i ^ 2) else 0 := by
    intro i k
    by_cases h : i = k
    · subst h
      simp only [if_true]
      have : (fun ω => P i ω * P i ω) = fun ω => P i ω ^ 2 := by funext ω; ring
      rw [this]; ring
    · simp only [h, if_false, add_zero]
      exact (hP.2.2.2.indepFun h).integral_fun_mul_eq_mul_integral (hPi i).aestronglyMeasurable
        (hPi k).aestronglyMeasurable
  -- pointwise deterministic inequality and its expectation
  have hdet : ∀ ω, (∑ j ∈ W, P j ω) ^ 2 / (2 * m)
      ≤ ∑ j ∈ W, (P j ω * Sf j ω + P j ω ^ 2 / 2) := by
    intro ω
    have hf := hpol.1 (fun k => P k ω) (hX0 ω)
    have := SSP_det_load W m hm (fun k => P k ω) (pol (fun k => P k ω)) (hX0 ω)
      (fun j => le_trans (hr j) (hf.1 j)) hf.2.2
    refine le_trans this (le_of_eq (Finset.sum_congr rfl (fun j _ => ?_)))
    simp only [Sf]
    ring
  have hsumsq : ∀ ω, (∑ j ∈ W, P j ω) ^ 2 = ∑ i ∈ W, ∑ k ∈ W, P i ω * P k ω := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  have hLi : Integrable (fun ω => (∑ j ∈ W, P j ω) ^ 2 / (2 * m)) Pr := by
    have : Integrable (fun ω => ∑ i ∈ W, ∑ k ∈ W, P i ω * P k ω) Pr :=
      integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hprod i k))
    refine (this.div_const (2 * (m : ℝ))).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hsumsq ω]
  have hRi : Integrable (fun ω => ∑ j ∈ W, (P j ω * Sf j ω + P j ω ^ 2 / 2)) Pr :=
    integrable_finsetSum _ (fun j _ => (hPSi j).add ((hsq j).div_const 2))
  have hE := integral_mono hLi hRi hdet
  have hEL : ∫ ω, (∑ j ∈ W, P j ω) ^ 2 / (2 * m) ∂Pr
      = ((∑ j ∈ W, μ j) ^ 2 + ∑ j ∈ W, (∫ ω, P j ω ^ 2 ∂Pr - μ j ^ 2)) / (2 * m) := by
    rw [integral_div]
    congr 1
    simp only [hsumsq]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hprod i k))]
    simp only [fun i => integral_finsetSum (μ := Pr) W (fun k _ => hprod i k), hEprod]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, sq, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp [hi]
  have hER : ∫ ω, ∑ j ∈ W, (P j ω * Sf j ω + P j ω ^ 2 / 2) ∂Pr
      = ∑ j ∈ W, (μ j * ∫ ω, Sf j ω ∂Pr + (∫ ω, P j ω ^ 2 ∂Pr) / 2) := by
    rw [integral_finsetSum (f := fun j ω => P j ω * Sf j ω + P j ω ^ 2 / 2) _
      (fun j _ => (hPSi j).add ((hsq j).div_const 2))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_add (hPSi j) ((hsq j).div_const 2), hPS j, integral_div]
  rw [hEL, hER] at hE
  -- expected completion times
  have hEC : ∀ j, ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr = ∫ ω, Sf j ω ∂Pr + μ j := by
    intro j
    rw [← integral_add (hSi j) (hPi j)]
  simp only [hEC]
  -- variance bounds
  have hvar : ∀ j, ∫ ω, P j ω ^ 2 ∂Pr - μ j ^ 2 ≤ Δ * μ j ^ 2 := by
    intro j
    have h1 := variance_eq_sub (hCV j).1
    have h2 := (hCV j).2.2
    rw [h1] at h2
    simpa [μ] using h2
  set B := ∑ j ∈ W, μ j ^ 2 with hB
  set Vs := ∑ j ∈ W, (∫ ω, P j ω ^ 2 ∂Pr - μ j ^ 2) with hVs
  set Xs := ∑ j ∈ W, μ j * ∫ ω, Sf j ω ∂Pr with hXs
  have hVsB : Vs ≤ Δ * B := by
    rw [hVs, hB, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hvar j)
  have hR' : ∑ j ∈ W, (μ j * ∫ ω, Sf j ω ∂Pr + (∫ ω, P j ω ^ 2 ∂Pr) / 2) = Xs + (Vs + B) / 2 := by
    rw [hXs, hVs, hB, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hR'] at hE
  have hgoal : ∑ j ∈ W, μ j * (∫ ω, Sf j ω ∂Pr + μ j) = Xs + B := by
    rw [hXs, hB, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hgoal]
  unfold loadFn
  rw [← hB]
  set A2 := (∑ j ∈ W, μ j) ^ 2
  rw [div_le_iff₀ (by positivity)] at hE
  have hmVs : ((m : ℝ) - 1) * Vs ≤ ((m : ℝ) - 1) * (Δ * B) :=
    mul_le_mul_of_nonneg_left hVsB (by linarith)
  have hgoal2 : 1 / (2 * (m : ℝ)) * (A2 + B) - ((m : ℝ) - 1) * (Δ - 1) / (2 * (m : ℝ)) * B
      = (A2 + B - ((m : ℝ) - 1) * (Δ - 1) * B) / (2 * m) := by
    field_simp
  rw [hgoal2, div_le_iff₀ (by positivity)]
  nlinarith

-- Prove2me | solution 1 for WaitJudge.Convex.prob_A_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T23:35:12.135533+00:00
-- url     : https://prove2.me/submissions/75e36c1a-a0dc-487f-ad9e-957e4e3fb0ec

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting
import Theorems.Thm_WaitJudge_Convex_A_ae_eq_B

open MeasureTheory ScenarioApproach.Generalization WaitJudge.Convex

theorem solution {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) [IsProbabilityMeasure P]
    (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ)
    (hA1 : Assumption1 c X Xδ tb) (hA2 : Assumption2 c X Xδ tb P)
    (hmeas : MeasurabilityPins c X Xδ tb)
    (ε : ℕ → ℝ) (N k : ℕ) (hk : k ≤ N) :
    (Measure.pi fun _ : Fin N => P) {ω | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧ sstar c X Xδ tb ω = k ∧
        ∀ i : Fin N, i.val < k → i ∈ supportSet c X Xδ tb ω} =
      ENNReal.ofReal (∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(Fk P c X Xδ tb k)) := by
  classical
  -- A = B almost surely
  rw [measure_congr (A_ae_eq_B P c X Xδ tb hA1 hA2 ε N k hk)]
  obtain ⟨n, rfl⟩ : ∃ n, N = k + n := ⟨N - k, by omega⟩
  have hS : MeasurableSet {q : E d × Δ | q.1 ∈ Xδ q.2} := hmeas.1
  have hviol : Measurable (fun x : E d => violation P Xδ x) := by
    have hs : MeasurableSet {q : E d × Δ | q.1 ∉ Xδ q.2} := hmeas.1.compl
    exact (measurable_measure_prodMk_left (ν := P) hs).ennreal_toReal
  have hsec : ∀ x : E d, MeasurableSet {δ | x ∈ Xδ δ} := fun x => measurable_prodMk_left hS
  have hviol01 : ∀ x : E d, violation P Xδ x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  -- probability that a single scenario is satisfied: 1 - V(x)
  have hsat : ∀ x : E d, P {δ | x ∈ Xδ δ} = ENNReal.ofReal (1 - violation P Xδ x) := by
    intro x
    have hc : {δ | x ∈ Xδ δ} = (violationSet Xδ x)ᶜ := by
      ext δ; simp [violationSet]
    have hm : MeasurableSet (violationSet Xδ x) := by
      have : violationSet Xδ x = {δ | x ∈ Xδ δ}ᶜ := by ext δ; simp [violationSet]
      rw [this]; exact (hsec x).compl
    rw [hc, prob_compl_eq_one_sub hm, violation, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
      ENNReal.ofReal_one, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  -- measurability for samples of size k
  have hV : Measurable (fun ω : Fin k → Δ => violation P Xδ (xstar c X Xδ tb ω)) :=
    hviol.comp (hmeas.2 k)
  have hsupp : ∀ i : Fin k, MeasurableSet {ω : Fin k → Δ | i ∈ supportSet c X Xδ tb ω} := by
    intro i
    obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by have := i.isLt; omega⟩
    subst hm
    have hF : ∀ ω : Fin (m + 1) → Δ, feasibleOn X Xδ ω (Finset.univ.erase i) =
        feasibleOn X Xδ (fun j => ω (i.succAbove j)) Finset.univ := by
      intro ω
      ext x
      simp only [feasibleOn, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_erase,
        Finset.mem_univ, and_true, true_implies]
      constructor
      · rintro ⟨hx, h⟩; exact ⟨hx, fun j => h _ (Fin.succAbove_ne i j)⟩
      · rintro ⟨hx, h⟩; refine ⟨hx, fun j hj => ?_⟩
        obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        exact h j'
    have hm1 : Measurable (fun ω : Fin (m + 1) → Δ =>
        sol c tb (feasibleOn X Xδ ω (Finset.univ.erase i))) := by
      simp_rw [hF]
      exact (hmeas.2 m).comp (measurable_pi_lambda _ (fun j => measurable_pi_apply _))
    have : {ω : Fin (m + 1) → Δ | i ∈ supportSet c X Xδ tb ω} =
        {ω | sol c tb (feasibleOn X Xδ ω (Finset.univ.erase i)) = xstar c X Xδ tb ω}ᶜ := by
      ext ω; simp [supportSet, IsSupport, xstar]
    rw [this]
    exact (measurableSet_eq_fun hm1 (hmeas.2 (m + 1))).compl
  have hsstar : Measurable (fun ω : Fin k → Δ => sstar c X Xδ tb ω) := by
    have : (fun ω : Fin k → Δ => sstar c X Xδ tb ω) =
        fun ω => ∑ i : Fin k, Set.indicator {ω | i ∈ supportSet c X Xδ tb ω} (fun _ => 1) ω := by
      funext ω
      simp only [sstar, Finset.card_eq_sum_ones, supportSet, Finset.sum_filter, Set.indicator,
        Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [this]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hsupp i))
  set C : Set (Fin k → Δ) := {ω | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧
    sstar c X Xδ tb ω = k} with hCdef
  have hC : MeasurableSet C :=
    (measurableSet_lt measurable_const hV).inter (measurableSet_eq_fun hsstar measurable_const)
  -- splitting the sample into the first k and the last n scenarios
  let app : (Fin k → Δ) × (Fin n → Δ) → (Fin (k + n) → Δ) := fun q => Fin.append q.1 q.2
  have happ : Measurable app := by
    apply measurable_pi_lambda
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [app, Fin.append_left]; exact (measurable_pi_apply j).comp measurable_fst
    · simp only [app, Fin.append_right]; exact (measurable_pi_apply j).comp measurable_snd
  have hmap : (Measure.pi fun _ : Fin (k + n) => P) =
      ((Measure.pi fun _ : Fin k => P).prod (Measure.pi fun _ : Fin n => P)).map app := by
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply happ (MeasurableSet.univ_pi hs)]
    have : app ⁻¹' Set.pi Set.univ s = (Set.pi Set.univ fun i => s (Fin.castAdd n i)) ×ˢ
        (Set.pi Set.univ fun j => s (Fin.natAdd k j)) := by
      ext q
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod, app]
      simp [Fin.forall_fin_add]
    rw [this, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fin.prod_univ_add]
  have hfirst : ∀ q : (Fin k → Δ) × (Fin n → Δ), firstK hk (app q) = q.1 := by
    intro q; funext j; simp [firstK, app]
  set D : Set ((Fin k → Δ) × (Fin n → Δ)) :=
    {q | q.1 ∈ C ∧ ∀ j : Fin n, (xstar c X Xδ tb q.1, q.2 j) ∈ {q : E d × Δ | q.1 ∈ Xδ q.2}}
    with hDdef
  have hD : MeasurableSet D := by
    have : D = (Prod.fst ⁻¹' C) ∩ ⋂ j : Fin n,
        (fun q : (Fin k → Δ) × (Fin n → Δ) => (xstar c X Xδ tb q.1, q.2 j)) ⁻¹'
          {q : E d × Δ | q.1 ∈ Xδ q.2} := by
      ext q; simp [hDdef]
    rw [this]
    exact (measurable_fst hC).inter (MeasurableSet.iInter fun j =>
      (((hmeas.2 k).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd)) hS)
  set B : Set (Fin (k + n) → Δ) := {ω | ε k < violation P Xδ (xstar c X Xδ tb (firstK hk ω)) ∧
        sstar c X Xδ tb (firstK hk ω) = k ∧
        ∀ j : Fin (k + n), k ≤ j.val → xstar c X Xδ tb (firstK hk ω) ∈ Xδ (ω j)} with hBdef
  have hpre : app ⁻¹' B = D := by
    ext q
    simp only [hBdef, hDdef, hCdef, Set.mem_preimage, Set.mem_setOf_eq, hfirst]
    rw [and_assoc]
    apply and_congr_right; intro _; apply and_congr_right; intro _
    constructor
    · intro h j
      have := h (Fin.natAdd k j) (by simp)
      simpa [app] using this
    · intro h j hj
      induction j using Fin.addCases with
      | left i => exact absurd hj (by simp)
      | right j => simpa [app] using h j
  have hBmeas : MeasurableSet B := by
    have hfk : Measurable (fun ω : Fin (k + n) → Δ => firstK hk ω) :=
      measurable_pi_lambda _ (fun j => measurable_pi_apply _)
    have : B = (fun ω => firstK hk ω) ⁻¹' C ∩ ⋂ j : Fin (k + n), ⋂ (_ : k ≤ j.val),
          (fun ω : Fin (k + n) → Δ => (xstar c X Xδ tb (firstK hk ω), ω j)) ⁻¹'
            {q : E d × Δ | q.1 ∈ Xδ q.2} := by
      ext ω; simp [hBdef, hCdef, and_assoc]
    rw [this]
    refine (hfk hC).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_)
    exact (((hmeas.2 k).comp hfk).prodMk (measurable_pi_apply j)) hS
  rw [hmap, Measure.map_apply happ hBmeas, hpre, Measure.prod_apply hD]
  have hslice : ∀ ω₁ : Fin k → Δ, (Measure.pi fun _ : Fin n => P) (Prod.mk ω₁ ⁻¹' D) =
      C.indicator (fun ω₁ => P {δ | xstar c X Xδ tb ω₁ ∈ Xδ δ} ^ n) ω₁ := by
    intro ω₁
    by_cases h : ω₁ ∈ C
    · have : Prod.mk ω₁ ⁻¹' D = Set.pi Set.univ fun _ => {δ | xstar c X Xδ tb ω₁ ∈ Xδ δ} := by
        ext ω₂; simp [hDdef, h]
      rw [this, Measure.pi_pi, Set.indicator_of_mem h]
      simp
    · have : Prod.mk ω₁ ⁻¹' D = ∅ := by
        ext ω₂; simp [hDdef, h]
      rw [this, Set.indicator_of_notMem h]
      simp
  rw [lintegral_congr (fun ω₁ => hslice ω₁), lintegral_indicator hC]
  -- the right-hand side
  have hcont : Continuous (fun v : ℝ => (1 - v) ^ (k + n - k)) := by fun_prop
  haveI : IsFiniteMeasure (Fk P c X Xδ tb k) := by unfold Fk; infer_instance
  have hint : Integrable (fun v : ℝ => (1 - v) ^ (k + n - k))
      ((Fk P c X Xδ tb k).restrict (Set.Ioc (ε k) 1)) :=
    (hcont.continuousOn.integrableOn_compact (K := Set.Icc (ε k) 1) isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[(Fk P c X Xδ tb k).restrict (Set.Ioc (ε k) 1)]
      (fun v : ℝ => (1 - v) ^ (k + n - k)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact pow_nonneg (by linarith [hv.2]) _
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
  unfold Fk
  rw [setLIntegral_map measurableSet_Ioc (by fun_prop) hV,
    Measure.restrict_restrict (hV measurableSet_Ioc)]
  have hset : (fun ω : Fin k → Δ => violation P Xδ (xstar c X Xδ tb ω)) ⁻¹' Set.Ioc (ε k) 1 ∩
      {ω | sstar c X Xδ tb ω = k} = C := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc, Set.mem_setOf_eq, hCdef]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, (hviol01 _).2⟩, h2⟩
  rw [hset]
  apply setLIntegral_congr_fun hC
  intro ω _
  dsimp only
  rw [hsat, Nat.add_sub_cancel_left, ENNReal.ofReal_pow (by linarith [(hviol01 (xstar c X Xδ tb ω)).2])]

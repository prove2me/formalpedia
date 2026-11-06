-- Prove2me | solution 1 for StochSchedPrec.CMNS.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:25:51.269655+00:00
-- url     : https://prove2.me/submissions/eb405064-66b2-4137-a524-f05094fedca5

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm
import Theorems.Thm_StochSchedPrec_CMNS_theorem_2_8
import Theorems.Thm_StochSchedPrec_CMNS_lemma_3_3
import Theorems.Thm_StochSchedPrec_CMNS_lp_relaxation
import Theorems.Thm_StochSchedPrec_CMNS_critical_chain_lower_bound

open MeasureTheory ProbabilityTheory

open StochSchedPrec.CMNS in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r w : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hw : ∀ j, 0 ≤ w j)
    (hAss : ∀ i j, Relation.TransGen A i j → r i ≤ r j)
    (P : V → Ω → ℝ) (hP : IsStochModel Pr P) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hCV : HasCVBound Pr P Δ)
    (C : V → ℝ) (hC : IsLPOptimal m A Δ (fun j => ∫ ω, P j ω ∂Pr) w C)
    (L : Fin (Fintype.card V) ≃ V) (hL : IsSortedBy L C) (β : ℝ) (hβ : 0 < β)
    (σ : (V → ℝ) → V → ℝ) (hσ : IsCMNSPolicy m A r L β (fun j => ∫ ω, P j ω ∂Pr) σ)
    (hσna : IsNonanticipatory σ)
    (hσm : AEMeasurable σ (Pr.map (fun ω k => P k ω)))
    (pol : (V → ℝ) → V → ℝ) (hpol : IsAdmissiblePolicy m A r Pr P pol)
    (hpolm : AEMeasurable pol (Pr.map (fun ω k => P k ω))) :
    Integrable (fun ω => ∑ j, w j * (σ (fun k => P k ω) j + P j ω)) Pr ∧
    ∫ ω, ∑ j, w j * (σ (fun k => P k ω) j + P j ω) ∂Pr
      ≤ (1 + β) * (1 + 1 / β + max 1 (((m : ℝ) - 1) / m * Δ))
          * ∫ ω, ∑ j, w j * (pol (fun k => P k ω) j + P j ω) ∂Pr := by
  set μ : V → ℝ := fun j => ∫ ω, P j ω ∂Pr with hμdef
  have hμpos : ∀ j, 0 < μ j := fun j => (hCV j).2.1
  have hμnn : ∀ j, 0 ≤ μ j := fun j => (hμpos j).le
  -- the LP order is a linear extension of the precedence constraints
  have hlt : ∀ i j, Relation.TransGen A i j → C i < C j := by
    intro i j h
    induction h with
    | single hab => linarith [hC.1.2.1 _ _ hab, hμpos ‹V›]
    | tail _ hbc ih => linarith [hC.1.2.1 _ _ hbc, hμpos ‹V›]
  have hLE : IsLinearExtension A L := by
    intro i j h
    by_contra hcon
    push Not at hcon
    have := hL _ _ hcon
    simp only [Equiv.apply_symm_apply] at this
    linarith [hlt i j h]
  set tb : V ≃ Fin (Fintype.card V) := L.symm
  have h28 := fun j => theorem_2_8 m hm A hacyc r hr hAss P hP L hLE β hβ tb σ hσ hσna hσm j
  set M : ℝ := max 1 (((m : ℝ) - 1) / m * Δ) with hM
  have h33 := fun j => lemma_3_3 m hm Δ hΔ μ hμnn C hC.1.1 hC.1.2.2 L hL j
  have hlp := lp_relaxation m hm A hacyc r w hr hw P hP Δ hΔ hCV pol hpol hpolm
  have hXm : Measurable (fun ω k => P k ω) := measurable_pi_lambda _ (fun k => hP.1 k)
  have hσm' : AEMeasurable (fun ω => σ (fun k => P k ω)) Pr :=
    hσm.comp_aemeasurable hXm.aemeasurable
  have hccl := (critical_chain_lower_bound m hm A hacyc r hr tb (Pr := Pr)).2 P hP σ hσm' pol hpol
  -- integrability
  have hIσ : ∀ j, Integrable (fun ω => σ (fun k => P k ω) j + P j ω) Pr := fun j => (h28 j).1
  have hIp : ∀ j, Integrable (fun ω => pol (fun k => P k ω) j + P j ω) Pr := hpol.2.2
  have hint : Integrable (fun ω => ∑ j, w j * (σ (fun k => P k ω) j + P j ω)) Pr :=
    integrable_finsetSum _ (fun j _ => (hIσ j).const_mul (w j))
  refine ⟨hint, ?_⟩
  rw [integral_finsetSum _ (fun j _ => (hIσ j).const_mul (w j)),
    integral_finsetSum _ (fun j _ => (hIp j).const_mul (w j))]
  simp only [integral_const_mul]
  set Eσ : V → ℝ := fun j => ∫ ω, (σ (fun k => P k ω) j + P j ω) ∂Pr
  set Ep : V → ℝ := fun j => ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr
  set El : V → ℝ := fun j =>
    ∫ ω, chainLength A r tb (fun k => P k ω) (σ (fun k => P k ω)) j ∂Pr
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- release date lower bound
  have hrE : ∀ j, r j ≤ Ep j := by
    intro j
    have : ∫ ω, r j ∂Pr ≤ Ep j := by
      apply integral_mono (integrable_const _) (hIp j)
      intro ω
      have h1 := (hpol.1 (fun k => P k ω) (fun k => hP.2.1 k ω)).1 j
      have h2 := hP.2.1 j ω
      simp only
      linarith
    simpa using this
  -- the LP value is a lower bound
  have hLPlb : ∑ j, w j * C j ≤ ∑ j, w j * Ep j := by
    have := hlp.2 C hC
    rw [integral_finsetSum _ (fun j _ => (hIp j).const_mul (w j))] at this
    simpa [integral_const_mul] using this
  -- per-job bound
  have hjob : ∀ j, Eσ j ≤ (1 + 1 / β) * Ep j + (1 + β) * (1 + M) * C j := by
    intro j
    have hA := (h28 j).2
    have hB := h33 j
    have hCc := hccl j
    have ha : 0 ≤ ((m : ℝ) - 1) / m + 1 / β := by
      have : 0 ≤ ((m : ℝ) - 1) / m := div_nonneg (by linarith) hmR.le
      have : 0 ≤ 1 / β := by positivity
      linarith
    have e1 : (((m : ℝ) - 1) / m + 1 / β) * El j ≤ (((m : ℝ) - 1) / m + 1 / β) * Ep j :=
      mul_le_mul_of_nonneg_left hCc ha
    have e2 : (1 + β) / m * ∑ i ∈ before L j, μ i ≤ (1 + β) * ((1 + M) * C j) := by
      have hB' : 1 / (m : ℝ) * ∑ i ∈ before L j, μ i ≤ (1 + M) * C j := hB
      calc (1 + β) / m * ∑ i ∈ before L j, μ i
          = (1 + β) * (1 / (m : ℝ) * ∑ i ∈ before L j, μ i) := by ring
        _ ≤ (1 + β) * ((1 + M) * C j) := mul_le_mul_of_nonneg_left hB' (by linarith)
    have e3 : 1 / (m : ℝ) * r j ≤ 1 / (m : ℝ) * Ep j :=
      mul_le_mul_of_nonneg_left (hrE j) (by positivity)
    have e4 : (((m : ℝ) - 1) / m + 1 / β) * Ep j + 1 / (m : ℝ) * Ep j = (1 + 1 / β) * Ep j := by
      field_simp
      ring
    have : Eσ j ≤ (((m : ℝ) - 1) / m + 1 / β) * El j
        + (1 + β) / m * ∑ i ∈ before L j, μ i + 1 / (m : ℝ) * r j := hA
    nlinarith
  calc ∑ j, w j * Eσ j
      ≤ ∑ j, w j * ((1 + 1 / β) * Ep j + (1 + β) * (1 + M) * C j) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hjob j) (hw j))
    _ = (1 + 1 / β) * ∑ j, w j * Ep j + (1 + β) * (1 + M) * ∑ j, w j * C j := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
    _ ≤ (1 + 1 / β) * ∑ j, w j * Ep j + (1 + β) * (1 + M) * ∑ j, w j * Ep j := by
        have : 0 ≤ (1 + β) * (1 + M) := by
          have : (1 : ℝ) ≤ M := le_max_left _ _
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hLPlb this]
    _ = (1 + β) * (1 + 1 / β + M) * ∑ j, w j * Ep j := by
        field_simp
        ring

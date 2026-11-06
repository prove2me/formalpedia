-- Prove2me | solution 1 for StochSchedPrec.CMNS.lp_relaxation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:28:51.744652+00:00
-- url     : https://prove2.me/submissions/b5a5d807-da07-40be-850c-6cac192975d5

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm
import Theorems.Thm_StochSchedPrec_CMNS_theorem_3_1

open MeasureTheory ProbabilityTheory

open StochSchedPrec.CMNS in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r w : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hw : ∀ j, 0 ≤ w j)
    (P : V → Ω → ℝ) (hP : IsStochModel Pr P) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hCV : HasCVBound Pr P Δ)
    (pol : (V → ℝ) → V → ℝ) (hpol : IsAdmissiblePolicy m A r Pr P pol)
    (hpolm : AEMeasurable pol (Pr.map (fun ω k => P k ω))) :
    IsLPFeasible m A Δ (fun j => ∫ ω, P j ω ∂Pr)
        (fun j => ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr) ∧
      ∀ C : V → ℝ, IsLPOptimal m A Δ (fun j => ∫ ω, P j ω ∂Pr) w C →
        ∑ j, w j * C j ≤ ∫ ω, ∑ j, w j * (pol (fun k => P k ω) j + P j ω) ∂Pr := by
  have hIp : ∀ j, Integrable (fun ω => pol (fun k => P k ω) j + P j ω) Pr := hpol.2.2
  have hfeas : ∀ ω, IsFeasible m A r (fun k => P k ω) (pol (fun k => P k ω)) :=
    fun ω => hpol.1 (fun k => P k ω) (fun k => hP.2.1 k ω)
  have hF : IsLPFeasible m A Δ (fun j => ∫ ω, P j ω ∂Pr)
      (fun j => ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr) := by
    refine ⟨fun W => theorem_3_1 m hm A hacyc r hr P hP Δ hΔ hCV pol hpol hpolm W, ?_, ?_⟩
    · intro i j hij
      have h : ∫ ω, (pol (fun k => P k ω) i + P i ω + P j ω) ∂Pr
          ≤ ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr := by
        apply integral_mono ((hIp i).add (hP.2.2.1 j)) (hIp j)
        intro ω
        have := (hfeas ω).2.1 i j hij
        show pol (fun k => P k ω) i + P i ω + P j ω ≤ pol (fun k => P k ω) j + P j ω
        linarith
      rw [integral_add (hIp i) (hP.2.2.1 j)] at h
      exact h
    · intro j
      apply integral_mono (hP.2.2.1 j) (hIp j)
      intro ω
      have := (hfeas ω).1 j
      have h2 := hr j
      simp only at this ⊢
      linarith
  refine ⟨hF, fun C hC => ?_⟩
  rw [integral_finsetSum _ (fun j _ => (hIp j).const_mul (w j))]
  simp only [integral_const_mul]
  exact hC.2 _ hF

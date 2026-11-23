-- Prove2me | solution 1 for PI.NglqJacSplitW.chiM_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:07.310055+00:00
-- url     : https://prove2.me/submissions/a5cf2e4c-676a-44f4-9549-1aa79f1b9cc8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal
open PI PI.NglqJacSplitW
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.NglqJacSplitW
theorem _root_.solution [mF : MeasurableSpace (ι → F)] [hB : BorelSpace (ι → F)] (M : Matrix ι ι F)
    (hM : IsUnit M.det) (ν : Measure (ι → F)) [ν.IsAddHaarMeasure] (S : Set (ι → F)) :
    ν ((fun x => M *ᵥ x) '' S) = chiM M hM * ν S := by
  obtain rfl : mF = borel (ι → F) := hB.measurable_eq
  let _ : MeasurableSpace (ι → F) := borel _
  have _ : BorelSpace (ι → F) := ⟨rfl⟩
  have e : chiM M hM = addEquivAddHaarChar (phiM M hM) := rfl
  have himg : (fun x => M *ᵥ x) '' S = (phiM M hM).symm ⁻¹' S := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (phiM M hM).symm ((phiM M hM) x) = x := (phiM M hM).symm_apply_apply x
      rw [show M *ᵥ x = (phiM M hM) x from rfl, this]
      exact hx
    · intro hy
      exact ⟨(phiM M hM).symm y, hy, (phiM M hM).apply_symm_apply y⟩
  have key := addEquivAddHaarChar_smul_preimage ν (X := S) (phiM M hM).symm
  rw [addEquivAddHaarChar_symm, ENNReal.smul_def, smul_eq_mul] at key
  rw [himg, e, ← key, ← mul_assoc, ← ENNReal.coe_mul,
    mul_inv_cancel₀ (addEquivAddHaarChar_pos (phiM M hM)).ne', ENNReal.coe_one, one_mul]
end PI.NglqJacSplitW

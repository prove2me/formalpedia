-- Prove2me | solution 1 for PI.Dv.Tr.degL_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:29.003051+00:00
-- url     : https://prove2.me/submissions/8668af4a-9281-45be-a9dc-9ba8d009c4ab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_FgOfLeL
import Theorems.Thm_PI_Dv_Tr_fg_of_le_L
import Theorems.Thm_Formalism_F_covolBasic
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HN_plLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
namespace PI.Dv.Tr
theorem _root_.solution (A : Formalism.BasicNotions.HLat K) (hA : A.Good) (M : Submodule (𝓞 K) A.V) (hM : M ≤ A.L) :
    degL A M = (2 / (finrank ℚ K : ℝ)) * Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize A.b A.X) M +
      (Formalism.HN.rkK M : ℝ) * kap K := by
  have hpl := Formalism.HN.plLat K A.V A.ι A.b A.X hA.1 M (fg_of_le_L A hA M hM)
  have hq : (finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  unfold degL Formalism.HN.muDef kap
  by_cases h0 : Formalism.HN.rkK M = 0
  · have hMb : M = ⊥ := by
      have hs : Submodule.span K (M : Set A.V) = ⊥ := by
        have : FiniteDimensional K A.V := Module.Finite.of_basis A.b
        exact Submodule.finrank_eq_zero.mp h0
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ Submodule.span K (M : Set A.V) := Submodule.subset_span hx
      rw [hs] at this
      exact (Submodule.mem_bot K).mp this ▸ (Submodule.mem_bot _).mpr rfl
    have hdeg : Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize A.b A.X) M = 0 := by
      rw [hMb]
      unfold Formalism.HN.deg
      have : Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize A.b A.X) (⊥ : Submodule (𝓞 K) A.V) = ⊥ := by
        ext u
        simp [Formalism.HN.zl]
      rw [this]
      unfold Formalism.F.deg
      rw [(Formalism.F.covolBasic _).1, Real.log_one, neg_zero]
    rw [h0, hdeg]
    simp
  · have hrk : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize A.b A.X) M : ℝ) = (finrank ℚ K : ℝ) * (Formalism.HN.rkK M : ℝ) := by
      rw [hpl.2.1]
      push_cast
      ring
    have h0' : (Formalism.HN.rkK M : ℝ) ≠ 0 := by exact_mod_cast h0
    unfold Formalism.HN.slope Formalism.F.slope
    have : (Formalism.F.rk (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize A.b A.X) M) : ℝ) =
        (finrank ℚ K : ℝ) * (Formalism.HN.rkK M : ℝ) := hrk
    rw [this]
    unfold Formalism.HN.deg
    field_simp
    ring
end PI.Dv.Tr

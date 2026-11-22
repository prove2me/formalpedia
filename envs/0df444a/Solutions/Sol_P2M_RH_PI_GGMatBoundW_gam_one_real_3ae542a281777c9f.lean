-- Prove2me | solution 1 for P2M_RH_PI_GGMatBoundW_gam_one_real_3ae542a281777c9f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:46.586315+00:00
-- url     : https://prove2.me/submissions/3da449df-2191-40ab-9a24-3c8c8b4bf3f2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_RepresentationDimensionPos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_IrreducibleOfMinimal
import Theorems.Thm_Formalism_L2_SG_GGMirabolic_isUni_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace PI.GGMatBoundW
theorem _root_.solution (ψ₀ : AddChar F ℂ) :
    gam ψ₀ (1 : GL (Fin k) F) = (((Fintype.card (GL (Fin k) F) : ℝ) / (cardU F k : ℝ) : ℝ) : ℂ) := by
  have hsd : superdiag k (1 : Matrix (Fin k) (Fin k) F) = 0 := by
    unfold superdiag
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h
    · rw [Matrix.one_apply_ne]
      intro hij
      subst hij
      omega
    · rfl
  have hpsi : psiNat ψ₀ (1 : GL (Fin k) F) = 1 := by
    unfold psiNat psiU
    rw [if_pos isUni_one, Units.val_one, hsd, AddChar.map_zero_eq_one]
  unfold gam
  have h1 : ∀ y : GL (Fin k) F, y * 1 * y⁻¹ = 1 := fun y => by group
  have h2 : ∀ y : GL (Fin k) F, y * y⁻¹ = 1 := fun y => by group
  simp only [h1, h2, hpsi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  push_cast
  ring
end PI.GGMatBoundW

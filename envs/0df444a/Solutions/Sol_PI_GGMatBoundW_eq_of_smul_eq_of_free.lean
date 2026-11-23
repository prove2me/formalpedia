-- Prove2me | solution 1 for PI.GGMatBoundW.eq_of_smul_eq_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:41.461986+00:00
-- url     : https://prove2.me/submissions/6c04a318-a0b1-4140-b070-8238d480dde1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GammaMatrixInverse
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_MatrixCoefficientEquation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {G : Type} [Group G] {X : Type} [MulAction Gᵐᵒᵖ X]
namespace PI.GGMatBoundW
theorem _root_.solution (hfree : ∀ (x : Gᵐᵒᵖ) (j : X), x • j = j → x = 1) {a b : Gᵐᵒᵖ} {j : X}
    (h : a • j = b • j) : a = b := by
  have h1 : (b⁻¹ * a) • j = j := by rw [mul_smul, h, inv_smul_smul]
  exact (inv_mul_eq_one.mp (hfree _ _ h1)).symm
end PI.GGMatBoundW

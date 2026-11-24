-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormOfDividedForm_algebraMap_sum_smul_6222df7c2298
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:59.029406+00:00
-- url     : https://prove2.me/submissions/4d88f2d6-52db-47b8-a6b4-b174c0793746

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormOfDividedForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PNormOfDividedForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.NormOfDividedForm
variable {O B K L : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [Field K] [Field L] [Algebra O K]
  [IsFractionRing O K] [Algebra B L] [Algebra K L] [Algebra O L] [IsScalarTower O K L] [IsScalarTower O B L]
  [IsLocalization (Algebra.algebraMapSubmonoid B O⁰) L]
omit [IsDomain O] [IsFractionRing O K] [IsLocalization (Algebra.algebraMapSubmonoid B O⁰) L]
namespace GroundTheory.Heights₂.Heights.NormOfDividedForm
theorem _root_.solution {n : ℕ} (η : Fin n → B) (v : Fin n → O) :
    algebraMap B L (∑ m, v m • η m) = ∑ m, algebraMap O K (v m) • algebraMap B L (η m) := by
  simp only [map_sum, Algebra.smul_def, map_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← IsScalarTower.algebraMap_apply O B L, IsScalarTower.algebraMap_apply O K L]
end GroundTheory.Heights₂.Heights.NormOfDividedForm

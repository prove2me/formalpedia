-- Prove2me | solution 1 for PI.WAU.coord_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:42.944055+00:00
-- url     : https://prove2.me/submissions/fe656e40-2f56-4285-9c68-9af1b4c7ee85

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Theorems.Thm_PI_WAU_coord_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open scoped TensorProduct
variable {F E B : Type} [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
namespace PI.WAU
theorem _root_.solution (e : E) :
    coord b (Algebra.TensorProduct.includeLeftRingHom (R := F) (B := B) e) = fun k => algebraMap F B (b.repr e k) := by
  funext k
  simp [Algebra.TensorProduct.includeLeftRingHom_apply, coord_tmul, Algebra.algebraMap_eq_smul_one]
end PI.WAU

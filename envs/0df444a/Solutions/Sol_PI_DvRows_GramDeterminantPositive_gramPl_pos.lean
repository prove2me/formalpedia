-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.gramPl_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:21:19.147272+00:00
-- url     : https://prove2.me/submissions/bb072726-b3d9-4400-aef5-ad10a30b0db6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
import Theorems.Thm_PI_DvRows_GramDeterminantPositive_pd_det_real
import Theorems.Thm_PI_DvRows_GramDeterminantPositive_gramPl_posDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
open NumberField Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution (A : HLat K) (v : InfinitePlace K) (hX : IsUnit (A.X v).det) {m : ℕ}
    (f : Fin m → A.V) (hf : LinearIndependent K f) : 0 < (Formalism.HN.gramPl A.b A.X v f).det.re :=
  (pd_det_real (gramPl_posDef A v hX f hf)).2
end PI.DvRows.GramDeterminantPositive

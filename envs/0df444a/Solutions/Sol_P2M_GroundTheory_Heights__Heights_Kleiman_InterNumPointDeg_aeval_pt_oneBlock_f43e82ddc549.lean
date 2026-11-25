-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_aeval_pt_oneBlock_f43e82ddc549
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:29:52.991208+00:00
-- url     : https://prove2.me/submissions/0ec400f0-cf38-4363-8e4f-a0d3fb46f967

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumPointDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_apply_c807c9273bfc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.InterNumPointDeg
variable {k : Type u} [Field k] {N : ℕ}
variable [Small.{w} k] (pp : Ideal (Poly k N)) [pp.IsPrime]
namespace GroundTheory.Heights₂.Heights.Kleiman.InterNumPointDeg
theorem _root_.solution (f : OneRing k N) :
    aeval (pt.{u, w} pp) (oneBlock (S := k) (N := N) f) = coneHom pp f := by
  rw [← AlgHom.comp_apply]
  refine congrFun (congrArg DFunLike.coe (MvPolynomial.algHom_ext fun v => ?_)) f
  rcases v with ⟨⟨⟩, i⟩
  rw [AlgHom.comp_apply]
  show aeval (pt.{u, w} pp) (rename (fun v : Σ _ : Unit, Fin (N + 1) => v.2) (X ⟨(), i⟩)) = _
  rw [rename_X, aeval_X]
  rfl
end GroundTheory.Heights₂.Heights.Kleiman.InterNumPointDeg

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLeibniz_dzb_cplx_mul_0e331d7f37e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:27.915793+00:00
-- url     : https://prove2.me/submissions/0b009b67-ad52-41b2-91be-671ba3dfa436

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Theorems.Thm_ReciprocityTheory_AnForm_A_dz_cplx_mul
import Theorems.Thm_ReciprocityTheory_AnForm_A_dzb_cplx_eq_star


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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLeibniz
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.MaDensLeibniz
theorem _root_.solution (k : Fin D) (f g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    dzb k (cplx fun x => f x * g x) y = cplx f y * dzb k (cplx g) y + cplx g y * dzb k (cplx f) y := by
  rw [dzb_cplx_eq_star, dz_cplx_mul k f g y hf hg, dzb_cplx_eq_star, dzb_cplx_eq_star]
  simp [cplx, star_add]
end GroundTheory.Heights₂.Heights.MaDensLeibniz

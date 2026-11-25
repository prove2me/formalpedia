-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_eval__genSubst_eq_map_1ab8fb3a62a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:47.87222+00:00
-- url     : https://prove2.me/submissions/cdc20fe0-da45-42de-970c-79ee754b71aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_map_genSubst_X_a8867dcefebe

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
noncomputable section
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution {B : Type*} [CommRing B] {e : ℕ} (q : MvPolynomial (Fin n) F →+* B)
    (t : Fin n → F) (g : MvPolynomial (Fin e × Fin n) F) :
    eval₂ (C.comp (q.comp C)) (genSubst (fun m => q (X m)) (fun m => q (C (t m)))) g =
      map q (aeval (genSubst (fun m => (X m : MvPolynomial (Fin n) F)) (fun m => C (t m))) g) := by
  rw [aeval_def, eval₂_comp_left]
  congr 1
  · exact RingHom.ext fun r => by
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.algebraMap_apply, map_C,
        MvPolynomial.algebraMap_eq]
  · funext ij
    exact (map_genSubst_X q t ij).symm
end GroundTheory.Heights₂.Heights.ChartKernel

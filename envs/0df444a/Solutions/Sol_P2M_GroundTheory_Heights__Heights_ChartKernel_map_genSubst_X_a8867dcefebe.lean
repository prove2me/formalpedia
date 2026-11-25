-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_map_genSubst_X_a8867dcefebe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:52:08.62086+00:00
-- url     : https://prove2.me/submissions/39587711-4a64-46c4-8e17-4be6b49d3eea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel

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
theorem _root_.solution {B : Type*} [CommRing B] {e : ℕ} (q : MvPolynomial (Fin n) F →+* B) (t : Fin n → F)
    (ij : Fin e × Fin n) :
    map q (genSubst (fun m => (X m : MvPolynomial (Fin n) F)) (fun m => C (t m)) ij) =
      genSubst (fun m => q (X m)) (fun m => q (C (t m))) ij := by
  simp [genSubst, map_sum]
end GroundTheory.Heights₂.Heights.ChartKernel

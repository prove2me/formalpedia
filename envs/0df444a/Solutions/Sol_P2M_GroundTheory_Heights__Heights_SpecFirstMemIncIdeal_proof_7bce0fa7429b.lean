-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpecFirstMemIncIdeal_proof_7bce0fa7429b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:14.541834+00:00
-- url     : https://prove2.me/submissions/ddd3b188-0470-46f4-9d62-b4a764bccf3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PSpecFirstMemIncIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_incIdeal_iff_08da98833496


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
namespace GroundTheory.Heights₂.Heights
namespace SpecFirstMemIncIdeal
theorem _root_.solution : SpecFirstMemIncIdeal.Statement := by
  intro F _ n e I W f t hf hIW ht
  rw [mem_incIdeal_iff]
  rintro v ⟨x, hx0, hxW, hv⟩
  let w : Fin (e + 1) × Fin n → AlgebraicClosure F := fun ij =>
    Fin.cases (motive := fun _ => AlgebraicClosure F) (algebraMap F (AlgebraicClosure F) (t ij.2))
      (fun i => v (i, ij.2)) ij.1
  have hw : w ∈ incidence I (e + 1) := by
    refine ⟨x, hx0, fun g hg => hxW g (hIW hg), fun i => ?_⟩
    induction i using Fin.cases with
    | zero =>
      have h := hxW _ ht
      simpa [w, linForm, map_sum, aeval_X, aeval_C] using h
    | succ i => simpa [w] using hv i
  have hfw : aeval w f = 0 := (hf.2 f).mpr dvd_rfl w hw
  have hev : aeval v (specFirst f t) = aeval w f := by
    rw [specFirst, aeval_bind₁]
    congr 2
    funext ij
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases with
    | zero => simp [specFirstVar, w]
    | succ i => simp [specFirstVar, w]
  rw [hev, hfw]
end SpecFirstMemIncIdeal
end GroundTheory.Heights₂.Heights

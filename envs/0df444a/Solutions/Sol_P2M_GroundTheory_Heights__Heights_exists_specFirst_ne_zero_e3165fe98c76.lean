-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_specFirst_ne_zero_e3165fe98c76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:49:42.637794+00:00
-- url     : https://prove2.me/submissions/1f2c5568-5e29-4381-879d-c7d93485a0ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PSpecFirstNe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_specFirstSplit_injective_40cd8caf3b1a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_specFirst_eq_map_eval_e6fa4097f9e8

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
variable {F : Type} [Field F] {k n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution [Infinite F] {f : MvPolynomial (Fin (k + 1) × Fin n) F} (hf : f ≠ 0) :
    ∃ t : Fin n → F, specFirst f t ≠ 0 := by
  set g := sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit f) with hg_def
  have hg : g ≠ 0 :=
    (map_ne_zero_iff _ (sumAlgEquiv F (Fin k × Fin n) (Fin n)).injective).mpr
      ((map_ne_zero_iff _ (rename_injective _ specFirstSplit_injective)).mpr hf)
  obtain ⟨β, hβ⟩ := ne_zero_iff.mp hg
  have ht : ∃ t : Fin n → F, eval t (coeff β g) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hβ (MvPolynomial.funext fun x => by simp [h x])
  obtain ⟨t, ht⟩ := ht
  refine ⟨t, fun h0 => ht ?_⟩
  have := congr_arg (coeff β) h0
  rwa [specFirst_eq_map_eval, ← hg_def, coeff_map, coeff_zero] at this
end GroundTheory.Heights₂.Heights

-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.comap_extC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:50.818956+00:00
-- url     : https://prove2.me/submissions/c155459e-04ee-41b8-86b8-6598e7a06960

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExtCContract
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_linearForm_one
import Theorems.Thm_ReciprocityTheory_AnForm_R_projQ_add
import Theorems.Thm_ReciprocityTheory_AnForm_R_projQ_zero
import Theorems.Thm_ReciprocityTheory_AnForm_R_projQ_map
import Theorems.Thm_ReciprocityTheory_AnForm_R_projQ_map_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (I : Ideal (MvPolynomial σ ℚ)) :
    (extC I).comap (MvPolynomial.map (algebraMap ℚ ℂ)) = I := by
  obtain ⟨ℓ, hℓ⟩ := exists_linearForm_one
  refine le_antisymm ?_ Ideal.le_comap_map
  intro f hf
  have key : ∀ x ∈ extC I, ∀ h : MvPolynomial σ ℂ, projQ ℓ (h * x) ∈ I := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨g, hg, rfl⟩ h
      rw [mul_comm, projQ_map_mul]
      exact I.mul_mem_right _ hg
    · intro h
      rw [mul_zero, projQ_zero]
      exact I.zero_mem
    · intro a b _ _ ha hb h
      rw [mul_add, projQ_add]
      exact I.add_mem (ha h) (hb h)
    · intro a b _ hb h
      rw [smul_eq_mul, ← mul_assoc]
      exact hb (h * a)
  have := key _ hf 1
  rwa [one_mul, projQ_map ℓ hℓ] at this
end ReciprocityTheory.AnForm.R

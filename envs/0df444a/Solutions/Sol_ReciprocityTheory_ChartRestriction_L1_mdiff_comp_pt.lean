-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.mdiff_comp_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:38:23.971807+00:00
-- url     : https://prove2.me/submissions/06f3a879-0741-489a-ab0a-144deab3bb4d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmSlash
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmForm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_pt_im
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_pt_coe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) {f : ℍ → ℂ} (hf : MDiff f) :
    MDiff (fun τ => f (pt a b e τ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have hmap : Set.MapsTo (fun z : ℂ => ((a : ℂ) * z + b) / e) {z | 0 < z.im} {z | 0 < z.im} := by
    intro z hz
    have h := pt_im ha he b ⟨z, hz⟩
    have h2 := congrArg Complex.im (pt_coe ha he b ⟨z, hz⟩)
    have h3 := (pt a b e ⟨z, hz⟩).im_pos
    rw [UpperHalfPlane.coe_im] at h2
    rw [h2] at h3
    exact h3
  have hd : DifferentiableOn ℂ (fun z : ℂ => ((a : ℂ) * z + b) / e) {z | 0 < z.im} := by
    fun_prop
  refine (hf.comp hd hmap).congr fun z hz => ?_
  simp only [Function.comp_apply, pt, ofComplex_apply_of_im_pos hz]
end ReciprocityTheory.ChartRestriction.L1

-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.slice2_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:32:08.523983+00:00
-- url     : https://prove2.me/submissions/077b066f-6064-4493-9189-4683709c2d3a

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan
import Theorems.Thm_ReciprocityTheory_PGsh_L2_SecondCohomologyLattice_slice2_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
theorem _root_.solution {X : Type} (E : (X → C) →ₗ[C] (X → C)) (M M' : Submodule R (X → C))
    (hM : ∀ f ∈ M, E f ∈ M') {F : X × X → C} (hF : F ∈ tensorSpan R M) :
    slice2 E F ∈ tensorSpan R M' := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨g, hg, h, hh, rfl⟩ := hF
    rw [slice2_tmul]
    exact Submodule.subset_span ⟨E g, hM g hg, E h, hM h hh, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add F G _ _ hF hG => rw [map_add]; exact Submodule.add_mem _ hF hG
  | smul r F _ hF =>
    rw [← algebraMap_smul C r F, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ r hF
end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

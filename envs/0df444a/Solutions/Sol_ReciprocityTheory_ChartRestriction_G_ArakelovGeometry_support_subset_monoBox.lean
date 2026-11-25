-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.support_subset_monoBox
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:07.596556+00:00
-- url     : https://prove2.me/submissions/8b2d8227-a948-4d86-94d1-1e1e3cd6273c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsHomogeneousGrL
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_le_of_mem_support_mHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {a : K → ℕ} {f : MRing ι} (hf : f ∈ mHom ι a) :
    f.support ⊆ monoBox a := by
  intro m hm
  simp only [monoBox, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact fun p => le_of_mem_support_mHom hf hm p
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

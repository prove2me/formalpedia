-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.IsMF.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:32.892575+00:00
-- url     : https://prove2.me/submissions/2f0ce202-052c-48b2-a132-341726823085

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic

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
namespace IsMF
theorem _root_.solution {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k (fun τ => f τ - g τ) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' - g', fun τ => by simp [hf', hg']⟩
end IsMF
end ReciprocityTheory.ChartRestriction.L1

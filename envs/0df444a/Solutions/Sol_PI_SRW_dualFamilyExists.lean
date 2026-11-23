-- Prove2me | solution 1 for PI.SRW.dualFamilyExists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:50.175453+00:00
-- url     : https://prove2.me/submissions/2a910811-24dd-4add-b91e-cfe92437aa10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SesquilinearRowSplitting_CoordStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SesquilinearRowSplitting_DualFamilyExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open PI PI.SRW
namespace PI.SRW
theorem _root_.solution : CoordStep := by
  intro E V _ _ _ n g hg
  classical
  let b := Basis.span hg
  choose c hc using fun i => LinearMap.exists_extend (b.coord i)
  refine ⟨c, fun i j => ?_⟩
  have hmem : g j ∈ Submodule.span E (Set.range g) := Submodule.subset_span ⟨j, rfl⟩
  have h1 : c i (g j) = b.coord i ⟨g j, hmem⟩ := by
    rw [← hc i]; rfl
  have h2 : (⟨g j, hmem⟩ : Submodule.span E (Set.range g)) = b j := by
    rw [Basis.span_apply]
  rw [h1, h2, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]
end PI.SRW

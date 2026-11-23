-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.map_tensorSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:59.136906+00:00
-- url     : https://prove2.me/submissions/7cf1fee6-6889-441e-8389-670e101d3758

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan

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
theorem _root_.solution {X Y : Type} (σ : Y → X) (M : Submodule R (X → C)) :
    (tensorSpan R M).map (LinearMap.funLeft R C (Prod.map σ σ)) =
      tensorSpan R (M.map (LinearMap.funLeft R C σ)) := by
  rw [tensorSpan, tensorSpan, Submodule.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨_, ⟨g, hg, h, hh, rfl⟩, rfl⟩
    exact ⟨_, Submodule.mem_map_of_mem hg, _, Submodule.mem_map_of_mem hh, by
      funext p; simp [LinearMap.funLeft_apply]⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, _, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, h, hh, rfl⟩, by funext p; simp [LinearMap.funLeft_apply]⟩
end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

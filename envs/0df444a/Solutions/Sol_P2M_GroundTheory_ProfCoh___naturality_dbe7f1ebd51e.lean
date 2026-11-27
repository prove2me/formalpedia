-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh___naturality_dbe7f1ebd51e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:40.739158+00:00
-- url     : https://prove2.me/submissions/ab12503d-ff7e-4469-9ce6-41fef9c29a77

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_LongExactSequence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory ShortComplex
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {S₁ S₂ : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S₁.X₁] [IsDiscreteRep S₁.X₂]
  [IsDiscreteRep S₁.X₃] [IsDiscreteRep S₂.X₁] [IsDiscreteRep S₂.X₂] [IsDiscreteRep S₂.X₃]
namespace GroundTheory.ProfCoh
theorem _root_.solution (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (i j : ℕ)
    (hij : i + 1 = j) :
    δ hS₁ i j hij ≫ cohomologyMap φ.τ₁ j = cohomologyMap φ.τ₃ i ≫ δ hS₂ i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (cochainsShortComplexMap φ)
    (cochainsShortComplex_shortExact hS₁) (cochainsShortComplex_shortExact hS₂) i j hij
end GroundTheory.ProfCoh

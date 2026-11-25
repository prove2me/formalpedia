-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_subsingleton_cohomology_X__77ff456b320e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:01.892634+00:00
-- url     : https://prove2.me/submissions/90776174-b961-454b-b01a-461f7f1167b1

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_P2M_GroundTheory_ProfCoh_cohomology_exact__bae5173fa4e3


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
open CategoryTheory Limits
universe u
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) (n : ℕ)
    (h₁ : Subsingleton (cohomology S.X₁ n)) (h₃ : Subsingleton (cohomology S.X₃ n)) :
    Subsingleton (cohomology S.X₂ n) := by
  suffices h : ∀ x : cohomology S.X₂ n, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS n) x
    (Subsingleton.elim _ _)
  rw [← hz, Subsingleton.elim z 0]
  exact map_zero _
end GroundTheory.ProfCoh

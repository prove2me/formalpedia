-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_mem_coboundaries__intRepOfMonoidEnd_iff_8d7a2be120d0
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:19:58.807591+00:00
-- url     : https://prove2.me/submissions/99146889-1a3a-4df5-86f5-f9bfc972e67d

import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalClassFormation_OrderScalars
import Mathlib
import Mathlib.Tactic




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
open CategoryTheory groupCohomology
variable {G M : Type} [Group G] [CommGroup M] (φ : G →* Monoid.End M)
theorem _root_.solution (f : G × G → Additive M) :
    f ∈ coboundaries₂ (Rep.of (intRepOfMonoidEnd.{0} φ)) ↔
      f ∈ coboundaries₂ (Rep.of (zRepOfMonoidEnd φ)) := by
  first
    | (intros; rfl)
    | (intros; ext; rfl)
    | (intros; exact LinearMap.ext fun _ => rfl)
    | (intros; apply Subtype.ext; rfl)
    | (intros; infer_instance)
    | (refine ⟨?_, ?_⟩ <;> infer_instance)
    | (intros; ext; simp; done)
    | (intros; assumption)
    | (intros; omega)
    | (intros; simp []; done)
    | (intros; grind)
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_17_0"




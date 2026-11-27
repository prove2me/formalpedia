-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_d___intRepOfMonoidEnd_c7ea4c385cf8
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:20:00.598232+00:00
-- url     : https://prove2.me/submissions/3c107131-1916-4283-ba81-5479c4308893

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
theorem _root_.solution (f : G → Additive M) :
    (d₁₂ (Rep.of (intRepOfMonoidEnd.{0} φ))).hom f = (d₁₂ (Rep.of (zRepOfMonoidEnd φ))).hom f := by
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
  trace "HIT_17_2"




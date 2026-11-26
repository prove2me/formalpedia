-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_smul_def__ff4c4016e5a6
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:08:13.646445+00:00
-- url     : https://prove2.me/submissions/fc3add81-b270-4c18-83a5-cb278ce3492e

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable (S : Type u) [CommRing S] (N : ℕ)
variable {S N}
attribute [local instance] algP
theorem _root_.solution (p : Poly S N) (x : LRing S N) : p • x = toL S N p * x := by
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
    | (intros; simp [LRing, toL]; done)
    | (intros; grind)
    | (intros; grind [LRing, toL])
    | (intros; unfold LRing toL; grind)
    | (intros; simp only [LRing, toL] at * <;> grind)
    | (intros; simp_all [LRing, toL] <;> grind)
    | (intros; ext <;> grind [LRing, toL])
    | (intros; constructor <;> intro _ <;> grind [LRing, toL])
    | (intro x; cases x <;> grind [LRing, toL])
    | (intro x; induction x <;> simp_all [LRing, toL])
    | (intro x y; induction x <;> grind [LRing, toL])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [LRing, toL])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [LRing, toL])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_15_1"



end 

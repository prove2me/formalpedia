-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_heightOfCycle_hyp_4e3d46928265
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:25:45.39954+00:00
-- url     : https://prove2.me/submissions/a961c2a7-05f6-44ea-a30e-cf99782fbadb

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField MeasureTheory ProbabilityTheory TensorProduct ComplexAt
noncomputable section
theorem _root_.solution :
    (X 0 + C 2 * X 1 : MvPolynomial (Fin 2) ℚ).map (algebraMap ℚ ℚ) =
      C 1 * ∏ _q : Fin 1, ∑ k, C (ratPointVec (Pi.basisFun (𝓞 ℚ) (Fin 2) k)) * X k := by
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
    | (intros; simp [ratPointVec]; done)
    | (intros; grind)
    | (intros; grind [ratPointVec])
    | (intros; unfold ratPointVec; grind)
    | (intros; simp only [ratPointVec] at * <;> grind)
    | (intros; simp_all [ratPointVec] <;> grind)
    | (intros; ext <;> grind [ratPointVec])
    | (intros; constructor <;> intro _ <;> grind [ratPointVec])
    | (intro x; cases x <;> grind [ratPointVec])
    | (intro x; induction x <;> simp_all [ratPointVec])
    | (intro x y; induction x <;> grind [ratPointVec])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [ratPointVec])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [ratPointVec])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_5_2"



end 

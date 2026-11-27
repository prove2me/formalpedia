-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_metric_b6d4d757a33f
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:25:46.646015+00:00
-- url     : https://prove2.me/submissions/b2638292-b31d-4391-84fd-b5de8c16681d

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
theorem _root_.solution (M : HermLine n) (p a : ℕ) (C : ℝ) (z : Cone n ℂ) :
    (twistPow M p a C).metric z =
      Real.exp (-(a * C)) * (((M.pow p).mul (HermLine.standard n)).pow a).metric z := by
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
    | (intros; simp [pow, mul, twistPow]; done)
    | (intros; grind)
    | (intros; grind [pow, mul, twistPow])
    | (intros; unfold pow mul twistPow; grind)
    | (intros; simp only [pow, mul, twistPow] at * <;> grind)
    | (intros; simp_all [pow, mul, twistPow] <;> grind)
    | (intros; ext <;> grind [pow, mul, twistPow])
    | (intros; constructor <;> intro _ <;> grind [pow, mul, twistPow])
    | (intro x; cases x <;> grind [pow, mul, twistPow])
    | (intro x; induction x <;> simp_all [pow, mul, twistPow])
    | (intro x y; induction x <;> grind [pow, mul, twistPow])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [pow, mul, twistPow])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [pow, mul, twistPow])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_7_0"



end 

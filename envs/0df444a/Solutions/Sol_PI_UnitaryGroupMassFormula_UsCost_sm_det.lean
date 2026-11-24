-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.sm_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:55:13.441852+00:00
-- url     : https://prove2.me/submissions/d3e00f5f-fada-459f-b142-369b7b0da8ef

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Smooth
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section smoothAt
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
private lemma contDiffAt_finset_prod' {ι : Type*} (s : Finset ι) (f : ι → X → ℂ)
    (h : ∀ i ∈ s, ContDiffAt ℝ n (f i) x₀) : ContDiffAt ℝ n (fun x => ∏ i ∈ s, f i x) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (contDiffAt_const : ContDiffAt ℝ n (fun _ : X => (1 : ℂ)) x₀)
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end smoothAt
section slice
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
end slice
end PI.UnitaryGroupMassFormula.UsCost
end
end

set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {F : X → Matrix ι ι ℂ} (hF : ContDiffAt ℝ n F x₀) :
    ContDiffAt ℝ n (fun x => (F x).det) x₀ := by
  rw [sm_iff] at hF
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun τ _ => contDiffAt_const.mul (contDiffAt_finset_prod' _ _ fun i _ => hF (τ i) i)
end PI.UnitaryGroupMassFormula.UsCost

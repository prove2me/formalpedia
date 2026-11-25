-- Prove2me | solution 1 for PI.SwSandwichOfWork.SideB_pick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:44.640123+00:00
-- url     : https://prove2.me/submissions/201626bf-17cb-4bc2-a711-2b8b93fb3698

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SideBUnrealifyRL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
namespace PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
private theorem SideB_unrealify_RL (X : Mat k r) : unrealify (RL X) = X := by
  ext i j
  simp [unrealify, RL]
  apply Complex.ext <;> simp [realifyFun]
private theorem SideB_below (S : Set (Mat k r)) (x : Mt k r) (t : ℝ) (ht : 0 < t)
    (hlt : rhoS k r S x < ENNReal.ofReal t) :
    ∃ Y : lieE S, (fun i j => NormedSpace.exp (unrealify (Y : EuclideanSpace ℝ _)) i j : Mt k r) = x ∧
      ‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ < t := by
  unfold rhoS at hlt
  obtain ⟨Y, hY⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hex, hY2⟩ := iInf_lt_iff.1 hY
  refine ⟨Y, hex, ?_⟩
  have h3 : ENNReal.ofReal ‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ <
      ENNReal.ofReal t := by
    rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]; exact hY2
  exact (ENNReal.ofReal_lt_ofReal_iff ht).1 h3
end PI.SwSandwichOfWork
end
end

set_option autoImplicit false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
namespace PI.SwSandwichOfWork
theorem _root_.solution (S : Set (Mat k r)) (T : Submodule ℝ (Mat k r)) (hST : lieE S = T.map RL) (x : Mt k r)
    (h : rhoS k r S x ≠ ⊤) (τ : ℝ) (hτ : 0 < τ) :
    ∃ X ∈ T, NormedSpace.exp X = Matrix.of x ∧ ‖RL X‖ ^ 2 < (rhoS k r S x).toReal ^ 2 + τ := by
  have ha : 0 ≤ (rhoS k r S x).toReal := ENNReal.toReal_nonneg
  have hs : 0 < Real.sqrt ((rhoS k r S x).toReal ^ 2 + τ) := Real.sqrt_pos.2 (by positivity)
  have hlt : rhoS k r S x < ENNReal.ofReal (Real.sqrt ((rhoS k r S x).toReal ^ 2 + τ)) := by
    have e : rhoS k r S x = ENNReal.ofReal (rhoS k r S x).toReal := (ENNReal.ofReal_toReal h).symm
    calc rhoS k r S x = ENNReal.ofReal (rhoS k r S x).toReal := e
      _ < ENNReal.ofReal (Real.sqrt ((rhoS k r S x).toReal ^ 2 + τ)) := by
        refine (ENNReal.ofReal_lt_ofReal_iff hs).2 ?_
        rw [Real.lt_sqrt ha]; linarith
  obtain ⟨Y, hex, hY⟩ := SideB_below S x _ hs hlt
  have hm : (Y : EuclideanSpace ℝ _) ∈ T.map RL := hST ▸ Y.2
  obtain ⟨X, hX, hXe⟩ := Submodule.mem_map.1 hm
  refine ⟨X, hX, ?_, ?_⟩
  · ext i j; rw [← hex, ← hXe, SideB_unrealify_RL]; rfl
  · rw [hXe]
    exact (Real.lt_sqrt (norm_nonneg _)).1 hY
end PI.SwSandwichOfWork

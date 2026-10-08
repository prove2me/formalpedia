-- Prove2me | solution 1 for RobustPower.Hypercube.eq_5_14_corner_cost_le_adapt_cost
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:56:11.339224+00:00
-- url     : https://prove2.me/submissions/15a2a68d-6958-4f4e-b23a-3f41fd1f0bda

import Definitions.Def_RobustPower_Hypercube_Problems

open Matrix RobustPower.Hypercube

theorem solution
    {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (hd : ∀ ω, 0 ≤ d ω)
    (ωbar : Ω) (hdbar : ∀ ω j, d ω j ≤ d ωbar j)
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ)
    (hxy : adaptFeasible A B b I₁ I₂ x y) :
    RobustPower.AdaptGap.robCost c d x (y ωbar) ≤ RobustPower.AdaptGap.adaptCost c d x y := by
  unfold RobustPower.AdaptGap.robCost RobustPower.AdaptGap.adaptCost
  apply add_le_add le_rfl
  refine iSup_le fun ω => ?_
  calc
    ((d ω ⬝ᵥ y ωbar : ℝ) : EReal) ≤ ((d ωbar ⬝ᵥ y ωbar : ℝ) : EReal) :=
      EReal.coe_le_coe (dotProduct_le_dotProduct_of_nonneg_right (hdbar ω) (hxy.2 ωbar).1.1)
    _ ≤ ⨆ ω, ((d ω ⬝ᵥ y ω : ℝ) : EReal) :=
      le_iSup (fun ω : Ω => ((d ω ⬝ᵥ y ω : ℝ) : EReal)) ωbar

-- Prove2me | solution 1 for RobustPower.Hypercube.eq_5_11_5_13_corner_rob_feasible
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:56:08.474839+00:00
-- url     : https://prove2.me/submissions/24496bed-97eb-435a-83cf-5de23a29200e

import Definitions.Def_RobustPower_Hypercube_Problems

open Matrix RobustPower.Hypercube

theorem solution
    {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (ωbar : Ω)
    (hA : ∀ ω i j, A ωbar i j ≤ A ω i j)
    (hB : ∀ ω i j, B ωbar i j ≤ B ω i j)
    (hb : ∀ ω i, b ω i ≤ b ωbar i)
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ)
    (hxy : adaptFeasible A B b I₁ I₂ x y) :
    robFeasible A B b I₁ I₂ x (y ωbar) := by
  refine ⟨hxy.1, (hxy.2 ωbar).1, ?_⟩
  intro ω i
  calc
    b ω i ≤ b ωbar i := hb ω i
    _ ≤ (A ωbar *ᵥ x + B ωbar *ᵥ y ωbar) i := (hxy.2 ωbar).2 i
    _ ≤ (A ω *ᵥ x + B ω *ᵥ y ωbar) i :=
      add_le_add
        (dotProduct_le_dotProduct_of_nonneg_right (hA ω i) hxy.1.1)
        (dotProduct_le_dotProduct_of_nonneg_right (hB ω i) (hxy.2 ωbar).1.1)

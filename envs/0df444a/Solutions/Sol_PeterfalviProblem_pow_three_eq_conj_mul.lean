-- Prove2me | solution 1 for PeterfalviProblem.pow_three_eq_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-27T04:59:35.736803+00:00
-- url     : https://prove2.me/submissions/cce5e2d3-cc3e-4b44-b229-724b7c12a3f1

import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group
import Definitions.Def_PeterfalviProblem_Proof_GroupIdentities
section
namespace PeterfalviProblem
variable {G : Type*} [Group G]
section PowThree
variable {x c g : G}
private theorem mul_mul_eq_one_of_pow_three (hx : x ^ 3 = 1) : x * (x * x) = 1 := by
  rw [pow_succ, pow_succ, pow_one] at hx
  rwa [← mul_assoc]
private theorem inv_eq_mul_self (hx : x ^ 3 = 1) : x⁻¹ = x * x :=
  inv_eq_of_mul_eq_one_left (by
    have h := mul_mul_eq_one_of_pow_three hx
    rwa [mul_assoc])
private theorem cancel_three (hx : x ^ 3 = 1) (r : G) : x * (x * (x * r)) = r := by
  have h : x * x * x = 1 := by
    have h := mul_mul_eq_one_of_pow_three hx
    rwa [← mul_assoc] at h
  rw [← mul_assoc, ← mul_assoc, h, one_mul]
end PowThree
section CrossCommute
variable {a₀ a₁ a₂ b₀ b₁ b₂ : G}
section Semilinear
end Semilinear
end CrossCommute
end PeterfalviProblem
end

set_option autoImplicit false
open PeterfalviProblem
variable {G : Type*} [Group G]
variable {x c g : G}
namespace PeterfalviProblem
theorem _root_.solution (hx : x ^ 3 = 1) (c : G) :
    (x * c) ^ 3 = x⁻¹ * (x⁻¹ * c * x) * x * ((x⁻¹ * c * x) * c) := by
  have hxi : x⁻¹ = x * x := inv_eq_mul_self hx
  have hcan : ∀ r : G, x * (x * (x * r)) = r := cancel_three hx
  simp only [hxi, pow_succ, pow_zero, one_mul, mul_assoc, hcan]
end PeterfalviProblem

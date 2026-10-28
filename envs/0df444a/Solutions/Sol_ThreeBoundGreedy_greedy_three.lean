-- Prove2me | solution 1 for ThreeBoundGreedy.greedy_three
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:37:50.866556+00:00
-- url     : https://prove2.me/submissions/c3702fab-5176-4308-a3b0-51f407d68e77

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring


section
/- Exact greedy allocation for the simultaneous negative-candidate prefix caps.
The hypotheses concern actual counts and decreasing costs.  No transfer
inequality is assumed. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundGreedy



theorem weighted_three_prefix (n₀ n₁ n₂ g₀ g₁ g₂ a₀ a₁ a₂ : ℕ)
    (h₀ : n₀ ≤ g₀) (h₁ : n₀+n₁ ≤ g₀+g₁)
    (h₂ : n₀+n₁+n₂ ≤ g₀+g₁+g₂)
    (ha₀ : a₁ ≤ a₀) (ha₁ : a₂ ≤ a₁) :
    n₀*a₀+n₁*a₁+n₂*a₂ ≤ g₀*a₀+g₁*a₁+g₂*a₂ := by
  let d₀ := a₀-a₁
  let d₁ := a₁-a₂
  have e₀ : a₀ = d₀+a₁ := (Nat.sub_add_cancel ha₀).symm
  have e₁ : a₁ = d₁+a₂ := (Nat.sub_add_cancel ha₁).symm
  rw [e₀,e₁]
  calc
    _ = n₀*d₀+(n₀+n₁)*d₁+(n₀+n₁+n₂)*a₂ := by ring
    _ ≤ g₀*d₀+(g₀+g₁)*d₁+(g₀+g₁+g₂)*a₂ :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right d₀ h₀)
        (Nat.mul_le_mul_right d₁ h₁)) (Nat.mul_le_mul_right a₂ h₂)
    _ = _ := by ring













end ThreeBoundGreedy




end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ThreeBoundGreedy
end ThreeBoundGreedy
open ThreeBoundGreedy

/-- The three-level fill used at q=2.  Suffix minima make every
    simultaneous prefix constraint hold, even if the original caps fall. -/
theorem solution (n₀ n₁ n₂ c₀ c₁ c₂ a₀ a₁ a₂ : ℕ)
    (h₀ : n₀ ≤ c₀) (h₁ : n₀+n₁ ≤ c₁) (h₂ : n₀+n₁+n₂ ≤ c₂)
    (ha₀ : a₁ ≤ a₀) (ha₁ : a₂ ≤ a₁) :
    let g₀ := min c₀ (min c₁ c₂)
    let g₁ := min c₁ c₂-g₀
    let g₂ := c₂-(g₀+g₁)
    n₀*a₀+n₁*a₁+n₂*a₂ ≤ g₀*a₀+g₁*a₁+g₂*a₂ := by
  dsimp only
  apply weighted_three_prefix
  · exact le_min h₀ (le_min (by omega) (by omega))
  · have hh := Nat.sub_add_cancel (min_le_right c₀ (min c₁ c₂))
    have hx : n₀+n₁ ≤ min c₁ c₂ := le_min h₁ (by omega)
    omega
  · have hh := Nat.sub_add_cancel (min_le_right c₀ (min c₁ c₂))
    have hl := min_le_right c₁ c₂
    omega
  · exact ha₀
  · exact ha₁
end

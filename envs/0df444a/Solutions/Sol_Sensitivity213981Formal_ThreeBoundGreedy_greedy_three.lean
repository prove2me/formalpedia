-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundGreedy.greedy_three
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:31:05.438108+00:00
-- url     : https://prove2.me/submissions/f4185439-9b83-4da5-a3e6-81cf7a6723af

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring


namespace Sensitivity213981Formal
section
/- Exact greedy allocation for the simultaneous negative-candidate prefix caps.
The hypotheses concern actual counts and decreasing costs.  No transfer
inequality is assumed. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundGreedy



theorem weighted_three_prefix (n₀ n₁ n₂ g₀ g₁ g₂ a₀ a₁ a₂ : ℕ)
    (h₀ : n₀ ≤  g₀) (h₁ : n₀+n₁ ≤  g₀+g₁)
    (h₂ : n₀+n₁+n₂ ≤  g₀+g₁+g₂)
    (ha₀ : a₁ ≤  a₀) (ha₁ : a₂ ≤  a₁) :
    n₀*a₀+n₁*a₁+n₂*a₂ ≤  g₀*a₀+g₁*a₁+g₂*a₂ := by
  let d₀ := a₀-a₁
  let d₁ := a₁-a₂
  have e₀ : a₀ = d₀+a₁ := (Nat.sub_add_cancel ha₀).symm
  have e₁ : a₁ = d₁+a₂ := (Nat.sub_add_cancel ha₁).symm
  rw [e₀,e₁]
  calc
    _ = n₀*d₀+(n₀+n₁)*d₁+(n₀+n₁+n₂)*a₂ := by ring
    _ ≤  g₀*d₀+(g₀+g₁)*d₁+(g₀+g₁+g₂)*a₂ :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right d₀ h₀)
        (Nat.mul_le_mul_right d₁ h₁)) (Nat.mul_le_mul_right a₂ h₂)
    _ = _ := by ring





/-- The three-level fill used at q=2.  Suffix minima make every
    simultaneous prefix constraint hold, even if the original caps fall. -/
theorem greedy_three (n₀ n₁ n₂ c₀ c₁ c₂ a₀ a₁ a₂ : ℕ)
    (h₀ : n₀ ≤  c₀) (h₁ : n₀+n₁ ≤  c₁) (h₂ : n₀+n₁+n₂ ≤  c₂)
    (ha₀ : a₁ ≤  a₀) (ha₁ : a₂ ≤  a₁) :
    let g₀ := min c₀ (min c₁ c₂)
    let g₁ := min c₁ c₂-g₀
    let g₂ := c₂-(g₀+g₁)
    n₀*a₀+n₁*a₁+n₂*a₂ ≤  g₀*a₀+g₁*a₁+g₂*a₂ := by
  dsimp only
  apply weighted_three_prefix
  · exact le_min h₀ (le_min (by omega) (by omega))
  · have hh := Nat.sub_add_cancel (min_le_right c₀ (min c₁ c₂))
    have hx : n₀+n₁ ≤  min c₁ c₂ := le_min h₁ (by omega)
    omega
  · have hh := Nat.sub_add_cancel (min_le_right c₀ (min c₁ c₂))
    have hl := min_le_right c₁ c₂
    omega
  · exact ha₀
  · exact ha₁







end ThreeBoundGreedy




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (n₀ n₁ n₂ c₀ c₁ c₂ a₀ a₁ a₂ : Nat) (h₀ : @LE.le.{0} Nat instLENat n₀ c₀)
  (h₁ : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n₀ n₁) c₁)
  (h₂ :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n₀ n₁) n₂)
      c₂)
  (ha₀ : @LE.le.{0} Nat instLENat a₁ a₀) (ha₁ : @LE.le.{0} Nat instLENat a₂ a₁),
  have g₀ : Nat := @Min.min.{0} Nat instMinNat c₀ (@Min.min.{0} Nat instMinNat c₁ c₂);
  have g₁ : Nat :=
    @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Min.min.{0} Nat instMinNat c₁ c₂) g₀;
  have g₂ : Nat :=
    @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) c₂
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g₀ g₁);
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₀ a₀)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₁ a₁))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₂ a₂))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₀ a₀)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₁ a₁))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₂ a₂)) := @Sensitivity213981Formal.ThreeBoundGreedy.greedy_three

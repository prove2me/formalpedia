-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundGreedy.greedy_four
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:31:54.722713+00:00
-- url     : https://prove2.me/submissions/d3d7b835-9895-49bc-a086-123bd4a75a02

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





theorem weighted_four_prefix
    (n₀ n₁ n₂ n₃ g₀ g₁ g₂ g₃ a₀ a₁ a₂ a₃ : ℕ)
    (h₀ : n₀ ≤  g₀) (h₁ : n₀+n₁ ≤  g₀+g₁)
    (h₂ : n₀+n₁+n₂ ≤  g₀+g₁+g₂)
    (h₃ : n₀+n₁+n₂+n₃ ≤  g₀+g₁+g₂+g₃)
    (ha₀ : a₁ ≤  a₀) (ha₁ : a₂ ≤  a₁) (ha₂ : a₃ ≤  a₂) :
    n₀*a₀+n₁*a₁+n₂*a₂+n₃*a₃ ≤  g₀*a₀+g₁*a₁+g₂*a₂+g₃*a₃ := by
  let d₀ := a₀-a₁
  let d₁ := a₁-a₂
  let d₂ := a₂-a₃
  have e₀ : a₀ = d₀+a₁ := (Nat.sub_add_cancel ha₀).symm
  have e₁ : a₁ = d₁+a₂ := (Nat.sub_add_cancel ha₁).symm
  have e₂ : a₂ = d₂+a₃ := (Nat.sub_add_cancel ha₂).symm
  rw [e₀,e₁,e₂]
  calc
    _ = n₀*d₀+(n₀+n₁)*d₁+(n₀+n₁+n₂)*d₂+(n₀+n₁+n₂+n₃)*a₃ := by ring
    _ ≤  g₀*d₀+(g₀+g₁)*d₁+(g₀+g₁+g₂)*d₂+(g₀+g₁+g₂+g₃)*a₃ :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_right d₀ h₀) (Nat.mul_le_mul_right d₁ h₁))
        (Nat.mul_le_mul_right d₂ h₂)) (Nat.mul_le_mul_right a₃ h₃)
    _ = _ := by ring





/-- The q=3 negative allocation uses the same argument with four tiers. -/
theorem greedy_four (n₀ n₁ n₂ n₃ c₀ c₁ c₂ c₃ a₀ a₁ a₂ a₃ : ℕ)
    (h₀ : n₀ ≤  c₀) (h₁ : n₀+n₁ ≤  c₁)
    (h₂ : n₀+n₁+n₂ ≤  c₂) (h₃ : n₀+n₁+n₂+n₃ ≤  c₃)
    (ha₀ : a₁ ≤  a₀) (ha₁ : a₂ ≤  a₁) (ha₂ : a₃ ≤  a₂) :
    let g₀ := min c₀ (min c₁ (min c₂ c₃))
    let g₁ := min c₁ (min c₂ c₃)-g₀
    let g₂ := min c₂ c₃-(g₀+g₁)
    let g₃ := c₃-(g₀+g₁+g₂)
    n₀*a₀+n₁*a₁+n₂*a₂+n₃*a₃ ≤  g₀*a₀+g₁*a₁+g₂*a₂+g₃*a₃ := by
  dsimp only
  have hm₀ := min_le_right c₀ (min c₁ (min c₂ c₃))
  have hm₁ := min_le_right c₁ (min c₂ c₃)
  have hm₂ := min_le_right c₂ c₃
  have he₀ := Nat.sub_add_cancel hm₀
  have he₁ := Nat.sub_add_cancel hm₁
  apply weighted_four_prefix
  · exact le_min h₀ (le_min (by omega) (le_min (by omega) (by omega)))
  · have hx : n₀+n₁ ≤  min c₁ (min c₂ c₃) :=
      le_min h₁ (le_min (by omega) (by omega))
    omega
  · have hx : n₀+n₁+n₂ ≤  min c₂ c₃ := le_min h₂ (by omega)
    omega
  · omega
  · exact ha₀
  · exact ha₁
  · exact ha₂





end ThreeBoundGreedy




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (n₀ n₁ n₂ n₃ c₀ c₁ c₂ c₃ a₀ a₁ a₂ a₃ : Nat) (h₀ : @LE.le.{0} Nat instLENat n₀ c₀)
  (h₁ : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n₀ n₁) c₁)
  (h₂ :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n₀ n₁) n₂)
      c₂)
  (h₃ :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n₀ n₁) n₂)
        n₃)
      c₃)
  (ha₀ : @LE.le.{0} Nat instLENat a₁ a₀) (ha₁ : @LE.le.{0} Nat instLENat a₂ a₁) (ha₂ : @LE.le.{0} Nat instLENat a₃ a₂),
  have g₀ : Nat := @Min.min.{0} Nat instMinNat c₀ (@Min.min.{0} Nat instMinNat c₁ (@Min.min.{0} Nat instMinNat c₂ c₃));
  have g₁ : Nat :=
    @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
      (@Min.min.{0} Nat instMinNat c₁ (@Min.min.{0} Nat instMinNat c₂ c₃)) g₀;
  have g₂ : Nat :=
    @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Min.min.{0} Nat instMinNat c₂ c₃)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g₀ g₁);
  have g₃ : Nat :=
    @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) c₃
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g₀ g₁) g₂);
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₀ a₀)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₁ a₁))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₂ a₂))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n₃ a₃))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₀ a₀)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₁ a₁))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₂ a₂))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) g₃ a₃)) := @Sensitivity213981Formal.ThreeBoundGreedy.greedy_four

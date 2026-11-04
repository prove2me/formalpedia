-- Prove2me | solution 1 for ThreeSum.LightTernaryMomentAccumulate.other_row_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:04.734185+00:00
-- url     : https://prove2.me/submissions/7ed10481-41c8-46c1-b413-1d62b6c7c122

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentAccumulate
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryMomentAccumulate
theorem _root_.solution {μ ν : ℕ→ℤ} {matrix count k l : ℕ}
    (hkeep : SameOutside μ ν (matrix+k*count) count) (hkl : k≠l) :
    ∀ i<count, ν (matrix+l*count+i)=μ (matrix+l*count+i) := by
  intro i hi
  apply hkeep
  by_cases hlk : l<k
  · left
    have hm := Nat.mul_le_mul_right count (show l+1≤k by omega)
    simp only [Nat.add_mul,one_mul] at hm
    omega
  · right
    have hm := Nat.mul_le_mul_right count (show k+1≤l by omega)
    simp only [Nat.add_mul,one_mul] at hm
    omega
end ThreeSum.LightTernaryMomentAccumulate

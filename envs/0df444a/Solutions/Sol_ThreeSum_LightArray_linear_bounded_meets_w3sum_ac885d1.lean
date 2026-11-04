-- Prove2me | solution 1 for ThreeSum.LightArray.linear_bounded_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:11:36.688503+00:00
-- url     : https://prove2.me/submissions/f44dc929-26dd-41ff-a7b4-c2999123dd20

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_ThreeSum_LightArray_linear_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightArray
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightArray
theorem _root_.solution {p : ℕ} (hp : P[p]? = some linearBody)
    {μ : ℕ → ℤ} {srcA srcB dst n U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA + n ≤ lim.space) (hB : srcB + n ≤ lim.space)
    (hD : dst + n ≤ lim.space)
    (hsepA : SourceSafe srcA dst n) (hsepB : SourceSafe srcB dst n)
    (hc : |c| ≤ 1) (hword : 2 * (U : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (srcA + i)| ≤ U ∧ |μ (srcB + i)| ≤ U) :
    Meets lim P p d [(srcA : ℤ), srcB, dst, n, c] μ (linearTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (srcA + i) + c * μ (srcB + i)) ∧
        SameOutside μ μ' dst n := by
  have hm : ∀ i < n, |c * μ (srcB + i)| ≤ U := by
    intro i hi
    rw [abs_mul]
    calc
      _ ≤ 1 * (U : ℤ) := mul_le_mul hc (hvalues i hi).2 (abs_nonneg _) (by omega)
      _ = U := one_mul _
  apply linear_meets hp hw hA hB hD hsepA hsepB
  · intro i hi
    exact (hm i hi).trans (by omega)
  · intro i hi
    exact (abs_add_le _ _).trans ((add_le_add (hvalues i hi).1 (hm i hi)).trans (by omega))
end ThreeSum.LightArray

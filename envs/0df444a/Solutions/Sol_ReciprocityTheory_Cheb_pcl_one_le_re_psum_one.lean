-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pcl_one_le_re_psum_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:53.522805+00:00
-- url     : https://prove2.me/submissions/c9d19837-f1e0-415d-93d7-c01b34f6f831

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth
import Theorems.Thm_ReciprocityTheory_Cheb_cyor_cast_rpow
import Theorems.Thm_ReciprocityTheory_Cheb_cyor_summable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (l : ℕ) [NeZero l] (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    Pcl E l 1 s ≤ (Psum E (1 : DirichletCharacter ℂ l) s).re := by
  unfold Pcl Psum
  rw [Complex.re_tsum (cyor_summable _ s hS)]
  have hS2 : Summable (fun q : Prm E =>
      if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
    refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hS
    · split_ifs
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine Summable.tsum_le_tsum (fun q => ?_) hS2 (Complex.reCLM.summable (cyor_summable _ s hS))
  rw [← cyor_cast_rpow]
  split_ifs with h
  · rw [h]; simp
  · by_cases hu : IsUnit ((Nrm q : ℕ) : ZMod l)
    · rw [MulChar.one_apply hu, one_mul, Complex.ofReal_re]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · rw [MulChar.map_nonunit _ hu]; simp
end ReciprocityTheory.Cheb

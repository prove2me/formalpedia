-- Prove2me | solution 1 for ReciprocityTheory.Cheb.psum_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:38:43.851348+00:00
-- url     : https://prove2.me/submissions/da3eec7c-0a17-4873-8f85-4bbbe3f55dae

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
theorem _root_.solution (l : ℕ) [NeZero l] (a : (ZMod l)ˣ) (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    ∑ χ : DirichletCharacter ℂ l, χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l) * Psum E χ s
      = ((Nat.totient l : ℕ) : ℂ) * (Pcl E l (a : ZMod l) s : ℂ) := by
  unfold Psum Pcl
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun χ _ => (cyor_summable χ s hS).mul_left _)]
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  congr 1
  funext q
  have hinv : (((a⁻¹ : (ZMod l)ˣ) : ZMod l)) = ((a : ZMod l))⁻¹ := by
    rw [ZMod.inv_coe_unit]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  simp_rw [hinv]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit]
  by_cases h : (a : ZMod l) = ((Nrm q : ℕ) : ZMod l)
  · rw [if_pos h, if_pos h.symm, cyor_cast_rpow]
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp
end ReciprocityTheory.Cheb

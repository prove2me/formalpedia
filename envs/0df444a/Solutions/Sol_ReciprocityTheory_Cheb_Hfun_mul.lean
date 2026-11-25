-- Prove2me | solution 1 for ReciprocityTheory.Cheb.Hfun_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:05:54.642947+00:00
-- url     : https://prove2.me/submissions/7b719961-5595-45d0-aa8a-e2ca79f5e788

import Definitions.Def_ReciprocityTheory_Chebotarev_NormGsEmbZLe
import Definitions.Def_ReciprocityTheory_Chebotarev_RpowNegFinrankSubOne
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
import Definitions.Def_ReciprocityTheory_Chebotarev_MeanZero
import Definitions.Def_ReciprocityTheory_Chebotarev_LatSum
import Definitions.Def_ReciprocityTheory_Chebotarev_KHoldA
import Theorems.Thm_ReciprocityTheory_Cheb_natCast_cpow_mul_cpow_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units Set
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (a : NZIdeal E) :
    Hfun χ b c s (a.1 * b.1) = gfun χ c s a := by
  have hb : Ideal.absNorm b.1 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact b.2
  have hdvd : (b.1 * c.1 ∣ a.1 * b.1) ↔ c.1 ∣ a.1 := by
    rw [mul_comm a.1]; exact mul_dvd_mul_iff_left b.2
  simp only [Hfun, gfun, map_mul, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb), hdvd, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  have := natCast_cpow_mul_cpow_neg hb (s : ℂ)
  linear_combination (χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) *
    (1 - (Ideal.absNorm c.1 : ℂ) * (if c.1 ∣ a.1 then 1 else 0)) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) * this
end ReciprocityTheory.Cheb

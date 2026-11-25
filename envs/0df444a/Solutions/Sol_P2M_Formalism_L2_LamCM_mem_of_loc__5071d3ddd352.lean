-- Prove2me | solution 1 for P2M_Formalism_L2_LamCM_mem_of_loc__5071d3ddd352
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:45:24.621702+00:00
-- url     : https://prove2.me/submissions/bcf1b9c2-afc1-4ce1-addb-52c91287a897

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Theorems.Thm_Formalism_L2_LamCM_mul_le_mul_r
import Theorems.Thm_Formalism_L2_LamCM_valuation_eq_exp_count
import Theorems.Thm_Formalism_L2_LamCM_le_one_of_count_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace Formalism.L2.LamCM
theorem _root_.solution : MemOfLoc := by
  intro K _ _ I x hI hloc
  by_cases hx : x = 0
  · rw [hx]; exact FractionalIdeal.zero_mem I
  have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have hge : ∀ p : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K p I ≤ FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) := by
    intro p
    obtain ⟨c, ⟨hc0, hcount⟩, hle⟩ := hloc p
    rw [valuation_eq_exp_count p hx, valuation_eq_exp_count p hc0, WithZero.exp_le_exp, hcount] at hle
    linarith
  set J := FractionalIdeal.spanSingleton (𝓞 K)⁰ x * I⁻¹ with hJdef
  have hJ0 : J ≠ 0 := mul_ne_zero hs (inv_ne_zero hI)
  have hJ : J ≤ 1 := by
    refine le_one_of_count_nonneg hJ0 fun p => ?_
    rw [hJdef, FractionalIdeal.count_mul K p hs (inv_ne_zero hI), FractionalIdeal.count_inv]
    linarith [hge p]
  have hJI : J * I = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
    rw [hJdef, mul_assoc, inv_mul_cancel₀ hI, mul_one]
  rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← hJI]
  calc J * I ≤ 1 * I := mul_le_mul_r hJ I
    _ = I := one_mul I
end Formalism.L2.LamCM

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.gtE_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:34.364185+00:00
-- url     : https://prove2.me/submissions/1bb36802-9816-4ef4-bf65-4fa55784bb26

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Module Submodule
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (m lam A Bt N : ℝ) (hm : 0 ≤ m) (hlam : 0 < lam) (hA0 : 0 ≤ A)
    (hA : A ≤ m ^ 2 / lam) (hB0 : 0 ≤ Bt) (hBt : Bt ≤ 1 / 2) (hN0 : 0 ≤ N)
    (hN : N ≤ (m + 1) / lam) : A ^ 2 + (Bt * N) ^ 2 ≤ ((m + 1) ^ 2 / lam) ^ 2 := by
  have hA' : A * lam ≤ m ^ 2 := by rwa [le_div_iff₀ hlam] at hA
  have hN' : N * lam ≤ m + 1 := by rwa [le_div_iff₀ hlam] at hN
  have h1 : (A * lam) ^ 2 ≤ (m ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hA' 2
  have hBN : Bt * (N * lam) ≤ 1 / 2 * (m + 1) :=
    mul_le_mul hBt hN' (by positivity) (by norm_num)
  have h2 : (Bt * (N * lam)) ^ 2 ≤ (1 / 2 * (m + 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hBN 2
  have h3 : (m ^ 2) ^ 2 + (1 / 2 * (m + 1)) ^ 2 ≤ ((m + 1) ^ 2) ^ 2 := by
    nlinarith [pow_nonneg hm 3, sq_nonneg m, hm]
  rw [div_pow, le_div_iff₀ (by positivity)]
  calc (A ^ 2 + (Bt * N) ^ 2) * lam ^ 2 = (A * lam) ^ 2 + (Bt * (N * lam)) ^ 2 := by ring
    _ ≤ ((m + 1) ^ 2) ^ 2 := by linarith
end ReciprocityTheory.ChartRestriction.G.T0

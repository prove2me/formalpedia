-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.KE.rmu_isIntegral_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:33:53.740524+00:00
-- url     : https://prove2.me/submissions/5a6a5d29-7647-446c-8f90-9e3aaabbb2a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1 ReciprocityTheory.ChartRestriction.L1.KE
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1.KE
theorem _root_.solution {x : ℂ_[l]} (hx : x ∈ Rmu l) : IsIntegral ℤ x := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨n, hn, -, h⟩ := hx
    exact IsIntegral.of_pow hn (h ▸ isIntegral_one)
  | zero => exact isIntegral_zero
  | one => exact isIntegral_one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | mul x y _ _ hx hy => exact hx.mul hy
end ReciprocityTheory.ChartRestriction.L1.KE

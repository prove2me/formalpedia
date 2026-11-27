-- Prove2me | solution 1 for PositivityTheory.Mirab.Irr.avg_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:24.847684+00:00
-- url     : https://prove2.me/submissions/378c4f09-4b14-4abd-a24f-9f7556bcc931

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndIrr
import Theorems.Thm_PositivityTheory_Mirab_Irr_char_inv_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open PositivityTheory PositivityTheory.Mirab PositivityTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
namespace PositivityTheory.Mirab.Irr
theorem _root_.solution [Fintype (uniSub k n)] (ψ₀ : AddChar k ℂ) (f : mirabSub k n → ℂ) (x : mirabSub k n)
    (v : uniSub k n) :
    ∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (x * (v : mirabSub k n) * u) =
      (∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (x * u)) * genericChar n ψ₀ v := by
  rw [Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ (fun u => ?_)
  have h3 := char_inv_mul n ψ₀ v
  have e : x * (v : mirabSub k n) * u = x * ((v * u : uniSub k n) : mirabSub k n) := by
    rw [Subgroup.coe_mul, mul_assoc]
  change _ = genericChar n ψ₀ ((v * u)⁻¹) * f (x * ((v * u : uniSub k n) : mirabSub k n)) * genericChar n ψ₀ v
  rw [e, mul_inv_rev, map_mul]
  linear_combination (-(genericChar n ψ₀ (u⁻¹) * f (x * ((v * u : uniSub k n) : mirabSub k n)))) * h3
end PositivityTheory.Mirab.Irr

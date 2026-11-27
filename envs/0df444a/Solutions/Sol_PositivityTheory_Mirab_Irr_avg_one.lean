-- Prove2me | solution 1 for PositivityTheory.Mirab.Irr.avg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:21.273343+00:00
-- url     : https://prove2.me/submissions/54fadd4e-c35e-49ba-ab0d-327924111308

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndIrr
import Theorems.Thm_PositivityTheory_Mirab_Irr_char_inv_mul
import Theorems.Thm_GlobalTheory_FiniteGL_mem_mirabInducedSpace


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
theorem _root_.solution [Fintype (uniSub k n)] (ψ₀ : AddChar k ℂ) (f : mirabSub k n → ℂ)
    (hf : f ∈ MirabInducedSpace n ψ₀) :
    ∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (1 * u) = (Nat.card (uniSub k n) : ℂ) * f 1 := by
  rw [mem_mirabInducedSpace] at hf
  have e : ∀ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (1 * u) = f 1 := by
    intro u
    have h2 : f (u : mirabSub k n) = genericChar n ψ₀ u * f 1 := by rw [← hf u 1, mul_one]
    rw [one_mul, h2]
    linear_combination f 1 * char_inv_mul n ψ₀ u
  rw [Finset.sum_congr rfl (fun u _ => e u), Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
    nsmul_eq_mul]
end PositivityTheory.Mirab.Irr

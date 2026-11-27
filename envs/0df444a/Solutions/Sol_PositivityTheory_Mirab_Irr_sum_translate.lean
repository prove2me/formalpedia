-- Prove2me | solution 1 for PositivityTheory.Mirab.Irr.sum_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:54:08.93636+00:00
-- url     : https://prove2.me/submissions/1ebfcefc-657a-4bee-83fc-fe28f77691d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndIrr
import Theorems.Thm_PositivityTheory_Mirab_Irr_vanish_off_uni
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
theorem _root_.solution (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) [Fintype (mirabSub k n)] [Fintype (uniSub k n)]
    (F g : mirabSub k n → ℂ) (hF : F ∈ MirabInducedSpace n ψ₀)
    (hr : ∀ (x : mirabSub k n) (u : uniSub k n), F (x * (u : mirabSub k n)) = F x * genericChar n ψ₀ u)
    (hg : g ∈ MirabInducedSpace n ψ₀) (x : mirabSub k n) :
    ∑ p : mirabSub k n, g p * F (x * p⁻¹) = (Nat.card (uniSub k n) : ℂ) * F 1 * g x := by
  rw [mem_mirabInducedSpace] at hF hg
  have e1 : ∑ p : mirabSub k n, g p * F (x * p⁻¹) = ∑ y : mirabSub k n, g (y⁻¹ * x) * F y := by
    refine Fintype.sum_equiv ((Equiv.inv _).trans (Equiv.mulLeft x)) _ _ (fun p => ?_)
    change _ = g ((x * p⁻¹)⁻¹ * x) * F (x * p⁻¹)
    rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  have e2 : ∑ u : uniSub k n, g ((u : mirabSub k n)⁻¹ * x) * F u =
      ∑ y ∈ Finset.univ.map (Function.Embedding.subtype (· ∈ uniSub k n)), g (y⁻¹ * x) * F y := by
    rw [Finset.sum_map]; rfl
  have e3 : ∑ y : mirabSub k n, g (y⁻¹ * x) * F y =
      ∑ y ∈ Finset.univ.map (Function.Embedding.subtype (· ∈ uniSub k n)), g (y⁻¹ * x) * F y := by
    refine (Finset.sum_subset (Finset.subset_univ _) (fun y _ hy => ?_)).symm
    have hy' : y ∉ uniSub k n := fun hm => hy (Finset.mem_map.2 ⟨⟨y, hm⟩, Finset.mem_univ _, rfl⟩)
    rw [vanish_off_uni n ψ₀ hψ F hF hr y hy', mul_zero]
  have e4 : ∀ u : uniSub k n, g ((u : mirabSub k n)⁻¹ * x) * F u = F 1 * g x := by
    intro u
    have h1 : g ((u : mirabSub k n)⁻¹ * x) = genericChar n ψ₀ (u⁻¹) * g x := hg (u⁻¹) x
    have h2 : F (u : mirabSub k n) = genericChar n ψ₀ u * F 1 := by rw [← hF u 1, mul_one]
    rw [h1, h2]
    linear_combination (F 1 * g x) * char_inv_mul n ψ₀ u
  rw [e1, e3, ← e2, Finset.sum_congr rfl (fun u _ => e4 u), Finset.sum_const, Finset.card_univ,
    Fintype.card_eq_nat_card, nsmul_eq_mul]
  ring
end PositivityTheory.Mirab.Irr

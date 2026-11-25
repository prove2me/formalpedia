-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r20a.PositivityTheory.Rg.BcN.F2.LocOpPf.finsum_quot_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:58:25.858905+00:00
-- url     : https://prove2.me/submissions/b84385d1-69f3-448a-89f0-01aaaef79eb3

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_QuotientOutRightInvariant
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r20a_finsum_const_eq_card_mul
import Theorems.Thm_UpperTheory_Reformulated_B_P6_r20a_quotient_out_right_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r20a
namespace UpperTheory.Reformulated.B.P6.r20a
namespace PositivityTheory.Rg.BcN.F2.LocOpPf
theorem _root_.solution :
    ∀ {H : Type} [inst : Group H] {S T : Subgroup H}, S ≤ T → ∀ (u : H → ℂ), (∀ (x t : H), t ∈ T → u (x * t) = u x) → S.relIndex T ≠ OfNat.ofNat (nat_lit 0) → (Function.support fun (q : H ⧸ S) ↦ u (Quotient.out q)).Finite → ∑ᶠ (q : H ⧸ S), u (Quotient.out q) = (S.relIndex T).cast * ∑ᶠ (q : H ⧸ T), u (Quotient.out q) := by
  intro H _ S T hST u hu hidx hfin
  have huS : ∀ (x s : H), s ∈ S → u (x * s) = u x := fun x s hs => hu x s (hST hs)
  set e := Subgroup.quotientEquivProdOfLE hST with he
  have hfst : ∀ x : H, (e (x : H ⧸ S)).1 = (x : H ⧸ T) := fun x => rfl
  have key : ∀ q : H ⧸ S, u (Quotient.out q) = u (Quotient.out (e q).1) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [hfst x, quotient_out_right_invariant S u huS x, quotient_out_right_invariant T u hu x]
  have hcard : S.relIndex T = Nat.card (T ⧸ S.subgroupOf T) := rfl
  haveI : Finite (T ⧸ S.subgroupOf T) := Nat.finite_of_card_ne_zero (by rw [← hcard]; exact hidx)
  set F : (H ⧸ T) × (T ⧸ S.subgroupOf T) → ℂ := fun pr => u (Quotient.out pr.1) with hF
  have h1 : ∑ᶠ (q : H ⧸ S), u (Quotient.out q) = ∑ᶠ (q : H ⧸ S), F (e q) :=
    finsum_congr key
  have h2 : ∑ᶠ (q : H ⧸ S), F (e q) = ∑ᶠ pr, F pr := finsum_comp_equiv e
  have hFfin : (Function.support F).Finite := by
    apply (hfin.image e).subset
    intro pr hpr
    refine ⟨e.symm pr, ?_, by simp⟩
    have : u (Quotient.out (e.symm pr)) = F pr := by
      rw [key]; simp [hF]
    simpa [Function.mem_support, this] using hpr
  have h3 : ∑ᶠ pr, F pr = ∑ᶠ (p : H ⧸ T) (r : T ⧸ S.subgroupOf T), F (p, r) := finsum_curry F hFfin
  have h4 : ∀ p : H ⧸ T, ∑ᶠ (r : T ⧸ S.subgroupOf T), F (p, r)
      = (Nat.card (T ⧸ S.subgroupOf T) : ℂ) * u (Quotient.out p) := fun p =>
    finsum_const_eq_card_mul (u (Quotient.out p))
  have hffin : (Function.support fun (p : H ⧸ T) => u (Quotient.out p)).Finite := by
    apply (hfin.image fun q => (e q).1).subset
    intro p hp
    refine ⟨((Quotient.out p : H) : H ⧸ S), ?_, ?_⟩
    · have h5 : u (Quotient.out ((Quotient.out p : H) : H ⧸ S)) = u (Quotient.out p) :=
        quotient_out_right_invariant S u huS _
      simpa [Function.mem_support, h5] using hp
    · show (e ((Quotient.out p : H) : H ⧸ S)).1 = p
      rw [hfst]
      exact QuotientGroup.out_eq' p
  rw [h1, h2, h3, finsum_congr h4, hcard]
  have hsub : (Function.support fun p : H ⧸ T =>
      (Nat.card (T ⧸ S.subgroupOf T) : ℂ) * u (Quotient.out p)) ⊆ ↑hffin.toFinset := by
    intro p hp
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    rw [Function.mem_support] at hp
    intro h0
    apply hp
    simp only [h0, mul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsub, finsum_eq_sum _ hffin, Finset.mul_sum]
end PositivityTheory.Rg.BcN.F2.LocOpPf
end UpperTheory.Reformulated.B.P6.r20a

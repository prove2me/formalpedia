-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.k2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:01:13.26163+00:00
-- url     : https://prove2.me/submissions/6abfbac9-8cd9-451b-b344-8e9214fb0946

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FirstFamilySymbolMulVariablePow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainInlInr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_kpow
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_mapDomain_inl_inl
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_mapDomain_inl_inr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_first_family_symbol_mul_variable_pow
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_good_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_good_le
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_good_mul_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_good_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
theorem _root_.solution (γ : Ix m n →₀ ℕ) : (∀ k ∈ γ.support, inF1 ε k) → ∀ (d : ℕ) (u : Sym m n), SymbolInFirstFamily ε u → EtaLe u d →
    ∃ r, Good ε d r ∧ ∀ g, op u (monomial γ 1 * g) = op (u * monomial (γ.mapDomain Sum.inl) 1) g + op r g := by
  induction γ using Finsupp.induction with
  | zero => intro _ d u _ _; exact ⟨0, good_zero d, fun g => by simp [monomial_zero', op_zero]⟩
  | single_add a b f haf hb ih =>
    intro hsup d u hu hue
    have hsf : ∀ k ∈ f.support, inF1 ε k := by
      intro k hk
      apply hsup k
      have hka : k ≠ a := fun h => haf (h ▸ hk)
      rw [Finsupp.mem_support_iff] at hk ⊢
      simpa [Finsupp.single_apply, Ne.symm hka] using hk
    have hai : inF1 ε a := by
      apply hsup a
      rw [Finsupp.mem_support_iff]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.1 haf, add_zero]
      exact hb
    obtain ⟨r₁, hr₁, e₁⟩ := kpow hai b d u hu hue
    have hu' := first_family_symbol_mul_variable_pow hu hai b
    obtain ⟨r₂, hr₂, e₂⟩ := ih hsf d (u * X (Sum.inl a) ^ b) hu'.1 (hu'.2 d hue)
    obtain ⟨r₃, hr₃, e₃⟩ := ih hsf d r₁ hr₁.1 (good_le hr₁)
    have hM : ∀ k, ((f.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
        (f.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      rw [mapDomain_inl_inl, mapDomain_inl_inr] at hk
      exact hsf k (Finsupp.mem_support_iff.2 (by tauto))
    have g3 : Good ε d (r₁ * monomial (f.mapDomain Sum.inl) 1) := by
      have := good_mul_monomial (e := 0) hr₁ _ hM (by simp [mapDomain_inl_inr])
      simpa using this
    refine ⟨r₂ + r₁ * monomial (f.mapDomain Sum.inl) 1 + r₃, good_add (good_add hr₂ g3) hr₃, fun g => ?_⟩
    rw [monomial_single_add, mul_assoc, e₁, e₂, e₃, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      monomial_single_add, op_add, op_add]
    have : u * (X (Sum.inl a) ^ b * monomial (Finsupp.mapDomain Sum.inl f) 1) =
        u * X (Sum.inl a) ^ b * monomial (Finsupp.mapDomain Sum.inl f) 1 := by ring
    rw [this]
    ring
end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

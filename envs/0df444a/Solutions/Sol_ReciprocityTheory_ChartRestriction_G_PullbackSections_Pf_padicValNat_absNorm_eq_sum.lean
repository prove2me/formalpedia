-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.padicValNat_absNorm_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:33:02.723672+00:00
-- url     : https://prove2.me/submissions/f8d36cea-f162-4ed1-a6d8-826e274beb69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_padicValNat_multiset_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_mem_factors_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
theorem _root_.solution (ℓ : ℕ) [Fact ℓ.Prime] {X : Ideal (𝓞 E)} (hX : X ≠ ⊥) :
    padicValNat ℓ (Ideal.absNorm X) = ∑ Q ∈ (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).toFinset,
      (normalizedFactors X).count Q * padicValNat ℓ (Ideal.absNorm Q) := by
  classical
  have hv : ∀ Q : Ideal (𝓞 E), Q.IsPrime → Q ≠ ⊥ → (ℓ : 𝓞 E) ∉ Q →
      padicValNat ℓ (Ideal.absNorm Q) = 0 := by
    intro Q hQp hQ0 hlQ
    apply padicValNat.eq_zero_of_not_dvd
    intro hdvd
    haveI : Q.IsMaximal := hQp.isMaximal hQ0
    letI : Field (𝓞 E ⧸ Q) := Ideal.Quotient.field Q
    have hfin : Finite (𝓞 E ⧸ Q) := by
      apply Nat.finite_of_card_ne_zero
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
      exact hQ0
    haveI := Fintype.ofFinite (𝓞 E ⧸ Q)
    haveI := ringChar.charP (𝓞 E ⧸ Q)
    obtain ⟨n, hp, hcard⟩ := FiniteField.card (𝓞 E ⧸ Q) (ringChar (𝓞 E ⧸ Q))
    have hN : Ideal.absNorm Q = Fintype.card (𝓞 E ⧸ Q) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    rw [hN, hcard] at hdvd
    have heq : ℓ = ringChar (𝓞 E ⧸ Q) :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) hp).mp ((Fact.out : ℓ.Prime).dvd_of_dvd_pow hdvd)
    apply hlQ
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, heq, ringChar.Nat.cast_ringChar]
  have hX' : (normalizedFactors X).prod = X :=
    associated_iff_eq.mp (prod_normalizedFactors (by simpa using hX))
  have hN : Ideal.absNorm X = ((normalizedFactors X).map Ideal.absNorm).prod := by
    conv_lhs => rw [← hX']
    exact map_multiset_prod Ideal.absNorm _
  have hnz : ∀ x ∈ (normalizedFactors X).map Ideal.absNorm, x ≠ 0 := by
    intro x hx
    obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hx
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact ne_zero_of_mem_normalizedFactors hQ
  rw [hN, padicValNat_multiset_prod ℓ _ hnz, Multiset.map_map, Finset.sum_multiset_map_count]
  simp only [smul_eq_mul, Function.comp_apply]
  set A := (normalizedFactors X).toFinset
  set B := (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).toFinset
  calc ∑ Q ∈ A, (normalizedFactors X).count Q * padicValNat ℓ (Ideal.absNorm Q)
      = ∑ Q ∈ A ∪ B, (normalizedFactors X).count Q * padicValNat ℓ (Ideal.absNorm Q) := by
        apply Finset.sum_subset Finset.subset_union_left
        intro Q hQ hQA
        have hQB : Q ∈ B := by
          rcases Finset.mem_union.mp hQ with h | h
          · exact absurd h hQA
          · exact h
        have hc : (normalizedFactors X).count Q = 0 :=
          Multiset.count_eq_zero.mpr (fun h => hQA (Multiset.mem_toFinset.mpr h))
        rw [hc, zero_mul]
    _ = ∑ Q ∈ B, (normalizedFactors X).count Q * padicValNat ℓ (Ideal.absNorm Q) := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro Q hQ hQB
        have hQA : Q ∈ (normalizedFactors X) := by
          rcases Finset.mem_union.mp hQ with h | h
          · exact Multiset.mem_toFinset.mp h
          · exact absurd h hQB
        have hQp : Q.IsPrime := Ideal.isPrime_of_prime (prime_of_normalized_factor Q hQA)
        have hQ0 : Q ≠ ⊥ := ne_zero_of_mem_normalizedFactors hQA
        have hl : (ℓ : 𝓞 E) ∉ Q := fun h =>
          hQB (Multiset.mem_toFinset.mpr (mem_factors_span ℓ hQp hQ0 h))
        rw [hv Q hQp hQ0 hl, mul_zero]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

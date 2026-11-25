-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.normValuation_eq_factorization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:25:11.605497+00:00
-- url     : https://prove2.me/submissions/9bced055-9ced-4520-a3c4-9d186f131e29

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_NormOrdLengthResidue
import Definitions.Def_ReciprocityTheory_SemistableReduction_NormValuationEqFactorization
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_normOrd_length_pow
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_normOrd_length_residue


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module UniqueFactorizationMonoid
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hC1 : NormLengthStatement) : NormOrdStatement := by
  classical
  intro O B _ _ _ _ _ _ _ _ _ g hg
  rw [hC1 O B g hg]
  set I : Ideal B := Ideal.span {g} with hIdef
  have hI : I ≠ ⊥ := by rwa [Ne, hIdef, Ideal.span_singleton_eq_bot]
  have hfac : UniqueFactorizationMonoid.factors I = normalizedFactors I :=
    UniqueFactorizationMonoid.factors_eq_normalizedFactors I
  have hmax : ∀ P ∈ UniqueFactorizationMonoid.factors I, P.IsMaximal ∧ P ≠ ⊥ := by
    intro P hP
    have hpr : Prime P := UniqueFactorizationMonoid.prime_of_factor P hP
    exact ⟨(Ideal.isPrime_of_prime hpr).isMaximal hpr.ne_zero, hpr.ne_zero⟩
  let φ := IsDedekindDomain.quotientEquivPiFactors hI
  let ψ : (B ⧸ I) ≃ₗ[O] ((P : (UniqueFactorizationMonoid.factors I).toFinset) →
      B ⧸ (P : Ideal B) ^ Multiset.count (P : Ideal B) (UniqueFactorizationMonoid.factors I)) :=
    { φ with
      map_smul' := by
        intro o x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        change φ (Ideal.Quotient.mk I (o • b)) = o • φ (Ideal.Quotient.mk I b)
        rw [IsDedekindDomain.quotientEquivPiFactors_mk, IsDedekindDomain.quotientEquivPiFactors_mk]
        rfl }
  rw [ψ.length_eq, Module.length_pi_of_fintype]
  have hterm : ∀ P : (UniqueFactorizationMonoid.factors I).toFinset,
      Module.length O (B ⧸ (P : Ideal B) ^
        Multiset.count (P : Ideal B) (UniqueFactorizationMonoid.factors I)) =
      ((Multiset.count (P : Ideal B) (UniqueFactorizationMonoid.factors I) *
        (P : Ideal B).inertiaDeg O : ℕ) : ℕ∞) := by
    intro P
    obtain ⟨hPm, hP0⟩ := hmax P (Multiset.mem_toFinset.mp P.2)
    rw [normOrd_length_pow O B _ hP0, normOrd_length_residue O B]
    norm_cast
  rw [Finset.sum_congr rfl (fun P _ => hterm P), ← Nat.cast_sum]
  congr 1
  rw [← hfac, Finset.sum_coe_sort (UniqueFactorizationMonoid.factors I).toFinset
    (fun P => Multiset.count P (UniqueFactorizationMonoid.factors I) * P.inertiaDeg O)]
  rw [finsum_eq_sum_of_support_subset (s := (UniqueFactorizationMonoid.factors I).toFinset.subtype
    (fun Q : Ideal B => Q.IsMaximal)) _ ?sup]
  · rw [Finset.sum_subtype_eq_sum_filter (fun Q : Ideal B =>
        Q.inertiaDeg O * Multiset.count Q (UniqueFactorizationMonoid.factors I)),
      Finset.filter_true_of_mem]
    · exact Finset.sum_congr rfl fun P _ => mul_comm _ _
    · intro P hP
      exact (hmax P (Multiset.mem_toFinset.mp hP)).1
  case sup =>
    intro Q hQ
    rw [Function.mem_support] at hQ
    rw [Finset.mem_coe, Finset.mem_subtype, Multiset.mem_toFinset]
    by_contra hn
    exact hQ (by rw [Multiset.count_eq_zero.mpr hn, mul_zero])
end ReciprocityTheory.MultiplicativeHeights

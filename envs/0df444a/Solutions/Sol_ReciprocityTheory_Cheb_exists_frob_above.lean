-- Prove2me | solution 1 for ReciprocityTheory.Cheb.exists_frob_above
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:22.067698+00:00
-- url     : https://prove2.me/submissions/9c53a659-2d01-4923-90e8-47606a427ad6

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossFrobE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {M : Type} [Field M] [NumberField M] (E : IntermediateField ℚ M) [IsGalois E M]
    (l : ℕ) [Fact l.Prime] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (q : Ideal (𝓞 E)) (hq : q.IsPrime)
    (hqp : (Ideal.absNorm q).Prime) (hql : Ideal.absNorm q ≠ l) :
    ∃ (P : Ideal (𝓞 M)) (_ : P.IsPrime) (φ : M ≃ₐ[E] M),
      P.LiesOver (Ideal.span {((Ideal.absNorm q : ℕ) : ℤ)}) ∧ φ ζ = ζ ^ Ideal.absNorm q ∧
      IsArithFrobAt ℤ (φ.restrictScalars ℚ) P := by
  set p := Ideal.absNorm q with hpdef
  have hq0 : q ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hpdef
    exact Nat.not_prime_zero (hpdef ▸ hqp)
  have hqmax : q.IsMaximal := hq.isMaximal hq0
  obtain ⟨P, hPmax, hPq⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) q
  have hPunder : P.under (𝓞 E) = q := hPq.over.symm
  have hP0 : P ≠ ⊥ := by
    intro h
    apply hq0
    rw [← hPunder, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  have hPfin : Finite (𝓞 M ⧸ P) :=
    (Ideal.absNorm_ne_zero_iff P).mp (fun h => hP0 (Ideal.absNorm_eq_zero_iff.mp h))
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) (M ≃ₐ[E] M) P

  have hqZ : q.under ℤ = Ideal.span {(p : ℤ)} := by
    have hpr : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hqp).irreducible
    have hle : Ideal.span {(p : ℤ)} ≤ q.under ℤ := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap]
      have := Ideal.absNorm_mem q
      rw [← hpdef] at this
      simpa using this
    exact (hpr.eq_of_le (Ideal.IsPrime.under ℤ q).ne_top hle).symm
  have hPZ : P.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← Ideal.under_under (B := 𝓞 E), hPunder, hqZ]
  have hcardZ : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [hPZ, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hcardE : Nat.card (𝓞 E ⧸ P.under (𝓞 E)) = p := by
    rw [hPunder, hpdef, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfrob : IsArithFrobAt ℤ (σ.restrictScalars ℚ) P := by
    intro x
    have := hσ x
    rw [hcardE] at this
    show (σ.restrictScalars ℚ) • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P
    rw [hcardZ]
    exact this
  refine ⟨P, hPmax.isPrime, σ, ⟨hPZ.symm⟩, ?_, hfrob⟩

  have hint : IsIntegral ℤ ζ := hζ.isIntegral (Nat.Prime.pos Fact.out)
  let z : 𝓞 M := ⟨ζ, hint⟩
  have hz : z ^ l = 1 := by
    apply RingOfIntegers.ext
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_one]
    exact (map_pow (algebraMap (𝓞 M) M) z l).trans hζ.pow_eq_one
  have hl : ((l : ℕ) : 𝓞 M) ∉ P := by
    intro h
    have h' : ((l : ℕ) : ℤ) ∈ P.under ℤ := by
      rw [Ideal.mem_comap]; simpa using h
    rw [hPZ, Ideal.mem_span_singleton] at h'
    have hdvd : p ∣ l := by exact_mod_cast h'
    exact hql ((Nat.prime_dvd_prime_iff_eq hqp Fact.out).mp hdvd)
  have key := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hfrob hz hl
  rw [hcardZ] at key
  calc σ ζ = (((σ.restrictScalars ℚ) • z : 𝓞 M) : M) := rfl
    _ = ((z ^ p : 𝓞 M) : M) := congrArg (fun y : 𝓞 M => (y : M)) key
    _ = ζ ^ p := by
      rw [RingOfIntegers.coe_eq_algebraMap]
      exact (map_pow (algebraMap (𝓞 M) M) z p).trans rfl
end ReciprocityTheory.Cheb

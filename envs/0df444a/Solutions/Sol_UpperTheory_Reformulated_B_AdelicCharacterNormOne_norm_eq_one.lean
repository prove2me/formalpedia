-- Prove2me | solution 1 for UpperTheory.Reformulated.B.AdelicCharacterNormOne.norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:32.844854+00:00
-- url     : https://prove2.me/submissions/d276c1c2-0032-4a0f-a86d-9e26a4927bdc

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FactorialTendstoZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter Topology NumberField IsDedekindDomain
private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.factorial_tendsto_zero {K : Type*} [NormedField K]
    (h1 : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (N : ℕ) (hN : 0 < N) (hlt : ‖(N : K)‖ < 1) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : K)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (norm_nonneg _),
    fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one ha hlt
  filter_upwards [eventually_ge_atTop (N ^ k)] with n hn
  obtain ⟨m, hm⟩ := Nat.dvd_factorial (pow_pos hN k) hn
  rw [hm, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow]
  exact (mul_le_of_le_one_right (by positivity) (h1 m)).trans_lt hk
private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.local_tendsto {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : v.adicCompletion F)) atTop (𝓝 0) := by
  refine UpperTheory.Reformulated.B.AdelicCharacterNormOne.factorial_tendsto_zero (K := v.adicCompletion F) (fun n => ?_)
    (Ideal.absNorm v.asIdeal) (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)) ?_
  · have := FinitePlace.norm_le_one F v (n : 𝓞 F)
    rwa [map_natCast, map_natCast] at this
  · have := (FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
    rwa [map_natCast, map_natCast] at this
private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.finite_tendsto {F : Type} [Field F] [NumberField F] :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F)) atTop (𝓝 0) := by
  have h : Tendsto (fun (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) =>
      ((n.factorial : ℕ) : v.adicCompletionIntegers F)) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro v
    rw [tendsto_subtype_rng]
    simpa using UpperTheory.Reformulated.B.AdelicCharacterNormOne.local_tendsto v
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := cofinite)).continuous
  exact (hc.tendsto _).comp h
private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.eq_one_of_tendsto {r : ℝ} (hr : 0 ≤ r)
    (h : Tendsto (fun n : ℕ => r ^ n.factorial) atTop (𝓝 1)) : r = 1 := by
  have hf : Tendsto Nat.factorial atTop atTop :=
    tendsto_atTop_mono Nat.self_le_factorial tendsto_id
  rcases lt_trichotomy r 1 with hlt | heq | hgt
  · exact absurd (tendsto_nhds_unique ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hlt).comp hf) h)
      zero_ne_one
  · exact heq
  · exact absurd h (not_tendsto_nhds_of_tendsto_atTop
      ((tendsto_pow_atTop_atTop_of_one_lt hgt).comp hf) 1)
end

set_option autoImplicit false
open Filter Topology NumberField IsDedekindDomain
namespace UpperTheory.Reformulated.B.AdelicCharacterNormOne
theorem _root_.solution :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ℂ),
    Continuous (⇑ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ) →
      (∀ (a : F),
          (ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ)
              ((Algebra.algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) :
                  F → NumberField.AdeleRing (NumberField.RingOfIntegers F) F)
                a) =
            (1 : ℂ)) →
        ∀ (x : NumberField.AdeleRing (NumberField.RingOfIntegers F) F),
          ‖(ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ) x‖ = (1 : ℝ) := by
  intro F _ _ ψ hψ htriv
  let i : InfiniteAdeleRing F → AdeleRing (𝓞 F) F := fun x => (x, 0)
  let j : FiniteAdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F := fun y => (0, y)
  have hi : Continuous i := continuous_id.prodMk continuous_const
  have hj : Continuous j := continuous_const.prodMk continuous_id
  have hsplit : ∀ x : AdeleRing (𝓞 F) F, x = i x.1 + j x.2 := fun x =>
    Prod.ext (add_zero x.1).symm (zero_add x.2).symm
  have hfin : ∀ y, ‖ψ (j y)‖ = 1 := by
    intro y
    apply UpperTheory.Reformulated.B.AdelicCharacterNormOne.eq_one_of_tendsto (norm_nonneg _)
    have h1 := (UpperTheory.Reformulated.B.AdelicCharacterNormOne.finite_tendsto (F := F)).mul_const y
    rw [zero_mul] at h1
    have h2 := (((hψ.comp hj).norm).tendsto 0).comp h1
    have h0 : j 0 = 0 := rfl
    have hs : ∀ n : ℕ, j ((n : FiniteAdeleRing (𝓞 F) F) * y) = n • j y := fun n =>
      Prod.ext (nsmul_zero n).symm (nsmul_eq_mul n y).symm
    simp only [Function.comp_def, h0, hs, AddChar.map_zero_eq_one, norm_one,
      AddChar.map_nsmul_eq_pow, norm_pow] at h2
    exact h2
  have hinf : ∀ x, ‖ψ (i x)‖ = 1 := by
    intro x
    refine (InfiniteAdeleRing.denseRange_algebraMap F).induction_on x
      (isClosed_eq (hψ.comp hi).norm continuous_const) fun a => ?_
    have h := congrArg norm (htriv a)
    rw [hsplit (algebraMap F _ a), AddChar.map_add_eq_mul, norm_mul, hfin, mul_one, norm_one] at h
    exact h
  intro x
  rw [hsplit x, AddChar.map_add_eq_mul, norm_mul, hfin, hinf, mul_one]
end UpperTheory.Reformulated.B.AdelicCharacterNormOne

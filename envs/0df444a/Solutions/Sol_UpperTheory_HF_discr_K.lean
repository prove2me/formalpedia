-- Prove2me | solution 1 for UpperTheory.HF.discr_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:58:11.183695+00:00
-- url     : https://prove2.me/submissions/0c66c673-3c98-49c8-8839-e4d12a3b8b30

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiscrK
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_finrank_K
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_d_mod_four
import Theorems.Thm_Formalism_HC_HostRaw_finrank_K
import Theorems.Thm_Formalism_HC_HostRaw_sqd_mem_K
import Theorems.Thm_Formalism_HF_quadDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
section
open Polynomial
private theorem diffQuadK (K : Type) [Field K] [NumberField K] (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤)
    (hrank : Module.finrank ℚ K = 2) (β : 𝓞 K) (hβ : (β : K) = x) :
    discr K = -(d : ℤ) ∧ differentIdeal ℤ (𝓞 K) = span {β} := by
  have hdisc : discr K = -(d : ℤ) :=
    Formalism.HF.quadDiscr K (-(d : ℤ)) x (by push_cast; exact hx) hadj
      ((Nat.prime_iff_prime_int.mp hd).neg.squarefree) (by omega)
  refine ⟨hdisc, ?_⟩
  have hN : (differentIdeal ℤ (𝓞 K)).absNorm = d := by
    rw [absNorm_differentIdeal K, hdisc]; simp
  have hβ2 : β ^ 2 = -(d : 𝓞 K) := by
    apply RingOfIntegers.ext
    have : ((β ^ 2 : 𝓞 K) : K) = (β : K) ^ 2 := by push_cast; rfl
    rw [this, hβ, hx]
    push_cast; rfl
  have hadj' : Algebra.adjoin ℚ {algebraMap (𝓞 K) K β} = ⊤ := by
    have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
    have h2 := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1
    rw [hadj] at h2
    show Algebra.adjoin ℚ {(β : K)} = ⊤
    rw [hβ, ← h2]
    rfl
  have hmem := aeval_derivative_mem_differentIdeal ℤ ℚ K β hadj'
  have hint : IsIntegral ℤ β := Algebra.IsIntegral.isIntegral β
  obtain ⟨r, hr⟩ := minpoly.isIntegrallyClosed_dvd hint (p := X ^ 2 + C (d : ℤ))
    (by simp [hβ2])
  have h2β : 2 * β ∈ differentIdeal ℤ (𝓞 K) := by
    have := congrArg (fun p => aeval β (derivative p)) hr
    simp only [derivative_X_pow, derivative_C, derivative_mul, map_add, map_mul,
      minpoly.aeval, zero_mul, add_zero] at this
    have e : (2 : 𝓞 K) * β = aeval β (derivative (minpoly ℤ β)) * aeval β r := by
      rw [← this]; simp [map_ofNat]
    rw [e]
    exact Ideal.mul_mem_right _ _ hmem
  have hdmem : (d : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K) := by
    have := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 K))
    rwa [hN] at this
  have hβmem : β ∈ differentIdeal ℤ (𝓞 K) := by
    have e : β = (d : 𝓞 K) * β - ((d / 2 : ℕ) : 𝓞 K) * (2 * β) := by
      have h : (d : 𝓞 K) = 2 * ((d / 2 : ℕ) : 𝓞 K) + 1 := by
        have : d = 2 * (d / 2) + 1 := by omega
        exact_mod_cast this
      linear_combination (-β) * h
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hdmem) (Ideal.mul_mem_left _ _ h2β)
  have hle : span {β} ≤ differentIdeal ℤ (𝓞 K) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hβmem
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hNβ : (span {β}).absNorm ^ 2 = d ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, hβ2, Ideal.absNorm_span_singleton]
    have : (-(d : 𝓞 K)) = algebraMap ℤ (𝓞 K) (-(d : ℤ)) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hrank]
    simp [Int.natAbs_pow]
  have hNβ' : (span {β}).absNorm = d := by
    exact Nat.pow_left_injective (n := 2) (by norm_num) hNβ
  have hC1 : C.absNorm = 1 := by
    have := congrArg Ideal.absNorm hC
    rw [map_mul, hNβ', hN] at this
    exact Nat.eq_of_mul_eq_mul_left hd.pos (by rw [mul_one]; exact this.symm)
  rw [Ideal.absNorm_eq_one_iff] at hC1
  rw [hC, hC1, Ideal.mul_top]
end
end

set_option autoImplicit false
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), (discr H.K).natAbs = H.d ∧ ∃ s : 𝓞 H.E, (s : H.E) = H.sqd ∧ (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) = span {s} ∧ differentIdeal ℤ (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E) * span {s} := by
  intro φ H
  let x : H.K := ⟨H.sqd, H.sqd_mem_K⟩
  have hx : x ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa [x] using H.sqd_sq
  have hint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hx]
    exact (isIntegral_natCast H.d).neg
  have hadj : IntermediateField.adjoin ℚ {x} = ⊤ := by
    have h' : IntermediateField.lift (@IntermediateField.adjoin ℚ _ H.K _ H.K.algebra' {x}) =
        IntermediateField.lift (⊤ : @IntermediateField ℚ H.K _ _ H.K.algebra') := by
      rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, Set.image_singleton]
      rfl
    have key := IntermediateField.lift_injective H.K h'
    convert key <;> exact Subsingleton.elim _ _
  obtain ⟨β, hβ⟩ : ∃ β : 𝓞 H.K, (β : H.K) = x := ⟨⟨x, hint⟩, rfl⟩
  obtain ⟨hd, hK⟩ := diffQuadK H.K H.d H.d_prime H.d_mod_four x hx hadj H.finrank_K β hβ
  have hmap : (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) =
      span {algebraMap (𝓞 H.K) (𝓞 H.E) β} := by
    rw [hK, Ideal.map_span, Set.image_singleton]
  refine ⟨by rw [hd]; simp, algebraMap (𝓞 H.K) (𝓞 H.E) β, ?_, hmap, ?_⟩
  · show ((β : H.K) : H.E) = H.sqd
    rw [hβ]
  · rw [← hmap]
    exact differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 H.K) (𝓞 H.E)
end UpperTheory.HF

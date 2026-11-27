-- Prove2me | solution 1 for UpperTheory.dvd_norm_sub_one_of_idempotent_interpolation_relNorm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:50.251809+00:00
-- url     : https://prove2.me/submissions/4d6dd04f-dc59-4016-af7e-f77fff3a2ea2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_DvdNormSubOneOfIdempotentInterpolationRelNormOne
import Theorems.Thm_UpperTheory_MU_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain
private theorem prod_interp_mod {Ω ι : Type*} [CommRing Ω] (n : ℕ) (e t : Ω) (he : e * e - e = n * t)
    (hei : IsIntegral ℤ e) (hti : IsIntegral ℤ t) (f g : ι → Ω) (hf : ∀ i, IsIntegral ℤ (f i))
    (hg : ∀ i, IsIntegral ℤ (g i)) (s : Finset ι) :
    ∃ z, IsIntegral ℤ z ∧ ∏ i ∈ s, (e * f i + (1 - e) + n * g i) = e * ∏ i ∈ s, f i + (1 - e) + n * z := by
  classical
  have hn : IsIntegral ℤ (n : Ω) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := Ω) (x := (n : ℤ)))
  induction s using Finset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨z, hz, hprod⟩ := ih
    set P := ∏ i ∈ s, f i with hP
    have hPi : IsIntegral ℤ P := IsIntegral.prod _ fun i _ => hf i
    refine ⟨t * f a * P - t * f a - t * P + t + g a * (e * P + (1 - e)) +
      z * (e * f a + (1 - e)) + n * g a * z, ?_, ?_⟩
    · have h1e : IsIntegral ℤ (1 - e) := isIntegral_one.sub hei
      exact ((((((hti.mul (hf a)).mul hPi).sub (hti.mul (hf a))).sub (hti.mul hPi)).add hti).add
        ((hg a).mul ((hei.mul hPi).add h1e))).add (hz.mul ((hei.mul (hf a)).add h1e)) |>.add
        ((hn.mul (hg a)).mul hz)
    · rw [Finset.prod_insert ha, Finset.prod_insert ha, hprod]
      linear_combination (f a * P - f a - P + 1) * he
private theorem descend_mod {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (n : ℕ) (a : F) (z : Ω)
    (hz : IsIntegral ℤ z) (h : algebraMap F Ω a = 1 + n * z) :
    ∃ w : F, IsIntegral ℤ w ∧ a = 1 + n * w := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, isIntegral_zero, ?_⟩
    apply (algebraMap F Ω).injective
    simpa using h
  · have hnF : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
    refine ⟨(a - 1) / n, ?_, by field_simp; ring⟩
    have hmap : algebraMap F Ω ((a - 1) / n) = z := by
      have hnΩ : (n : Ω) ≠ 0 := by
        rw [← map_natCast (algebraMap F Ω)]
        exact (map_ne_zero _).mpr hnF
      rw [map_div₀, map_sub, map_one, map_natCast, h]
      field_simp
      ring
    rw [← isIntegral_algebraMap_iff (algebraMap F Ω).injective, hmap]
    exact hz
end

set_option autoImplicit false
open NumberField IsDedekindDomain
namespace UpperTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (n : ℕ) (e t δ y : 𝓞 E), (e : E) ∈ K → e * e - e = n * t →
      Algebra.norm K (δ : E) = 1 → (n : ℤ) ∣ Algebra.norm ℤ (e * δ + (1 - e) + n * y : 𝓞 E) - 1 := by
  intro E _ _ K n e t δ y heK he hδ
  classical
  let Ω := AlgebraicClosure E
  have hint : ∀ u : 𝓞 E, IsIntegral ℤ (u : E) := fun u => u.2
  have hintΩ : ∀ (u : 𝓞 E) (σ : E →ₐ[K] Ω), IsIntegral ℤ (σ u) := fun u σ =>
    (hint u).map (σ.restrictScalars ℚ).toRingHom.toIntAlgHom
  have hσe : ∀ σ : E →ₐ[K] Ω, σ (e : E) = algebraMap E Ω e := by
    intro σ
    have h := σ.commutes (⟨e, heK⟩ : K)
    rw [IsScalarTower.algebraMap_apply K E Ω] at h
    exact h
  have heE : ((e : E) * e - e) = n * (t : E) := by
    have h := congrArg (fun u : 𝓞 E => (u : E)) he
    simpa using h
  have heΩ : algebraMap E Ω e * algebraMap E Ω e - algebraMap E Ω e = n * algebraMap E Ω t := by
    have h := congrArg (algebraMap E Ω) heE
    simpa using h
  obtain ⟨z, hz, hprod⟩ := prod_interp_mod n (algebraMap E Ω e) (algebraMap E Ω t) heΩ
    ((hint e).map (IsScalarTower.toAlgHom ℤ E Ω)) ((hint t).map (IsScalarTower.toAlgHom ℤ E Ω))
    (fun σ : E →ₐ[K] Ω => σ δ) (fun σ => σ y) (fun σ => hintΩ δ σ) (fun σ => hintΩ y σ) Finset.univ
  have hδΩ : ∏ σ : E →ₐ[K] Ω, σ δ = 1 := by
    rw [← Algebra.norm_eq_prod_embeddings, hδ, map_one]
  have hK : algebraMap K Ω (Algebra.norm K ((e * δ + (1 - e) + n * y : 𝓞 E) : E)) = 1 + n * z := by
    rw [Algebra.norm_eq_prod_embeddings]
    have hσ : ∀ σ : E →ₐ[K] Ω, σ ((e * δ + (1 - e) + n * y : 𝓞 E) : E) =
        algebraMap E Ω e * σ δ + (1 - algebraMap E Ω e) + n * σ y := by
      intro σ
      push_cast
      rw [map_add, map_add, map_mul, map_sub, map_one, map_mul, map_natCast, hσe]
    simp_rw [hσ]
    rw [hprod, hδΩ]
    ring
  obtain ⟨w, hw, hwK⟩ := descend_mod n _ z hz hK
  let Ω₂ := AlgebraicClosure K
  obtain ⟨z₂, hz₂, hprod₂⟩ := prod_interp_mod (Ω := Ω₂) n 1 0 (by simp) isIntegral_one isIntegral_zero
    (fun _ : K →ₐ[ℚ] Ω₂ => 1) (fun τ => τ w) (fun _ => isIntegral_one)
    (fun τ => hw.map τ.toRingHom.toIntAlgHom) Finset.univ
  simp only [one_mul, sub_self, add_zero, Finset.prod_const_one] at hprod₂
  have hQ : algebraMap ℚ Ω₂ (Algebra.norm ℚ (1 + n * w)) = 1 + n * z₂ := by
    rw [Algebra.norm_eq_prod_embeddings]
    simp_rw [map_add, map_one, map_mul, map_natCast]
    exact hprod₂
  obtain ⟨w₂, hw₂, hw₂Q⟩ := descend_mod n _ z₂ hz₂ hQ
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hw₂
  have hnorm : ((Algebra.norm ℤ (e * δ + (1 - e) + n * y : 𝓞 E) : ℤ) : ℚ) = 1 + n * m := by
    rw [Algebra.coe_norm_int, ← Algebra.norm_norm (S := K), hwK, hw₂Q, ← hm]
    simp
  have hZ : Algebra.norm ℤ (e * δ + (1 - e) + n * y : 𝓞 E) = 1 + n * m := by
    exact_mod_cast hnorm
  exact ⟨m, by rw [hZ]; ring⟩
end UpperTheory

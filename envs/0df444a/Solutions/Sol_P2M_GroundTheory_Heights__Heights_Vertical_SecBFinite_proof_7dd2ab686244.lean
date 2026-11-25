-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_proof_7dd2ab686244
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:18.651752+00:00
-- url     : https://prove2.me/submissions/33a228d1-ae9b-432c-b3e8-b9d0a37b807f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_linForm_f08d93cacfab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_homogeneousComponent_mul_of_deg_one_f4bb220a562a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_span_of_6218751a8226
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_map_of_c719dbf86e3f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_finite_of_pow_mem_d0bf03a092a4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_homogeneousComponent_mem_integralModel_b60d90841886
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_exists_C_mul_mem_4f0656e53394
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_incIdeal_le_map_cbf637ec4a9e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_parIdx_injective_fcb9d9eec217
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_X_inl_7dae525d82ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_rename_inr_8f0acfaa3c65
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_incIdeal_le_comap_specHom_2c5b1ebdb7b3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
open SecBFinite
namespace GroundTheory.Heights₂.Heights.Vertical
namespace SecBFinite
theorem _root_.solution (hIN : IncidenceNull.Statement) (hCT : ChartTorsion.Statement)
    (hPS : PrimitiveScale.Statement) : SecBFinite.Statement := by
  intro K _ _ n e I f v hI hf
  obtain ⟨c, g, -, hg, m0, hm0⟩ := hPS K v _ f hf.1
  obtain ⟨m, hm⟩ := hIN K n (e + 1) I f hf
  have := hI.isPrime
  have hPprime : (integralModel I).IsPrime := by
    show (I.comap _).IsPrime
    infer_instance
  have hPC : ∀ a : 𝓞 K, C a ∈ integralModel I → a = 0 := by
    intro a ha
    by_contra h0
    have haI : (C (algebraMap (𝓞 K) K a) : MvPolynomial (Fin n) K) ∈ I := by
      simpa [integralModel] using ha
    have hu : IsUnit (C (algebraMap (𝓞 K) K a) : MvPolynomial (Fin n) K) :=
      (isUnit_iff_ne_zero.mpr
        ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr h0)).map C
    exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ haI hu)

  set γ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename (parIdx e n) g) with hγdef
  have hγ : IsUnit γ := by
    rw [hγdef, IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v),
      Ideal.mem_primeCompl_iff]
    intro hmem
    rw [parPrime, MvPolynomial.mem_map_C_iff] at hmem
    have h0 := hmem (m0.mapDomain (parIdx e n))
    rw [coeff_rename_mapDomain _ (parIdx_injective e n)] at h0
    exact hm0 h0
  obtain ⟨w, hw⟩ := hγ

  have hpow : ∀ j, ∃ M, X j ^ (M + 1) ∈ modelR e I v ⊔ Ideal.span (Set.range (secForm (parY e n v))) ⊔
      Ideal.span {chartForm (parY e n v)} := by
    intro j
    have hmapped : MvPolynomial.map (algebraMap (𝓞 K) K) ((rename Sum.inr g * X (Sum.inl j)) ^ m) ∈
        (incIdeal (integralModel I) (e + 1)).map (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
      apply incIdeal_le_map I
      have hmap : MvPolynomial.map (algebraMap (𝓞 K) K) ((rename Sum.inr g * X (Sum.inl j)) ^ m) =
          C c ^ m * (rename Sum.inr f * X (Sum.inl j)) ^ m := by
        rw [map_pow, map_mul, map_rename, hg, map_X, map_mul, rename_C]
        ring
      rw [hmap]
      exact Ideal.mul_mem_left _ _ (hm j)
    obtain ⟨d, hd, hdh⟩ := exists_C_mul_mem _ _ hmapped
    obtain ⟨N, hN⟩ := hCT (𝓞 K) n (e + 1) (integralModel I) hPprime hPC d _ hd hdh j
    have hsp := incIdeal_le_comap_specHom e I v hN
    rw [Ideal.mem_comap, map_mul, map_pow, map_pow, map_mul, specHom_X_inl, specHom_rename_inr,
      ← hγdef, ← hw] at hsp
    refine ⟨N + m, ?_⟩
    set u : ParDVR e n v := ((w : (ParDVR e n v)ˣ) : ParDVR e n v) with hu
    set u' : ParDVR e n v := ((w⁻¹ : (ParDVR e n v)ˣ) : ParDVR e n v) with hu'
    have h1 : (C u' : MvPolynomial (Fin n) (ParDVR e n v)) * C u = 1 := by
      rw [← C_mul, hu, hu', Units.inv_mul, C_1]
    have hX : X j ^ (N + m + 1) = (X j * C u' ^ m) * (X j ^ N * (C u * X j) ^ m) := by
      rw [show (X j * C u' ^ m) * (X j ^ N * (C u * X j) ^ m) =
          X j ^ (N + m + 1) * ((C u' : MvPolynomial (Fin n) (ParDVR e n v)) * C u) ^ m
          by ring, h1, one_pow, mul_one]
    rw [hX]
    exact Ideal.mul_mem_left _ _ hsp

  have hJ0 : (modelR e I v ⊔ Ideal.span (Set.range (secForm (parY e n v)))).IsHomogeneous
      (homogeneousSubmodule (Fin n) (ParDVR e n v)) := by
    refine (isHomogeneous_map_of _ _ (homogeneousComponent_mem_integralModel hI.isHomog)).sup
      (isHomogeneous_span_of ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨1, isHomogeneous_linForm _⟩
  have hq : ∀ j, ∃ M : ℕ, ∃ q : MvPolynomial (Fin n) (ParDVR e n v), q.totalDegree < M ∧
      X j ^ M - q ∈ secIdeal (modelR e I v) (parY e n v) := by
    intro j
    obtain ⟨M, hM⟩ := hpow j
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hM
    obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hb
    refine ⟨M + 1, homogeneousComponent M c', ?_, ?_⟩
    · exact lt_of_le_of_lt (homogeneousComponent_isHomogeneous M c').totalDegree_le (Nat.lt_succ_self M)
    · have hXM : homogeneousComponent (M + 1) (X j ^ (M + 1) : MvPolynomial (Fin n) (ParDVR e n v)) =
          X j ^ (M + 1) := homogeneousComponent_eq_self (isHomogeneous_X_pow _ _)
      have h2 := congrArg (homogeneousComponent (M + 1)) hab
      rw [map_add, homogeneousComponent_mul_of_deg_one _ (chartForm (parY e n v)) (isHomogeneous_linForm _), hXM] at h2
      have ha' : homogeneousComponent (M + 1) a ∈
          modelR e I v ⊔ Ideal.span (Set.range (secForm (parY e n v))) :=
        homogeneousComponent_mem_of_mem hJ0 ha _
      rw [← h2, show homogeneousComponent (M + 1) a + homogeneousComponent M c' * chartForm (parY e n v) -
          homogeneousComponent M c' = homogeneousComponent (M + 1) a +
            homogeneousComponent M c' * (chartForm (parY e n v) - 1) by ring]
      exact Ideal.add_mem _ (Ideal.mem_sup_left ha')
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
  choose M q hqdeg hqmem using hq
  exact finite_of_pow_mem _ M q hqdeg hqmem
end SecBFinite
end GroundTheory.Heights₂.Heights.Vertical

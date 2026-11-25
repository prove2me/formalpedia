-- Prove2me | solution 1 for PI.IsoDetW.Loc.relativeLength_localized_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:34.041977+00:00
-- url     : https://prove2.me/submissions/2b03b137-1ae0-4e8a-a376-79ba26d5952b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Theorems.Thm_PI_IsoDetW_Loc_length_quot_pow
import Theorems.Thm_PI_IsoDetW_Loc_algebraMap_mem_cI
import Theorems.Thm_PI_IsoDetW_Loc_smul_algebraMap
import Theorems.Thm_PI_IsoDetW_Loc_le_locP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
namespace PI.IsoDetW.Loc
theorem _root_.solution (P : HeightOneSpectrum R) (k : ℕ) :
    relative₂ (localization₂ P.asIdeal (cI K (P.asIdeal ^ k))) (localization₂ P.asIdeal (1 : Submodule R K)) = k := by
  haveI := P.isMaximal
  set p := P.asIdeal
  set Z := localization₂ p (1 : Submodule R K)
  set X := localization₂ p (cI K (p ^ k))
  have hZ : ∀ r : R, Algebra.linearMap R K r ∈ Z := fun r =>
    le_locP p _ (Submodule.mem_one.mpr ⟨r, rfl⟩)
  let φ : R →ₗ[R] Z := LinearMap.codRestrict Z (Algebra.linearMap R K) hZ
  let ψ : R →ₗ[R] (Z ⧸ X.comap Z.subtype) := (X.comap Z.subtype).mkQ.comp φ

  have hunit : ∀ t : R, t ∉ p → ∃ t' : R, t * t' - 1 ∈ p ^ k := by
    intro t ht
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (Ideal.Quotient.isUnit_mk_pow_of_notMem p (n := k) ht)
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨t', ?_⟩
    rw [← Ideal.Quotient.eq, map_mul, hb, map_one]
  have hψ : Function.Surjective ψ := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨y, hy⟩ := z
      obtain ⟨t, ht, hty⟩ := hy
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp hty
      obtain ⟨t', ht'⟩ := hunit t ht
      refine ⟨r * t', ?_⟩
      simp only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, φ,
        LinearMap.codRestrict_apply, Algebra.linearMap_apply]
      refine ⟨t, ht, ?_⟩
      rw [smul_sub, ← hr, smul_algebraMap, ← map_sub, algebraMap_mem_cI]
      have : t * (r * t') - r = r * (t * t' - 1) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ ht'
  have hker : LinearMap.ker ψ = p ^ k := by
    ext r
    simp only [LinearMap.mem_ker, ψ, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, φ,
      LinearMap.codRestrict_apply, Algebra.linearMap_apply]
    constructor
    · rintro ⟨s, hs, hsr⟩
      rw [smul_algebraMap, algebraMap_mem_cI] at hsr
      have hu := Ideal.Quotient.isUnit_mk_pow_of_notMem p (n := k) hs
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hsr ⊢
      rw [map_mul] at hsr
      exact (hu.mul_right_eq_zero).mp hsr
    · intro hr
      exact ⟨1, p.primeCompl.one_mem, by rw [one_smul, algebraMap_mem_cI]; exact hr⟩
  have e := (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective ψ hψ)
  unfold relative₂
  rw [← e.length_eq, length_quot_pow]
end PI.IsoDetW.Loc

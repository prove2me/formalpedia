-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_LocalMultComap_proof_04be5379acb4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:47.238801+00:00
-- url     : https://prove2.me/submissions/64380b9f-6a3d-4fba-b25c-6a4f5606b883

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLocalMultComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLocalMultComap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights (localMult)
namespace GroundTheory.Heights₂.Heights.Targets
namespace LocalMultComap
theorem _root_.solution : LocalMultComap.Statement := by
  intro R S _ _ σ I W hσ hW
  set P := W.comap σ with hPdef
  have hPW : P = W.comap σ := rfl
  unfold localMult
  rw [dif_pos hW, dif_pos (Ideal.comap_isPrime σ W)]

  have hM : P.primeCompl.map σ = W.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hσ y
      exact ⟨x, hy, rfl⟩
  have : IsLocalization (P.primeCompl.map σ) (Localization.AtPrime W) := by
    rw [hM]; infer_instance
  let φ : Localization.AtPrime P →+* Localization.AtPrime W := Localization.localRingHom P W σ hPW
  have hφ : Function.Surjective φ := IsLocalization.map_surjective_of_surjective _ _ _ hσ
  let _ : Algebra (Localization.AtPrime P) (Localization.AtPrime W) := φ.toAlgebra
  set J : Ideal (Localization.AtPrime P) := (I.comap σ).map (algebraMap R (Localization.AtPrime P))
  set I' : Ideal (Localization.AtPrime W) := I.map (algebraMap S (Localization.AtPrime W))
  have hcomp : φ.comp (algebraMap R (Localization.AtPrime P)) =
      (algebraMap S (Localization.AtPrime W)).comp σ :=
    RingHom.ext fun x => Localization.localRingHom_to_map P W σ hPW x
  have hJ : J.map φ = I' := by
    simp only [J, I', Ideal.map_map, hcomp]
    rw [← Ideal.map_map, Ideal.map_comap_of_surjective σ hσ]
  have hker : RingHom.ker φ ≤ J := by
    intro x hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    have h0 : φ (IsLocalization.mk' _ r s) = 0 := hx
    simp only [φ, Localization.localRingHom, IsLocalization.map_mk'] at h0
    obtain ⟨⟨t, ht⟩, htr⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp h0
    obtain ⟨t', rfl⟩ := hσ t
    have hmem : t' * r ∈ I.comap σ := by
      simp only [Ideal.mem_comap, map_mul]
      rw [htr]; exact I.zero_mem
    have ht' : t' ∈ P.primeCompl := ht
    rw [IsLocalization.mk'_mem_iff]
    have h1 : algebraMap R (Localization.AtPrime P) (t' * r) ∈ J := Ideal.mem_map_of_mem _ hmem
    rw [map_mul] at h1
    have hu : IsUnit (algebraMap R (Localization.AtPrime P) t') :=
      IsLocalization.map_units _ (⟨t', ht'⟩ : P.primeCompl)
    exact (Submodule.smul_mem_iff_of_isUnit J hu).mp h1

  let ψ : Localization.AtPrime P →ₐ[Localization.AtPrime P] Localization.AtPrime W ⧸ I' :=
    (Ideal.Quotient.mkₐ _ I').comp (Algebra.ofId (Localization.AtPrime P) (Localization.AtPrime W))
  have hψ : Function.Surjective ψ :=
    (Ideal.Quotient.mkₐ_surjective (Localization.AtPrime P) I').comp hφ
  have hkerψ : RingHom.ker ψ = J := by
    have : RingHom.ker ψ = I'.comap φ := by
      ext x
      simp only [ψ, RingHom.mem_ker, Ideal.mem_comap, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Algebra.ofId_apply]
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [this, ← hJ, Ideal.comap_map_of_surjective' φ hφ, sup_eq_left.mpr hker]
  have e := (Submodule.quotEquivOfEq J (RingHom.ker ψ) hkerψ.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hψ).toLinearEquiv
  rw [e.length_eq, Module.length_eq_of_surjective hφ]
end LocalMultComap
end GroundTheory.Heights₂.Heights.Targets

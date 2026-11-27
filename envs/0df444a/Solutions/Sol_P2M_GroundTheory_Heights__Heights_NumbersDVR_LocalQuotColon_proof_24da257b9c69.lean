-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_LocalQuotColon_proof_24da257b9c69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:06:49.321819+00:00
-- url     : https://prove2.me/submissions/c203de01-60fd-4444-af43-3ec52a7b7b57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocalQuotColon

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace LocalQuotColon
theorem _root_.solution : LocalQuotColon.Statement.{u} := by
  intro R _ P U _ f g
  set S := Localization.AtPrime U
  set I := P.map (algebraMap R S)
  have hφ : ∀ x : R, localQuotMap P U x = Ideal.Quotient.mk I (algebraMap R S x) := fun _ => rfl
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul]
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx
    obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hp0 : localQuotMap P U p = 0 := by
      rw [hφ, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hp
    refine Ideal.mem_span_singleton'.mpr ⟨localQuotMap P U a, ?_⟩
    rw [← map_mul, ← map_mul, ← hpz, map_add, hp0, zero_add, map_mul]
  · intro y hy
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hy
    obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl y0
    obtain ⟨⟨r', t'⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl b0
    simp only [hφ] at hb
    have hI := Ideal.Quotient.eq.mp hb
    have e1 := IsLocalization.mk'_spec S r t
    have e2 := IsLocalization.mk'_spec S r' t'
    have hw : algebraMap R S ((t : R) * r' * f - (t' : R) * r * g) ∈ I := by
      have := I.mul_mem_left (algebraMap R S ((t : R) * t')) hI
      convert this using 1
      simp only [map_mul, map_sub]
      linear_combination (algebraMap R S t' * algebraMap R S g) * e1 -
        (algebraMap R S t * algebraMap R S f) * e2
    obtain ⟨⟨p, s⟩, hps⟩ := (IsLocalization.mem_map_algebraMap_iff U.primeCompl S).mp hw
    rw [← map_mul] at hps
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists U.primeCompl S).mp hps
    have hx : (c : R) * s * t' * r ∈ (P ⊔ Ideal.span {f}).colon {g} := by
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      refine Submodule.mem_sup.mpr ⟨-((c : R) * p), P.neg_mem (P.mul_mem_left _ p.2),
        (c : R) * s * t * r' * f, Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩, ?_⟩
      linear_combination hc
    have hy' : Ideal.Quotient.mk I (IsLocalization.mk' S r t) =
        localQuotMap P U ((c : R) * s * t' * r) *
          Ideal.Quotient.mk I (IsLocalization.mk' S (1 : R) (c * s * t' * t)) := by
      rw [hφ, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one]
      congr 1
      rw [IsLocalization.mk'_eq_iff_eq]
      congr 1
      push_cast
      ring
    rw [hy']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)
end LocalQuotColon
end GroundTheory.Heights₂.Heights.NumbersDVR

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_fracMap_unit_ede7a277c87b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:41.396366+00:00
-- url     : https://prove2.me/submissions/f5848d0b-23d8-4ce1-9e82-9dbf3ed705c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_zero_of_forall_mem_minimalPrimes_3d9fe51fc8ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_mem_nonZeroDivisors_of_notMem_minimalPrimes_4676f1a7448f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_separating_c1a2c10f0a84

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.MinimalPrimePlace
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GroundTheory.Heights₂.Heights.MinimalPrimePlace
theorem _root_.solution [IsNoetherianRing A] [IsReduced A] [IsDomain B] (π : A →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π ∈ minimalPrimes A) :
    ∃ e : FractionRing A, fracMap π hker e = 1 ∧ (∀ z, fracMap π hker z = 0 → e * z = 0) ∧
      ∀ y : FractionRing B, ∃ x, fracMap π hker x = y := by
  obtain ⟨s, t, htp, hsp, hq⟩ := exists_separating hker
  have hpP : (RingHom.ker π).IsPrime := hker.1.1
  have hπt : π t = 0 := RingHom.mem_ker.1 htp
  have hπs : π s ≠ 0 := fun h ↦ hsp (RingHom.mem_ker.2 h)
  have hst : ∀ c, c ∉ RingHom.ker π → c * s + t ∈ nonZeroDivisors A := by
    intro c hc
    refine mem_nonZeroDivisors_of_notMem_minimalPrimes fun q hqm hmem ↦ ?_
    by_cases hqp : q = RingHom.ker π
    · rw [hqp] at hmem
      have hcs : c * s ∈ RingHom.ker π := by simpa using (RingHom.ker π).sub_mem hmem htp
      rcases hpP.mem_or_mem hcs with h | h
      · exact hc h
      · exact hsp h
    · obtain ⟨hs, ht⟩ := hq q hqm hqp
      exact ht (by simpa using q.sub_mem hmem (q.mul_mem_left c hs))
  have h1 : (1 : A) ∉ RingHom.ker π := fun h ↦ hpP.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hw : s + t ∈ nonZeroDivisors A := by simpa using hst 1 h1
  have hsa : ∀ a ∈ RingHom.ker π, s * a = 0 := fun a ha ↦ eq_zero_of_forall_mem_minimalPrimes fun q hqm ↦ by
    by_cases hqp : q = RingHom.ker π
    · rw [hqp]; exact Ideal.mul_mem_left _ _ ha
    · exact Ideal.mul_mem_right _ _ (hq q hqm hqp).1
  have hinj := IsFractionRing.injective B (FractionRing B)
  refine ⟨IsLocalization.mk' (FractionRing A) s (⟨s + t, hw⟩ : nonZeroDivisors A), ?_, ?_, ?_⟩
  · have h := congrArg (fracMap π hker)
      (IsLocalization.mk'_spec (FractionRing A) s (⟨s + t, hw⟩ : nonZeroDivisors A))
    rw [map_mul, IsLocalization.map_eq, IsLocalization.map_eq] at h
    simp only [map_add, hπt, add_zero] at h
    have hne : algebraMap B (FractionRing B) (π s) ≠ 0 := fun h0 ↦ hπs (hinj (by rw [h0, map_zero]))
    exact mul_right_cancel₀ hne (h.trans (one_mul _).symm)
  · intro z hz
    obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
    have h := congrArg (fracMap π hker) (IsLocalization.mk'_spec (FractionRing A) a u)
    rw [map_mul, hz, zero_mul, IsLocalization.map_eq] at h
    have ha : a ∈ RingHom.ker π := RingHom.mem_ker.2 (hinj (by rw [← h, map_zero]))
    have hu : IsUnit (algebraMap A (FractionRing A) ((s + t) * u)) :=
      IsLocalization.map_units (FractionRing A) (⟨(s + t) * u, Submonoid.mul_mem _ hw u.2⟩ : nonZeroDivisors A)
    refine (hu.mul_left_eq_zero).1 ?_
    rw [map_mul, mul_mul_mul_comm, IsLocalization.mk'_spec, IsLocalization.mk'_spec, ← map_mul, hsa a ha,
      map_zero]
  · intro y
    obtain ⟨⟨b, v⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) y
    obtain ⟨a, rfl⟩ := hπ b
    obtain ⟨c, hc⟩ := hπ v
    have hcp : c ∉ RingHom.ker π := fun h ↦ nonZeroDivisors.ne_zero v.2 (by rw [← hc]; exact RingHom.mem_ker.1 h)
    refine ⟨IsLocalization.mk' (FractionRing A) (a * s) (⟨c * s + t, hst c hcp⟩ : nonZeroDivisors A), ?_⟩
    rw [IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [map_mul, map_add, hπt, add_zero, hc]
    ring
end GroundTheory.Heights₂.Heights.MinimalPrimePlace

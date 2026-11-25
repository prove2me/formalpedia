-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_ker_delta_8ea97096ed60
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:29.90885+00:00
-- url     : https://prove2.me/submissions/a0e20818-ea4d-47ee-8786-774a496a783c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DegZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CohMkEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_cohMap_mk_a56981702285
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_delta_toCohC_70e565d2f6bb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES
open Module
variable {F : Type} [Field F] {A B C : ℕ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)]
  [∀ n, AddCommGroup (B n)] [∀ n, Module F (B n)] [∀ n, AddCommGroup (C n)] [∀ n, Module F (C n)]
variable {CA : ∀ n, Submodule F (A n)} {CB : ∀ n, Submodule F (B n)} {CC : ∀ n, Submodule F (C n)}
  {dA : ∀ n, A n →ₗ[F] A (n + 1)} {dB : ∀ n, B n →ₗ[F] B (n + 1)} {dC : ∀ n, C n →ₗ[F] C (n + 1)}
  {f : ∀ n, A n →ₗ[F] B n} {g : ∀ n, B n →ₗ[F] C n}
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES.IsSES
variable (H : IsSES CA CB CC dA dB dC f g)
include H
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES.IsSES
theorem _root_.solution (n : ℕ) : LinearMap.ker (H.delta n) = LinearMap.range (H.pB n) := by
  ext q
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  obtain ⟨y, rfl⟩ := H.toCohC_surj n q
  have hyl := mem_liftSp.1 y.2
  constructor
  · intro hq
    rw [delta_toCohC, toCohA_apply, coh_mk_eq_zero] at hq
    obtain ⟨x, hx, hdx⟩ := mem_bnd_succ.1 hq
    have hmem : (y : B n) - f n x ∈ cyc CB dB n := by
      refine mem_cyc.2 ⟨sub_mem hyl.1 (H.f_mem n x hx), ?_⟩
      rw [map_sub, H.f_d n x hx, hdx, H.f_liftB, sub_self]
    refine ⟨Submodule.Quotient.mk ⟨_, hmem⟩, ?_⟩
    rw [pB, cohMap_mk, toCohC_apply]
    congr 1
    apply Subtype.ext
    show g n ((y : B n) - f n x) = g n y
    rw [map_sub, H.g_f n x hx, sub_zero]
  · rintro ⟨q, hq⟩
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hy' := mem_cyc.1 y'.2
    have hyl' : (y' : B n) ∈ liftSp CB dC g n :=
      mem_liftSp.2 ⟨hy'.1, by rw [H.g_d n _ hy'.1, hy'.2, map_zero]⟩
    have he : H.pB n (Submodule.Quotient.mk y') = H.toCohC n ⟨y', hyl'⟩ := rfl
    rw [← hq, he, delta_toCohC, toCohA_apply, coh_mk_eq_zero]
    have h0 : (H.liftB n ⟨y', hyl'⟩ : A (n + 1)) = 0 :=
      H.f_inj (n + 1) _ (H.liftB n ⟨y', hyl'⟩).2 (by rw [H.f_liftB]; exact hy'.2)
    show (H.liftB n ⟨y', hyl'⟩ : A (n + 1)) ∈ _
    rw [h0]
    exact zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES.IsSES

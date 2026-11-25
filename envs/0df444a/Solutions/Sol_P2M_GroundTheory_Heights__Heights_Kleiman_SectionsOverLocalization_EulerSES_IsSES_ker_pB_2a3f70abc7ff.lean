-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_ker_pB_2a3f70abc7ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:07:24.070031+00:00
-- url     : https://prove2.me/submissions/b773adba-e96e-4253-8cdd-1947fd8257ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DegZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CohMkEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_coh_mk_eq_904b9ec6a130
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_cohMap_mk_a56981702285

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
theorem _root_.solution (n : ℕ) : LinearMap.ker (H.pB n) = LinearMap.range (H.iA n) := by
  ext q
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [pB, cohMap_mk, coh_mk_eq_zero] at hq
    have hy := mem_cyc.1 y.2
    obtain ⟨x, hx, hb⟩ := H.lift_bnd n y hy.1 hq
    have hdx : dA n x = 0 := by
      refine H.f_inj (n + 1) _ (H.dA_mem n x hx) ?_
      have h1 := d_of_mem_bnd H.dB_dB hb
      rw [map_sub, hy.2, zero_sub, neg_eq_zero, H.f_d n x hx] at h1
      exact h1
    refine ⟨Submodule.Quotient.mk ⟨x, mem_cyc.2 ⟨hx, hdx⟩⟩, ?_⟩
    rw [iA, cohMap_mk, coh_mk_eq]
    rw [← neg_sub]
    exact neg_mem hb
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [iA, pB, cohMap_mk, cohMap_mk, coh_mk_eq_zero]
    show g n (f n x) ∈ _
    rw [H.g_f n x (mem_cyc.1 x.2).1]
    exact zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES.IsSES

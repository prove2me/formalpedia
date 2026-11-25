-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_ker_iA_succ_e16bc66519a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:30.678575+00:00
-- url     : https://prove2.me/submissions/2af6535b-b437-4567-a9d0-a56fa7f414c1

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
theorem _root_.solution (n : ℕ) : LinearMap.ker (H.iA (n + 1)) = LinearMap.range (H.delta n) := by
  ext q
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [iA, cohMap_mk, coh_mk_eq_zero] at hq
    obtain ⟨y, hy, hfy⟩ := mem_bnd_succ.1 hq
    have hx := mem_cyc.1 x.2
    have hyl : y ∈ liftSp CB dC g n := by
      refine mem_liftSp.2 ⟨hy, ?_⟩
      rw [H.g_d n y hy, hfy]
      exact H.g_f (n + 1) x hx.1
    have hlx : (H.liftB n ⟨y, hyl⟩ : A (n + 1)) = x :=
      congrArg Subtype.val (H.fInj (n + 1) (a₁ := H.liftB n ⟨y, hyl⟩) (a₂ := ⟨x, hx.1⟩)
        (by show f (n + 1) (H.liftB n ⟨y, hyl⟩ : A (n + 1)) = f (n + 1) x; rw [H.f_liftB]; exact hfy))
    refine ⟨H.toCohC n ⟨y, hyl⟩, ?_⟩
    rw [delta_toCohC, toCohA_apply]
    congr 1
    exact Subtype.ext hlx
  · rintro ⟨q, rfl⟩
    obtain ⟨y, rfl⟩ := H.toCohC_surj n q
    rw [delta_toCohC, toCohA_apply, iA, cohMap_mk, coh_mk_eq_zero]
    show f (n + 1) (H.liftB n y : A (n + 1)) ∈ _
    rw [H.f_liftB]
    exact mem_bnd_succ.2 ⟨y, (mem_liftSp.1 y.2).1, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES.IsSES

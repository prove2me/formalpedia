-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSupSmall_proof_81abc59a4dca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:32.913178+00:00
-- url     : https://prove2.me/submissions/abbe86ec-3c63-4270-9d30-69bcfb625ad3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSupSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSupSmall_eval_map_int_3fe0911283fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSupSmall_evalCone_unflatCone_cbfa18dac529
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSupSmall_scale_e8aa871c45ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSupSmall_subst_homog_4755280d7a4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_oldFlat_mem_mcPts_981d85412699


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open YPlusSupSmall
namespace GroundTheory.Heights₂.Heights
namespace YPlusSupSmall
theorem _root_.solution (hForms : ChartFormsAlt.Statement) (hPts : ConePoints.Statement) :
    YPlusSupSmall.Statement := by
  intro ι _ _ n P D Ω _ y x' N Ap τ s hR hNa hInd _ hsmall f hf hfs z hz
  classical
  obtain ⟨d, hd⟩ := hForms ι n P D
  obtain ⟨g, hg⟩ := hd d le_rfl
  have hζ : D.oldFlat z ∈ Geo.mcPts (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) :=
    D.oldFlat_mem_mcPts y x' z hz

  have hw : unflatCone z ∈ D.extPoints := by
    refine ⟨(blockNonzero_unflatCone_iff z).mpr hz.1, fun p hp ↦ ?_⟩
    rw [evalCone_unflatCone, ← eval_map_int]
    exact hz.2 p (hR.ext_eq ▸ hp)
  obtain ⟨-, la, hla, hrel⟩ := (hPts ι n P D d g hg).2 _ hw

  obtain ⟨c, hc⟩ : ∃ c : (k : ι) → Fin (n k + 1), ∀ k, z ⟨some k, c k⟩ ≠ 0 :=
    ⟨fun k ↦ (hz.1 (some k)).choose, fun k ↦ (hz.1 (some k)).choose_spec⟩
  have hmz : aeval (D.oldFlat z) (chartMonomial (n := n) c d) ≠ 0 := by
    simp only [chartMonomial, map_prod, map_pow, aeval_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  have hlive : P.IsLive c := by
    intro k hk
    have h := hζ.2 _ (by rw [← hR.ideal_eq]; exact hk)
    rw [eval_map_int, aeval_X] at h
    exact hc k h

  obtain ⟨e, he⟩ : ∃ e : ι → ℕ, ∀ k, (e k : ℤ) = d k + D.deg k :=
    ⟨fun k ↦ ((d k : ℤ) + D.deg k).toNat, fun k ↦ Int.toNat_of_nonneg (hg.nonneg k)⟩
  have hgh : ∀ j, IsWeightedHomogeneous (coordDeg n) (g c j) e := by
    intro j
    obtain ⟨δ, hδ, hδe⟩ := hg.homog c j
    have : δ = e := funext fun k ↦ by have h1 := hδe k; have h2 := he k; omega
    rwa [← this]
  have hmh : IsWeightedHomogeneous (coordDeg n) (chartMonomial (n := n) c d) d :=
    isWeightedHomogeneous_chartMonomial c d

  have hval : ∀ j, aeval y (g c j) = x' j * aeval y (chartMonomial c d) := fun j ↦
    (hR.reads j (g c j) (chartMonomial c d) e d (hgh j) hmh fun k ↦ he k).mpr
      (by rw [hg.value c hlive j, mul_comm])

  have hrelj : ∀ j : Fin (D.size + 1), aeval (D.oldFlat z) (chartMonomial c d) * z ⟨none, j⟩ =
      la * aeval (D.oldFlat z) (g c j) := by
    intro j
    have hold : D.basePart₂ (unflatCone z) = unflatCone (D.oldFlat z) := rfl
    have h := hrel c (by rw [hold, evalCone_unflatCone]; exact hmz) j
    rw [hold, evalCone_unflatCone, evalCone_unflatCone] at h
    change z ⟨none, j⟩ = _ at h
    rw [h]
    field_simp

  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin (D.size + 1), z ⟨none, j⟩ ≠ 0 := hz.1 none
  have hAp : Ap.h z = ‖la‖ * N.h (D.oldFlat z) := by
    have h := hInd j₀ (g c j₀) (chartMonomial c d) e d ((geoMultiHomog_iff _ _).mpr (hgh j₀))
      ((geoMultiHomog_iff _ _).mpr hmh) (fun k ↦ by rw [hNa]; exact he k)
      (by rw [hval, mul_comm]) z hz
    rw [eval_map_int, eval_map_int] at h
    have hgz : aeval (D.oldFlat z) (g c j₀) ≠ 0 := by
      intro h0
      have h1 := hrelj j₀
      rw [h0, mul_zero] at h1
      exact mul_ne_zero hmz hj₀ h1
    have h2 := congrArg norm (hrelj j₀)
    rw [norm_mul, norm_mul] at h2
    apply mul_left_cancel₀ (norm_ne_zero_iff.mpr hgz)
    linear_combination -h + N.h (D.oldFlat z) * h2

  set G := newSubst D (g c) with hG
  have hcomp : ∀ {R : Type} [CommRing R] (w : Coord n → R) (p : MvPolynomial (Coord D.extSizes) ℤ),
      aeval w (aeval G p) = aeval (fun v ↦ aeval w (G v)) p := fun w p ↦ by
    rw [← AlgHom.comp_apply, comp_aeval]
  have hFh : IsWeightedHomogeneous (coordDeg n) (aeval G f) (τ • e) :=
    subst_homog D hf G e (by rintro ⟨_ | k, i⟩; exacts [hgh i, isWeightedHomogeneous_zero _ _ _])
  have hFy : aeval y (aeval G f) = s * aeval y (chartMonomial c d ^ τ) := by
    have h := scale D hf (fun v ↦ aeval y (G v)) (D.plusCoord y x') 1 (aeval y (chartMonomial c d))
      (fun j ↦ by
        change 1 * aeval y (g c j) = aeval y (chartMonomial c d) * x' j
        rw [one_mul, hval, mul_comm])
    rw [one_pow, one_mul, hfs] at h
    rw [hcomp, h, map_pow, mul_comm]
  have hb := hsmall (τ • e) (τ • d) (aeval G f) (chartMonomial c d ^ τ) (D.oldFlat z)
    ((geoMultiHomog_iff _ _).mpr hFh) ((geoMultiHomog_iff _ _).mpr (hmh.pow τ))
    (fun k ↦ by simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, he k, hNa]; ring) hFy hζ
  rw [eval_map_int, eval_map_int, map_pow, norm_pow] at hb

  have hsc := scale D hf z (fun v ↦ aeval (D.oldFlat z) (G v)) (aeval (D.oldFlat z) (chartMonomial c d)) la
    (fun j ↦ hrelj j)
  rw [← hcomp] at hsc
  suffices hfin : ‖aeval z f‖ ≤ Ap.h z ^ τ from (congrArg norm (eval_map_int z f)).trans_le hfin
  have hpos : 0 < ‖aeval (D.oldFlat z) (chartMonomial c d)‖ ^ τ := pow_pos (norm_pos_iff.mpr hmz) τ
  refine le_of_mul_le_mul_left ?_ hpos
  calc ‖aeval (D.oldFlat z) (chartMonomial c d)‖ ^ τ * ‖aeval z f‖
      = ‖la‖ ^ τ * ‖aeval (D.oldFlat z) (aeval G f)‖ := by
        rw [← norm_pow, ← norm_pow, ← norm_mul, ← norm_mul, hsc]
    _ ≤ ‖la‖ ^ τ * (‖aeval (D.oldFlat z) (chartMonomial c d)‖ ^ τ * N.h (D.oldFlat z) ^ τ) := by
        gcongr
    _ = ‖aeval (D.oldFlat z) (chartMonomial c d)‖ ^ τ * Ap.h z ^ τ := by
        rw [hAp, mul_pow]; ring
end YPlusSupSmall
end GroundTheory.Heights₂.Heights

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_xiH_identity_cd3d2b67d6ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:29.312915+00:00
-- url     : https://prove2.me/submissions/20edabd1-27c8-47a4-945a-f2eeb761d8ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_tensQ_pluck_84a22b3e2f66
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_evC_congr_bdcd31b11aa6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_evC_rename_eval_1872a0066848
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_lineV_yyEmb0_64dba564c4d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_lineV_yyEmb1_dd4f08188389
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_good_yyEmb_1a6c398b5953

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open scoped ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
variable {D : ℕ} (S : ProjectiveLineBundle D) {N : ℕ} {F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx} {q : ℕ}
  {r : Fin q → MRing S.YIdx} {b : Fin q → T.YBlk → ℕ}
namespace GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
theorem _root_.solution (hF : S.IsPluckerRel N F) (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0)
    (hrW : ∀ j, rename (T.yyEmb 0) (r j) ∈ S.WW) {z : (Σ k, S.WIdx k) → ℂ} (hz : z ∈ mcPts S.WW) :
    ‖eval z (map (Int.castRingHom ℂ) S.g)‖ ^ 2 * xiH S.G N F r b (fun p => z (T.yyEmb 0 p)) *
        xiH S.G N F r b (fun p => z (T.yyEmb 1 p)) =
      ‖eval z (map (Int.castRingHom ℂ) S.h)‖ ^ 2 *
        sinSqG (S.G fun p => z (T.yyEmb 0 p)) (fun k => z ⟨.line0, k⟩) (fun k => z ⟨.line1, k⟩) := by
  set w0 : (Σ k, S.YIdx k) → ℂ := fun p => z (T.yyEmb 0 p) with hw0def
  set w1 : (Σ k, S.YIdx k) → ℂ := fun p => z (T.yyEmb 1 p) with hw1def
  set gz := eval z (map (Int.castRingHom ℂ) S.g)
  set hz' := eval z (map (Int.castRingHom ℂ) S.h)
  set v0 : S.κ → ℂ := fun k => z ⟨.line0, k⟩
  set v1 : S.κ → ℂ := fun k => z ⟨.line1, k⟩
  have hw0 := good_yyEmb S hz.1 0
  have hw1 := good_yyEmb S hz.1 1
  have hG01 : S.G w1 = S.G w0 := S.metric.2.1 w1 w0 (fun i => rfl) (fun l => rfl)
  have hFe : ∀ i l k m, evC (F i l k m) w1 = evC (F i l k m) w0 := fun i l k m =>
    evC_congr (hF.1 i l k m) fun p hp => by
      rcases p with ⟨_ | _ | _, i⟩
      · rfl
      · simp at hp
      · simp at hp
  have hre : ∀ j, evC (r j) w1 = evC (r j) w0 := fun j =>
    evC_congr (hr j) fun p hp => by
      rcases p with ⟨_ | _ | _, i⟩
      · rfl
      · rfl
      · exact absurd (hrl j) hp
  have hratio : ratio S.G N F r b w1 = ratio S.G N F r b w0 := by
    simp only [ratio, numF, remR, hG01, hFe, hre]
    rfl
  have hr0 : ∀ j, evC (r j) w0 = 0 := fun j => by
    have h0 := hz.2 _ (hrW j)
    rwa [evC_rename_eval] at h0
  have hrem0 : remR N r b w0 = 0 := by
    simp [remR, hr0]
  have hrelz : ∀ i l k m, gz * evC (F i l k m) w0 =
      (hz' * z ⟨.det, l⟩ * z ⟨.base, i⟩ ^ N) * (v0 k * v1 m - v0 m * v1 k) := fun i l k m => by
    have h0 := hz.2 _ (hF.2 i l k m)
    simp only [map_sub, map_mul, map_pow, map_X, eval_X, ProjectiveLineBundle.pluckerWW,
      evC_rename_eval] at h0
    rw [← hw0def] at h0
    linear_combination h0
  have hherm : (S.G w0).IsHermitian := (S.metric.1 w0).isHermitian
  have hv0 : lineV w0 = v0 := lineV_yyEmb0 S z
  have hv1 : lineV w1 = v1 := lineV_yyEmb1 S z
  set H0 := (hermG (S.G w0) v0 v0).re
  set H1 := (hermG (S.G w0) v1 v1).re
  set C := hermG (S.G w0) v0 v1
  have hterm : ∀ i l, ‖gz‖ ^ 2 * tensQ (S.G w0) (fun p => evC (F i l p.1 p.2) w0) =
      (2 * ‖hz'‖ ^ 2 * (H0 * H1 - ‖C‖ ^ 2)) * ((‖z ⟨.base, i⟩‖ ^ 2) ^ N * ‖z ⟨.det, l⟩‖ ^ 2) := fun i l => by
    rw [← tensQ_smul]
    have e : gz • (fun p : S.κ × S.κ => evC (F i l p.1 p.2) w0) =
        (hz' * z ⟨.det, l⟩ * z ⟨.base, i⟩ ^ N) • fun p : S.κ × S.κ => v0 p.1 * v1 p.2 - v0 p.2 * v1 p.1 := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
      exact hrelz i l p.1 p.2
    rw [e, tensQ_smul, tensQ_pluck hherm, norm_mul, norm_mul, norm_pow]
    ring
  have hnum : ‖gz‖ ^ 2 * numF S.G F w0 = 2 * ‖hz'‖ ^ 2 * (H0 * H1 - ‖C‖ ^ 2) * (ypow N w0 * dnorm w0) := by
    rw [numF, ypow, dnorm, Finset.sum_mul_sum]
    simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => hterm i l
  have hH0 : 0 < H0 := by
    have := hv_pos (w := w0) hw0 S.metric.1
    rwa [hv, hv0] at this
  have hH1 : 0 < H1 := by
    have := hv_pos (w := w1) hw1 S.metric.1
    rwa [hv, hv1, hG01] at this
  have hY : 0 < ypow N w0 := ypow_pos (w := w0) hw0 N
  have hD : 0 < dnorm w0 := dnorm_pos (w := w0) hw0
  have hrat0 : 0 ≤ ratio S.G N F r b w0 :=
    div_nonneg (add_nonneg (numF_nonneg S.metric.1 F w0) (remR_nonneg N r b w0)) (by positivity)
  have hxi1 : xiH S.G N F r b w1 = Real.sqrt (ratio S.G N F r b w0) / H1 := by
    rw [xiH, hratio, hv, hv1, hG01]
  have hxi0 : xiH S.G N F r b w0 = Real.sqrt (ratio S.G N F r b w0) / H0 := by
    rw [xiH, hv, hv0]
  rw [hxi0, hxi1, sinSqG]
  change _ = ‖hz'‖ ^ 2 * (1 - ‖C‖ ^ 2 / (H0 * H1))
  have hs : Real.sqrt (ratio S.G N F r b w0) / H0 * (Real.sqrt (ratio S.G N F r b w0) / H1) =
      ratio S.G N F r b w0 / (H0 * H1) := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hrat0]
  rw [mul_assoc, hs, ratio, hrem0, add_zero]
  calc _ = 2 * ‖hz'‖ ^ 2 * (H0 * H1 - ‖C‖ ^ 2) * (ypow N w0 * dnorm w0) / (2 * (ypow N w0 * dnorm w0)) /
        (H0 * H1) := by rw [← hnum]; ring
    _ = _ := by
      field_simp
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness

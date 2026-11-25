-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_local_rel_12f56c435678
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:10:23.004153+00:00
-- url     : https://prove2.me/submissions/15c0ab02-99a7-4ff0-88f1-0277d966c61e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_frame_gen_572f531e0883
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_frame_bound_bbfbf4b931ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_chart_rel_f6b2a434feeb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_yyc_base_29c3d2390e14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_Xpow_33fd54a9e382
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_Xpow_homog_6fdb90b2f59f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_single_smul_base_59626f6b3961
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homog_sub_e0c49124b765
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homogenize_fam_b09891dd724c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_F_value_59f019138684
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_good_of_e28dc548cf6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_iff_weighted_ebc17bcac6a7


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {D : ℕ} (S : ProjectiveLineBundle D)
namespace GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
theorem _root_.solution (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx) (hF : S.IsPluckerRel N F) (i : S.ι) :
    ∃ s : Finset (MRing S.YIdx), (∀ r ∈ s, Good S r) ∧
      ∀ w : (Σ k, S.YIdx k) → ℂ, (∀ r ∈ s, eval w (map (Int.castRingHom ℂ) r) = 0) →
        (∀ l k m, eval w (map (Int.castRingHom ℂ) (F i l k m)) = 0) → w ⟨.base, i⟩ = 0 := by
  classical
  by_cases hx : S.x i = 0
  · refine ⟨{X ⟨.base, i⟩}, ?_, ?_⟩
    · intro r hr
      rw [Finset.mem_singleton] at hr
      subst hr
      exact good_of S (d := 1) (isWeightedHomogeneous_X ℤ _ _) (by rw [aeval_X, yyc_base, hx, map_zero])
    · intro w hw _
      simpa using hw _ (Finset.mem_singleton_self _)
  obtain ⟨K, f, c, hf, hc, hs, hloc⟩ := S.B.frame i hx
  choose bb hli hsp hloc' using hloc
  have hrel : ∀ l, ∃ n : ℕ, f l ^ n ∈ Submodule.span (chartRing ℤ S.x i) (Set.range fun t : S.κ × S.κ × S.ν =>
      (S.x i)⁻¹ ^ 3 * (S.φ t.1 (S.e 0) * S.φ t.2.1 (S.e 1) - S.φ t.1 (S.e 1) * S.φ t.2.1 (S.e 0)) * S.δ t.2.2) := by
    intro l
    obtain ⟨M, hM⟩ := frame_bound S.x i S.B f c hf hc hs bb hli hsp hloc' l
    exact chart_rel S.x i S.B S.e S.φ S.δ (S.dualGen i hx) (S.detGen i hx).2 (hf l) (bb l) (hli l) (hsp l)
      (frame_gen S.x i S.B (bb l) (hloc' l)) M hM
  choose n hn using hrel
  have hcoef : ∀ l, ∃ C : S.κ × S.κ × S.ν → S.Ω, (∀ t, C t ∈ chartRing ℤ S.x i) ∧
      f l ^ n l = ∑ t, C t * ((S.x i)⁻¹ ^ 3 *
        (S.φ t.1 (S.e 0) * S.φ t.2.1 (S.e 1) - S.φ t.1 (S.e 1) * S.φ t.2.1 (S.e 0)) * S.δ t.2.2) := by
    intro l
    obtain ⟨C, hC⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hn l)
    refine ⟨fun t => C t, fun t => (C t).2, ?_⟩
    rw [← hC]
    simp only [Subalgebra.smul_def, smul_eq_mul]
  choose C hC hCeq using hcoef
  obtain ⟨Df, Pf, hPf⟩ := homogenize_fam S i hx f hf
  obtain ⟨Dc, Pc, hPc⟩ := homogenize_fam S i hx c hc
  choose E Q hQ using fun l => homogenize_fam S i hx (C l) (hC l)
  have hFh : ∀ l k m, IsWeightedHomogeneous (wt S) (F i l k m) (Pi.single .base (N + 3)) :=
    fun l k m => (isMultiHomog_iff_weighted _ _).1 (hF.1 i l k m)
  let r0 : MRing S.YIdx := X ⟨.base, i⟩ ^ (Dc + Df) - ∑ l, Pc l * Pf l
  let rl : Fin K → MRing S.YIdx := fun l => X ⟨.base, i⟩ ^ (E l + N + 3) * Pf l ^ n l -
    ∑ t, X ⟨.base, i⟩ ^ (n l * Df) * Q l t * F i t.2.2 t.1 t.2.1
  have hr0 : Good S r0 := by
    refine good_of S (d := Dc + Df) ?_ ?_
    · refine homog_sub S (Xpow_homog S i _) (IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_)
      rw [Pi.single_add]
      exact (hPc l).1.mul (hPf l).1
    · have hΩ : S.x i ^ (Dc + Df) - ∑ l, (c l * S.x i ^ Dc) * (f l * S.x i ^ Df) = 0 := by
        have : ∑ l, (c l * S.x i ^ Dc) * (f l * S.x i ^ Df) = (∑ l, c l * f l) * S.x i ^ (Dc + Df) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, hs]
        ring
      have := congrArg (algebraMap S.Ω S.Φ) hΩ
      simp only [r0, map_sub, map_sum, map_mul, aeval_Xpow, (hPc _).2, (hPf _).2, map_zero] at this ⊢
      simpa [map_pow] using this
  have hrl : ∀ l, Good S (rl l) := by
    intro l
    refine good_of S (d := E l + N + 3 + n l * Df) ?_ ?_
    · refine homog_sub S ?_ (IsWeightedHomogeneous.sum _ _ _ fun t _ => ?_)
      · have := (Xpow_homog S i (E l + N + 3)).mul ((hPf l).1.pow (n l))
        rwa [single_smul_base, ← Pi.single_add] at this
      · have hdeg : Pi.single .base (n l * Df) + Pi.single .base (E l) + Pi.single .base (N + 3) =
            (Pi.single .base (E l + N + 3 + n l * Df) : T.YBlk → ℕ) := by
          rw [← Pi.single_add, ← Pi.single_add]
          congr 1
          ring
        rw [← hdeg]
        exact ((Xpow_homog S i _).mul (hQ l t).1).mul (hFh _ _ _)
    · have hΩ : S.x i ^ (E l + N + 3) * (f l * S.x i ^ Df) ^ n l - ∑ t, S.x i ^ (n l * Df) * (C l t * S.x i ^ E l) *
          ((S.φ t.1 (S.e 0) * S.φ t.2.1 (S.e 1) - S.φ t.1 (S.e 1) * S.φ t.2.1 (S.e 0)) * S.δ t.2.2 * S.x i ^ N) = 0 := by
        rw [mul_pow, hCeq l, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_eq_zero fun t _ => ?_
        field_simp
        ring
      have := congrArg (algebraMap S.Ω S.Φ) hΩ
      have ePf : ∀ l, aeval (yyc S) (Pf l) = algebraMap S.Ω S.Φ (f l * S.x i ^ Df) := fun l => (hPf l).2
      have eQ : ∀ t, aeval (yyc S) (Q l t) = algebraMap S.Ω S.Φ (C l t * S.x i ^ E l) := fun t => (hQ l t).2
      simp only [rl, map_sub, map_sum, map_mul, map_pow, aeval_X, yyc_base, ePf, eQ, F_value S N F hF, map_zero]
        at this ⊢
      simpa [map_pow] using this
  refine ⟨insert r0 (Finset.univ.image rl), ?_, ?_⟩
  · intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · exact hr0
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hr
      exact hrl l
  · intro w hw hFw
    by_contra hwi
    have hPl : ∀ l, eval w (map (Int.castRingHom ℂ) (Pf l)) = 0 := by
      intro l
      have h := hw (rl l) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ l)))
      simp only [rl, map_sub, map_mul, map_pow, map_sum, map_X, eval_X, hFw, mul_zero, Finset.sum_const_zero,
        sub_zero] at h
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hwi))
    have h := hw r0 (Finset.mem_insert_self _ _)
    simp only [r0, map_sub, map_mul, map_pow, map_sum, map_X, eval_X, hPl, mul_zero, Finset.sum_const_zero,
      sub_zero] at h
    exact hwi (eq_zero_of_pow_eq_zero h)
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover

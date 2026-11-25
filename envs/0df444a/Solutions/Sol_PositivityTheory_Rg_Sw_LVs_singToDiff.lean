-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.singToDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:54.119253+00:00
-- url     : https://prove2.me/submissions/e1c4959e-c694-4a64-8017-b40690459c83

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiff
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_fourier_test
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_contDiffOn_dList
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_dList_ofFn
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_hermL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_herm_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_ibp_dList
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_integrable_mul_of_contOn
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_isT_dList
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_tsupport_dList_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open STD
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : SingToDiff := by
  intro n G r hr hG hyp
  classical
  set U : Set (Vr n) := (hermL n) ⁻¹' Metric.ball 0 r with hUdef
  have hU : IsOpen U := Metric.isOpen_ball.preimage (hermL n).continuous
  have h0U : (0 : Vr n) ∈ U := by simp [U, hermL_apply, herm_zero, hr]
  set F : Vr n → ℂ := fun y => G (herm y) with hFdef
  have hF : ContDiffOn ℝ ∞ F U :=
    (hG.restrict_scalars ℝ).comp (hermL n).contDiff.contDiffOn (fun y hy => hy)
  let H : Vr n → ℂ := fun x => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * dList (List.ofFn (ml σ)) F x
  have hHU : ContinuousOn H U := by
    refine continuousOn_finsetSum _ fun σ _ => continuousOn_const.mul ?_
    exact (contDiffOn_dList hU hF _).continuousOn
  have hH0 : H 0 = detD G := by
    simp only [H, detD]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [dList_ofFn hG _ (ml σ) 0 (by simpa [herm_zero] using hr), herm_zero]
    rfl
  obtain ⟨ε0, hε0, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have key : ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : ContDiffBump (0 : Vr n), b.rOut = ε →
      ∫ x, H x * ((b.normed volume x : ℝ) : ℂ) = 0 := by
    intro ε hε hεε b hb
    set φ : Vr n → ℂ := fun x => ((b.normed volume x : ℝ) : ℂ) with hφdef
    have hφsup : tsupport φ ⊆ Metric.closedBall 0 ε := by
      refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
      have h1 : b.normed volume x ≠ 0 := fun h0 => hx (by simp [φ, h0])
      have hx' : x ∈ Function.support (b.normed volume) := h1
      rw [b.support_normed_eq, hb] at hx'
      exact Metric.ball_subset_closedBall hx'
    have hφ : IsT U φ := by
      refine ⟨Complex.ofRealCLM.contDiff.comp b.contDiff_normed, ?_, ?_⟩
      · exact b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
      · exact hφsup.trans ((Metric.closedBall_subset_ball hεε).trans hball)
    have hφu : IsT Set.univ φ := ⟨hφ.smooth, hφ.cpt, Set.subset_univ _⟩
    set ψ : Vr n → ℂ := fun x =>
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * dList (List.ofFn (ml σ)).reverse φ x with hψdef
    have hψT : ∀ σ : Equiv.Perm (Fin n), IsT U (dList (List.ofFn (ml σ)).reverse φ) := fun σ => isT_dList hφ _
    have hψ0 : ∀ x, x ∉ tsupport φ → ψ x = 0 := by
      intro x hx
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_dList_subset φ _ h)), mul_zero]
    have hSing : IsSingTest ψ := by
      refine ⟨continuous_finsetSum _ fun σ _ => continuous_const.mul (hψT σ).smooth.continuous,
        HasCompactSupport.intro hφ.cpt hψ0, ?_⟩
      intro β _ hdet
      exact fourier_test β hdet hφu
    have h1 := hyp ψ hSing
    have hint : ∀ σ : Equiv.Perm (Fin n), Integrable (fun x => F x * dList (List.ofFn (ml σ)).reverse φ x) :=
      fun σ => integrable_mul_of_contOn hU hF.continuousOn (hψT σ).smooth.continuous (hψT σ).cpt (hψT σ).sub
    have h2 : ∫ x, G (herm x) * ψ x = (-1) ^ Fintype.card (Fin n) * ∫ x, H x * φ x := by
      have e1 : (fun x => G (herm x) * ψ x) = fun x => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
          (F x * dList (List.ofFn (ml σ)).reverse φ x) := by
        funext x; simp only [ψ, F, Finset.mul_sum]; refine Finset.sum_congr rfl fun σ _ => ?_; ring
      have hintH : ∀ σ : Equiv.Perm (Fin n), Integrable (fun x => dList (List.ofFn (ml σ)) F x * φ x) :=
        fun σ => integrable_mul_of_contOn hU (contDiffOn_dList hU hF _).continuousOn hφ.smooth.continuous
          hφ.cpt hφ.sub
      have e2 : (fun x => H x * φ x) = fun x => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
          (dList (List.ofFn (ml σ)) F x * φ x) := by
        funext x; simp only [H, Finset.sum_mul]; refine Finset.sum_congr rfl fun σ _ => ?_; ring
      rw [e1, e2, integral_finsetSum _ (fun σ _ => (hint σ).const_mul _),
        integral_finsetSum _ (fun σ _ => (hintH σ).const_mul _), Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [integral_const_mul, integral_const_mul, ibp_dList hU _ hF hφ, List.reverse_reverse, List.length_reverse,
        List.length_ofFn]
      ring
    rw [h2] at h1
    have hne : ((-1 : ℂ)) ^ Fintype.card (Fin n) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.1 h1).resolve_left hne

  rw [← hH0]
  by_contra hne
  have hδ : 0 < ‖H 0‖ / 2 := by positivity
  obtain ⟨ε1, hε1, hcont⟩ := Metric.continuousAt_iff.1 (hHU.continuousAt (hU.mem_nhds h0U)) _ hδ
  set ε := min (ε0 / 2) (ε1 / 2) with hεdef
  have hε : 0 < ε := lt_min (half_pos hε0) (half_pos hε1)
  have hεε0 : ε < ε0 := (min_le_left _ _).trans_lt (half_lt_self hε0)
  have hεε1 : ε < ε1 := (min_le_right _ _).trans_lt (half_lt_self hε1)
  let b : ContDiffBump (0 : Vr n) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have hk := key ε hε hεε0 b rfl
  set φr : Vr n → ℝ := b.normed volume
  have hφr1 : ∫ x, φr x = 1 := b.integral_normed
  have hφint : Integrable φr := b.integrable_normed
  have hcpt : HasCompactSupport (fun x => ((φr x : ℝ) : ℂ)) := b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  have hφc : Continuous (fun x => ((φr x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp b.continuous_normed
  have hsub : tsupport (fun x => ((φr x : ℝ) : ℂ)) ⊆ U := by
    refine (closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall).trans
      ((Metric.closedBall_subset_ball hεε0).trans hball)
    have h1 : φr x ≠ 0 := fun h0 => hx (by simp [h0])
    have hx' : x ∈ Function.support φr := h1
    rw [b.support_normed_eq] at hx'
    exact Metric.ball_subset_closedBall hx'
  have hi1 : Integrable (fun x => H x * ((φr x : ℝ) : ℂ)) := integrable_mul_of_contOn hU hHU hφc hcpt hsub
  have hi2 : Integrable (fun x => (H 0 - H x) * ((φr x : ℝ) : ℂ)) :=
    integrable_mul_of_contOn hU (continuousOn_const.sub hHU) hφc hcpt hsub
  have hrep : H 0 = ∫ x, (H 0 - H x) * ((φr x : ℝ) : ℂ) := by
    have : ∫ x, (H 0 - H x) * ((φr x : ℝ) : ℂ) = H 0 * (∫ x, ((φr x : ℝ) : ℂ)) - ∫ x, H x * ((φr x : ℝ) : ℂ) := by
      have hA : Integrable (fun x => H 0 * ((φr x : ℝ) : ℂ)) :=
        integrable_mul_of_contOn hU continuousOn_const hφc hcpt hsub
      have e : (fun x => (H 0 - H x) * ((φr x : ℝ) : ℂ)) =
          fun x => H 0 * ((φr x : ℝ) : ℂ) - H x * ((φr x : ℝ) : ℂ) := by
        funext x; ring
      rw [e, integral_sub hA hi1, integral_const_mul]
    rw [this, hk, integral_complex_ofReal, hφr1]; simp
  have hbound : ‖∫ x, (H 0 - H x) * ((φr x : ℝ) : ℂ)‖ ≤ ∫ x, ‖H 0‖ / 2 * φr x := by
    refine norm_integral_le_of_norm_le (hφint.const_mul _) (Eventually.of_forall fun x => ?_)
    by_cases hx : φr x = 0
    · simp [hx]
    · have hx' : x ∈ Function.support φr := hx
      rw [b.support_normed_eq] at hx'
      have hd : dist x 0 < ε1 := (Metric.mem_ball.1 hx').trans hεε1
      have := hcont hd
      rw [dist_eq_norm, norm_sub_rev] at this
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (b.nonneg_normed x)]
      exact mul_le_mul_of_nonneg_right this.le (b.nonneg_normed x)
  rw [integral_const_mul, hφr1, mul_one, ← hrep] at hbound
  have : ‖H 0‖ ≤ 0 := by linarith
  exact hne (norm_le_zero_iff.1 this)
end PositivityTheory.Rg.Sw.LVs

-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.strong_of_weak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:35.411941+00:00
-- url     : https://prove2.me/submissions/7af7ce80-2b1e-462f-9497-dd7de83532e9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_SliceAn
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_cont_seminorm
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SchwartzBaire_iteratedFDeriv_sub_apply__4bfc50ada7a9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap NNReal
variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution [FiniteDimensional ℝ V] {K : Type} [TopologicalSpace K] (g : K → 𝓢(V, ℂ))
    (hw : ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, Continuous fun k => T (g k))
    (hb : ∀ q : Seminorm ℂ 𝓢(V, ℂ), Continuous q → ∃ C, ∀ k, q (g k) ≤ C) : Continuous g := by
  have hd : ∀ n x, Continuous fun k => iteratedFDeriv ℝ n (g k) x := fun n x => by
    haveI : Module.Finite ℝ (V [×n]→L[ℝ] ℂ) :=
      Module.Finite.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
        ContinuousMultilinearMap.toMultilinearMap_injective
    haveI : Module.Finite ℂ (V [×n]→L[ℝ] ℂ) := Module.Finite.of_restrictScalars_finite ℝ ℂ _
    let b := (Module.finBasis ℂ (V [×n]→L[ℝ] ℂ)).equivFunL
    have : Continuous fun k => b (derAt n x (g k)) := continuous_pi fun i =>
      hw ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ => ℂ) i).comp (b.toContinuousLinearMap.comp (derAt n x)))
    refine (b.symm.continuous.comp this).congr fun k => ?_
    exact b.symm_apply_apply _
  refine continuous_iff_continuousAt.2 fun k₀ => ?_
  rw [ContinuousAt, (schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]
  rintro ⟨j, n⟩ ε hε
  obtain ⟨C₁, h₁⟩ := hb _ (cont_seminorm (j + 1) n)
  obtain ⟨C₂, h₂⟩ := hb _ (cont_seminorm 0 (n + 1))
  have c₁ : 0 ≤ C₁ := (apply_nonneg _ _).trans (h₁ k₀)
  have c₂ : 0 ≤ C₂ := (apply_nonneg _ _).trans (h₂ k₀)
  set R : ℝ := 4 * C₁ / ε + 1 with hR
  have R1 : 1 ≤ R := by have : 0 ≤ 4 * C₁ / ε := by positivity
                        linarith
  set η : ℝ := ε / 4 / R ^ j with hη
  have η0 : 0 < η := by positivity
  set δ : ℝ := η / (2 * C₂ + 1) with hδ
  have δ0 : 0 < δ := by positivity
  obtain ⟨t, -, tf, ht⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : V) R) δ0
  have hev : ∀ᶠ k in 𝓝 k₀, ∀ x ∈ t, ‖iteratedFDeriv ℝ n (g k - g k₀) x‖ < η := by
    rw [eventually_all_finite tf]
    intro x _
    have := ((hd n x).tendsto k₀).eventually (Metric.ball_mem_nhds _ η0)
    filter_upwards [this] with k hk
    have e := GlobalTheory.CompanionTheory.SchwartzBaire.iteratedFDeriv_sub_apply' (g k) (g k₀) n x
    rw [e, ← dist_eq_norm]
    exact hk
  filter_upwards [hev] with k hk
  refine lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℂ j n _ (half_pos hε).le fun x => ?_) (half_lt_self hε)
  have s1 : ∀ a b, SchwartzMap.seminorm ℂ a b (g k - g k₀) ≤
      SchwartzMap.seminorm ℂ a b (g k) + SchwartzMap.seminorm ℂ a b (g k₀) := fun a b => map_sub_le_add _ _ _
  by_cases hx : ‖x‖ ≤ R
  · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht (mem_closedBall_zero_iff.2 hx))
    have hs : ContDiff ℝ (n + 1 : ℕ) (g k - g k₀ : 𝓢(V, ℂ)) := (g k - g k₀).smooth'.of_le (by exact_mod_cast le_top)
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ))) :=
      hs.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
    have hl := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := univ) (C := 2 * C₂)
      (fun z _ => hdiff z) (fun z _ => by
        rw [norm_fderiv_iteratedFDeriv]
        have := (g k - g k₀).norm_iteratedFDeriv_le_seminorm ℂ (n + 1) z
        linarith [s1 0 (n + 1), h₂ k, h₂ k₀]) convex_univ (mem_univ y) (mem_univ x)
    have hd' : ‖x - y‖ ≤ δ := by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hxy).le
    have e1 : 2 * C₂ * ‖x - y‖ ≤ η := by
      calc 2 * C₂ * ‖x - y‖ ≤ (2 * C₂ + 1) * δ := by gcongr; linarith
        _ = η := by rw [hδ]; field_simp
    have e2 : ‖iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) x‖ ≤ 2 * η := by
      have := norm_le_insert' (iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) x) (iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) y)
      have h3 : ‖iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) y‖ < η := hk y hy
      linarith
    calc ‖x‖ ^ j * ‖iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) x‖ ≤ R ^ j * (2 * η) := by gcongr
      _ = ε / 2 := by rw [hη]; field_simp; ring
  · push Not at hx
    have h4 := (g k - g k₀).le_seminorm ℂ (j + 1) n x
    have h5 : ‖x‖ * (‖x‖ ^ j * ‖iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) x‖) ≤ 2 * C₁ := by
      rw [← mul_assoc, ← pow_succ']
      linarith [s1 (j + 1) n, h₁ k, h₁ k₀]
    have h6 : 2 * C₁ ≤ ‖x‖ * (ε / 2) := by
      have : 4 * C₁ / ε ≤ ‖x‖ := by linarith
      rw [div_le_iff₀ hε] at this
      linarith
    exact le_of_mul_le_mul_left (h5.trans h6) (by linarith)
end PositivityTheory.ThKG.Loc.Bump

-- Prove2me | solution 1 for SalesforceComp.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T00:09:05.815457+00:00
-- url     : https://prove2.me/submissions/61b3cfec-9fd7-4761-be15-fca652c1becd

import Mathlib
import Definitions.Def_SalesforceComp_Model

set_option autoImplicit false

open MeasureTheory SalesforceComp

theorem solution (M : Model) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) (fun x : ℝ × ℝ => M.S x.1 x.2) := by
  haveI := M.G_prob
  have hconc : ∀ᵐ ε ∂M.G, ConcaveOn ℝ (Set.Ici 0) (fun r => M.d r ε) := by
    filter_upwards [M.d11_nonpos] with ε hε
    have hcd : ContDiff ℝ 3 (fun r => M.d r ε) :=
      M.d_contDiff.comp (contDiff_id.prodMk contDiff_const)
    have hd1 : Differentiable ℝ (fun r => M.d r ε) := hcd.differentiable (by norm_num)
    have hd2 : Differentiable ℝ (deriv (fun r => M.d r ε)) := by
      have := hcd.differentiable_iteratedDeriv 1 (by norm_num)
      rwa [iteratedDeriv_one] at this
    apply concaveOn_of_deriv2_nonpos (convex_Ici 0) hd1.continuous.continuousOn
      hd1.differentiableOn hd2.differentiableOn
    intro r hr
    rw [interior_Ici] at hr
    have := hε r (le_of_lt hr)
    show deriv (deriv (fun r => M.d r ε)) r ≤ 0
    exact this
  have hint : ∀ r, 0 ≤ r → ∀ Q : ℝ, Integrable (fun ε => min (M.d r ε) Q) M.G := fun r hr Q =>
    (M.d_integrable r hr).inf (integrable_const Q)
  refine ⟨(convex_Ici 0).prod convex_univ, ?_⟩
  rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb α β hα hβ hαβ
  simp only [Set.mem_prod, Set.mem_Ici, Set.mem_univ, and_true] at ha hb
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  unfold Model.S
  have hr : 0 ≤ α * a1 + β * b1 := by positivity
  have i1 := (hint a1 ha a2).const_mul α
  have i2 := (hint b1 hb b2).const_mul β
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2]
  apply integral_mono_ae (i1.add i2) (hint _ hr _)
  filter_upwards [hconc] with ε hε
  have hd := hε.2 (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb) hα hβ hαβ
  simp only [smul_eq_mul] at hd
  simp only [Pi.add_apply]
  apply le_min
  · have h1 := mul_le_mul_of_nonneg_left (min_le_left (M.d a1 ε) a2) hα
    have h2 := mul_le_mul_of_nonneg_left (min_le_left (M.d b1 ε) b2) hβ
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (min_le_right (M.d a1 ε) a2) hα
    have h2 := mul_le_mul_of_nonneg_left (min_le_right (M.d b1 ε) b2) hβ
    linarith

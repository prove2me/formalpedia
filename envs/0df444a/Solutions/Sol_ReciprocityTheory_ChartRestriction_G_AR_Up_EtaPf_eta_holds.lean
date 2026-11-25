-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.EtaPf.eta_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:05.869702+00:00
-- url     : https://prove2.me/submissions/2264fb64-325b-494d-ac90-d56214b91b09

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_EtaStatementHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_leviM_comb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_orth_mem_dom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app


section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.EtaPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff
private lemma fderiv_const_mul_apply {n : ℕ} (t : ℝ) (g : V n → ℂ) (y : V n) (v : V n) :
    fderiv ℝ (fun w => (t : ℂ) * g w) y v = (t : ℂ) * fderiv ℝ g y v := by
  by_cases hd : DifferentiableAt ℝ g y
  · rw [fderiv_const_mul hd]
    simp
  · by_cases ht : t = 0
    · subst ht
      simp
    · have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      have hd' : ¬ DifferentiableAt ℝ (fun w => (t : ℂ) * g w) y := by
        intro h'
        apply hd
        have h'' := h'.const_mul ((t : ℂ)⁻¹)
        simpa [← mul_assoc, inv_mul_cancel₀ ht'] using h''
      rw [fderiv_zero_of_not_differentiableAt hd', fderiv_zero_of_not_differentiableAt hd]
      simp
private lemma wd_const_mul (n : ℕ) (j : Fin n) (t : ℝ) (g : V n → ℂ) (y : V n) :
    wd n j (fun w => (t : ℂ) * g w) y = (t : ℂ) * wd n j g y := by
  unfold wd
  rw [fderiv_const_mul_apply, fderiv_const_mul_apply]
  ring
private lemma wdb_const_mul (n : ℕ) (j : Fin n) (t : ℝ) (g : V n → ℂ) :
    wdb n j (fun w => (t : ℂ) * g w) = fun y => (t : ℂ) * wdb n j g y := by
  funext y
  unfold wdb
  rw [fderiv_const_mul_apply, fderiv_const_mul_apply]
  ring
private lemma leviM_const_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (g : Frame X.Ψ r → ℝ) (t : ℝ) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    leviM X (fun x => t * g x) x0 z ξ = t * leviM X g x0 z ξ := by
  unfold leviM leviV
  have h1 : (fun w => (((t * g (cpt X x0 w) : ℝ)) : ℂ)) =
      fun w => (t : ℂ) * ((g (cpt X x0 w) : ℝ) : ℂ) := by
    funext w
    push_cast
    ring
  simp only [h1, wdb_const_mul, wd_const_mul, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul]
end ReciprocityTheory.ChartRestriction.G.AR.Up.EtaPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField
end ReciprocityTheory.ChartRestriction.G.AR.Up
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.EtaPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.EtaPf
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] : EtaStatement (E := E) := by
  intro r X Xa
  obtain ⟨η, hη, h⟩ := Xa.posF
  refine ⟨η, hη, fun x0 ho z hz ξ => ?_⟩
  have hx0 : x0 ∈ X.dom := IW.orth_mem_dom (X := X) (x0 := x0) (ho := ho)
  have hzd : cpt X x0 z ∈ X.dom := hz
  have hc1 := Xa.frame_theta_const_pos
  have ha1 := Xa.frame_theta_weight_pos
  have ht0 : (0 : ℝ) ≤ 1 + Xa.c1 / Xa.a1 := by positivity
  have htr : (1 + Xa.c1 / Xa.a1) * Xa.rr ≤ 2 * (Xa.T : ℝ) := by
    rw [mul_comm]
    exact Xa.rr_le
  have h1 := h (1 + Xa.c1 / Xa.a1) ht0 htr x0 hx0 z hzd ξ
  have h2 := Xa.base_psi_levi_lower_bound x0 hx0 z hzd ξ
  have h3 := IW.leviM_comb (X := X) (x0 := x0) (ho := ho) (hz := hz) (la1 := Xa.Fp) (la2 := Xa.L)
    (k := nd X) (ξ := ξ)
  have h4 := leviM_const_mul X Xa.ps0 (1 + Xa.c1 / Xa.a1) x0 z ξ
  have h5 := mul_le_mul_of_nonneg_left h2 ht0
  rw [h3] at h1
  unfold leviO at h1 ⊢
  rw [h4]
  nlinarith [h1, h5]
end ReciprocityTheory.ChartRestriction.G.AR.Up.EtaPf

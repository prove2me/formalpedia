-- Prove2me | solution 1 for STVFriedmann.theorem5_kneg_friedmann_order2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T10:14:35.353132+00:00
-- url     : https://prove2.me/submissions/fe0c508d-9f55-4070-abb8-4e291ca8f6bc

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Filter Topology Real STVFriedmann

namespace STK

lemma B_pos {θ : ℝ} (h : 0 < θ) : 0 < bigBangTime θ := by
  unfold bigBangTime
  have := self_lt_sinh_iff.2 (show 0 < 2 * θ by linarith)
  linarith

lemma hasDerivAt_B (θ : ℝ) : HasDerivAt bigBangTime (cosh (2 * θ) - 1) θ := by
  unfold bigBangTime
  have h1 : HasDerivAt (fun t => sinh (2 * t)) (cosh (2 * θ) * 2) θ := by
    have := ((hasDerivAt_id θ).const_mul 2).sinh
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
  refine ((h1.sub h2).div_const 2).congr_deriv ?_
  ring

lemma Bp_pos {θ : ℝ} (h : 0 < θ) : 0 < cosh (2 * θ) - 1 := by
  have := one_lt_cosh.2 (show 2 * θ ≠ 0 by positivity)
  linarith

lemma B_continuous : Continuous bigBangTime := by unfold bigBangTime; fun_prop

lemma B_tendsto_zero : Tendsto bigBangTime (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := (B_continuous.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [bigBangTime] using this
  · filter_upwards [self_mem_nhdsWithin] with θ hθ using B_pos hθ

lemma B_tendsto_top : Tendsto bigBangTime atTop atTop := by
  -- B θ ≥ θ^3 * ... ; use B θ ≥ (2θ)^3/12 ≥ ... simpler: sinh x - x ≥ x for x ≥ ... use sinh x ≥ x + x^3/6
  have h : ∀ θ ≥ (2:ℝ), θ / 2 ≤ bigBangTime θ := by
    intro θ hθ
    unfold bigBangTime
    have hs : θ + θ ^ 2 ≤ sinh (2 * θ) := by
      rw [Real.sinh_eq]
      have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * θ by linarith)
      have hn : exp (-(2 * θ)) ≤ 1 := exp_le_one_iff.2 (by linarith)
      nlinarith
    nlinarith
  exact tendsto_atTop_mono' atTop (eventually_ge_atTop 2 |>.mono h)
    (tendsto_id.atTop_div_const (by norm_num))

lemma B_strictMonoOn : StrictMonoOn bigBangTime (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) B_continuous.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  rw [(hasDerivAt_B x).deriv]
  exact Bp_pos hx

noncomputable def f (Δ₀ σ : ℝ) : ℝ := log (Δ₀ * bigBangTime (exp σ))

variable {Δ₀ : ℝ}

lemma f_mono (hΔ : 0 < Δ₀) : StrictMono (f Δ₀) := by
  intro a b hab
  unfold f
  have ha := B_pos (exp_pos a)
  have h := B_strictMonoOn (exp_pos a).le (exp_pos b).le (exp_lt_exp.2 hab)
  exact log_lt_log (by positivity) (by nlinarith)

lemma f_cont (hΔ : 0 < Δ₀) : Continuous (f Δ₀) := by
  unfold f
  refine Continuous.log (continuous_const.mul (B_continuous.comp continuous_exp)) fun σ => ?_
  have := B_pos (exp_pos σ); positivity

lemma f_atTop (hΔ : 0 < Δ₀) : Tendsto (f Δ₀) atTop atTop := by
  unfold f
  exact tendsto_log_atTop.comp ((B_tendsto_top.comp tendsto_exp_atTop).const_mul_atTop hΔ)

lemma f_atBot (hΔ : 0 < Δ₀) : Tendsto (f Δ₀) atBot atBot := by
  unfold f
  have h1 : Tendsto (fun σ => Δ₀ * bigBangTime (exp σ)) atBot (𝓝[>] 0) := by
    have := B_tendsto_zero.comp tendsto_exp_atBot_nhdsGT
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h2 := (tendsto_nhdsWithin_iff.1 this).1.const_mul Δ₀
      simpa using h2
    · exact Eventually.of_forall fun σ => by have := B_pos (exp_pos σ); simp only [Set.mem_Ioi]; positivity
  exact tendsto_log_nhdsGT_zero.comp h1

noncomputable def e (hΔ : 0 < Δ₀) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (f Δ₀) (f_mono hΔ) ((f_cont hΔ).surjective (f_atTop hΔ) (f_atBot hΔ))

noncomputable def Θ (hΔ : 0 < Δ₀) (τ : ℝ) : ℝ := exp ((e hΔ).symm τ)

lemma f_sig (hΔ : 0 < Δ₀) (τ : ℝ) : f Δ₀ ((e hΔ).symm τ) = τ :=
  StrictMono.orderIsoOfSurjective_self_symm_apply _ _ _ τ

lemma Θ_pos (hΔ : 0 < Δ₀) (τ : ℝ) : 0 < Θ hΔ τ := exp_pos _

lemma Θ_log (hΔ : 0 < Δ₀) {θ : ℝ} (hθ : 0 < θ) : Θ hΔ (log (Δ₀ * bigBangTime θ)) = θ := by
  have : log (Δ₀ * bigBangTime θ) = f Δ₀ (log θ) := by unfold f; rw [exp_log hθ]
  unfold Θ
  rw [this]
  have h2 : (e hΔ).symm (f Δ₀ (log θ)) = log θ :=
    StrictMono.orderIsoOfSurjective_symm_apply_self _ _ _ _
  rw [h2, exp_log hθ]

lemma hasDerivAt_f (hΔ : 0 < Δ₀) (σ : ℝ) :
    HasDerivAt (f Δ₀) ((cosh (2 * exp σ) - 1) * exp σ / bigBangTime (exp σ)) σ := by
  have hB := B_pos (exp_pos σ)
  have h1 : HasDerivAt (fun σ => Δ₀ * bigBangTime (exp σ)) (Δ₀ * ((cosh (2 * exp σ) - 1) * exp σ)) σ :=
    ((hasDerivAt_B (exp σ)).comp σ (hasDerivAt_exp σ)).const_mul Δ₀
  refine (h1.log (by positivity)).congr_deriv ?_
  field_simp

lemma hasDerivAt_Θ (hΔ : 0 < Δ₀) (τ : ℝ) :
    HasDerivAt (Θ hΔ) (bigBangTime (Θ hΔ τ) / (cosh (2 * Θ hΔ τ) - 1)) τ := by
  set σ := (e hΔ).symm τ
  have hcont : Continuous (fun τ => (e hΔ).symm τ) := (e hΔ).symm.continuous
  have hθ := exp_pos σ
  have hB := B_pos hθ
  have hBp := Bp_pos hθ
  have hne : (cosh (2 * exp σ) - 1) * exp σ / bigBangTime (exp σ) ≠ 0 := by positivity
  have hs := HasDerivAt.of_local_left_inverse hcont.continuousAt (hasDerivAt_f hΔ σ) hne
    (Eventually.of_forall fun y => f_sig hΔ y)
  refine ((hasDerivAt_exp _).comp τ hs).congr_deriv ?_
  simp only [Θ]
  rw [← show σ = (e hΔ).symm τ from rfl]
  field_simp

lemma Θ_atTop (hΔ : 0 < Δ₀) : Tendsto (Θ hΔ) atTop atTop :=
  tendsto_exp_atTop.comp (e hΔ).symm.tendsto_atTop

lemma Θ_atBot (hΔ : 0 < Δ₀) : Tendsto (Θ hΔ) atBot (𝓝[>] 0) :=
  tendsto_exp_atBot_nhdsGT.comp (e hΔ).symm.tendsto_atBot

/-- generic construction of the solution from a curve satisfying the reparametrized ODE -/
lemma solution_of_curve {m : ℕ} (hΔ : 0 < Δ₀) (F : (Fin m → ℝ) → Fin m → ℝ) (c c' : ℝ → Fin m → ℝ)
    (a b : Fin m → ℝ)
    (hc : ∀ θ, 0 < θ → ∀ i, HasDerivAt (fun t => c t i) (c' θ i) θ)
    (hode : ∀ θ, 0 < θ → ∀ i, c' θ i * (bigBangTime θ / (cosh (2 * θ) - 1)) = F (c θ) i)
    (h0 : ∀ i, Tendsto (fun θ => c θ i) (𝓝[>] 0) (𝓝 (a i)))
    (hinf : ∀ i, Tendsto (fun θ => c θ i) atTop (𝓝 (b i))) :
    ∃ U : ℝ → Fin m → ℝ, IsSTVSolution F U ∧
      (∀ θ : ℝ, 0 < θ → U (Real.log (Δ₀ * bigBangTime θ)) = c θ) ∧
      Tendsto U atBot (𝓝 a) ∧ Tendsto U atTop (𝓝 b) := by
  refine ⟨fun τ => c (Θ hΔ τ), ?_, ?_, ?_, ?_⟩
  · intro τ
    rw [hasDerivAt_pi]
    intro i
    have := (hc _ (Θ_pos hΔ τ) i).comp τ (hasDerivAt_Θ hΔ τ)
    refine this.congr_deriv ?_
    exact hode _ (Θ_pos hΔ τ) i
  · intro θ hθ
    simp only [Θ_log hΔ hθ]
  · rw [tendsto_pi_nhds]; intro i
    exact (h0 i).comp (Θ_atBot hΔ)
  · rw [tendsto_pi_nhds]; intro i
    exact (hinf i).comp (Θ_atTop hΔ)

end STK

open Filter Topology Real

namespace STL

lemma ev_ne : ∀ᶠ x in 𝓝[>] (0:ℝ), x ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with x hx using ne_of_gt hx

lemma cl (f : ℝ → ℝ) (hf : Continuous f) : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
  (hf.tendsto 0).mono_left nhdsWithin_le_nhds

lemma L3 : Tendsto (fun x => sinh x / x) (𝓝[>] 0) (𝓝 1) := by
  have := HasDerivAt.lhopital_zero_nhdsGT (f := sinh) (g := id) (f' := cosh) (g' := fun _ => 1)
    (Eventually.of_forall fun x => hasDerivAt_sinh x) (Eventually.of_forall fun x => hasDerivAt_id x)
    (Eventually.of_forall fun _ => one_ne_zero)
    (by have := (continuous_sinh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)); simpa using this)
    (by have := (continuous_id.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ))); simpa using this)
    (by have := (continuous_cosh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)); simpa using this)
  simpa using this

lemma L2 : Tendsto (fun x => (cosh x - 1) / x ^ 2) (𝓝[>] 0) (𝓝 (1/2)) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => x ^ 2) (2 * x) x := fun x => by
    simpa using hasDerivAt_pow 2 x
  have := HasDerivAt.lhopital_zero_nhdsGT (f := fun x => cosh x - 1) (g := fun x => x ^ 2)
    (f' := sinh) (g' := fun x => 2 * x)
    (Eventually.of_forall fun x => (hasDerivAt_cosh x).sub_const 1) (Eventually.of_forall hd)
    (by filter_upwards [ev_ne] with x hx; positivity)
    (by simpa using cl (fun x => cosh x - 1) (by fun_prop))
    (by convert cl (fun x : ℝ => x ^ 2) (by fun_prop) using 2; norm_num)
    (by
      have := L3.div_const 2
      refine this.congr' ?_
      filter_upwards [ev_ne] with x hx
      field_simp)
  exact this

lemma L1 : Tendsto (fun x => (sinh x - x) / x ^ 3) (𝓝[>] 0) (𝓝 (1/6)) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => x ^ 3) (3 * x ^ 2) x := fun x => by
    simpa using hasDerivAt_pow 3 x
  have := HasDerivAt.lhopital_zero_nhdsGT (f := fun x => sinh x - x) (g := fun x => x ^ 3)
    (f' := fun x => cosh x - 1) (g' := fun x => 3 * x ^ 2)
    (Eventually.of_forall fun x => (hasDerivAt_sinh x).sub (hasDerivAt_id x)) (Eventually.of_forall hd)
    (by filter_upwards [ev_ne] with x hx; positivity)
    (by simpa using cl (fun x => sinh x - x) (by fun_prop))
    (by convert cl (fun x : ℝ => x ^ 3) (by fun_prop) using 2; norm_num)
    (by
      have := L2.div_const 3
      rw [show (1:ℝ)/2/3 = 1/6 by norm_num] at this
      refine this.congr' ?_
      filter_upwards [ev_ne] with x hx
      field_simp)
  exact this

lemma two_mul_nhdsGT : Tendsto (fun θ : ℝ => 2 * θ) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · simpa using cl (fun θ : ℝ => 2 * θ) (by fun_prop)
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    simp only [Set.mem_Ioi] at *; linarith

lemma cosh_atTop : Tendsto cosh atTop atTop := by
  refine tendsto_atTop_mono (fun x => ?_) (tendsto_exp_atTop.atTop_div_const (by norm_num : (0:ℝ) < 2))
  rw [cosh_eq]; have := exp_pos (-x); linarith

lemma cosh2_atTop : Tendsto (fun θ => cosh (2 * θ)) atTop atTop :=
  cosh_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))

end STL

open Filter Topology Real STVFriedmann

namespace ST5

lemma hX (θ : ℝ) : HasDerivAt (fun t => sinh (2 * t)) (2 * cosh (2 * θ)) θ := by
  have := ((hasDerivAt_id θ).const_mul 2).sinh
  refine (by simpa using this : HasDerivAt (fun t => sinh (2 * t)) (cosh (2 * θ) * 2) θ).congr_deriv ?_
  ring

lemma hY (θ : ℝ) : HasDerivAt (fun t => cosh (2 * t)) (2 * sinh (2 * θ)) θ := by
  have := ((hasDerivAt_id θ).const_mul 2).cosh
  refine (by simpa using this : HasDerivAt (fun t => cosh (2 * t)) (sinh (2 * θ) * 2) θ).congr_deriv ?_
  ring

lemma hN (θ : ℝ) : HasDerivAt (fun t => sinh (2 * t) - 2 * t) (2 * cosh (2 * θ) - 2) θ := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
  exact (hX θ).sub h2

lemma Ym1_pos {θ : ℝ} (h : 0 < θ) : 0 < cosh (2 * θ) - 1 := STK.Bp_pos h

lemma N_pos {θ : ℝ} (h : 0 < θ) : 0 < sinh (2 * θ) - 2 * θ := by
  have := self_lt_sinh_iff.2 (show 0 < 2 * θ by linarith); linarith

lemma Y_sq (θ : ℝ) : cosh (2 * θ) ^ 2 = sinh (2 * θ) ^ 2 + 1 := cosh_sq _

/-- derivative of z̃₂ -/
lemma hz (θ : ℝ) (h : 0 < θ) : HasDerivAt friedmannZ2
    (24 * (sinh (2 * θ) - 2 * θ) / (cosh (2 * θ) - 1) ^ 2
      - 36 * (sinh (2 * θ) - 2 * θ) ^ 2 * sinh (2 * θ) / (cosh (2 * θ) - 1) ^ 4) θ := by
  have hp := Ym1_pos h
  have := (((hN θ).fun_pow 2).const_mul 6).div (((hY θ).sub_const 1).fun_pow 3) (by positivity)
  unfold friedmannZ2
  refine this.congr_deriv ?_
  field_simp
  ring

lemma hw (θ : ℝ) (h : 0 < θ) : HasDerivAt friedmannW0
    (2 * sinh (2 * θ) / (cosh (2 * θ) - 1) + 2 * (sinh (2 * θ) - 2 * θ) * cosh (2 * θ) / (cosh (2 * θ) - 1) ^ 2
      - 4 * (sinh (2 * θ) - 2 * θ) * sinh (2 * θ) ^ 2 / (cosh (2 * θ) - 1) ^ 3) θ := by
  have hp := Ym1_pos h
  have := ((hN θ).fun_mul (hX θ)).div (((hY θ).sub_const 1).fun_pow 2) (by positivity)
  unfold friedmannW0
  refine this.congr_deriv ?_
  field_simp
  ring

lemma ode_z (θ : ℝ) (h : 0 < θ) :
    (24 * (sinh (2 * θ) - 2 * θ) / (cosh (2 * θ) - 1) ^ 2
      - 36 * (sinh (2 * θ) - 2 * θ) ^ 2 * sinh (2 * θ) / (cosh (2 * θ) - 1) ^ 4)
      * (bigBangTime θ / (cosh (2 * θ) - 1))
    = 2 * friedmannZ2 θ - 3 * friedmannZ2 θ * friedmannW0 θ := by
  have hp := Ym1_pos h
  unfold bigBangTime friedmannZ2 friedmannW0
  field_simp
  ring

lemma ode_w (θ : ℝ) (h : 0 < θ) :
    (2 * sinh (2 * θ) / (cosh (2 * θ) - 1) + 2 * (sinh (2 * θ) - 2 * θ) * cosh (2 * θ) / (cosh (2 * θ) - 1) ^ 2
      - 4 * (sinh (2 * θ) - 2 * θ) * sinh (2 * θ) ^ 2 / (cosh (2 * θ) - 1) ^ 3)
      * (bigBangTime θ / (cosh (2 * θ) - 1))
    = -(1 / 6) * friedmannZ2 θ + friedmannW0 θ - friedmannW0 θ ^ 2 := by
  have hp := Ym1_pos h
  have hs := Y_sq θ
  unfold bigBangTime friedmannZ2 friedmannW0
  set X := sinh (2 * θ)
  set Y := cosh (2 * θ)
  set N := X - 2 * θ
  have key : ∀ A : ℝ, A = (2 * X / (Y - 1) + 2 * N * Y / (Y - 1) ^ 2 - 4 * N * X ^ 2 / (Y - 1) ^ 3)
      * (N / 2 / (Y - 1)) - (-(1 / 6) * (6 * N ^ 2 / (Y - 1) ^ 3) + N * X / (Y - 1) ^ 2
        - (N * X / (Y - 1) ^ 2) ^ 2) → A = N ^ 2 * (Y ^ 2 - X ^ 2 - 1) / (Y - 1) ^ 4 := by
    intro A hA; rw [hA]; field_simp; ring
  have := key _ rfl
  rw [hs, show X ^ 2 + 1 - X ^ 2 - 1 = (0:ℝ) by ring, mul_zero, zero_div, sub_eq_zero] at this
  exact this

lemma lim0_z : Tendsto friedmannZ2 (𝓝[>] 0) (𝓝 (4 / 3)) := by
  have ha := STL.L1.comp STL.two_mul_nhdsGT
  have hb := STL.L2.comp STL.two_mul_nhdsGT
  have := ((ha.pow 2).const_mul 6).div (hb.pow 3) (by norm_num)
  rw [show 6 * (1 / 6 : ℝ) ^ 2 / (1 / 2) ^ 3 = 4 / 3 by norm_num] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ' : (0:ℝ) < θ := hθ
  simp only [Function.comp, friedmannZ2, Pi.div_apply]
  have := Ym1_pos hθ'
  field_simp

lemma lim0_w : Tendsto friedmannW0 (𝓝[>] 0) (𝓝 (2 / 3)) := by
  have ha := STL.L1.comp STL.two_mul_nhdsGT
  have hb := STL.L2.comp STL.two_mul_nhdsGT
  have hs := STL.L3.comp STL.two_mul_nhdsGT
  have := (ha.mul hs).div (hb.pow 2) (by norm_num)
  rw [show (1 / 6 : ℝ) * 1 / (1 / 2) ^ 2 = 2 / 3 by norm_num] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ' : (0:ℝ) < θ := hθ
  simp only [Function.comp, friedmannW0, Pi.div_apply]
  have := Ym1_pos hθ'
  field_simp

/-- rational limits in `u = 1/Y` -/
lemma ratlim (g : ℝ → ℝ) (hg : ContinuousAt g 0) (F : ℝ → ℝ)
    (hF : ∀ᶠ θ in atTop, F θ = g (cosh (2 * θ))⁻¹) : Tendsto F atTop (𝓝 (g 0)) := by
  have hu : Tendsto (fun θ => (cosh (2 * θ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp STL.cosh2_atTop
  exact ((hg.tendsto).comp hu).congr' (hF.mono fun θ h => h.symm)

lemma ev_Y : ∀ᶠ θ in atTop, (2:ℝ) ≤ cosh (2 * θ) := STL.cosh2_atTop.eventually_ge_atTop 2

lemma liminf_z : Tendsto friedmannZ2 atTop (𝓝 0) := by
  have hup : Tendsto (fun θ => 6 * (cosh (2 * θ) + 1) / (cosh (2 * θ) - 1) ^ 2) atTop (𝓝 0) := by
    have := ratlim (fun u => 6 * u * (1 + u) / (1 - u) ^ 2) (by fun_prop (disch := norm_num))
      (fun θ => 6 * (cosh (2 * θ) + 1) / (cosh (2 * θ) - 1) ^ 2) (by
        filter_upwards [ev_Y] with θ hθ
        have h1 : cosh (2 * θ) - 1 ≠ 0 := by linarith
        have h2 : cosh (2 * θ) ≠ 0 := by linarith
        field_simp)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with θ hθ
    unfold friedmannZ2; have := Ym1_pos hθ; positivity
  · filter_upwards [eventually_gt_atTop 0] with θ hθ
    have hp := Ym1_pos hθ
    have hN0 := N_pos hθ
    have hNX : sinh (2 * θ) - 2 * θ ≤ sinh (2 * θ) := by linarith
    have hs := Y_sq θ
    unfold friedmannZ2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : 6 * (cosh (2 * θ) + 1) * (cosh (2 * θ) - 1) ^ 3
        = 6 * sinh (2 * θ) ^ 2 * (cosh (2 * θ) - 1) ^ 2 := by
      have : (cosh (2 * θ) + 1) * (cosh (2 * θ) - 1) = sinh (2 * θ) ^ 2 := by nlinarith
      linear_combination 6 * (cosh (2 * θ) - 1) ^ 2 * this
    rw [e]
    have : (sinh (2 * θ) - 2 * θ) ^ 2 ≤ sinh (2 * θ) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right this (show 0 ≤ 6 * (cosh (2 * θ) - 1) ^ 2 by positivity)
    nlinarith

lemma cosh_ge (x : ℝ) (hx : 0 ≤ x) : 1 + x ^ 2 / 4 ≤ cosh x := by
  rw [cosh_eq]
  have h1 := Real.quadratic_le_exp_of_nonneg hx
  have h2 := Real.add_one_le_exp (-x)
  nlinarith

lemma liminf_w : Tendsto friedmannW0 atTop (𝓝 1) := by
  have hR : Tendsto (fun θ => (cosh (2 * θ) + 1) / (cosh (2 * θ) - 1)) atTop (𝓝 1) := by
    have := ratlim (fun u => (1 + u) / (1 - u)) (by fun_prop (disch := norm_num))
      (fun θ => (cosh (2 * θ) + 1) / (cosh (2 * θ) - 1)) (by
        filter_upwards [ev_Y] with θ hθ
        have h1 : cosh (2 * θ) - 1 ≠ 0 := by linarith
        have h2 : cosh (2 * θ) ≠ 0 := by linarith
        have h3 : 1 - (cosh (2 * θ))⁻¹ ≠ 0 := by
          have : (cosh (2 * θ))⁻¹ ≤ 1/2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hθ
          linarith
        field_simp)
    simpa using this
  have hE : Tendsto (fun θ => 2 * θ * sinh (2 * θ) / (cosh (2 * θ) - 1) ^ 2) atTop (𝓝 0) := by
    have hup : Tendsto (fun θ : ℝ => 4 / θ) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with θ hθ
      have := Ym1_pos hθ
      have : 0 < sinh (2 * θ) := sinh_pos_iff.2 (by linarith)
      positivity
    · filter_upwards [eventually_gt_atTop 0, ev_Y] with θ hθ hY2
      have hp := Ym1_pos hθ
      have hs := Y_sq θ
      have hX0 : 0 < sinh (2 * θ) := sinh_pos_iff.2 (by linarith)
      have hXY : sinh (2 * θ) ≤ cosh (2 * θ) := by nlinarith
      have hc := cosh_ge (2 * θ) (by linarith)
      rw [div_le_div_iff₀ (by positivity) hθ]
      -- 2θ X θ ≤ 4 (Y-1)^2 ; X ≤ Y ≤ 2(Y-1), θ² ≤ (Y-1)
      have h1 : θ ^ 2 ≤ cosh (2 * θ) - 1 := by nlinarith
      have h2 : sinh (2 * θ) ≤ 2 * (cosh (2 * θ) - 1) := by linarith
      have h3 : 2 * θ * sinh (2 * θ) * θ = 2 * θ ^ 2 * sinh (2 * θ) := by ring
      rw [h3]
      have := mul_le_mul h1 h2 hX0.le hp.le
      nlinarith
  have := hR.sub hE
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with θ hθ
  have hp := Ym1_pos hθ
  have hs := Y_sq θ
  unfold friedmannW0
  have e : cosh (2 * θ) + 1 = sinh (2 * θ) ^ 2 / (cosh (2 * θ) - 1) := by
    field_simp; nlinarith
  rw [e]
  field_simp

end ST5


open Filter Topology Real STVFriedmann

namespace ST5b
open ST5

lemma hS (θ : ℝ) : HasDerivAt sinh (cosh θ) θ := hasDerivAt_sinh θ
lemma hC (θ : ℝ) : HasDerivAt cosh (sinh θ) θ := hasDerivAt_cosh θ

lemma S_pos {θ : ℝ} (h : 0 < θ) : 0 < sinh θ := sinh_pos_iff.2 h

/-- exponential substitution -/
lemma exp_sub (θ : ℝ) :
    sinh θ = (exp θ ^ 2 - 1) / (2 * exp θ) ∧ cosh θ = (exp θ ^ 2 + 1) / (2 * exp θ) ∧
    sinh (2 * θ) = (exp θ ^ 4 - 1) / (2 * exp θ ^ 2) ∧
    cosh (2 * θ) - 1 = (exp θ ^ 2 - 1) ^ 2 / (2 * exp θ ^ 2) ∧
    cosh (2 * θ) = (exp θ ^ 4 + 1) / (2 * exp θ ^ 2) := by
  have hp : exp θ ≠ 0 := (exp_pos θ).ne'
  have h2 : exp (2 * θ) = exp θ ^ 2 := by rw [← exp_nat_mul]; push_cast; ring_nf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sinh_eq, exp_neg]; field_simp
  · rw [cosh_eq, exp_neg]; field_simp
  · rw [sinh_eq, exp_neg, h2]; field_simp
  · rw [cosh_eq, exp_neg, h2]; field_simp; ring
  · rw [cosh_eq, exp_neg, h2]; field_simp

lemma ode_z4 (θ : ℝ) (h : 0 < θ) :
    deriv friedmannZ4 θ * (bigBangTime θ / (cosh (2 * θ) - 1))
    = (5 / 12) * friedmannZ2 θ ^ 2 * friedmannW0 θ + 4 * friedmannZ4 θ
      - 5 * friedmannW0 θ * friedmannZ4 θ - 5 * friedmannZ2 θ * friedmannW2 θ := by
  have hp := Ym1_pos h
  have hs := S_pos h
  have hd0 := ((((hN θ).fun_pow 4).const_mul 30).fun_mul ((hC θ).fun_pow 2)).div
    (((hY θ).sub_const 1).fun_pow 6) (pow_ne_zero 6 (Ym1_pos h).ne')
  have hd : HasDerivAt friedmannZ4 _ θ := hd0
  rw [hd.deriv]
  unfold bigBangTime friedmannZ2 friedmannW0 friedmannZ4 friedmannW2
  obtain ⟨e1, e2, e3, e4, e5⟩ := exp_sub θ
  have hq : 1 < exp θ := by have := add_one_lt_exp (ne_of_gt h); linarith
  simp only [e4]
  simp only [e1, e2, e3, e5]
  set p := exp θ
  have hp0 : p ≠ 0 := by positivity
  have hp1 : p ^ 2 - 1 ≠ 0 := by nlinarith
  norm_num only [Nat.cast_ofNat]
  generalize (p ^ 4 - 1) / (2 * p ^ 2) - 2 * θ = N
  field_simp
  ring

lemma ode_w2 (θ : ℝ) (h : 0 < θ) :
    deriv friedmannW2 θ * (bigBangTime θ / (cosh (2 * θ) - 1))
    = -(1 / 24) * friedmannZ2 θ ^ 2 + (1 / 4) * friedmannZ2 θ * friedmannW0 θ ^ 2
      - (1 / 10) * friedmannZ4 θ + 3 * friedmannW2 θ - 4 * friedmannW0 θ * friedmannW2 θ := by
  have hp := Ym1_pos h
  have hs := S_pos h
  have hd0 := ((((hN θ).fun_pow 3).const_mul 3).fun_mul (hC θ)).div
    (((((hY θ).sub_const 1).fun_pow 4).const_mul 2).fun_mul (hS θ))
    (mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 4 (Ym1_pos h).ne')) (S_pos h).ne')
  have hd : HasDerivAt friedmannW2 _ θ := hd0
  rw [hd.deriv]
  unfold bigBangTime friedmannZ2 friedmannW0 friedmannZ4 friedmannW2
  obtain ⟨e1, e2, e3, e4, e5⟩ := exp_sub θ
  have hq : 1 < exp θ := by have := add_one_lt_exp (ne_of_gt h); linarith
  simp only [e4]
  simp only [e1, e2, e3, e5]
  set p := exp θ
  have hp0 : p ≠ 0 := by positivity
  have hp1 : p ^ 2 - 1 ≠ 0 := by nlinarith
  norm_num only [Nat.cast_ofNat]
  generalize (p ^ 4 - 1) / (2 * p ^ 2) - 2 * θ = N
  field_simp
  ring

lemma diff_z4 (θ : ℝ) (h : 0 < θ) : DifferentiableAt ℝ friedmannZ4 θ := by
  have hd0 := ((((hN θ).fun_pow 4).const_mul 30).fun_mul ((hC θ).fun_pow 2)).div
    (((hY θ).sub_const 1).fun_pow 6) (pow_ne_zero 6 (Ym1_pos h).ne')
  have hd : HasDerivAt friedmannZ4 _ θ := hd0
  exact hd.differentiableAt

lemma diff_w2 (θ : ℝ) (h : 0 < θ) : DifferentiableAt ℝ friedmannW2 θ := by
  have hd0 := ((((hN θ).fun_pow 3).const_mul 3).fun_mul (hC θ)).div
    (((((hY θ).sub_const 1).fun_pow 4).const_mul 2).fun_mul (hS θ))
    (mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 4 (Ym1_pos h).ne')) (S_pos h).ne')
  have hd : HasDerivAt friedmannW2 _ θ := hd0
  exact hd.differentiableAt

lemma C_lim : Tendsto cosh (𝓝[>] 0) (𝓝 1) := by simpa using STL.cl cosh continuous_cosh

lemma lim0_z4 : Tendsto friedmannZ4 (𝓝[>] 0) (𝓝 (40 / 27)) := by
  have ha := STL.L1.comp STL.two_mul_nhdsGT
  have hb := STL.L2.comp STL.two_mul_nhdsGT
  have := (((ha.pow 4).const_mul 30).mul (C_lim.pow 2)).div (hb.pow 6) (by norm_num)
  rw [show 30 * (1 / 6 : ℝ) ^ 4 * 1 ^ 2 / (1 / 2) ^ 6 = 40 / 27 by norm_num] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ' : (0:ℝ) < θ := hθ
  simp only [Function.comp, friedmannZ4, Pi.div_apply, Pi.mul_apply]
  have := Ym1_pos hθ'
  field_simp

lemma lim0_w2 : Tendsto friedmannW2 (𝓝[>] 0) (𝓝 (2 / 9)) := by
  have ha := STL.L1.comp STL.two_mul_nhdsGT
  have hb := STL.L2.comp STL.two_mul_nhdsGT
  have := ((((ha.pow 3).const_mul 3).mul C_lim).mul_const 2).div ((((hb.pow 4)).const_mul 2).mul STL.L3)
    (by norm_num)
  rw [show 3 * (1 / 6 : ℝ) ^ 3 * 1 * 2 / (2 * (1 / 2) ^ 4 * 1) = 2 / 9 by norm_num] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ' : (0:ℝ) < θ := hθ
  simp only [Function.comp, friedmannW2, Pi.div_apply, Pi.mul_apply]
  have := Ym1_pos hθ'
  have := S_pos hθ'
  field_simp

lemma liminf_z4 : Tendsto friedmannZ4 atTop (𝓝 0) := by
  have hup : Tendsto (fun θ => 15 * (cosh (2 * θ) + 1) ^ 3 / (cosh (2 * θ) - 1) ^ 4) atTop (𝓝 0) := by
    have := ratlim (fun u => 15 * u * (1 + u) ^ 3 / (1 - u) ^ 4) (by fun_prop (disch := norm_num))
      (fun θ => 15 * (cosh (2 * θ) + 1) ^ 3 / (cosh (2 * θ) - 1) ^ 4) (by
        filter_upwards [ev_Y] with θ hθ
        have h1 : cosh (2 * θ) - 1 ≠ 0 := by linarith
        have h2 : cosh (2 * θ) ≠ 0 := by linarith
        field_simp)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with θ hθ
    unfold friedmannZ4; have := Ym1_pos hθ; positivity
  · filter_upwards [eventually_gt_atTop 0] with θ hθ
    have hp := Ym1_pos hθ
    have hN0 := N_pos hθ
    have hNX : sinh (2 * θ) - 2 * θ ≤ sinh (2 * θ) := by linarith
    have heq : 30 * sinh (2 * θ) ^ 4 * cosh θ ^ 2 / (cosh (2 * θ) - 1) ^ 6
        = 15 * (cosh (2 * θ) + 1) ^ 3 / (cosh (2 * θ) - 1) ^ 4 := by
      obtain ⟨e1, e2, e3, e4, e5⟩ := exp_sub θ
      have hq : 1 < exp θ := by have := add_one_lt_exp (ne_of_gt hθ); linarith
      simp only [e4]; simp only [e2, e3, e5]
      have hp0 : exp θ ≠ 0 := by positivity
      have hp1 : exp θ ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp; ring
    rw [← heq]
    unfold friedmannZ4
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : (sinh (2 * θ) - 2 * θ) ^ 4 ≤ sinh (2 * θ) ^ 4 := pow_le_pow_left₀ hN0.le hNX 4
    have := mul_le_mul_of_nonneg_right this (sq_nonneg (cosh θ))
    nlinarith

lemma liminf_w2 : Tendsto friedmannW2 atTop (𝓝 0) := by
  have hup : Tendsto (fun θ => 3 * (cosh (2 * θ) + 1) ^ 2 / (2 * (cosh (2 * θ) - 1) ^ 3)) atTop (𝓝 0) := by
    have := ratlim (fun u => 3 * u * (1 + u) ^ 2 / (2 * (1 - u) ^ 3)) (by fun_prop (disch := norm_num))
      (fun θ => 3 * (cosh (2 * θ) + 1) ^ 2 / (2 * (cosh (2 * θ) - 1) ^ 3)) (by
        filter_upwards [ev_Y] with θ hθ
        have h1 : cosh (2 * θ) - 1 ≠ 0 := by linarith
        have h2 : cosh (2 * θ) ≠ 0 := by linarith
        field_simp)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with θ hθ
    unfold friedmannW2; have := Ym1_pos hθ; have := S_pos hθ; have := N_pos hθ; positivity
  · filter_upwards [eventually_gt_atTop 0] with θ hθ
    have hp := Ym1_pos hθ
    have hN0 := N_pos hθ
    have hS0 := S_pos hθ
    have hX0 : 0 < sinh (2 * θ) := sinh_pos_iff.2 (by linarith)
    have hNX : sinh (2 * θ) - 2 * θ ≤ sinh (2 * θ) := by linarith
    have heq1 : friedmannW2 θ = 3 * (sinh (2 * θ) - 2 * θ) ^ 3 * sinh (2 * θ) / (2 * (cosh (2 * θ) - 1) ^ 5) := by
      unfold friedmannW2
      obtain ⟨e1, e2, e3, e4, e5⟩ := exp_sub θ
      have hq : 1 < exp θ := by have := add_one_lt_exp (ne_of_gt hθ); linarith
      simp only [e4]; simp only [e1, e2, e3, e5]
      have hp0 : exp θ ≠ 0 := by positivity
      have hp1 : exp θ ^ 2 - 1 ≠ 0 := by nlinarith
      generalize (exp θ ^ 4 - 1) / (2 * exp θ ^ 2) - 2 * θ = N
      field_simp; ring
    have heq2 : 3 * sinh (2 * θ) ^ 4 / (2 * (cosh (2 * θ) - 1) ^ 5)
        = 3 * (cosh (2 * θ) + 1) ^ 2 / (2 * (cosh (2 * θ) - 1) ^ 3) := by
      obtain ⟨e1, e2, e3, e4, e5⟩ := exp_sub θ
      have hq : 1 < exp θ := by have := add_one_lt_exp (ne_of_gt hθ); linarith
      simp only [e4]; simp only [e3, e5]
      have hp0 : exp θ ≠ 0 := by positivity
      have hp1 : exp θ ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp; ring
    rw [heq1, ← heq2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : (sinh (2 * θ) - 2 * θ) ^ 3 ≤ sinh (2 * θ) ^ 3 := pow_le_pow_left₀ hN0.le hNX 3
    nlinarith

end ST5b

open STK ST5 ST5b in
theorem solution (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀) :
    ∃ U : ℝ → Fin 4 → ℝ, IsSTVSolution stvField2 U ∧
      (∀ θ : ℝ, 0 < θ → U (Real.log (Δ₀ * bigBangTime θ)) = friedmannCurve2 θ) ∧
      Tendsto U atBot (𝓝 restSM2) ∧ Tendsto U atTop (𝓝 restM2) := by
  refine STK.solution_of_curve hΔ₀ stvField2 friedmannCurve2
    (fun θ => ![deriv friedmannZ2 θ, deriv friedmannW0 θ, deriv friedmannZ4 θ, deriv friedmannW2 θ])
    restSM2 restM2 ?_ ?_ ?_ ?_
  · intro θ hθ i
    fin_cases i
    · simpa [friedmannCurve2] using (hz θ hθ).differentiableAt.hasDerivAt
    · simpa [friedmannCurve2] using (hw θ hθ).differentiableAt.hasDerivAt
    · simpa [friedmannCurve2] using (diff_z4 θ hθ).hasDerivAt
    · simpa [friedmannCurve2] using (diff_w2 θ hθ).hasDerivAt
  · intro θ hθ i
    fin_cases i
    · simpa [friedmannCurve2, stvField2, (hz θ hθ).deriv] using ode_z θ hθ
    · simpa [friedmannCurve2, stvField2, (hw θ hθ).deriv] using ode_w θ hθ
    · simpa [friedmannCurve2, stvField2] using ode_z4 θ hθ
    · simpa [friedmannCurve2, stvField2] using ode_w2 θ hθ
  · intro i
    fin_cases i
    · simpa [friedmannCurve2, restSM2] using lim0_z
    · simpa [friedmannCurve2, restSM2] using lim0_w
    · simpa [friedmannCurve2, restSM2] using lim0_z4
    · simpa [friedmannCurve2, restSM2] using lim0_w2
  · intro i
    fin_cases i
    · simpa [friedmannCurve2, restM2] using liminf_z
    · simpa [friedmannCurve2, restM2] using liminf_w
    · simpa [friedmannCurve2, restM2] using liminf_z4
    · simpa [friedmannCurve2, restM2] using liminf_w2

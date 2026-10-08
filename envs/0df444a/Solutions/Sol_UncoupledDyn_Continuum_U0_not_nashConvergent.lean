-- Prove2me | solution 1 for UncoupledDyn.Continuum.U0_not_nashConvergent
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:58:51.338702+00:00
-- url     : https://prove2.me/submissions/165f2bfe-e31c-49d5-8fb4-02bcc70d08e6

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting
open UncoupledDyn.Continuum
open Filter Topology
open scoped Matrix
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private noncomputable def ξ (z : ℂ) : ℂ := ((1 / (1 + Complex.normSq z) : ℝ) : ℂ) * z
private noncomputable def G : Game := fun i x => -‖x i - ξ (x (i+1))‖^2

private theorem xi_zero : ξ 0 = 0 := by simp [ξ]
private theorem xi_cont : Continuous ξ := by
  unfold ξ
  apply Continuous.mul
  · apply Complex.continuous_ofReal.comp
    apply Continuous.div continuous_const
    · exact continuous_const.add Complex.continuous_normSq
    · intro z
      have := Complex.normSq_nonneg z
      positivity
  · exact continuous_id

private theorem xi_norm (z : ℂ) : ‖ξ z‖ = ‖z‖/(1+‖z‖^2) := by
  have hp : 0 < 1+Complex.normSq z := by linarith [Complex.normSq_nonneg z]
  simp only [ξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 1) hp)]
  rw [Complex.normSq_eq_norm_sq]
  ring

private theorem xi_maps : Set.MapsTo ξ D D := by
  intro z hz
  apply (show ξ z ∈ D ↔ ‖ξ z‖ ≤ 1 by simp [D, Metric.mem_closedBall, dist_zero_right]).mpr
  rw [xi_norm]
  apply (div_le_one (by positivity : 0 < 1+‖z‖^2)).mpr
  nlinarith [sq_nonneg (‖z‖-1)]

private theorem xi_shrink (z : ℂ) (hne : z ≠ 0) : ‖ξ z‖ < ‖z‖ := by
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hne
  rw [xi_norm]
  apply (div_lt_iff₀ (by positivity : 0 < 1+‖z‖^2)).mpr
  nlinarith [mul_pos hp (sq_pos_of_pos hp)]

private theorem xi_cycle (z : ℂ) (he : ξ (ξ z) = z) : z = 0 := by
  by_contra hn
  have hξ : ξ z ≠ 0 := by
    intro h
    rw [h, xi_zero] at he
    exact hn he.symm
  have h1 := xi_shrink z hn
  have h2 := xi_shrink (ξ z) hξ
  rw [he] at h2
  linarith

private theorem g_mem : G ∈ U0 := by
  refine ⟨fun _ => ξ, (fun _ => ⟨xi_cont.continuousOn, xi_maps⟩), ?_, ?_⟩
  · intro i
    refine ⟨0, ⟨by simp [D], by simp [xi_zero]⟩, ?_⟩
    intro z hz
    exact xi_cycle z hz.2
  · intro i x hx
    rfl

private theorem sq_game_nash (η : Fin 2 → ℂ → ℂ) (x : Fin 2 → ℂ)
    (hx : x ∈ X) (he : ∀ i, x i = η i (x (i+1))) :
    IsNash (fun i y => -‖y i - η i (y (i+1))‖^2) x := by
  refine ⟨hx, ?_⟩
  intro i z hz
  have hi : i+1 ≠ i := by fin_cases i <;> decide
  simp only [Function.update_self, Function.update_of_ne hi, ← he i, sub_self,
    norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero]
  exact neg_nonpos.mpr (sq_nonneg _)

private theorem g_nash_zero : IsNash G 0 := by
  apply sq_game_nash (fun _ => ξ)
  · intro i hi
    simp [D]
  · intro i
    simp [xi_zero]

private theorem forced_rest (F : (Fin 2 → ℂ) → Game → (Fin 2 → ℂ))
    (hF : Uncoupled U0 F) (hN : NashConvergent U0 F)
    (i : Fin 2) (a : ℂ) (ha : a ∈ D) :
    F (fun j => if j = i then ξ a else a) G i = 0 := by
  let η : Fin 2 → ℂ → ℂ := fun j => if j = i then ξ else fun _ => a
  let H : Game := fun j x => -‖x j - η j (x (j+1))‖^2
  let x : Fin 2 → ℂ := fun j => if j = i then ξ a else a
  have hH : H ∈ U0 := by
    refine ⟨η, ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · simp only [η, hj, if_pos]
        exact ⟨xi_cont.continuousOn, xi_maps⟩
      · simp only [η, hj, if_neg]
        exact ⟨continuousOn_const, fun _ _ => ha⟩
    · intro j
      fin_cases i <;> fin_cases j <;> simp only [η, Fin.reduceAdd, Fin.mk_one,
        Fin.isValue, ↓reduceIte]
      · exact ⟨ξ a, ⟨xi_maps ha, rfl⟩, fun z hz => hz.2.symm⟩
      · exact ⟨a, ⟨ha, rfl⟩, fun z hz => hz.2.symm⟩
      · exact ⟨a, ⟨ha, rfl⟩, fun z hz => hz.2.symm⟩
      · exact ⟨ξ a, ⟨xi_maps ha, rfl⟩, fun z hz => hz.2.symm⟩
    · intro j y hy
      rfl
  have hx : x ∈ X := by
    intro j hj
    dsimp [x]
    split_ifs <;> first | exact xi_maps ha | exact ha
  have hn : IsNash H x := by
    apply sq_game_nash η x hx
    intro j
    fin_cases i <;> fin_cases j <;> simp [x, η]
  have hr := (hN H hH x hn).1
  have he := hF G g_mem H hH i (by intro y hy; simp [G,H,η]) x hx
  rw [he]
  exact congrFun hr i

private theorem xi_deriv : HasFDerivAt ξ (ContinuousLinearMap.id ℝ ℂ) 0 := by
  unfold ξ
  have hd : HasFDerivAt (fun z : ℂ => (1/(1+Complex.normSq z) : ℝ))
      (0 : ℂ →L[ℝ] ℝ) 0 := by
    have hnorm : HasFDerivAt (fun z : ℂ => Complex.normSq z) (0 : ℂ →L[ℝ] ℝ) 0 := by
      have hre : HasFDerivAt (fun z : ℂ => z.re) Complex.reCLM 0 := Complex.reCLM.hasFDerivAt
      have him : HasFDerivAt (fun z : ℂ => z.im) Complex.imCLM 0 := Complex.imCLM.hasFDerivAt
      simpa [Pi.add_def, Pi.mul_def, Complex.normSq_apply] using (hre.mul hre).add (him.mul him)
    have hden := (hasFDerivAt_const (1 : ℝ) (0 : ℂ)).add hnorm
    have hinv := (hasFDerivAt_inv (by norm_num : 1+Complex.normSq (0 : ℂ) ≠ 0)).comp (0 : ℂ)
      (show HasFDerivAt (fun z => 1+Complex.normSq z) (0 : ℂ →L[ℝ] ℝ) 0 by
        simpa [Pi.add_def] using hden)
    simpa only [one_div, ContinuousLinearMap.comp_zero, Function.comp_def] using hinv
  have hc := Complex.ofRealCLM.hasFDerivAt.comp (0 : ℂ) hd
  simpa [Pi.mul_def, Function.comp_def] using hc.mul (hasFDerivAt_id (𝕜 := ℝ) (0 : ℂ))

theorem solution (F : (Fin 2 → ℂ) → Game → (Fin 2 → ℂ)) (hF : Uncoupled U0 F) :
    ¬ NashConvergent U0 F := by
  intro hN
  have hr := forced_rest F hF hN
  have hs := (hN G g_mem 0 g_nash_zero).2.2.1
  have hX : X ∈ nhds (0 : Fin 2 → ℂ) := by
    apply Metric.mem_nhds_iff.mpr
    refine ⟨1, by norm_num, ?_⟩
    intro x hx
    have hx' : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
    intro i hi
    apply (show x i ∈ D ↔ ‖x i‖ ≤ 1 by simp [D, Metric.mem_closedBall, dist_zero_right]).mpr
    exact (norm_le_pi_norm x i).trans hx'.le
  have hdf : DifferentiableAt ℝ (fun x => F x G) 0 :=
    ((hN G g_mem 0 g_nash_zero).2.1.differentiableOn_one 0 g_nash_zero.1).differentiableAt hX
  let v : Fin 2 → ℂ := fun _ => 1
  have hkernel : fderiv ℝ (fun x => F x G) 0 v = 0 := by
    funext i
    let u : ℝ → (Fin 2 → ℂ) := fun t j => if j = i then ξ (t : ℂ) else (t : ℂ)
    have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) 0 := by
      convert! Complex.ofRealCLM.hasFDerivAt.hasDerivAt (x := (0 : ℝ)) using 1
    have hu : HasDerivAt u v 0 := by
      apply hasDerivAt_pi.mpr
      intro j
      by_cases hj : j = i
      · have hxid : HasFDerivAt ξ (ContinuousLinearMap.id ℝ ℂ) ((0 : ℝ) : ℂ) := by
          simpa using xi_deriv
        simpa [u, v, hj, Function.comp_def] using hxid.comp_hasDerivAt 0 ht
      · simpa [u, v, hj] using ht
    have hu0 : u 0 = 0 := by ext j; simp [u, xi_zero]
    have hdfu : HasFDerivAt (fun x => F x G) (fderiv ℝ (fun x => F x G) 0) (u 0) := by
      rw [hu0]
      exact hdf.hasFDerivAt
    have hd := hdfu.comp_hasDerivAt 0 hu
    have hdi := hasDerivAt_pi.mp hd i
    have he : (fun t => F (u t) G i) =ᶠ[nhds (0 : ℝ)] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
      have ha : (t : ℂ) ∈ D := by
        have hh : |t| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using ht
        simpa [D, Metric.mem_closedBall, dist_zero_right, Complex.norm_real] using hh.le
      exact hr i (t : ℂ) ha
    have hz : HasDerivAt (fun t => F (u t) G i) (0 : ℂ) 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq he
    exact hdi.unique hz
  have hwithin : fderivWithin ℝ (fun x => F x G) X 0 = fderiv ℝ (fun x => F x G) 0 :=
    hdf.fderivWithin (uniqueDiffWithinAt_of_mem_nhds hX)
  have hv : v = Pi.single (0 : Fin 2) (1 : ℂ) + Pi.single (1 : Fin 2) (1 : ℂ) := by
    ext i
    fin_cases i <;> simp [v]
  have hrow (p : Fin 2 × Fin 2) : jac F G 0 p (0,0) + jac F G 0 p (1,0) = 0 := by
    rw [hv, map_add] at hkernel
    have hh := congrArg (fun x : Fin 2 → ℂ => coord p.2 (x p.1)) hkernel
    rcases p with ⟨i,k⟩
    fin_cases k <;> simpa [jac, jacOf, hwithin, basisVec, coord] using hh
  let M := Matrix.reindex finProdFinEquiv finProdFinEquiv (jac F G 0)
  have hm : M *ᵥ (![1,0,1,0] : Fin 4 → ℝ) = 0 := by
    ext i
    fin_cases i <;>
      simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.reindex_apply,
        finProdFinEquiv, Fin.divNat, Fin.modNat, hrow]
  have hdet : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨![1,0,1,0], by intro he; have hh := congrFun he 0; norm_num at hh, hm⟩
  have hc : (M.map (algebraMap ℝ ℂ)).det = 0 := by
    have hh := (algebraMap ℝ ℂ).map_det M
    change (M.det : ℂ) = (M.map (algebraMap ℝ ℂ)).det at hh
    rw [← hh, hdet]
    simp
  have hspec : (0 : ℂ) ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) := by
    simpa [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det] using hc
  have hh := hs 0 hspec
  norm_num at hh

#print axioms solution


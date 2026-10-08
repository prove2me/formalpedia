-- Prove2me | solution 1 for UncoupledDyn.Finite.jacobian_diag_zero
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:44:14.961273+00:00
-- url     : https://prove2.me/submissions/baa73a27-e4b6-4bcb-a89a-70745836e453

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix
import Definitions.Def_UncoupledDyn_Finite_Setting

open UncoupledDyn.Finite Filter Topology

set_option maxHeartbeats 1000000

private theorem profiles :
    (Finset.univ : Finset Profile) =
      {![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1],
       ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1]} := by decide

private theorem payoff_formula (a x : Fin 3 → ℝ) (i : Fin 3) :
    expPayoff (jordanGame a) i x =
      a i * x i * (1 - x (i+1)) + (1-x i) * x (i+1) := by
  unfold expPayoff
  rw [profiles]
  fin_cases i <;>
    norm_num [Fin.prod_univ_succ, jordanGame, Fin.add_def, Matrix.cons_val,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> ring!

private theorem nash_of_indifferent (a x : Fin 3 → ℝ) (hx : x ∈ X)
    (ha : ∀ i, a i * (1-x (i+1)) = x (i+1)) : IsNash (jordanGame a) x := by
  refine ⟨hx, ?_⟩
  intro i y hy
  have hne : i+1 ≠ i := by fin_cases i <;> decide
  rw [payoff_formula, payoff_formula]
  simp only [Function.update_self, Function.update_of_ne hne]
  rw [mul_right_comm (a i) y, mul_right_comm (a i) (x i), ha i]
  nlinarith

private theorem half_mem : (fun _ : Fin 3 => (1/2 : ℝ)) ∈ X := by
  intro j hj
  constructor <;> norm_num

private theorem gamma_nash : IsNash Gamma0 (fun _ => 1/2) := by
  apply nash_of_indifferent _ _ half_mem
  intro i; norm_num

private theorem half_nhds : X ∈ nhds (fun _ : Fin 3 => (1/2 : ℝ)) :=
  set_pi_mem_nhds Set.finite_univ (fun _ _ => Icc_mem_nhds (by norm_num) (by norm_num))

theorem solution (U : Set Game) (hU : ∀ G ∈ U, ∃! x, IsNash G x)
    (F : (Fin 3 → ℝ) → Game → (Fin 3 → ℝ))
    (hnbhd : ∃ η > 0, ∀ a : Fin 3 → ℝ, IsNear (jordanGame a) Gamma0 η → jordanGame a ∈ U)
    (hF : Uncoupled U F) (hNC : NashConvergent U F) :
    (∀ i : Fin 3, ∀ᶠ y in nhds (1 / 2 : ℝ),
        F (Function.update (fun _ : Fin 3 => (1 / 2 : ℝ)) i y) Gamma0 i = 0) ∧
    (∀ i : Fin 3, jac F Gamma0 (fun _ => 1 / 2) i i = 0) ∧
    (jac F Gamma0 (fun _ => 1 / 2)).trace = 0 := by
  classical
  obtain ⟨η, hη, hnb⟩ := hnbhd
  have hG : Gamma0 ∈ U := hnb (fun _ => 1) (by intro i s; simp [Gamma0, hη])
  have haxis : ∀ i : Fin 3, ∀ᶠ y in nhds (1/2 : ℝ),
      F (Function.update (fun _ : Fin 3 => (1/2 : ℝ)) i y) Gamma0 i = 0 := by
    intro i
    have ht : Tendsto (fun y : ℝ => y/(1-y)) (nhds (1/2)) (nhds 1) := by
      convert! (continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by norm_num : (1:ℝ)-(1/2) ≠ 0)).tendsto using 1 <;> norm_num
    have he : ∀ᶠ y in nhds (1/2 : ℝ), |y/(1-y)-1| < η := by
      have hh := (ht.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
      exact hh.eventually (by simpa using eventually_lt_nhds hη)
    filter_upwards [he, Ioo_mem_nhds (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)] with y he hy
    let a : Fin 3 → ℝ := fun j => if j+1=i then y/(1-y) else 1
    let x : Fin 3 → ℝ := Function.update (fun _ => 1/2) i y
    have hx : x ∈ X := by
      intro j hj
      by_cases hji : j=i
      · subst j; simpa [x] using ⟨hy.1.le,hy.2.le⟩
      · simp [x, Function.update_of_ne hji]; norm_num
    have ha : ∀ j, a j * (1-x (j+1)) = x (j+1) := by
      intro j
      by_cases hj : j+1=i
      · simp [a,x,hj]
        field_simp [ne_of_gt (sub_pos.mpr hy.2)]
      · simp [a,x,hj,Function.update_of_ne hj]
        norm_num
    have hnear : IsNear (jordanGame a) Gamma0 η := by
      intro j s
      simp only [Gamma0, jordanGame]
      by_cases h1 : s j = 0 ∧ s (j+1) = 1
      · simp only [if_pos h1]
        by_cases hji : j+1=i
        · simpa only [a, if_pos hji] using he
        · simpa only [a, if_neg hji, sub_self, abs_zero] using hη
      · by_cases h2 : s j = 1 ∧ s (j+1) = 0
        · simpa only [if_neg h1, if_pos h2, sub_self, abs_zero] using hη
        · simpa only [if_neg h1, if_neg h2, sub_self, abs_zero] using hη
    have hGa := hnb a hnear
    have hsame : (jordanGame a) i = Gamma0 i := by
      have hi : i+1 ≠ i := by fin_cases i <;> decide
      ext s
      simp [jordanGame,Gamma0,a,hi]
    have hrest := (hNC (jordanGame a) hGa x (nash_of_indifferent a x hx ha)).1
    rw [← hF (jordanGame a) hGa Gamma0 hG i hsame x hx]
    exact congrFun hrest i
  have hdiag : ∀ i : Fin 3, jac F Gamma0 (fun _ => 1/2) i i = 0 := by
    intro i
    have hd := ((hNC Gamma0 hG _ gamma_nash).2.1.differentiableOn (by norm_num)).differentiableAt half_nhds
    have hf : HasFDerivAt (fun y => F y Gamma0) (fderiv ℝ (fun y => F y Gamma0) (fun _ => 1/2))
        (Function.update (fun _ : Fin 3 => (1/2 : ℝ)) i (1/2)) := by
      simpa only [Function.update_eq_self] using hd.hasFDerivAt
    have hu := (hasFDerivAt_update (𝕜 := ℝ) (fun _ : Fin 3 => (1/2 : ℝ)) (i := i) (1/2 : ℝ)).hasDerivAt
    have hh := ((hasFDerivAt_apply i (F (Function.update (fun _ : Fin 3 => (1/2 : ℝ)) i (1/2)) Gamma0)).comp (1/2 : ℝ)
      (hf.comp_hasDerivAt (1/2 : ℝ) hu)).hasDerivAt
    have hz : HasDerivAt (fun y => F (Function.update (fun _ : Fin 3 => (1/2 : ℝ)) i y) Gamma0 i) 0 (1/2 : ℝ) :=
      (hasDerivAt_const (1/2 : ℝ) (0 : ℝ)).congr_of_eventuallyEq (haxis i)
    have he := hh.unique hz
    have hsingle : (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) :
        ℝ →L[ℝ] (Fin 3 → ℝ)) (1 : ℝ) =
        (Pi.single i (1 : ℝ) : Fin 3 → ℝ) := by
      ext j
      change ((Pi.single i (ContinuousLinearMap.id ℝ ℝ) : Fin 3 → ℝ →L[ℝ] ℝ) j) 1 =
        (Pi.single i (1 : ℝ) : Fin 3 → ℝ) j
      by_cases h : j=i <;> simp [h]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, ContinuousLinearMap.pi_apply,
      Pi.single_apply] at he
    rw [hsingle] at he
    unfold jac
    rw [fderivWithin_of_mem_nhds half_nhds]
    exact he
  refine ⟨haxis,hdiag,?_⟩
  change (∑ i, jac F Gamma0 (fun _ => 1/2) i i) = 0
  simp only [hdiag, Finset.sum_const_zero]

#print axioms solution

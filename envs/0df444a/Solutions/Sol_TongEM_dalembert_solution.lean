-- Prove2me | solution 1 for TongEM.dalembert_solution
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T02:57:20.804433+00:00
-- url     : https://prove2.me/submissions/cb3c7c9b-c5fe-44eb-91b0-04186fa08355

import Definitions.Def_TongEM_wave_ops

open TongEM Larmor

namespace DAux

lemma pd_comp (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (j : Fin 3) (y : Vec) :
    pd j (fun y : Vec => φ (y 0)) y = (EuclideanSpace.single j (1 : ℝ) : Vec) 0 * deriv φ (y 0) := by
  unfold pd
  have hlin : HasFDerivAt (fun y : Vec => y 0) (EuclideanSpace.proj (0 : Fin 3) : Vec →L[ℝ] ℝ) y := by
    rw [show (fun y : Vec => y 0) = ⇑(EuclideanSpace.proj (0 : Fin 3) : Vec →L[ℝ] ℝ) from by
      funext z; simp]
    exact (EuclideanSpace.proj (0 : Fin 3) : Vec →L[ℝ] ℝ).hasFDerivAt
  have h := (hφ (y 0)).hasDerivAt.comp_hasFDerivAt y hlin
  rw [show (fun y : Vec => φ (y 0)) = φ ∘ (fun y : Vec => y 0) from rfl, h.fderiv]
  simp [mul_comm]

lemma lap_comp (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (y : Vec) :
    lap (fun y : Vec => φ (y 0)) y = deriv (deriv φ) (y 0) := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφ' : Differentiable ℝ (deriv φ) := (hφ.iterate_deriv' 1 1).differentiable (by norm_num)
  unfold lap
  have hj : ∀ j : Fin 3, pd j (fun y : Vec => φ (y 0)) =
      fun y : Vec => (fun z => (EuclideanSpace.single j (1 : ℝ) : Vec) 0 * deriv φ z) (y 0) := by
    intro j; funext y; exact pd_comp φ hφd j y
  simp_rw [hj]
  rw [Fin.sum_univ_three]
  rw [pd_comp _ ((hφ'.const_mul _)) 0 y, pd_comp _ ((hφ'.const_mul _)) 1 y,
    pd_comp _ ((hφ'.const_mul _)) 2 y]
  simp [deriv_const_mul_field']

end DAux

open DAux in
theorem solution (c : ℝ) (hc : c ≠ 0) (f g : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (t : ℝ) (x : Vec) :
    boxScalar c (fun s y => f (y 0 - c * s) + g (y 0 + c * s)) t x = 0 := by
  have hf2 : ContDiff ℝ 2 f := contDiff_infty.mp hf 2
  have hg2 : ContDiff ℝ 2 g := contDiff_infty.mp hg 2
  have hfd : Differentiable ℝ f := hf2.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg2.differentiable (by norm_num)
  have hf' : Differentiable ℝ (deriv f) := (hf2.iterate_deriv' 1 1).differentiable (by norm_num)
  have hg' : Differentiable ℝ (deriv g) := (hg2.iterate_deriv' 1 1).differentiable (by norm_num)
  -- spatial part
  have hΦ : ∀ s : ℝ, ContDiff ℝ 2 (fun z => f (z - c * s) + g (z + c * s)) := fun s =>
    (hf2.comp (contDiff_id.sub contDiff_const)).add (hg2.comp (contDiff_id.add contDiff_const))
  have hlap : lap (fun y : Vec => f (y 0 - c * t) + g (y 0 + c * t)) x =
      deriv (deriv f) (x 0 - c * t) + deriv (deriv g) (x 0 + c * t) := by
    rw [lap_comp (fun z => f (z - c * t) + g (z + c * t)) (hΦ t) x]
    have e1 : deriv (fun z => f (z - c * t) + g (z + c * t)) =
        fun z => deriv f (z - c * t) + deriv g (z + c * t) := by
      funext z
      have h1 := ((hfd (z - c * t)).hasDerivAt.comp z ((hasDerivAt_id z).sub_const (c * t)))
      have h2 := ((hgd (z + c * t)).hasDerivAt.comp z ((hasDerivAt_id z).add_const (c * t)))
      simpa using (h1.fun_add h2).deriv
    rw [e1]
    have h1 := ((hf' (x 0 - c * t)).hasDerivAt.comp (x 0) ((hasDerivAt_id (x 0)).sub_const (c * t)))
    have h2 := ((hg' (x 0 + c * t)).hasDerivAt.comp (x 0) ((hasDerivAt_id (x 0)).add_const (c * t)))
    simpa using (h1.fun_add h2).deriv
  -- time part
  have htime : deriv (fun s => deriv (fun r => f (x 0 - c * r) + g (x 0 + c * r)) s) t =
      c ^ 2 * (deriv (deriv f) (x 0 - c * t) + deriv (deriv g) (x 0 + c * t)) := by
    have e1 : (fun s => deriv (fun r => f (x 0 - c * r) + g (x 0 + c * r)) s) =
        fun s => -c * deriv f (x 0 - c * s) + c * deriv g (x 0 + c * s) := by
      funext s
      have h1 := (hfd (x 0 - c * s)).hasDerivAt.comp s (((hasDerivAt_id s).const_mul c).const_sub (x 0))
      have h2 := (hgd (x 0 + c * s)).hasDerivAt.comp s (((hasDerivAt_id s).const_mul c).const_add (x 0))
      have := (h1.fun_add h2).deriv
      simp only [Function.comp_def, id] at this
      rw [this]; ring
    rw [e1]
    have h1 := (hf' (x 0 - c * t)).hasDerivAt.comp t (((hasDerivAt_id t).const_mul c).const_sub (x 0))
    have h2 := (hg' (x 0 + c * t)).hasDerivAt.comp t (((hasDerivAt_id t).const_mul c).const_add (x 0))
    have := ((h1.const_mul (-c)).fun_add (h2.const_mul c)).deriv
    simp only [Function.comp_def, id] at this
    rw [this]; ring
  unfold boxScalar
  rw [htime, hlap]
  field_simp
  ring

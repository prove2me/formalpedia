-- Prove2me | solution 1 for UniversalSubmod.concavity_segment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:47:07.077224+00:00
-- url     : https://prove2.me/submissions/3ce95e51-691a-471b-80de-a80de7ea42f4

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Theorems.Thm_UniversalSubmod_eq_2_second_partials

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Concavity

open NonmonotoneSubmod.Shared

variable {n : ℕ}

lemma F_contDiff (f : Finset (Fin n) → ℝ) : ContDiff ℝ 2 (F f) := by
  unfold F
  refine ContDiff.sum (fun S _ => ?_)
  refine ContDiff.mul contDiff_const ?_
  have : ∀ l, ContDiff ℝ 2 (fun y : Fin n → ℝ => if l ∈ S then y l else 1 - y l) := by
    intro l; by_cases h : l ∈ S <;> simp [h] <;> fun_prop
  fun_prop

lemma G_diff (f : Finset (Fin n) → ℝ) (v : Fin n → ℝ) :
    Differentiable ℝ (fun y => fderiv ℝ (F f) y v) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ (F f)) := (F_contDiff f).fderiv_right (by norm_num)
  exact (h1.differentiable (by norm_num)).clm_apply (differentiable_const v)

lemma v_eq (v : Fin n → ℝ) : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

lemma first_dir (f : Finset (Fin n) → ℝ) (y v : Fin n → ℝ) :
    fderiv ℝ (F f) y v = ∑ j, v j * fderiv ℝ (F f) y (Pi.single j (1 : ℝ)) := by
  conv_lhs => rw [v_eq v]
  simp [map_sum]

lemma second_dir (f : Finset (Fin n) → ℝ) (x v : Fin n → ℝ) :
    fderiv ℝ (fun y => fderiv ℝ (F f) y v) x v =
      ∑ i, ∑ j, v i * v j *
        fderiv ℝ (fun y => fderiv ℝ (F f) y (Pi.single j (1 : ℝ))) x (Pi.single i (1 : ℝ)) := by
  have e : (fun y => fderiv ℝ (F f) y v) =
      fun y => ∑ j, v j * fderiv ℝ (F f) y (Pi.single j (1 : ℝ)) :=
    funext (fun y => first_dir f y v)
  rw [e, fderiv_fun_sum (fun j _ => ((G_diff f _).const_mul (v j)) x)]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  have e2 : ∀ j, fderiv ℝ (fun y => v j * fderiv ℝ (F f) y (Pi.single j (1 : ℝ))) x =
      v j • fderiv ℝ (fun y => fderiv ℝ (F f) y (Pi.single j (1 : ℝ))) x := by
    intro j
    rw [fderiv_const_mul (G_diff f _ x)]
  simp only [e2, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have e3 : ∀ j, fderiv ℝ (fun y => fderiv ℝ (F f) y (Pi.single j (1 : ℝ))) x v =
      ∑ i, v i * fderiv ℝ (fun y => fderiv ℝ (F f) y (Pi.single j (1 : ℝ))) x
        (Pi.single i (1 : ℝ)) := by
    intro j
    conv_lhs => rw [v_eq v]
    simp [map_sum]
  simp only [e3]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

end UniversalSubmod.Dev.Concavity

namespace UniversalSubmod

open NonmonotoneSubmod.Shared

theorem chk_concavity_segment {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) :
    (∀ x v : Fin n → ℝ, (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, 0 ≤ v i) →
      fderiv ℝ (fun y => fderiv ℝ (F f) y v) x v =
        ∑ i, ∑ j, v i * v j *
          fderiv ℝ (fun y => fderiv ℝ (F f) y (Pi.single j (1 : ℝ))) x (Pi.single i (1 : ℝ)) ∧
      fderiv ℝ (fun y => fderiv ℝ (F f) y v) x v ≤ 0) ∧
    (∀ x y : Fin n → ℝ, (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, x i ≤ y i) →
      ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ => F f (x + t • (y - x)))) := by
  have part1 : ∀ x v : Fin n → ℝ, (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, 0 ≤ v i) →
      fderiv ℝ (fun y => fderiv ℝ (F f) y v) x v ≤ 0 := by
    intro x v hx hv
    rw [Dev.Concavity.second_dir]
    refine Finset.sum_nonpos (fun i _ => Finset.sum_nonpos (fun j _ => ?_))
    have := (eq_2_second_partials f hf0 hf x hx i j).2.2.1
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hv i) (hv j)) this
  refine ⟨fun x v hx hv => ⟨Dev.Concavity.second_dir f x v, part1 x v hx hv⟩, ?_⟩
  intro x y hx hy hxy
  set v : Fin n → ℝ := y - x with hvdef
  have hv : ∀ i, 0 ≤ v i := fun i => by simp [hvdef, hxy i]
  have hz : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hF : Differentiable ℝ (F f) := (Dev.Concavity.F_contDiff f).differentiable (by norm_num)
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => F f (x + t • v))
      (fderiv ℝ (F f) (x + t • v) v) t := fun t =>
    by
      have h := (hF (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hz t)
      exact h
  have hdg : deriv (fun t : ℝ => F f (x + t • v)) =
      fun t => fderiv ℝ (F f) (x + t • v) v := funext (fun t => (hg t).deriv)
  have hg2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => fderiv ℝ (F f) (x + t • v) v)
      (fderiv ℝ (fun y => fderiv ℝ (F f) y v) (x + t • v) v) t := fun t =>
    by
      have h := ((Dev.Concavity.G_diff f v) (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hz t)
      exact h
  refine concaveOn_of_deriv2_nonpos' (convex_Icc 0 1) ?_ ?_ ?_
  · exact (fun t _ => (hg t).differentiableAt.differentiableWithinAt)
  · rw [hdg]
    exact (fun t _ => (hg2 t).differentiableAt.differentiableWithinAt)
  · intro t ht
    have : deriv^[2] (fun t : ℝ => F f (x + t • v)) t =
        fderiv ℝ (fun y => fderiv ℝ (F f) y v) (x + t • v) v := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
      rw [hdg]
      exact (hg2 t).deriv
    rw [this]
    apply part1 _ v _ hv
    intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hvdef, Pi.sub_apply]
    have h0 := (hx i).1; have h1 := (hy i).2; have h2 := hxy i
    constructor
    · nlinarith [mul_nonneg ht.1 (sub_nonneg.2 h2)]
    · nlinarith [mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 h2)]

end UniversalSubmod
end

theorem solution : type_of% @UniversalSubmod.chk_concavity_segment := @UniversalSubmod.chk_concavity_segment

-- Prove2me | solution 1 for WeightedRainbowCycle.Weighted.russo_margulis
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:46:58.761639+00:00
-- url     : https://prove2.me/submissions/a981161d-01bf-41c0-82cc-8ec8628034a0

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Model
import Theorems.Thm_DiffNeighbors_Bias_first_partial

section
set_option autoImplicit false

namespace WeightedRainbowCycle.Dev.RM

open DiffNeighbors.Bias

theorem mlExt_diff {S : Type*} [Fintype S] [DecidableEq S] (h : (S → Bool) → ℝ) :
    Differentiable ℝ (fun w : S → ℝ => mlExt h w) := by
  unfold mlExt
  refine Differentiable.fun_sum fun z _ => ?_
  refine Differentiable.mul_const ?_ _
  have : ∀ j, Differentiable ℝ (fun w : S → ℝ => if z j then w j else 1 - w j) := by
    intro j
    by_cases hz : z j
    · simp only [hz, if_true]; fun_prop
    · have : z j = false := by simpa using hz
      simp only [this]; simp only [Bool.false_eq_true, if_false]; fun_prop
  intro w
  exact (HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ => ((this j) w).hasFDerivAt)).differentiableAt

theorem mlExt_lin {S : Type*} [Fintype S] [DecidableEq S] (f : S → (S → Bool) → ℝ) (w : S → ℝ) :
    mlExt (fun z => ∑ c, f c z) w = ∑ c, mlExt (f c) w := by
  unfold mlExt
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem mlExt_sub {S : Type*} [Fintype S] [DecidableEq S] (f g : (S → Bool) → ℝ) (w : S → ℝ) :
    mlExt (fun z => f z - g z) w = mlExt f w - mlExt g w := by
  unfold mlExt
  simp only [mul_sub, Finset.sum_sub_distrib]

end WeightedRainbowCycle.Dev.RM

namespace WeightedRainbowCycle.Weighted

theorem chk_russo_margulis {S : Type*} [Fintype S] [DecidableEq S]
    (f : (S → Bool) → ℝ) (q : ℝ) :
    HasDerivAt (fun p => DiffNeighbors.Bias.bernExp p f)
      (DiffNeighbors.Bias.bernExp q (fun z => ∑ c : S,
        (f (Function.update z c true) - f (Function.update z c false)))) q := by
  open DiffNeighbors.Bias WeightedRainbowCycle.Dev.RM in
  set w0 : S → ℝ := fun _ => q with hw0
  have hF := (mlExt_diff f).differentiableAt (x := w0)
  have hL := hF.hasFDerivAt
  set L := fderiv ℝ (fun w : S → ℝ => mlExt f w) w0 with hLdef
  have hdiag : HasDerivAt (fun t : ℝ => fun _ : S => t) (fun _ => (1:ℝ)) q :=
    hasDerivAt_pi.mpr fun _ => hasDerivAt_id q
  have h1 : HasDerivAt (fun p => bernExp p f) (L (fun _ => 1)) q := by
    have := hL.comp_hasDerivAt q hdiag
    exact this
  have h2 : (fun _ : S => (1:ℝ)) = ∑ c : S, Pi.single c (1:ℝ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  have h3 : ∀ c : S, L (Pi.single c 1) =
      mlExt (fun z => f (Function.update z c true)) w0
        - mlExt (fun z => f (Function.update z c false)) w0 := by
    intro c
    have hu : HasDerivAt (fun t : ℝ => Function.update w0 c t) (Pi.single c (1:ℝ)) (w0 c) :=
      hasDerivAt_update w0 c (w0 c)
    have hL' : HasFDerivAt (fun w : S → ℝ => mlExt f w) L (Function.update w0 c (w0 c)) := by
      rwa [Function.update_eq_self]
    have h4 := hL'.comp_hasDerivAt (w0 c) hu
    have h5 := first_partial f w0 c
    exact h4.unique h5
  have h6 : bernExp q (fun z => ∑ c : S,
        (f (Function.update z c true) - f (Function.update z c false)))
      = L (fun _ => 1) := by
    rw [h2, map_sum]
    unfold bernExp
    rw [mlExt_lin]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [h3 c, mlExt_sub]
  rw [h6]
  exact h1

end WeightedRainbowCycle.Weighted
end

theorem solution : type_of% @WeightedRainbowCycle.Weighted.chk_russo_margulis := @WeightedRainbowCycle.Weighted.chk_russo_margulis

-- Prove2me | solution 1 for WheelerDeWittSuperspace.poisson_eq_zero_of_sitewise
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T20:52:18.191445+00:00
-- url     : https://prove2.me/submissions/7bc77d07-ff97-4cdc-9644-42b4152170f8

import Definitions.Def_WheelerDeWittSuperspace
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

/-- A directional derivative vanishes along any direction in which the function is
constant. No differentiability is needed: otherwise `fderiv` is `0` anyway. -/
theorem fderiv_apply_eq_zero_of_line_invariant {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (w v : E)
    (hf : ∀ t : ℝ, f (w + t • v) = f w) : fderiv ℝ f w v = 0 := by
  by_cases hd : DifferentiableAt ℝ f w
  · have h1 : HasDerivAt (fun t : ℝ => f (w + t • v)) (fderiv ℝ f w v) 0 := by
      have hl : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
      have hd' : HasFDerivAt f (fderiv ℝ f w) (w + (0 : ℝ) • v) := by simpa using hd.hasFDerivAt
      exact hd'.comp_hasDerivAt (0 : ℝ) hl
    have h2 : HasDerivAt (fun t : ℝ => f (w + t • v)) 0 0 := by
      simp_rw [hf]; exact hasDerivAt_const _ _
    exact h1.unique h2
  · simp [fderiv_zero_of_not_differentiableAt hd]

/-- The coordinate direction at site `z` has no component at any other site. -/
theorem coordDir_apply_of_ne {X : Type*} [DecidableEq X] {z x : X} (hzx : z ≠ x)
    (a b : Fin 3) : coordDir z a b x = 0 := by
  funext i j
  simp [coordDir, Ne.symm hzx]

/-- A phase-space function is *local at `x`* if it depends only on `(h(x), p(x))`. -/
def IsLocalAt {X : Type*} (F : Phase X → ℝ) (x : X) : Prop :=
  ∀ w w' : Phase X, w.1 x = w'.1 x → w.2 x = w'.2 x → F w = F w'

/-- A function local at `x` has vanishing metric and momentum derivatives at every
other site. -/
theorem IsLocalAt.fderiv_eq_zero {X : Type*} [Fintype X] [DecidableEq X]
    {F : Phase X → ℝ} {x : X} (hF : IsLocalAt F x) {z : X} (hzx : z ≠ x) (a b : Fin 3)
    (w : Phase X) :
    fderiv ℝ F w (coordDir z a b, 0) = 0 ∧ fderiv ℝ F w (0, coordDir z a b) = 0 := by
  have hc := coordDir_apply_of_ne hzx a b
  refine ⟨fderiv_apply_eq_zero_of_line_invariant F w _ fun t => ?_,
    fderiv_apply_eq_zero_of_line_invariant F w _ fun t => ?_⟩ <;>
  · apply hF <;> simp [hc]

/-- The Poisson bracket of two functions local at distinct sites vanishes identically. -/
theorem poisson_eq_zero_of_isLocalAt {X : Type*} [Fintype X] [DecidableEq X]
    {F G : Phase X → ℝ} {x y : X} (hxy : x ≠ y) (hF : IsLocalAt F x) (hG : IsLocalAt G y)
    (w : Phase X) : poisson F G w = 0 := by
  unfold poisson
  refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun a _ =>
    Finset.sum_eq_zero fun b _ => ?_
  by_cases hzx : z = x
  · subst hzx
    obtain ⟨h1, h2⟩ := hG.fderiv_eq_zero hxy a b w
    simp [h1, h2]
  · obtain ⟨h1, h2⟩ := hF.fderiv_eq_zero hzx a b w
    simp [h1, h2]

/-- The Poisson bracket of any function with itself vanishes. -/
theorem poisson_self {X : Type*} [Fintype X] [DecidableEq X] (F : Phase X → ℝ)
    (w : Phase X) : poisson F F w = 0 := by
  unfold poisson
  exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ =>
    Finset.sum_eq_zero fun _ _ => by ring

/-- With an ultralocal potential, the constraint at `z` is local at `z`. -/
theorem classicalConstraint_isLocalAt {X : Type*} (kappa Lam : ℝ) (R : Config X → X → ℝ)
    (hloc : ∀ z (h h' : Config X), h z = h' z → R h z = R h' z) (z : X) :
    IsLocalAt (classicalConstraint kappa Lam R z) z := by
  intro w w' h1 h2
  simp only [classicalConstraint, potentialAt, metricAt, h1, h2, hloc z w.1 w'.1 h1]

end WheelerDeWittSuperspace

open WheelerDeWittSuperspace

/-- Milestone 7 (ultralocal case is first class): if every potential depends only on
the metric at its own site (the strong-coupling regime), the classical constraints
Poisson-commute everywhere. -/
theorem solution {X : Type*} [Fintype X] [DecidableEq X] (kappa Lam : ℝ)
    (hkappa : kappa ≠ 0)
    (R : Config X → X → ℝ) (hR : ∀ z, ContDiff ℝ 1 (fun h => R h z))
    (hloc : ∀ z (h h' : Config X), h z = h' z → R h z = R h' z)
    (x y : X) (w : Phase X) (hw : IsPhysical w.1) :
    poisson (classicalConstraint kappa Lam R x) (classicalConstraint kappa Lam R y) w = 0 := by
  by_cases hxy : x = y
  · subst hxy; exact poisson_self _ w
  · exact poisson_eq_zero_of_isLocalAt hxy (classicalConstraint_isLocalAt kappa Lam R hloc x)
      (classicalConstraint_isLocalAt kappa Lam R hloc y) w


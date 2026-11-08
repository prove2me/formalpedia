-- Prove2me | solution 1 for RobustToDynamics.step2_outer_ellipsoid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:12:51.375412+00:00
-- url     : https://prove2.me/submissions/44c28398-0034-4429-86dc-d859e04395a3

import Mathlib
import Definitions.Def_RobustToDynamics_polyhedron
import Definitions.Def_RobustToDynamics_ellipsoid
import Definitions.Def_RobustToDynamics_alpha2

open Matrix

namespace Aux_RobEll

lemma lin (c x lx ux : ℝ) (hx1 : lx ≤ x) (hx2 : x ≤ ux) : c * x ≤ max (c * lx) (c * ux) := by
  rcases le_total 0 c with h | h
  · exact le_max_of_le_right (by nlinarith)
  · exact le_max_of_le_left (by nlinarith)

lemma bil (a x y lx ux ly uy : ℝ) (hx1 : lx ≤ x) (hx2 : x ≤ ux) (hy1 : ly ≤ y) (hy2 : y ≤ uy) :
    a * x * y ≤ max (max |a * ux * uy| |a * lx * ly|) (max |a * ux * ly| |a * lx * uy|) := by
  have h1 : a * x * y ≤ max (a * lx * y) (a * ux * y) := by
    have := lin (a * y) x lx ux hx1 hx2
    have e1 : a * x * y = a * y * x := by ring
    have e2 : a * lx * y = a * y * lx := by ring
    have e3 : a * ux * y = a * y * ux := by ring
    rw [e1, e2, e3]; exact this
  have h2 : a * lx * y ≤ max (a * lx * ly) (a * lx * uy) := lin (a * lx) y ly uy hy1 hy2
  have h3 : a * ux * y ≤ max (a * ux * ly) (a * ux * uy) := lin (a * ux) y ly uy hy1 hy2
  have c1 : a * lx * ly ≤ max (max |a * ux * uy| |a * lx * ly|) (max |a * ux * ly| |a * lx * uy|) :=
    le_trans (le_abs_self _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have c2 : a * lx * uy ≤ max (max |a * ux * uy| |a * lx * ly|) (max |a * ux * ly| |a * lx * uy|) :=
    le_trans (le_abs_self _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have c3 : a * ux * ly ≤ max (max |a * ux * uy| |a * lx * ly|) (max |a * ux * ly| |a * lx * uy|) :=
    le_trans (le_abs_self _) (le_trans (le_max_left _ _) (le_max_right _ _))
  have c4 : a * ux * uy ≤ max (max |a * ux * uy| |a * lx * ly|) (max |a * ux * ly| |a * lx * uy|) :=
    le_trans (le_abs_self _) (le_trans (le_max_left _ _) (le_max_left _ _))
  exact le_trans h1 (max_le (le_trans h2 (max_le c1 c2)) (le_trans h3 (max_le c3 c4)))

end Aux_RobEll

open RobustToDynamics in
theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (l u : Fin n → ℝ) :
    (∀ x ∈ Set.Icc l u, x ⬝ᵥ (M *ᵥ x) ≤ alpha2 M l u) ∧
      ∀ {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
        polyhedron A b ⊆ Set.Icc l u → polyhedron A b ⊆ ellipsoid M (alpha2 M l u) := by
  have key : ∀ x ∈ Set.Icc l u, x ⬝ᵥ (M *ᵥ x) ≤ alpha2 M l u := by
    intro x hx
    simp only [dotProduct, mulVec, Finset.mul_sum]
    unfold alpha2
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have e : x i * (M i j * x j) = M i j * x i * x j := by ring
    rw [e]
    exact Aux_RobEll.bil (M i j) (x i) (x j) (l i) (u i) (l j) (u j) (hx.1 i) (hx.2 i)
      (hx.1 j) (hx.2 j)
  refine ⟨key, ?_⟩
  intro m A b hsub x hx
  exact key x (hsub hx)

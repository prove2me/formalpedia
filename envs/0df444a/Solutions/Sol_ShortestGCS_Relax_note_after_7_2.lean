-- Prove2me | solution 1 for ShortestGCS.Relax.note_after_7_2
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-11T12:18:06.23738+00:00
-- url     : https://prove2.me/submissions/fc1da016-8b2f-44c6-89f1-92d8a3bb78f4

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

open ShortestGCS.Relax Matrix
open scoped BigOperators

private theorem linear_dot {n : ℕ} (f : (Fin n → ℝ) →L[ℝ] ℝ) (x : Fin n → ℝ) :
    f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := by
  have hx : (∑ i, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) = x := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  conv_lhs => rw [← hx]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, dotProduct, mul_comm]

private theorem mem_of_valid {n : ℕ} (X : Set (Fin n → ℝ))
    (hXc : IsClosed X) (hXcv : Convex ℝ X) (x : Fin n → ℝ)
    (hx : ∀ ab ∈ validCone X, 0 ≤ ab.1 ⬝ᵥ x + ab.2) : x ∈ X := by
  by_contra hout
  obtain ⟨f, t, hfx, ht⟩ := geometric_hahn_banach_point_closed hXcv hXc hout
  let a : Fin n → ℝ := fun i => f (Pi.single i 1)
  have hvalid : (a, -t) ∈ validCone X := by
    intro z hz
    change 0 ≤ a ⬝ᵥ z + -t
    rw [← linear_dot f z]
    linarith [ht z hz]
  have h := hx (a, -t) hvalid
  change 0 ≤ a ⬝ᵥ x + -t at h
  rw [← linear_dot f x] at h
  linarith

theorem solution {n m : ℕ} (X : Set (Fin n → ℝ)) (Y : Set (Fin m → ℝ))
    (hXc : IsClosed X) (hXcv : Convex ℝ X) (hYc : IsClosed Y) (hYcv : Convex ℝ Y) :
    relaxSet X Y ⊆ {w | w.1 ∈ X ∧ w.2.1 ∈ Y} := by
  intro w hw
  have hconstX : ((0 : Fin n → ℝ), 1) ∈ validCone X := by
    intro x hx
    simp
  have hconstY : ((0 : Fin m → ℝ), 1) ∈ validCone Y := by
    intro y hy
    simp
  constructor
  · apply mem_of_valid X hXc hXcv w.1
    intro ab hab
    simpa using hw ab hab (0, 1) hconstY
  · apply mem_of_valid Y hYc hYcv w.2.1
    intro cd hcd
    simpa using hw (0, 1) hconstX cd hcd

#print axioms solution

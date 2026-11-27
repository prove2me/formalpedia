-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sum_monoNormSq_traceMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:36:28.183927+00:00
-- url     : https://prove2.me/submissions/408185df-b34f-4825-9955-9406256f38fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eval_map_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_aeval_eq_sum_traceMat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_form_sq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {r δ N : ℕ} (g : Fin r → Fin δ → MvPolynomial (Fin (D + 1)) ℤ)
    (hg : ∀ j l, (g j l).IsHomogeneous N) (c : Fin r → ℂ) (l : Fin δ) :
    ∑ i, monoNormSq (adtEnum D N i) *
        ‖((traceMat D N g).map (Int.cast : ℤ → ℂ) *ᵥ c) (finProdFinEquiv (l, i))‖ ^ 2 =
      ∫ w, ‖∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l))‖ ^ 2 ∂(sphProb (D + 1)) := by
  classical
  have reidx : ∀ {X : Type} [AddCommMonoid X] (F : (Fin (D + 1) → ℕ) → X),
      ∑ i, F (adtEnum D N i) = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, F a := by
    intro X _ F
    rw [← Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple (D + 1) N)]
    exact (Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm.sum_comp
      (fun a : (Finset.Nat.antidiagonalTuple (D + 1) N) => F (a : Fin (D + 1) → ℕ))
  let C : (Fin (D + 1) → ℕ) → ℂ := fun a =>
    ∑ j, ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : ℂ) * c j
  have hentry' : ∀ i, ((traceMat D N g).map (Int.cast : ℤ → ℂ) *ᵥ c) (finProdFinEquiv (l, i)) =
      C (adtEnum D N i) := by
    intro i
    first
    | simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, traceMat, Matrix.of_apply,
        Equiv.symm_apply_apply, C]
    | simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.map_apply, traceMat, Matrix.of_apply,
        Equiv.symm_apply_apply, C]
  have hj : ∀ (j : Fin r) (w : Fin (D + 1) → ℂ), eval w (map (Int.castRingHom ℂ) (g j l)) =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N,
        ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : ℂ) * monoC a w := by
    intro j w
    rw [eval_map_int, aeval_eq_sum_traceMat g j l (hg j l) w,
      ← reidx (fun a => ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : ℂ) * monoC a w)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [traceMat, Matrix.of_apply, Equiv.symm_apply_apply, monoC]
  have hint : ∀ w, ∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l)) =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, C a * monoC a w := by
    intro w
    simp only [hj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [C, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc ∑ i, monoNormSq (adtEnum D N i) *
        ‖((traceMat D N g).map (Int.cast : ℤ → ℂ) *ᵥ c) (finProdFinEquiv (l, i))‖ ^ 2
      = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, monoNormSq a * ‖C a‖ ^ 2 := by
        rw [← reidx (fun a => monoNormSq a * ‖C a‖ ^ 2)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hentry' i]
    _ = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, ‖C a‖ ^ 2 * monoNormSq a :=
        Finset.sum_congr rfl fun a _ => mul_comm _ _
    _ = ∫ z, ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, C a * monoC a z‖ ^ 2 ∂(sphProb (D + 1)) :=
        (integral_form_sq D N C).symm
    _ = ∫ w, ‖∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l))‖ ^ 2 ∂(sphProb (D + 1)) := by
        simp only [hint]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

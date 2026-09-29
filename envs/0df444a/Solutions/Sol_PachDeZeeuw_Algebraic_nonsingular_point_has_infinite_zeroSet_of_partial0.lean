-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.nonsingular_point_has_infinite_zeroSet_of_partial0
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:47:03.51677+00:00
-- url     : https://prove2.me/submissions/e7f05aab-d078-4c02-b0cb-2ed71d5f2136

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_mem_PlaneCurveZeroSet
import Theorems.Thm_PachDeZeeuw_Algebraic_nonsingular_point_has_infinite_zeroSet_of_partial1
import Theorems.Thm_PachDeZeeuw_Algebraic_swapPoint_swapPoint

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve
namespace PachDeZeeuw.Algebraic

/-- Swapping coordinates is injective on the plane. -/
lemma swapPoint_injective : Function.Injective swapPoint := by
  intro z₁ z₂ h
  have h' := congrArg swapPoint h
  simpa [swapPoint_swapPoint] using h'

end PachDeZeeuw.Algebraic

open PachDeZeeuw.Algebraic in
theorem solution (h : PlanePoly) {z : Point2}
    (hz : z ∈ PlaneCurveZeroSet h)
    (hnonsing :
      MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (0 : Fin 2) h) ≠ 0) :
    (PlaneCurveZeroSet h).Infinite := by
  let h' : PlanePoly := MvPolynomial.rename (Equiv.swap 0 1) h
  have hz' : swapPoint z ∈ PlaneCurveZeroSet h' := by
    dsimp [h']
    change MvPolynomial.eval (fun i => swapPoint z i)
      (MvPolynomial.rename (Equiv.swap 0 1) h) = 0
    rw [MvPolynomial.eval_rename]
    have hswapCoords :
        ((fun i => swapPoint z i) ∘ (Equiv.swap 0 1)) = fun i => z i := by
      funext i
      fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
    simpa [hswapCoords] using hz
  have h1' :
      MvPolynomial.eval (fun i => swapPoint z i) (MvPolynomial.pderiv (1 : Fin 2) h') ≠ 0 := by
    dsimp [h']
    have hrename :
        MvPolynomial.pderiv (1 : Fin 2) (MvPolynomial.rename (Equiv.swap 0 1) h) =
          MvPolynomial.rename (Equiv.swap 0 1) (MvPolynomial.pderiv (0 : Fin 2) h) := by
      simpa using
        (MvPolynomial.pderiv_rename (Equiv.swap 0 1).injective (x := (0 : Fin 2)) (p := h))
    rw [hrename, MvPolynomial.eval_rename]
    have hswapCoords :
        ((fun i => swapPoint z i) ∘ (Equiv.swap 0 1)) = fun i => z i := by
      funext i
      fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
    simpa [hswapCoords] using hnonsing
  have hinf' := nonsingular_point_has_infinite_zeroSet_of_partial1 h' hz' h1'
  have hswap : swapPoint '' PlaneCurveZeroSet h' = PlaneCurveZeroSet h := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      change MvPolynomial.eval (fun i => swapPoint u i) h = 0
      have hu' : MvPolynomial.eval (fun i => u i)
          (MvPolynomial.rename (Equiv.swap 0 1) h) = 0 := hu
      rw [MvPolynomial.eval_rename] at hu'
      have hswapCoords :
          ((fun i => u i) ∘ (Equiv.swap 0 1)) = fun i => swapPoint u i := by
        funext i
        fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
      rw [hswapCoords] at hu'
      exact hu'
    · intro hw
      refine ⟨swapPoint w, ?_, ?_⟩
      · change MvPolynomial.eval (fun i => swapPoint w i)
          (MvPolynomial.rename (Equiv.swap 0 1) h) = 0
        rw [MvPolynomial.eval_rename]
        have hswapCoords :
            ((fun i => swapPoint w i) ∘ (Equiv.swap 0 1)) = fun i => w i := by
          funext i
          fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
        rw [hswapCoords]
        exact hw
      · simp [swapPoint_swapPoint]
  have hswap_inf : (swapPoint '' PlaneCurveZeroSet h').Infinite :=
    hinf'.image (Function.Injective.injOn swapPoint_injective)
  simpa [hswap] using hswap_inf

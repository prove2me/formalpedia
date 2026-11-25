-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ct_jet_one_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:35:28.714974+00:00
-- url     : https://prove2.me/submissions/a137d9ce-651f-4b94-b765-4235d3c13f2a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_iter_single_eq_polyDeriv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_degree_toFinsupp_ofFn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {ι : Type} [Fintype ι] (β : EuclideanSpace ℂ ι → ℂ)
    (hβ : ContDiff ℂ (⊤ : ℕ∞) β) (c : ℕ)
    (hjet : ∀ α : ι →₀ ℕ, α.degree ≤ c →
      polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) β 0 =
        polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1)
          (fun v : EuclideanSpace ℂ ι => MvPolynomial.eval (fun i => v i) (1 : MvPolynomial ι ℂ)) 0) :
    β 0 = 1 ∧ ∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j β 0 = 0 := by
  have hone : ContDiff ℂ (⊤ : ℕ∞)
      (fun w : EuclideanSpace ℂ ι => MvPolynomial.eval (fun i => w i) (1 : MvPolynomial ι ℂ)) := by
    simp only [map_one]
    exact contDiff_const
  have key : ∀ j (v : Fin j → ι), j ≤ c →
      iteratedFDeriv ℂ j β 0 (fun k => EuclideanSpace.single (v k) (1 : ℂ)) =
        iteratedFDeriv ℂ j
          (fun w : EuclideanSpace ℂ ι => MvPolynomial.eval (fun i => w i) (1 : MvPolynomial ι ℂ)) 0
          (fun k => EuclideanSpace.single (v k) (1 : ℂ)) := by
    intro j v hj
    rw [ct_iter_single_eq_polyDeriv β hβ j v, ct_iter_single_eq_polyDeriv _ hone j v]
    exact hjet _ (by rw [ct_degree_toFinsupp_ofFn]; exact hj)
  refine ⟨?_, fun j hj1 hjc => ?_⟩
  · have h := key 0 Fin.elim0 (Nat.zero_le _)
    simpa [iteratedFDeriv_zero_apply] using h
  · have hz : ∀ v : Fin j → ι,
        iteratedFDeriv ℂ j β 0 (fun k => EuclideanSpace.single (v k) (1 : ℂ)) = 0 := by
      intro v
      rw [key j v hjc]
      simp only [map_one]
      rw [iteratedFDeriv_const_of_ne (by omega)]
      rfl
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    refine Module.Basis.ext_multilinear (fun _ => (EuclideanSpace.basisFun ι ℂ).toBasis) ?_
    intro v
    simpa using hz v
end ReciprocityTheory.ChartRestriction.G.I2

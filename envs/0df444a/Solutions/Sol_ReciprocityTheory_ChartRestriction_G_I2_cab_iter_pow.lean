-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cab_iter_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:10:30.291114+00:00
-- url     : https://prove2.me/submissions/ba52e4f9-9b1d-4d3a-b9f3-dc4c44aa2342

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelA

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
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ℓ : V →L[ℂ] ℂ) (c : ℕ) (x : Fin c → V) :
    iteratedFDeriv ℂ c (fun v => (ℓ v) ^ c) 0 x = (c.factorial : ℂ) * ∏ k, ℓ (x k) := by
  let f := (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin c) ℂ).compContinuousLinearMap (fun _ => ℓ)
  have hf : (fun v => (ℓ v) ^ c) = fun v => f (fun _ => v) := by
    funext v; simp [f, ContinuousMultilinearMap.mkPiAlgebra_apply, Finset.prod_const]
  rw [hf, ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]
  simp only [f, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  have : ∀ σ : Equiv.Perm (Fin c), ∏ i, ℓ (x (σ i)) = ∏ k, ℓ (x k) := fun σ =>
    Equiv.prod_comp σ (fun k => ℓ (x k))
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
end ReciprocityTheory.ChartRestriction.G.I2

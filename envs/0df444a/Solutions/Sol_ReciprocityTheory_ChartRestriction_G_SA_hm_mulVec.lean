-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.hm_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:27:59.639239+00:00
-- url     : https://prove2.me/submissions/dbde942d-a502-4be9-9cc2-f77dfce859c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (σ J)
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (e f : ι → K) (M : Matrix (Fin 2) (Fin 2) K) (x : ι → K) :
    hm σ J e f M *ᵥ x = x + ((M 0 0 - 1) * hf σ J x f + M 0 1 * hf σ J x e) • e
      + (M 1 0 * hf σ J x f + (M 1 1 - 1) * hf σ J x e) • f := by
  have hfd : ∀ x y : ι → K, ∑ i, (J *ᵥ (σ ∘ y)) i * x i = hf σ J x y := by
    intro x y
    simp only [hf, Matrix.mulVec, dotProduct, Function.comp_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have key : ∀ u y : ι → K, vecMulVec u (J *ᵥ (σ ∘ y)) *ᵥ x = hf σ J x y • u := by
    intro u y
    ext i
    rw [← hfd x y, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    simp only [Matrix.mulVec, dotProduct, vecMulVec_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hs : ∀ (a : K) (A : Matrix ι ι K) (v : ι → K), (a • A) *ᵥ v = a • (A *ᵥ v) := by
    intro a A v
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
      Finset.mul_sum, mul_assoc]
  simp only [hm, Matrix.add_mulVec, Matrix.one_mulVec, hs, key]
  module
end ReciprocityTheory.ChartRestriction.G.SA

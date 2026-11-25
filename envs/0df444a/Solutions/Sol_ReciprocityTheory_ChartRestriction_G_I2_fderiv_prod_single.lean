-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.fderiv_prod_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:09:50.436464+00:00
-- url     : https://prove2.me/submissions/a9b020d1-b182-46ac-a566-a4f58f3da8d3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {n : ℕ} {h : Fin n → W → ℂ} (hh : ∀ k, Differentiable ℂ (h k))
    (x : Fin n → W) (k0 : Fin n) (e : W) :
    fderiv ℂ (fun y : Fin n → W => ∏ k, h k (y k)) x (Pi.single k0 e) =
      (∏ k ∈ Finset.univ.erase k0, h k (x k)) * fderiv ℂ (h k0) (x k0) e := by
  classical
  have hd : ∀ k, HasFDerivAt (fun y : Fin n → W => h k (y k))
      ((fderiv ℂ (h k) (x k)).comp (ContinuousLinearMap.proj k)) x :=
    fun k => ((hh k) (x k)).hasFDerivAt.comp x (hasFDerivAt_apply k x)
  have hP : HasFDerivAt (fun y : Fin n → W => ∏ k, h k (y k))
      (∑ k, (∏ j ∈ Finset.univ.erase k, h j (x j)) •
        ((fderiv ℂ (h k) (x k)).comp (ContinuousLinearMap.proj k))) x :=
    HasFDerivAt.finset_prod (fun k _ => hd k)
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single k0]
  · simp
  · intro b _ hb
    simp [hb]
  · simp
end ReciprocityTheory.ChartRestriction.G.I2

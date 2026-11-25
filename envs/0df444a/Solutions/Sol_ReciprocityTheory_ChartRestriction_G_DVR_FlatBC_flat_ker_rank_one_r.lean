-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.flat_ker_rank_one_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:52.673897+00:00
-- url     : https://prove2.me/submissions/ee9e9a42-6a4c-4488-89b1-eed2762a20fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_flat_ker_rank_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
namespace ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
theorem _root_.solution (δ : M →ₗ[R] N) (θ : M) (hker : ∀ m, δ m = 0 ↔ ∃ r : R, m = r • θ)
    (hfree : ∀ r : R, r • θ = 0 → r = 0) (t : M ⊗[R] S) (ht : δ.rTensor S t = 0) :
    ∃! a : S, t = θ ⊗ₜ[R] a := by
  have hcomm : ∀ t : M ⊗[R] S, δ.lTensor S (TensorProduct.comm R M S t) = TensorProduct.comm R N S (δ.rTensor S t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m s => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have ht' : δ.lTensor S (TensorProduct.comm R M S t) = 0 := by rw [hcomm, ht, map_zero]
  obtain ⟨a, ha, hu⟩ := flat_ker_rank_one δ θ hker hfree _ ht'
  refine ⟨a, ?_, fun b hb => hu b ?_⟩
  · apply (TensorProduct.comm R M S).injective
    rw [ha]; simp
  · rw [hb]; simp
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

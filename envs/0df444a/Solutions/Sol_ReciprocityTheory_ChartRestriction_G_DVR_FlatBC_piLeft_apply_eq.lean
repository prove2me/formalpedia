-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.piLeft_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:33.579393+00:00
-- url     : https://prove2.me/submissions/8e6cbc7e-9bfe-418b-abe9-d0e20300b521

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec

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
omit [Module.Flat R S]
namespace ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (Mi : ι → Type*) [∀ i, AddCommGroup (Mi i)] [∀ i, Module R (Mi i)]
    (x : (∀ i, Mi i) ⊗[R] S) (i : ι) :
    (TensorProduct.piLeft (R := R) (N := S) (M := Mi)) x i = (LinearMap.proj i : (∀ i, Mi i) →ₗ[R] Mi i).rTensor S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m s => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

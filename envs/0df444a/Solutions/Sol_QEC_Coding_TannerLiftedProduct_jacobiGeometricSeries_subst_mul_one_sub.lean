-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiGeometricSeries_subst_mul_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:24:47.187285+00:00
-- url     : https://prove2.me/submissions/e64bebc9-5714-4262-907a-a4758563be60

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {a : ℚ⟦X⟧} (hs : PowerSeries.HasSubst a) :
    (jacobiGeometricSeries.subst a) * (1 - a) = 1 := by
  change (PowerSeries.mk 1 : ℚ⟦X⟧).subst a * (1 - a) = 1
  have hsubst_one : (1 : ℚ⟦X⟧).subst a = 1 := by
    rw [← PowerSeries.coe_substAlgHom hs]
    exact map_one (PowerSeries.substAlgHom hs)
  have hone :
      ((1 : ℚ⟦X⟧) - PowerSeries.X).subst a = 1 - a := by
    rw [PowerSeries.subst_sub hs]
    rw [hsubst_one, PowerSeries.subst_X hs]
  rw [← hone, ← PowerSeries.subst_mul hs]
  rw [PowerSeries.mk_one_mul_one_sub_eq_one]
  exact hsubst_one
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.uniformizerDifferential_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:04:46.431016+00:00
-- url     : https://prove2.me/submissions/926becf0-02c0-452e-837a-c3d2c0568652

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_uniformizerDifferential_order

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential._p2m_local_instance_8465ba921d_22
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]
namespace QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
theorem _root_.solution (π : (localValuationRing K a))
    (m : ℤ) (hm : 0 < m) (he : (localFieldOrder K a) (π : K) = (m : WithTop ℤ)) :
    KaehlerDifferential.D ℂ K (π : K) ≠ 0 := by
  intro hz
  have ho := uniformizerDifferential_order K a π m hm he
  rw [hz,map_zero,(meromorphicOrderValuation a).map_zero] at ho
  exact WithTop.top_ne_coe ho
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential

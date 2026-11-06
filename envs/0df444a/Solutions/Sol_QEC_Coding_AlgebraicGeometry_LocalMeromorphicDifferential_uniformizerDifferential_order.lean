-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.uniformizerDifferential_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:02:56.69022+00:00
-- url     : https://prove2.me/submissions/8761b4f7-e2fc-4d1a-8170-19dd42b90256

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_fieldLocalDifferentialMap_D
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_germDerivative_order


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
    meromorphicOrderValuation a
      (fieldLocalDifferentialMap K a (KaehlerDifferential.D ℂ K (π : K))) =
      ((m - 1 : ℤ) : WithTop ℤ) := by
  rw [fieldLocalDifferentialMap_D K a]
  exact germDerivative_order a _ m (ne_of_gt hm) he
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential

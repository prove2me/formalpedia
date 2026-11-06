-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.fieldLocalDifferentialMap_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:05:38.016943+00:00
-- url     : https://prove2.me/submissions/9f5fd207-222c-4f6c-8a7d-34020fc575fe

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential

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
theorem _root_.solution (f : K) :
    fieldLocalDifferentialMap K a (KaehlerDifferential.D ℂ K f) =
      germDerivative a ((IsScalarTower.toAlgHom ℂ K (MeromorphicGermRing a)) f) := by
  exact (fieldLocalDerivation K a).liftKaehlerDifferential_comp_D f
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential

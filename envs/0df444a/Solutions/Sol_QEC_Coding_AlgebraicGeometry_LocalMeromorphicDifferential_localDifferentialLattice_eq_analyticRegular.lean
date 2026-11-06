-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localDifferentialLattice_eq_analyticRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:11:36.509159+00:00
-- url     : https://prove2.me/submissions/95e96d88-9350-4040-a866-5521ce996e65

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_localDifferentialLattice_le_analyticRegular
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_analyticRegular_le_localDifferentialLattice

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential._p2m_local_instance_8465ba921d_22
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]
variable [IsDiscreteValuationRing (localValuationRing K a)]
namespace QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
theorem _root_.solution (e : (KaehlerDifferential ℂ K) ≃ₗ[K] K) :
    localDifferentialLattice K a =
      analyticRegularDifferentialSubmodule K a :=
  le_antisymm (localDifferentialLattice_le_analyticRegular K a)
    (analyticRegular_le_localDifferentialLattice K a e)
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential

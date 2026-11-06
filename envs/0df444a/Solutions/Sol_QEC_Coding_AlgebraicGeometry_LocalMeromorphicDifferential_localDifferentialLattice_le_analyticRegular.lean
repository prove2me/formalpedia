-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localDifferentialLattice_le_analyticRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:09:31.021771+00:00
-- url     : https://prove2.me/submissions/3a7e134d-0bcb-4a3d-9848-68361e10d64d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_fieldLocalDifferentialMap_D
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_germDerivative_nonnegative


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
theorem _root_.solution :
    localDifferentialLattice K a ≤
      analyticRegularDifferentialSubmodule K a := by
  apply Submodule.span_le.mpr
  rintro ω ⟨f,rfl⟩
  change 0 ≤ meromorphicOrderValuation a
    (fieldLocalDifferentialMap K a (KaehlerDifferential.D ℂ K f.val))
  rw [fieldLocalDifferentialMap_D K a]
  exact germDerivative_nonnegative a _ f.property
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential

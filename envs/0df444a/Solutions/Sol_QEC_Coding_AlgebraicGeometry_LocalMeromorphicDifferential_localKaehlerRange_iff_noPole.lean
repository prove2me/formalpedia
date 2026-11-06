-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localKaehlerRange_iff_noPole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:30.786211+00:00
-- url     : https://prove2.me/submissions/1d3516b3-4f46-433b-a674-4164b2d45d88

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_localDifferentialLattice_eq_analyticRegular
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_localDifferentialLattice_eq_KaehlerRange

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
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential._p2m_local_instance_8465ba921d_158
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential._p2m_local_instance_8465ba921d_159
namespace QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
theorem _root_.solution (e : (KaehlerDifferential ℂ K) ≃ₗ[K] K) (ω : (KaehlerDifferential ℂ K)) :
    ω ∈ ((KaehlerDifferential.D ℂ K).compAlgebraMap (localValuationRing K a)).liftKaehlerDifferential.range ↔
      0 ≤ meromorphicOrderValuation a (fieldLocalDifferentialMap K a ω) := by
  rw [← localDifferentialLattice_eq_KaehlerRange K a,
    localDifferentialLattice_eq_analyticRegular K a e]
  rfl
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential

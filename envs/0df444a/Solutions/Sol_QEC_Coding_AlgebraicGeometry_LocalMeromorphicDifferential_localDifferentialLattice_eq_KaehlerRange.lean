-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localDifferentialLattice_eq_KaehlerRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:02:19.143205+00:00
-- url     : https://prove2.me/submissions/4b26c290-8197-4477-93ec-1892c0aa453c

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
variable [IsDiscreteValuationRing (localValuationRing K a)]
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential._p2m_local_instance_8465ba921d_158
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential._p2m_local_instance_8465ba921d_159
omit [IsDiscreteValuationRing (localValuationRing K a)]
namespace QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
theorem _root_.solution :
    localDifferentialLattice K a =
      ((KaehlerDifferential.D ℂ K).compAlgebraMap (localValuationRing K a)).liftKaehlerDifferential.range := by
  let D := (KaehlerDifferential.D ℂ K).compAlgebraMap (localValuationRing K a)
  change Submodule.span (localValuationRing K a) (Set.range D) = D.liftKaehlerDifferential.range
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨f,rfl⟩
    exact ⟨KaehlerDifferential.D ℂ (localValuationRing K a) f,D.liftKaehlerDifferential_comp_D f⟩
  · rintro ω ⟨η,rfl⟩
    have hη : η ∈ Submodule.span (localValuationRing K a) (Set.range (KaehlerDifferential.D ℂ (localValuationRing K a))) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hη
    · rintro _ ⟨f,rfl⟩
      rw [D.liftKaehlerDifferential_comp_D]
      exact Submodule.subset_span ⟨f,rfl⟩
    · exact Submodule.zero_mem _
    · intro ξ ζ _ _ hξ hζ
      rw [map_add]
      exact Submodule.add_mem _ hξ hζ
    · intro c ξ _ hξ
      rw [map_smul]
      exact Submodule.smul_mem _ c hξ
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential

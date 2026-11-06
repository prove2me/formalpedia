-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.analyticRegular_le_localDifferentialLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:10:56.108815+00:00
-- url     : https://prove2.me/submissions/3976d231-54c9-4e47-ac98-4608ba999c22

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_uniformizerDifferential_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_differential_uniformizer_expansion
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_exists_uniformizer_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_valuation_uniformizer_derivative_shift


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
    analyticRegularDifferentialSubmodule K a ≤
      localDifferentialLattice K a := by
  obtain ⟨π,m,hπ,hm,he⟩ := exists_uniformizer_order (localFieldOrder K a)
  intro ω hω
  obtain ⟨f,hf⟩ := differential_uniformizer_expansion K a π m hm he e ω
  by_cases hf0 : f = 0
  · rw [hf,hf0,zero_smul]
    exact Submodule.zero_mem _
  · have hbound : 0 ≤ (localFieldOrder K a) f + ((m-1 : ℤ) : WithTop ℤ) := by
      change 0 ≤ meromorphicOrderValuation a
        (fieldLocalDifferentialMap K a ω) at hω
      rw [hf,map_smul, Algebra.smul_def] at hω
      change 0 ≤ meromorphicOrderValuation a
        ((IsScalarTower.toAlgHom ℂ K (MeromorphicGermRing a)) f *
          fieldLocalDifferentialMap K a (KaehlerDifferential.D ℂ K (π : K))) at hω
      rw [(meromorphicOrderValuation a).map_mul,
        uniformizerDifferential_order K a π m hm he] at hω
      exact hω
    have hv : 0 ≤ (localFieldOrder K a) f := (valuation_uniformizer_derivative_shift (localFieldOrder K a) π hπ hm he hf0).mp hbound
    rw [hf]
    exact (localDifferentialLattice K a).smul_mem (⟨f,hv⟩ : (localValuationRing K a))
      (Submodule.subset_span ⟨π,rfl⟩)
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential

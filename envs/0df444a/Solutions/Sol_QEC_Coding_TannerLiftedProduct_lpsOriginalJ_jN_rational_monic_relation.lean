-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJ_jN_rational_monic_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:41:13.516299+00:00
-- url     : https://prove2.me/submissions/d1d8488a-4e95-497c-a112-aa54c9d79e2d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalBivariateRetraction_monic_degree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalBivariateRetraction_original_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJ_jN_monic_relation


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ Φ : Polynomial (Polynomial ℚ), Φ.Monic ∧
      Φ.natDegree=Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧ ∀ τ : ℍ,
      Φ.eval₂ ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0 := by
  obtain ⟨P,hP,hdeg,hroot⟩ := lpsOriginalJ_jN_monic_relation N hN
  obtain ⟨hm,hd⟩ := lpsOriginalRationalBivariateRetraction_monic_degree P hP
  exact ⟨lpsOriginalRationalBivariateRetraction P,hm,hd.trans hdeg,
    lpsOriginalRationalBivariateRetraction_original_root N hN P hroot⟩
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJNMonicAnnihilatorUniqueQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:52:32.44135+00:00
-- url     : https://prove2.me/submissions/5a950ee4-442e-45b0-8cbc-15f069ab124d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNMinpolyDegreeQ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integralQ


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ∀ P : Polynomial (FractionRing (Polynomial ℚ)), P.Monic →
      P.natDegree ≤ Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) →
      Polynomial.aeval (lpsOriginalJNInFractionField N hN) P = 0 →
      P = minpoly (FractionRing (Polynomial ℚ))
        (lpsOriginalJNInFractionField N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  intro P hP hd he
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (lpsOriginalJNInFractionField_integralQ N hN)) hP
    (minpoly.dvd (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN) he)
  rw [lpsOriginalJNMinpolyDegreeQ N hN]
  exact hd
end QEC.Coding.TannerLiftedProduct

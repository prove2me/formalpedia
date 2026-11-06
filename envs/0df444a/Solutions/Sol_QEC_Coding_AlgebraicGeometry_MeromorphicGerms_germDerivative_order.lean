-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.germDerivative_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:02:18.334047+00:00
-- url     : https://prove2.me/submissions/7ab2c593-c748-4c32-8a17-84c3107bd056

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_germOrder_coe


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
theorem _root_.solution (x : ℂ) (A : MeromorphicGermRing x) (m : ℤ)
    (hm : m ≠ 0) (hA : meromorphicOrderValuation x A = (m : WithTop ℤ)) :
    meromorphicOrderValuation x (germDerivative x A) = ((m-1 : ℤ) : WithTop ℤ) := by
  obtain ⟨f,hf,he⟩ := A.property
  change germOrder x (germDerivative x A).val = _
  rw [germDerivative_value x A f hf he,germOrder_coe]
  apply meromorphicOrderAt_deriv_eq_sub_one (by exact_mod_cast hm)
  change germOrder x A.val = _ at hA
  rwa [he,germOrder_coe] at hA
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms

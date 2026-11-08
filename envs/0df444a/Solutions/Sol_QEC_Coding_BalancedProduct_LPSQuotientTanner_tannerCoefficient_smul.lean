-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSQuotientTanner.tannerCoefficient_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:44:12.821763+00:00
-- url     : https://prove2.me/submissions/43d4c3ae-b4d0-4c11-8b1d-dc3ccea1f7b7

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_edgeLocalCoordinate_smul
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_tannerBoundary_basis_apply_of_endpoint
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_tannerBoundary_basis_apply_of_not_endpoint


set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSQuotientTanner
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open Cyclic FreeOrbitCoordinates LPSTanner LPSArithmetic LPSGraph
open PKDistance
namespace QEC.Coding.BalancedProduct.LPSQuotientTanner
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (h : CyclicGroup q) (c : Check401 q) (e : Edge401 q hq) :
    tannerCoefficient q hq40 hq (h • c) (h • e) =
      tannerCoefficient q hq40 hq c e := by
  rcases c with ⟨g, j⟩
  change tannerBoundary q hq40 hq (canonicalBasisWord (h • e)) (h • g, j) =
    tannerBoundary q hq40 hq (canonicalBasisWord e) (g, j)
  by_cases hg : g ∈ e.1
  · have hg' : h • g ∈ (h • e).1 :=
      (mem_smul_edge_iff q hq h e g).2 hg
    rw [tannerBoundary_basis_apply_of_endpoint q hq40 hq (h • e) (h • g) j hg',
      tannerBoundary_basis_apply_of_endpoint q hq40 hq e g j hg]
    exact congrArg (fun a => localCheckCoefficient a j)
      (edgeLocalCoordinate_smul q hq40 hq h e g hg)
  · have hg' : h • g ∉ (h • e).1 := by
      intro hmem
      exact hg ((mem_smul_edge_iff q hq h e g).1 hmem)
    rw [tannerBoundary_basis_apply_of_not_endpoint q hq40 hq (h • e) (h • g) j hg',
      tannerBoundary_basis_apply_of_not_endpoint q hq40 hq e g j hg]
end QEC.Coding.BalancedProduct.LPSQuotientTanner

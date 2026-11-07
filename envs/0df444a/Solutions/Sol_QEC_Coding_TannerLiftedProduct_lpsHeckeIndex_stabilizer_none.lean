-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIndex_stabilizer_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:05.08941+00:00
-- url     : https://prove2.me/submissions/00b12deb-28be-4ce5-8452-3853add4b260

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_none_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    letI := lpsHeckeIndexAction N p hNp
    MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) (none:Option (Fin p)) =
      (CongruenceSubgroup.Gamma0 (N*p)).subgroupOf (CongruenceSubgroup.Gamma0 N) := by
  let := lpsHeckeIndexAction N p hNp
  ext γ
  change lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹ _ none=none ↔
    (γ:SL(2,ℤ)) ∈ CongruenceSubgroup.Gamma0 (N*p)
  rw [lpsHeckeRightIndex_none_iff]
  exact inv_mem_iff
end QEC.Coding.TannerLiftedProduct

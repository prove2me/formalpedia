-- Prove2me | solution 1 for P2M_GlobalTheory_HermDiag_toLinearMap_____eq_dotProduct_72a26b3ab9da
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:12.185123+00:00
-- url     : https://prove2.me/submissions/8d3aa43f-ed59-4c55-bca1-aa27ccfe433c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Theorems.Thm_GlobalTheory_HermDiag_dotProduct_mulVec_comp_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermDiag
open Module Matrix
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n]
variable [DecidableEq n]
namespace GlobalTheory.HermDiag
theorem _root_.solution (c : E →+* E) (G : Matrix n n E) (x y : n → E) :
    Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G x y = x ⬝ᵥ G *ᵥ (c ∘ y) := by
  rw [Matrix.toLinearMapₛₗ₂'_apply, dotProduct_mulVec_comp_eq_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [RingHom.id_apply, smul_eq_mul]
  ring
end GlobalTheory.HermDiag

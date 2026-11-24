-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ExistsForm_proof_d5dace6f400d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:44.562704+00:00
-- url     : https://prove2.me/submissions/c951935e-6d25-4725-adab-fe77569a8a27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_prod_pow_5715147e4abb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_not_mem_269c9461ec4e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace ExistsForm
theorem _root_.solution : ExistsForm.Statement := by
  intro F _ K _ _ ι _ P hP b
  have := hP.isPrime
  choose i hi using hP.relevant
  refine ⟨fun k => (b k).toNat, fun k => (-b k).toNat,
    ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ (b k).toNat, ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ (-b k).toNat,
    isMultiHomog_prod_pow i _, isMultiHomog_prod_pow i _, prod_pow_not_mem P i hi _,
    prod_pow_not_mem P i hi _, ?_⟩
  funext k
  simp only
  omega
end ExistsForm
end GroundTheory.Heights₂.Heights.FieldNumbers

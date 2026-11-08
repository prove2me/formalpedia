-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.BE20Balanced.exists_be20_balanced_family_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:45:21.068196+00:00
-- url     : https://prove2.me/submissions/7b2ca90a-b8b0-4570-aa96-2416e54f0bca

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_balancedFamilyCertificate_of_rayleigh

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.BE20Balanced
theorem _root_.solution
    (hLPS : LPS401FamilyRayleighBound) (B : Nat) :
    ∃ a : AdmissiblePrime401,
      max B BE20Unbalanced.familyThreshold < a.q ∧
      BalancedFamilyCertificate a.q a.gt40 a.legendre := by
  obtain ⟨a, ha⟩ := LPSFamily.exists_admissiblePrime401_gt
    (max B BE20Unbalanced.familyThreshold)
  have hLarge : BE20Unbalanced.familyThreshold ≤ a.q :=
    (Nat.le_max_right B BE20Unbalanced.familyThreshold).trans ha.le
  refine ⟨a, ha, ?_⟩
  exact balancedFamilyCertificate_of_rayleigh a.q hLarge a.legendre
    (hLPS a.q a.prime a.gt40 a.legendre)
end QEC.Coding.BalancedProduct.BE20Balanced

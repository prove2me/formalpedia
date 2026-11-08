-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.BE20Unbalanced.exists_be20_unbalanced_family_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:36:11.987743+00:00
-- url     : https://prove2.me/submissions/21c164c3-3d79-4dd9-bb58-604fac476650

import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_unbalancedFamilyCertificate_of_rayleigh

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Unbalanced
open QEC.Coding
open LPSFamily LPSGraph LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.BE20Unbalanced
theorem _root_.solution
    (hLPS : LPS401FamilyRayleighBound) (B : Nat) :
    ∃ a : AdmissiblePrime401,
      max B familyThreshold < a.q ∧
      UnbalancedFamilyCertificate a.q a.gt40 a.legendre := by
  obtain ⟨a, ha⟩ := LPSFamily.exists_admissiblePrime401_gt
    (max B familyThreshold)
  have hLarge : familyThreshold ≤ a.q :=
    (Nat.le_max_right B familyThreshold).trans ha.le
  refine ⟨a, ha, ?_⟩
  exact unbalancedFamilyCertificate_of_rayleigh a.q hLarge a.legendre
    (hLPS a.q a.prime a.gt40 a.legendre)
end QEC.Coding.BalancedProduct.BE20Unbalanced

-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.BE20Balanced.breuckmannEberhardtBalancedProductQLDPCFamilies
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:57:08.058158+00:00
-- url     : https://prove2.me/submissions/7aa4d8cb-fc76-456f-8c13-06ac87d7ed32

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
import Definitions.Def_QEC_Results_QLDPC_BalancedProductFamily
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_exists_be20_balanced_family_at
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_exists_be20_unbalanced_family_at


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open LPSFamily
namespace QEC.Coding.BalancedProduct.BE20Balanced
theorem _root_.solution
    (hLPS : LPS401FamilyRayleighBound) :
    (∀ B : Nat, ∃ a : AdmissiblePrime401,
      max B BE20Unbalanced.familyThreshold < a.q ∧
      BE20Unbalanced.UnbalancedFamilyCertificate
        a.q a.gt40 a.legendre) ∧
    (∀ B : Nat, ∃ a : AdmissiblePrime401,
      max B BE20Unbalanced.familyThreshold < a.q ∧
      BalancedFamilyCertificate a.q a.gt40 a.legendre) :=
  ⟨BE20Unbalanced.exists_be20_unbalanced_family_at hLPS,
    exists_be20_balanced_family_at hLPS⟩
end QEC.Coding.BalancedProduct.BE20Balanced

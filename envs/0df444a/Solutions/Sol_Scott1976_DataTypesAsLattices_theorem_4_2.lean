-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:18.205199+00:00
-- url     : https://prove2.me/submissions/6bf95524-23bb-47ac-9dfc-b2c9b14a8571

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_retractLe_refl
import Theorems.Thm_Scott1976_DataTypesAsLattices_retractLe_trans

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {a b c : Pomega} :
    (IsRetract a → retractLe a a) ∧
      (retractLe a b → retractLe b a → a = b) ∧
      (retractLe a b → retractLe b c → retractLe a c) := by
  refine ⟨retractLe_refl, ?_, ?_⟩
  · intro hab hba
    exact hab.1.trans (hba.2.symm)
  · intro hab hbc
    exact retractLe_trans hab hbc
end Scott1976.DataTypesAsLattices

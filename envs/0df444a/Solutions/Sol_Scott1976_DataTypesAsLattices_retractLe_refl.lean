-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.retractLe_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:15.975954+00:00
-- url     : https://prove2.me/submissions/568359a5-9929-469d-9dcd-c2ec9e0a4ad7

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {a : Pomega} (ha : IsRetract a) : retractLe a a :=
  ⟨ha, ha⟩
end Scott1976.DataTypesAsLattices

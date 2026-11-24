-- Prove2me | solution 1 for ULHC.T.fuelN_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:16:20.328811+00:00
-- url     : https://prove2.me/submissions/624493b0-3d97-4da2-bfad-8aa18238e29b

import Definitions.Def_ULHC_Timed_Strips
import Definitions.Def_ULHC_Timed_MinPath
import Definitions.Def_ULHC_Timed_TwoFactor
import Definitions.Def_ULHC_CostAlg
import Definitions.Def_ULHC_Timed_Alg

set_option autoImplicit true
open ULHC ULHC.T
open Finset
namespace ULHC.T
theorem _root_.solution (V : Finset Pt) : fuelN V.card = fuel V := rfl
end ULHC.T

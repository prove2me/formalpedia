-- Prove2me | solution 1 for ULHC.dval_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:38:05.747043+00:00
-- url     : https://prove2.me/submissions/460d5855-7c7e-424e-b05f-e042d550716c

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}
namespace ULHC
theorem _root_.solution {G : Finset Edge} {σ : StripSpec} {L : List StripSpec}
    (h : findPath V G = some (σ, L)) : dval V G = wt σ L := by
  unfold dval
  rw [h]
end ULHC

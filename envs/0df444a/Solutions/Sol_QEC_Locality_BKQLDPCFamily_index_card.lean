-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.index_card
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:04:30.923149+00:00
-- url     : https://prove2.me/submissions/efa41913-2794-451d-865c-4f9c439f2a2d

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]

theorem solution (family : BKQLDPCFamily ι κ) (i : family.Index) :
    Fintype.card (ι i.1) = i.1 :=
  family.blockLength_eq_index i.1 i.2

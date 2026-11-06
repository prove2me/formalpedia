-- Prove2me | solution 2 for QEC.Locality.BKQLDPCFamily.index_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:12:45.363959+00:00
-- url     : https://prove2.me/submissions/75307be4-f3cf-4eb3-98a5-734b5cba1be8

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
namespace QEC.Locality.BKQLDPCFamily
theorem _root_.solution (family : BKQLDPCFamily ι κ) (i : family.Index) :
    Fintype.card (ι i.1) = i.1 :=
  family.blockLength_eq_index i.1 i.2
end QEC.Locality.BKQLDPCFamily

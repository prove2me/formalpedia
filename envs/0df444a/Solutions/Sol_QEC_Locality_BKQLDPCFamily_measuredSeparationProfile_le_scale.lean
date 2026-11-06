-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.measuredSeparationProfile_le_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:08:22.254052+00:00
-- url     : https://prove2.me/submissions/3e2c427d-2f47-44c7-89fe-c8ab411b032f

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Theorems.Thm_QEC_Locality_twoThirdsSeparationProfile_le_scale

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]
namespace QEC.Locality.BKQLDPCFamily
theorem _root_.solution (family : BKQLDPCFamily ι κ)
    (i : family.Index) (r : Nat) :
    family.measuredSeparationProfile i r ≤ r :=
  twoThirdsSeparationProfile_le_scale (family.fixedGeneratorGraph i) r
end QEC.Locality.BKQLDPCFamily

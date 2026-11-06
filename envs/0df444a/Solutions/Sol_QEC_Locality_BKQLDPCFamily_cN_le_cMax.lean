-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.cN_le_cMax
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:08:57.285325+00:00
-- url     : https://prove2.me/submissions/d1ce3fc0-6935-4513-a58b-a777d10c17ef

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
theorem _root_.solution (family : BKQLDPCFamily ι κ)
    (i : family.Index) {r : Nat} (hr : r ∈ family.validScales i) :
    family.cN i r ≤ family.cMax i := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
end QEC.Locality.BKQLDPCFamily

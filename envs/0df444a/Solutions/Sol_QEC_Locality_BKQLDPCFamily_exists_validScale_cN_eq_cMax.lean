-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.exists_validScale_cN_eq_cMax
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:10:12.735911+00:00
-- url     : https://prove2.me/submissions/cf1140fd-bda5-490f-85e3-a88b2de1d632

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
theorem _root_.solution
    (family : BKQLDPCFamily ι κ) (i : family.Index) :
    ∃ r ∈ family.validScales i, family.cN i r = family.cMax i := by
  have hmem : family.cMax i ∈ family.observedExponents i := by
    exact Finset.max'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨r, hr, hvalue⟩
  exact ⟨r, hr, hvalue⟩
end QEC.Locality.BKQLDPCFamily

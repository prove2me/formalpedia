-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.cMax_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:21:10.332607+00:00
-- url     : https://prove2.me/submissions/3ccbb5ab-2821-4714-a2ca-2514ee99c31a

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_exists_validScale_cN_eq_cMax
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_cN_nonneg

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]
namespace QEC.Locality.BKQLDPCFamily
theorem _root_.solution (family : BKQLDPCFamily ι κ) (i : family.Index) :
    0 ≤ family.cMax i := by
  rcases family.exists_validScale_cN_eq_cMax i with ⟨r, hr, hvalue⟩
  rw [← hvalue]
  exact family.cN_nonneg i hr
end QEC.Locality.BKQLDPCFamily

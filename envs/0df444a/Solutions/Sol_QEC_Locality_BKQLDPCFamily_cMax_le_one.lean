-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.cMax_le_one
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:02:35.088344+00:00
-- url     : https://prove2.me/submissions/4cb58db6-4712-405b-840e-2f85557aa2d4

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_cN_le_one
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_exists_validScale_cN_eq_cMax
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]

theorem solution (family : BKQLDPCFamily ι κ) (i : family.Index) :
    family.cMax i ≤ 1 := by
  rcases family.exists_validScale_cN_eq_cMax i with ⟨r, hr, hvalue⟩
  rw [← hvalue]
  exact family.cN_le_one i hr

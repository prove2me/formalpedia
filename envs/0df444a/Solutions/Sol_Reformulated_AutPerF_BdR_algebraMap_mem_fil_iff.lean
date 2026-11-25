-- Prove2me | solution 1 for Reformulated.AutPerF.BdR.algebraMap_mem_fil_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:21:51.022431+00:00
-- url     : https://prove2.me/submissions/0ab83557-c678-4c5f-afa2-fc664e2058d9

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
import Theorems.Thm_Reformulated_AutPerF_BdR_fil_natCast
import Theorems.Thm_Reformulated_AutPerF_AinfInv_algebraMap_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]
open Reformulated.AutPerF.BdR
variable [IsAlgClosed (FractionRing R)]
namespace Reformulated.AutPerF.BdR
theorem _root_.solution (n : ℕ) (x : BdRPlus p R) :
    algebraMap _ (BdR p R) x ∈ fil p R n ↔ x ∈ BdRPlus.fil p R n := by
  rw [fil_natCast, filNat, Submodule.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => algebraMap_injective e ▸ hy, fun h => ⟨x, h, rfl⟩⟩
end Reformulated.AutPerF.BdR

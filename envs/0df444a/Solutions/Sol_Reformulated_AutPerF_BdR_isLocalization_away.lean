-- Prove2me | solution 1 for Reformulated.AutPerF.BdR.isLocalization_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:14:18.613387+00:00
-- url     : https://prove2.me/submissions/33f3a163-1fcf-48d8-8352-70f28a582318

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
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
variable {π : BdRPlus p R} (hπ : RingHom.ker (BdRPlus.theta p R) = span {π})
include hπ
namespace Reformulated.AutPerF.BdR
theorem _root_.solution : IsLocalization.Away π (BdR p R) := by
  have hirr := (BdRPlus.irreducible_iff π).2 hπ
  refine IsLocalization.Away.mk π (algebraMap_ne_zero hπ).isUnit ?_ ?_
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (BdRPlus p R) z
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hb) hirr
    refine ⟨n, a * ↑u⁻¹, ?_⟩
    have h0 := algebraMap_ne_zero hπ
    have hu : algebraMap (BdRPlus p R) (BdR p R) u ≠ 0 := (u.isUnit.map _).ne_zero
    rw [map_mul, map_mul, map_pow, map_units_inv]
    field_simp
  · intro a b h
    exact ⟨0, by rw [algebraMap_injective h]⟩
end Reformulated.AutPerF.BdR

-- Prove2me | solution 1 for Reformulated.AutPerF.Acris.hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:08.202063+00:00
-- url     : https://prove2.me/submissions/38ab033e-9884-4f06-9b04-eaabf80fa3d3

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Theorems.Thm_Reformulated_AutPerF_Acris_exists_eq_add
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Acris
namespace Reformulated.AutPerF.Acris
theorem _root_.solution {B : Type*} [CommRing B] [IsHausdorff (span {(p : B)}) B] {f g : Acris p R →+* B}
    (h : ∀ a : AcrisZero p R, f (algebraMap _ _ a) = g (algebraMap _ _ a)) : f = g := by
  ext x
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : B)})]
  intro n
  obtain ⟨a, y, rfl⟩ := exists_eq_add n x
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  refine ⟨f y - g y, ?_⟩
  simp only [map_add, map_mul, map_pow, map_natCast, h]
  ring
end Reformulated.AutPerF.Acris

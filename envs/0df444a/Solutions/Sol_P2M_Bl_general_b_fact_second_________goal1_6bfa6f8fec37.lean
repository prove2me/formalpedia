-- Prove2me | solution 1 for P2M_Bl_general_b_fact_second_________goal1_6bfa6f8fec37
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:31:02.25354+00:00
-- url     : https://prove2.me/submissions/60d1c5b5-9b5c-4335-a202-52c3687b59f6

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondBisAlt_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second''''''''
namespace Bl.general_b_fact_second''''''''
theorem _root_.solution :
  ∀ {K : Type} [inst : Field.{0} K] [NumberField.{0} K] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} K V] [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K V]
  (M : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) V) {x : V},
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} M)) x →
    Exists.{1} fun (d : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} d 0) (Membership.mem.{0, 0} M (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro K _ _ V _ _ _ _ M x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d1, hd1, h1⟩ := hy
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    rw [smul_add]
    apply M.add_mem
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h1
    · rw [mul_smul]; exact M.smul_mem _ h2
  | smul a y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨n, m⟩, hnm⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    dsimp only at hnm
    refine ⟨(m : NumberField.RingOfIntegers K) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero m) hd, ?_⟩
    have e : ∀ (r : NumberField.RingOfIntegers K) (v : V),
        r • v = (algebraMap (NumberField.RingOfIntegers K) K r) • v :=
      fun r v => (algebraMap_smul K r v).symm
    have key : ((m : NumberField.RingOfIntegers K) * d) • (a • y) = n • (d • y) := by
      simp only [e, smul_smul]
      congr 1
      rw [← hnm]
      simp only [map_mul]
      ring
    rw [key]
    exact M.smul_mem _ h
end Bl.general_b_fact_second''''''''

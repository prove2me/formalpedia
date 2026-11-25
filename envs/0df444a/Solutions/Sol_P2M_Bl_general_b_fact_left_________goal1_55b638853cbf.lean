-- Prove2me | solution 1 for P2M_Bl_general_b_fact_left_________goal1_55b638853cbf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:30:54.999261+00:00
-- url     : https://prove2.me/submissions/1427e395-46f1-4c31-87e9-cde4de5ae2bb

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftBisAlt_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_left''''''''
namespace Bl.general_b_fact_left''''''''
theorem _root_.solution :
  ∀ {K V : Type} [inst : Field.{0} K] [NumberField.{0} K] [inst_2 : AddCommGroup.{0} V] [inst_3 : Module.{0, 0} K V]
  [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K V]
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) V) (v : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} L)) v →
    Exists.{1} fun (d : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} d 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} d v)) := by
  intro K V _ _ _ _ _ _ L v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d1, hd1, h1⟩ := hx
    obtain ⟨d2, hd2, h2⟩ := hy
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem d2 h1
    · rw [mul_smul]
      exact L.smul_mem d1 h2
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨n, m⟩, hm⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    refine ⟨(m : NumberField.RingOfIntegers K) * d, mul_ne_zero (nonZeroDivisors.ne_zero m.2) hd, ?_⟩
    have key : ((m : NumberField.RingOfIntegers K) * d) • (a • x) = n • (d • x) := by
      rw [← algebraMap_smul K ((m : NumberField.RingOfIntegers K) * d) (a • x),
        ← algebraMap_smul K n (d • x), ← algebraMap_smul K d x, smul_smul, smul_smul, map_mul]
      congr 1
      rw [← hm]
      ring
    rw [key]
    exact L.smul_mem n h
end Bl.general_b_fact_left''''''''

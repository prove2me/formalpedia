-- Prove2me | solution 1 for P2M_Bl_general_b_fact_third_______goal1_4ace80324855
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:14.624243+00:00
-- url     : https://prove2.me/submissions/3ca9a246-d185-4f29-ba83-0b06afa0d853

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdTail_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third''''''
namespace Bl.general_b_fact_third''''''
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} E V] [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} E) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E V]
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) V),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} Λ)) Top.top.{0} →
    ∀ (x : V),
      Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} d 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro E _ _ V _ _ _ _ Λ hspan x
  have hx : x ∈ Submodule.span E (Λ : Set V) := by rw [hspan]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨d1, hd1, h1⟩ := hy
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem d2 h1
    · rw [mul_smul]; exact Λ.smul_mem d1 h2
  | smul a y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨b, m⟩, hm⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) a
    refine ⟨(m : NumberField.RingOfIntegers E) * d, mul_ne_zero (nonZeroDivisors.ne_zero m.2) hd, ?_⟩
    have key : (m : NumberField.RingOfIntegers E) • (a • y) = b • y := by
      rw [← algebraMap_smul E (m : NumberField.RingOfIntegers E), smul_smul, mul_comm]
      rw [show a * algebraMap (NumberField.RingOfIntegers E) E (m : NumberField.RingOfIntegers E) = algebraMap (NumberField.RingOfIntegers E) E b from hm]
      rw [algebraMap_smul]
    rw [mul_comm, mul_smul, key, smul_smul, mul_comm, ← smul_smul]
    exact Λ.smul_mem b h
end Bl.general_b_fact_third''''''

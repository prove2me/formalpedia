-- Prove2me | solution 1 for P2M_Bl_general_b_fact_second___goal1_ca370a2b430e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:14.452781+00:00
-- url     : https://prove2.me/submissions/405db506-49b6-4db7-846c-eea31bb68221

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second''
namespace Bl.general_b_fact_second''
theorem _root_.solution :
  ∀ {O K X : Type} [inst : CommRing.{0} O] [IsDomain.{0} O] [inst_2 : Field.{0} K] [inst_3 : Algebra.{0, 0} O K]
  [IsFractionRing.{0, 0} O K] [inst_5 : AddCommGroup.{0} X] [inst_6 : Module.{0, 0} K X] [inst_7 : Module.{0, 0} O X]
  [IsScalarTower.{0, 0, 0} O K X] (B : Submodule.{0, 0} O X),
  Eq.{1} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} B)) Top.top.{0} →
    ∀ (x : X), Exists.{1} fun (d : O) ↦ And (Ne.{1} d 0) (Membership.mem.{0, 0} B (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro O K X _ _ _ _ _ _ _ _ _ B hB x
  have hx : x ∈ Submodule.span K (B : Set X) := by rw [hB]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact B.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨d1, hd1, h1⟩ := hy
    obtain ⟨d2, hd2, h2⟩ := hz
    refine ⟨d2 * d1, mul_ne_zero hd2 hd1, ?_⟩
    rw [smul_add]
    apply B.add_mem
    · rw [mul_smul]; exact B.smul_mem d2 h1
    · rw [mul_comm, mul_smul]; exact B.smul_mem d1 h2
  | smul k y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) k
    have hb0 : algebraMap O K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hk : algebraMap O K b * (algebraMap O K a / algebraMap O K b) = algebraMap O K a := by
      field_simp
    have key : b • ((algebraMap O K a / algebraMap O K b) • y) = a • y := by
      rw [← smul_assoc, Algebra.smul_def, hk, algebraMap_smul]
    refine ⟨d * b, mul_ne_zero hd (nonZeroDivisors.ne_zero hb), ?_⟩
    rw [mul_smul, key, smul_comm]
    exact B.smul_mem a h
end Bl.general_b_fact_second''

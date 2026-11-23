-- Prove2me | solution 1 for P2M_Bl_general_b_fact_third__goal1_122fd7030837
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:15.466268+00:00
-- url     : https://prove2.me/submissions/ecde8ae9-e83a-47dc-9710-81676506a928

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdMore_Key
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.general_b_fact_third'
private lemma key {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * c) := by
  obtain ⟨y, hy0, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
  obtain h | h := Int.natAbs_eq y
  · rw [h, zsmul_eq_mul] at hy
    simpa using hy
  · rw [h, zsmul_eq_mul] at hy
    simpa using hy.neg
end Bl.general_b_fact_third'
end

set_option autoImplicit false
open Bl Bl.general_b_fact_third'
namespace Bl.general_b_fact_third'
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {n : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) (Fin n → E)),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L)) Top.top.{0} →
    ∀ (w : Fin n → E),
      Exists.{1} fun (m : Nat) ↦ And (LT.lt.{0} 0 m) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} m w)) := by
  intro E _ _ n L hL w
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have e : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [e]
    exact L.add_mem (nsmul_mem hax b) (nsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨d, hd, hdc⟩ := key c
    refine ⟨d * a, Nat.mul_pos hd ha, ?_⟩
    have h1 := L.smul_mem (⟨(d : E) * c, hdc⟩ : NumberField.RingOfIntegers E) hax
    convert h1 using 1
    ext i
    rw [Pi.smul_apply, Algebra.smul_def]
    change _ = ((d : E) * c) * _
    simp [nsmul_eq_mul]
    ring
end Bl.general_b_fact_third'

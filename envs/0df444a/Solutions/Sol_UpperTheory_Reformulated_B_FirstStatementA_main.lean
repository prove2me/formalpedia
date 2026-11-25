-- Prove2me | solution 1 for UpperTheory.Reformulated.B.FirstStatementA.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:02:27.171961+00:00
-- url     : https://prove2.me/submissions/ea5d7c82-4da6-43ac-a8ff-6e09f76385d1

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FirstStatementA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.FirstStatementA
theorem _root_.solution :
    ∀ {E : Type} [inst : Field E]
    [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
    ∀ x ∈ Submodule.span E (↑L : Set (Fin n → E)), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • x ∈ L := by
  intro E _ _ n L x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, ha, hya⟩ := h1
    obtain ⟨b, hb, hzb⟩ := h2
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : (a * b) • (y + z) = b • (a • y) + a • (b • z) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm a b y]
    rw [e]
    exact L.add_mem (L.smul_of_tower_mem b hya) (L.smul_of_tower_mem a hzb)
  | smul c y _ h =>
    obtain ⟨a, ha, hya⟩ := h
    have halg : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨d, hd, hint⟩ := halg.exists_integral_multiple
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    let r : NumberField.RingOfIntegers E := ⟨d • c, hint⟩
    have e : (d * a) • (c • y) = r • (a • y) := by
      have : r • (a • y) = (d • c) • (a • y) := rfl
      rw [this, mul_smul, smul_comm a c y, smul_assoc]
    rw [e]
    exact L.smul_mem r hya
end UpperTheory.Reformulated.B.FirstStatementA

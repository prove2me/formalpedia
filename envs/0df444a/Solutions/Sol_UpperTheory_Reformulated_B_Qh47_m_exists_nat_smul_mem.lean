-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qh47.m_exists_nat_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:38.660131+00:00
-- url     : https://prove2.me/submissions/29e60e67-6ddd-4225-b5be-4a579872d96f

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MExistsNatSmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Qh47.exists_nat_mul_integral {E : Type} [Field E] [NumberField E]
    (a : E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * a) := by
  have hq : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have hz : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hq
  obtain ⟨y, hy, hi⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hi
  rcases Int.natAbs_eq y with h | h
  · have h2 : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h]
      exact (Int.cast_natCast _).symm
    rw [h2]; exact hi
  · have h2 : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h]
      rw [Int.cast_neg, neg_neg, Int.cast_natCast]
    rw [h2, neg_mul]; exact hi.neg
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qh47
theorem _root_.solution :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : Formalism.BasicNotions.HSpace E}
      (M : Submodule (NumberField.RingOfIntegers E) S.V) {x : S.V},
      x ∈ Submodule.span E (↑M : Set S.V) → ∃ (n : ℕ), (0 : ℕ) < n ∧ n • x ∈ M := by
  intro E _ _ _ S M x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_pos, by rw [one_smul]; exact M.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hmx n
    · rw [mul_smul]; exact nsmul_mem hny m
  | smul a x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hi⟩ := UpperTheory.Reformulated.B.Qh47.exists_nat_mul_integral a
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    obtain ⟨b, hb⟩ : ∃ b : NumberField.RingOfIntegers E, algebraMap _ E b = (n : E) * a :=
      ⟨⟨(n : E) * a, hi⟩, rfl⟩
    have e : (n * m) • a • x = b • m • x := by
      rw [mul_smul n m, smul_comm m a x, ← algebraMap_smul E b, hb, mul_smul,
        Nat.cast_smul_eq_nsmul]
    rw [e]
    exact M.smul_mem b hmx
end UpperTheory.Reformulated.B.Qh47

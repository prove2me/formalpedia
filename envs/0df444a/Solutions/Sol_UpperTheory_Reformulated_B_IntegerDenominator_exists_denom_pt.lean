-- Prove2me | solution 1 for UpperTheory.Reformulated.B.IntegerDenominator.exists_denom_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:58.628715+00:00
-- url     : https://prove2.me/submissions/7a8d3808-04c0-4e44-b762-1cb91a55ae88

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegerDenominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.IntegerDenominator.exists_int_denom {E : Type} [Field E] [NumberField E] {n : Type}
    (L : Submodule (NumberField.RingOfIntegers E) (n → E))
    (x : n → E) (hx : x ∈ Submodule.span E (↑L : Set (n → E))) :
    ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (y + z) = b • (a • y) + a • (b • z) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [h]
    exact L.add_mem (zsmul_mem hay b) (zsmul_mem hbz a)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨b, hb, hbc⟩ := hc.exists_integral_multiple
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (c • y) =
        (⟨b • c, hbc⟩ : NumberField.RingOfIntegers E) • (a • y) := by
      change _ = (b • c) • (a • y)
      rw [smul_comm (b • c) a y, smul_assoc, mul_smul]
    rw [h]
    exact L.smul_mem _ hay
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.IntegerDenominator
theorem _root_.solution :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E]
    [NumberField E] [inst_4 : Algebra F E] {n : Type} [Fintype n] [DecidableEq n]
    (L : Submodule (NumberField.RingOfIntegers E) (n → E)),
    Submodule.span E (↑L : Set (n → E)) = ⊤ →
      ∀ (x : n → E),
        ∃ (D : NumberField.RingOfIntegers F),
          D ≠ (0 : NumberField.RingOfIntegers F) ∧ (Algebra.algebraMap F E : F → E) (↑D : F) • x ∈ L := by
  intro F E _ _ _ _ _ n _ _ L hL x
  obtain ⟨N, hN, hNx⟩ := UpperTheory.Reformulated.B.IntegerDenominator.exists_int_denom L x (hL ▸ Submodule.mem_top)
  refine ⟨(N : NumberField.RingOfIntegers F), Int.cast_ne_zero.2 hN, ?_⟩
  have h : (Algebra.algebraMap F E : F → E) ((N : NumberField.RingOfIntegers F) : F) = (N : E) := by
    have h1 : ((N : NumberField.RingOfIntegers F) : F) = (N : F) :=
      map_intCast (algebraMap (NumberField.RingOfIntegers F) F) N
    rw [h1]
    exact map_intCast (algebraMap F E) N
  rw [h, Int.cast_smul_eq_zsmul]
  exact hNx
end UpperTheory.Reformulated.B.IntegerDenominator

-- Prove2me | solution 1 for PI.InvTopW.exists_nat_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:37:40.380442+00:00
-- url     : https://prove2.me/submissions/b0e323eb-2914-43c4-aa1d-6cad96bc61da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PI.InvTopW
open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
private theorem exists_nat_mul_lemma {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ d : ℕ, 1 ≤ d ∧ (d : E) * x ∈ Formalism.UG.intOE E := by
  have H : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * x) := by
    have hq : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    first
    | (obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) x hq
       exact ⟨m, nonZeroDivisors.coe_ne_zero m, by rw [← zsmul_eq_mul]; exact hm⟩)
    | (obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := ℚ) (nonZeroDivisors ℤ) x hq
       exact ⟨m, nonZeroDivisors.coe_ne_zero m, by rw [← zsmul_eq_mul]; exact hm⟩)
    | (obtain ⟨y, hy, h⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hq.isAlgebraic).exists_integral_multiple
       exact ⟨y, hy, by rw [← zsmul_eq_mul]; exact h⟩)
  obtain ⟨y, hy0, hint⟩ := H
  have hmem : (y : E) * x ∈ Formalism.UG.intOE E :=
    RingHom.mem_range.2 ((IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨n, Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hy0), ?_⟩
    simpa using hmem
  · refine ⟨n, Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hy0), ?_⟩
    simpa using hmem
section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Loc
end PI.InvTopW
end
end

set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.InvTopW
theorem _root_.solution {E : Type} [Field E] [NumberField E] (s : Finset E) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ x ∈ s, (d : E) * x ∈ Formalism.UG.intOE E := by
  classical
  refine Finset.induction_on s ⟨1, le_rfl, by simp⟩ ?_
  intro a s _ ih
  obtain ⟨d, hd, hds⟩ := ih
  obtain ⟨e, he, hea⟩ := exists_nat_mul_lemma a
  refine ⟨d * e, Nat.mul_pos hd he, fun x hx => ?_⟩
  rcases Finset.mem_insert.1 hx with rfl | hx
  · rw [Nat.cast_mul, mul_assoc]
    exact mul_mem (natCast_mem _ d) hea
  · rw [Nat.cast_mul, mul_comm (d : E), mul_assoc]
    exact mul_mem (natCast_mem _ e) (hds x hx)
end PI.InvTopW

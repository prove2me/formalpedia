-- Prove2me | solution 1 for PI.SqPairW.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:40.431805+00:00
-- url     : https://prove2.me/submissions/e7e1841a-5df8-4731-8b05-ca723ec1f079

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ExistsDenLe
import Theorems.Thm_PI_SqPairW_ringInt_smul
import Theorems.Thm_PI_SqPairW_exists_den_le
import Theorems.Thm_PI_SqPairW_exists_nat_mul_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairW
theorem _root_.solution {L' L'' : Submodule (𝓞 E) (Fin N → E)} (hL' : IsSDG E N L') (hL'' : IsSDG E N L'')
    {n : 𝓞 E} (hn : n ≠ 0) :
    ∃ D : ℕ, 0 < D ∧ ∀ w, (w ∈ L' ∨ w ∈ L'') → (D : ℤ) • w ∈ yg L' L'' n := by
  obtain ⟨D1, hD1, h1⟩ := exists_den_le hL'.1 hL''.2.1
  obtain ⟨D2, hD2, h2⟩ := exists_den_le hL''.1 hL'.2.1
  have hnE : (n : E) ≠ 0 := by exact_mod_cast hn
  obtain ⟨k, hk, β, hβ⟩ := exists_nat_mul_int (n : E)⁻¹
  have hkY : ∀ u, u ∈ L' → u ∈ L'' → (k : ℤ) • u ∈ yg L' L'' n := by
    intro u hu hu'
    refine ⟨β • u, L'.smul_mem β hu, L''.smul_mem β hu', ?_⟩
    rw [ringInt_smul, smul_smul, hβ, ← Int.cast_smul_eq_zsmul E]
    congr 1
    field_simp
    push_cast
    ring
  refine ⟨k * D1 * D2, Nat.mul_pos (Nat.mul_pos hk hD1) hD2, ?_⟩
  rintro w (hw | hw)
  · have hu : (D1 : ℤ) • w ∈ L'' := h1 w hw
    have hu' : (D1 : ℤ) • w ∈ L' := L'.toAddSubgroup.zsmul_mem hw _
    have e1 : ((k * D1 * D2 : ℕ) : ℤ) • w = (k : ℤ) • ((D2 : ℤ) • ((D1 : ℤ) • w)) := by
      push_cast
      module
    rw [e1]
    exact hkY _ (L'.toAddSubgroup.zsmul_mem hu' _) (L''.toAddSubgroup.zsmul_mem hu _)
  · have hu : (D2 : ℤ) • w ∈ L' := h2 w hw
    have hu' : (D2 : ℤ) • w ∈ L'' := L''.toAddSubgroup.zsmul_mem hw _
    have e1 : ((k * D1 * D2 : ℕ) : ℤ) • w = (k : ℤ) • ((D1 : ℤ) • ((D2 : ℤ) • w)) := by
      push_cast
      module
    rw [e1]
    exact hkY _ (L'.toAddSubgroup.zsmul_mem hu _) (L''.toAddSubgroup.zsmul_mem hu' _)
end PI.SqPairW

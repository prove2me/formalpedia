-- Prove2me | solution 1 for PI.SqPairW.exists_nat_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:07.787008+00:00
-- url     : https://prove2.me/submissions/fb6f876c-bcaa-4170-bf9d-929e8d2c7d95

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ExistsDenLe
import Theorems.Thm_PI_SqPairW_ringInt_smul
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
theorem _root_.solution {L : Submodule (𝓞 E) (Fin N → E)}
    (hL : Submodule.span E (L : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ k : ℕ, 0 < k ∧ (k : ℤ) • v ∈ L := by
  let T : Submodule E (Fin N → E) :=
    { carrier := {v | ∃ k : ℕ, 0 < k ∧ (k : ℤ) • v ∈ L}
      add_mem' := by
        rintro a b ⟨k1, hk1, ha⟩ ⟨k2, hk2, hb⟩
        refine ⟨k1 * k2, Nat.mul_pos hk1 hk2, ?_⟩
        have e1 : ((k1 * k2 : ℕ) : ℤ) • (a + b) = (k2 : ℤ) • ((k1 : ℤ) • a) + (k1 : ℤ) • ((k2 : ℤ) • b) := by
          push_cast
          module
        rw [e1]
        exact L.add_mem (L.toAddSubgroup.zsmul_mem ha _) (L.toAddSubgroup.zsmul_mem hb _)
      zero_mem' := ⟨1, one_pos, by simp⟩
      smul_mem' := by
        rintro c v ⟨k2, hk2, hv⟩
        obtain ⟨k1, hk1, β, hβ⟩ := exists_nat_mul_int c
        refine ⟨k1 * k2, Nat.mul_pos hk1 hk2, ?_⟩
        have e1 : ((k1 * k2 : ℕ) : ℤ) • (c • v) = β • ((k2 : ℤ) • v) := by
          rw [ringInt_smul, hβ, ← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul,
            smul_smul]
          push_cast
          congr 1
          ring
        rw [e1]
        exact L.smul_mem β hv }
  have hLT : L ≤ T.restrictScalars (𝓞 E) := fun v hv => ⟨1, one_pos, by simpa using hv⟩
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← hL, Submodule.span_le]
    exact fun v hv => hLT hv
  have hv : v ∈ T := hT ▸ Submodule.mem_top
  exact hv
end PI.SqPairW

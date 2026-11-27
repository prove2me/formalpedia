-- Prove2me | solution 1 for UpperTheory.Top.imprimitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:37:56.632566+00:00
-- url     : https://prove2.me/submissions/3ae57d13-9805-4a80-af3c-b4e4b6b91466

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_Imprimitive
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



set_option autoImplicit false
open Formalism.HC
namespace UpperTheory.Top
theorem _root_.solution :
    ZeroFreeAll → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  intro h N _ χ s hs hχs
  haveI : NeZero χ.conductor := (PChar.of χ).ne
  have hL : DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0 := h (PChar.of χ) trivial s hs
  have hχ' : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases hχs with hχ | hs1
    · left
      intro h1
      apply hχ
      rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]
    · exact Or.inr hs1
  have hrw := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hχ'
  rw [χ.changeLevel_primitiveCharacter] at hrw
  rw [hrw]
  refine mul_ne_zero hL (Finset.prod_ne_zero_iff.mpr fun p hp => ?_)
  have hp' := Nat.prime_of_mem_primeFactors hp
  intro h0
  have key : χ.primitiveCharacter p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h0
  have h1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have h2 : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp'.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by linarith)
  have hn : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ * ‖(p : ℂ) ^ (-s)‖
        ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := by gcongr
      _ < 1 := by simpa using h2
  rw [key, norm_one] at hn
  exact lt_irrefl _ hn
end UpperTheory.Top

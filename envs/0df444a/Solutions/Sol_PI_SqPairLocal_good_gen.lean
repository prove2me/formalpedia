-- Prove2me | solution 1 for PI.SqPairLocal.good_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:36.099728+00:00
-- url     : https://prove2.me/submissions/52600b23-1e64-480f-a337-da83dbf197dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt
import Theorems.Thm_PI_SqPairLocal_intAt_coe
import Theorems.Thm_PI_SqPairLocal_intAt_zero
import Theorems.Thm_PI_SqPairLocal_intAt_one
import Theorems.Thm_PI_SqPairLocal_intAt_mul
import Theorems.Thm_PI_SqPairLocal_divAt_add
import Theorems.Thm_PI_SqPairLocal_divAt_sub
import Theorems.Thm_PI_SqPairLocal_divAt_mul_left
import Theorems.Thm_PI_SqPairLocal_divAt_mul_right
import Theorems.Thm_PI_SqPairLocal_small_of

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
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution {L : Submodule (𝓞 E) (Fin N → E)} {G : Matrix (Fin N) (Fin N) E}
    (hG1 : Gᴴ * G = 1) (hGG : G * Gᴴ = 1)
    (hD : ∀ y : Fin N → E, (∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L) ↔ ∀ i, IntAt Q ((Gᴴ *ᵥ y) i))
    {c : 𝓞 E} (hc : (c : E) ≠ 0) {f : Matrix (Fin N) (Fin N) E} (hf : ∀ i j, IntAt Q (f i j))
    (hf2 : ∀ i j, DivAt Q c ((f * f - f) i j)) (hf3 : ∀ i j, DivAt Q c ((f + fᴴ - 1) i j))
    {t : 𝓞 E} (ht : DivAt Q c ((t : E) - 1)) (ht' : DivAt Q c (star (t : E) - 1))
    (ht'' : IntAt Q (star (t : E)))
    {e : Matrix (Fin N) (Fin N) E} (he : Gᴴ * e * G = (t : E) • f) :
    SmallAt Q c L (e * e - e) ∧ SmallAt Q c L (e + eᴴ - 1) := by
  constructor
  · apply small_of hGG hD hc
    intro i j
    have hcs : Gᴴ * (e * e - e) * G = (Gᴴ * e * G) * (Gᴴ * e * G) - Gᴴ * e * G := by
      calc Gᴴ * (e * e - e) * G = Gᴴ * e * (G * Gᴴ) * e * G - Gᴴ * e * G := by
            rw [hGG, mul_one, mul_sub, sub_mul]
            simp only [mul_assoc]
        _ = _ := by simp only [mul_assoc]
    rw [hcs, he]
    have hm : ((t : E) • f) * ((t : E) • f) - (t : E) • f =
        ((t : E) * (t : E)) • (f * f - f) + ((t : E) * ((t : E) - 1)) • f := by
      rw [smul_mul_smul_comm, smul_sub, mul_sub, mul_one, sub_smul]
      abel
    rw [hm]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact divAt_add (divAt_mul_left (intAt_mul (intAt_coe t) (intAt_coe t)) (hf2 i j))
      (divAt_mul_right (divAt_mul_left (intAt_coe t) ht) (hf i j))
  · apply small_of hGG hD hc
    intro i j
    have hch : Gᴴ * (e + eᴴ - 1) * G = Gᴴ * e * G + (Gᴴ * e * G)ᴴ - 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        mul_sub, mul_add, sub_mul, add_mul, mul_one, hG1]
      simp only [mul_assoc]
    rw [hch, he]
    have hm : (t : E) • f + ((t : E) • f)ᴴ - 1 = star (t : E) • (f + fᴴ - 1) +
        ((t : E) - star (t : E)) • f + (star (t : E) - 1) • (1 : Matrix (Fin N) (Fin N) E) := by
      rw [Matrix.conjTranspose_smul, smul_sub, smul_add, sub_smul, sub_smul, one_smul]
      abel
    rw [hm]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : IntAt Q ((1 : Matrix (Fin N) (Fin N) E) i j) := by
      rw [Matrix.one_apply]
      split_ifs
      · exact intAt_one
      · exact intAt_zero
    have h2 : DivAt Q c ((t : E) - star (t : E)) := by
      rw [show (t : E) - star (t : E) = ((t : E) - 1) - (star (t : E) - 1) by ring]
      exact divAt_sub ht ht'
    exact divAt_add (divAt_add (divAt_mul_left ht'' (hf3 i j)) (divAt_mul_right h2 (hf i j)))
      (divAt_mul_right ht' h1)
end PI.SqPairLocal

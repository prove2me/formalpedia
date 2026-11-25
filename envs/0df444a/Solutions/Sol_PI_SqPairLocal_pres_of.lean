-- Prove2me | solution 1 for PI.SqPairLocal.pres_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:47.980669+00:00
-- url     : https://prove2.me/submissions/47edf75b-8409-4655-995c-b66bb2ce71d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt
import Theorems.Thm_PI_SqPairLocal_one_nmem
import Theorems.Thm_PI_SqPairLocal_divAt_mul_left
import Theorems.Thm_PI_SqPairLocal_divAt_sum
import Theorems.Thm_PI_SqPairLocal_divAt_one_of_int
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField Matrix
namespace PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
section Loc
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime]
end Loc
section Mat
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {N : ℕ}
private theorem intAt_of_divAt_one {x : E} (hx : DivAt Q 1 x) : IntAt Q x := by
  unfold DivAt at hx
  unfold IntAt
  obtain ⟨s, hs, w, hw⟩ := hx
  exact ⟨s, hs, w, by simpa using hw⟩
end Mat
end PI.SqPairLocal
end
end

set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution {L : Submodule (𝓞 E) (Fin N → E)} {G : Matrix (Fin N) (Fin N) E}
    (hGG : G * Gᴴ = 1)
    (hD : ∀ y : Fin N → E, (∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L) ↔ ∀ i, IntAt Q ((Gᴴ *ᵥ y) i))
    {M : Matrix (Fin N) (Fin N) E} (hM : ∀ i j, IntAt Q ((Gᴴ * M * G) i j)) :
    ∀ y ∈ L, ∃ s : 𝓞 E, s ∉ Q ∧ s • (M *ᵥ y) ∈ L := by
  intro y hy
  have hz := (hD y).mp ⟨1, one_nmem, by rw [one_smul]; exact hy⟩
  apply (hD (M *ᵥ y)).mpr
  intro i
  have hGM : Gᴴ *ᵥ (M *ᵥ y) = (Gᴴ * M * G) *ᵥ (Gᴴ *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc (Gᴴ * M) G Gᴴ, hGG, mul_one]
  rw [hGM]
  show IntAt Q (∑ j, (Gᴴ * M * G) i j * (Gᴴ *ᵥ y) j)
  exact intAt_of_divAt_one
    (divAt_sum Finset.univ _ (fun j _ => divAt_mul_left (hM i j) (divAt_one_of_int (hz j))))
end PI.SqPairLocal

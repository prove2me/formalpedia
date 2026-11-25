-- Prove2me | solution 1 for PI.SqPairLocal.small_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:28.729819+00:00
-- url     : https://prove2.me/submissions/23e3b3e1-bb38-42b9-b725-fec326e148d3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt
import Theorems.Thm_PI_SqPairLocal_one_nmem
import Theorems.Thm_PI_SqPairLocal_divAt_mul_right
import Theorems.Thm_PI_SqPairLocal_divAt_sum
import Theorems.Thm_PI_SqPairLocal_intAt_inv_mul

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
    (hGG : G * Gᴴ = 1)
    (hD : ∀ y : Fin N → E, (∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L) ↔ ∀ i, IntAt Q ((Gᴴ *ᵥ y) i))
    {c : 𝓞 E} (hc : (c : E) ≠ 0) {M : Matrix (Fin N) (Fin N) E}
    (hM : ∀ i j, DivAt Q c ((Gᴴ * M * G) i j)) : SmallAt Q c L M := by
  unfold SmallAt
  intro y hy
  have hz := (hD y).mp ⟨1, one_nmem, by rw [one_smul]; exact hy⟩
  have hGM : Gᴴ *ᵥ (M *ᵥ y) = (Gᴴ * M * G) *ᵥ (Gᴴ *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc (Gᴴ * M) G Gᴴ, hGG, mul_one]
  have hdiv : ∀ i, DivAt Q c ((Gᴴ *ᵥ (M *ᵥ y)) i) := by
    intro i
    rw [hGM]
    show DivAt Q c (∑ j, (Gᴴ * M * G) i j * (Gᴴ *ᵥ y) j)
    exact divAt_sum Finset.univ _ (fun j _ => divAt_mul_right (hM i j) (hz j))
  obtain ⟨s, hs, hsv⟩ := (hD ((c : E)⁻¹ • (M *ᵥ y))).mpr (fun i => by
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact intAt_inv_mul hc (hdiv i))
  refine ⟨s, hs, s • ((c : E)⁻¹ • (M *ᵥ y)), hsv, ?_⟩
  have hcc : (c • (c : E)⁻¹ : E) = 1 := by
    rw [Algebra.smul_def]
    exact mul_inv_cancel₀ hc
  rw [smul_comm c s, ← smul_assoc c ((c : E)⁻¹) (M *ᵥ y), hcc, one_smul]
end PI.SqPairLocal

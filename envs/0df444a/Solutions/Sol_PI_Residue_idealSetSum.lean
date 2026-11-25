-- Prove2me | solution 1 for PI.Residue.idealSetSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:25:13.773159+00:00
-- url     : https://prove2.me/submissions/1babf696-6b8b-4e6e-96d1-59b471f0f6c7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_DvdSpanOfIdealSet
import Theorems.Thm_PI_Residue_norm_eq_cof
import Theorems.Thm_PI_Residue_toPair_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units
open scoped nonZeroDivisors ENNReal Classical
noncomputable section
open PI PI.Residue
variable {K : Type} [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution : IdealSetSum := by
  intro K _ _ s C J hJ
  set g : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} × torsion K → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ^ (-s)) *
      ENNReal.ofReal ((Ideal.absNorm ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) with hg
  have h1 : ∀ x : idealSet K J, ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s)) =
      g (toPair J C hJ x) := by
    intro x
    rw [norm_eq_cof, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      ENNReal.ofReal_mul (by positivity)]
    rfl
  calc ∑' x : idealSet K J, ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s))
      = ∑' x : idealSet K J, g (toPair J C hJ x) := tsum_congr h1
    _ ≤ ∑' p, g p := ENNReal.tsum_comp_le_tsum_of_injective (toPair_injective J C hJ) g
    _ = _ := by
      rw [ENNReal.tsum_prod', classZeta, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun I => ?_
      have : Fintype (torsion K) := Fintype.ofFinite _
      rw [tsum_fintype]
      simp only [hg]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
        Nat.card_eq_fintype_card, mul_assoc]
end PI.Residue

-- Prove2me | solution 1 for PI.Residue.sum_ne_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:44.826735+00:00
-- url     : https://prove2.me/submissions/4ef956c0-8cf9-45d7-a316-6f27d64064a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold
import Theorems.Thm_PI_Residue_exists_rep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable {K : Type} [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution (J : (Ideal (𝓞 K))⁰) (F : mixedSpace K → ℝ≥0∞) :
    ∑' x : {x : lat K J // x ≠ 0}, F ((x : lat K J) : mixedSpace K) ≤
      ∑' p : idealSet K J × ((𝓞 K)ˣ ⧸ torsion K), F (urep p.2 • (p.1 : mixedSpace K)) := by
  have hex : ∀ x : {x : lat K J // x ≠ 0}, ∃ p : idealSet K J × ((𝓞 K)ˣ ⧸ torsion K),
      urep p.2 • (p.1 : mixedSpace K) = ((x : lat K J) : mixedSpace K) := by
    rintro ⟨⟨x, hx⟩, hx0⟩
    obtain ⟨x1, h1, g, hg⟩ := exists_rep hx (fun h => hx0 (Subtype.ext h))
    exact ⟨(⟨x1, h1⟩, g), hg⟩
  choose p hp using hex
  have hinj : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext; apply Subtype.ext
    rw [← hp x, ← hp y, hxy]
  calc _ = ∑' x : {x : lat K J // x ≠ 0}, F (urep (p x).2 • ((p x).1 : mixedSpace K)) :=
        tsum_congr fun x => by rw [hp x]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective hinj
        (fun p : idealSet K J × ((𝓞 K)ˣ ⧸ torsion K) => F (urep p.2 • (p.1 : mixedSpace K)))
end PI.Residue

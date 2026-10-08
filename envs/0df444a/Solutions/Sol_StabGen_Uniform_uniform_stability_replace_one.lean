-- Prove2me | solution 1 for StabGen.Uniform.uniform_stability_replace_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T14:07:58.505976+00:00
-- url     : https://prove2.me/submissions/adc21086-fed3-4d38-ab66-01f66d3e009c

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Uniform_Stability

open FoundationsML.Stability

theorem ab3463b8_removeAt_replaceAt {Z : Type*} {m : ℕ} (S : Fin m → Z) (i : Fin m) (z' : Z) :
    StabGen.Hypothesis.removeAt (StabGen.Hypothesis.replaceAt S i z') i =
      StabGen.Hypothesis.removeAt S i := by
  unfold StabGen.Hypothesis.removeAt StabGen.Hypothesis.replaceAt
  apply Multiset.map_congr rfl
  intro j hj
  have hji : j ≠ i := by
    have := Finset.mem_erase.mp (show j ∈ Finset.univ.erase i from hj)
    exact this.1
  exact Function.update_of_ne hji z' S

open FoundationsML.Stability StabGen.Uniform in
theorem solution {X Y Y' : Type*} (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y') (m : ℕ) (β : ℝ) (hstab : HasUniformStability L A m β) :
    ∀ (S : Fin m → X × Y) (i : Fin m) (z' z : X × Y),
      |Loss L (A (StabGen.Hypothesis.trainingSet S)) z - Loss L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))) z| ≤ 2 * β := by
  intro S i z' z
  have h1 := hstab S i z
  have h2 := hstab (StabGen.Hypothesis.replaceAt S i z') i z
  rw [ab3463b8_removeAt_replaceAt] at h2
  calc _ ≤ |Loss L (A (StabGen.Hypothesis.trainingSet S)) z - Loss L (A (StabGen.Hypothesis.removeAt S i)) z|
        + |Loss L (A (StabGen.Hypothesis.removeAt S i)) z - Loss L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))) z| :=
          abs_sub_le _ _ _
    _ ≤ β + β := by
          refine add_le_add h1 ?_
          rw [abs_sub_comm]; exact h2
    _ = 2 * β := by ring

-- Prove2me | solution 1 for SensitivityCampaign.reach_source_q5_best_3738277295413674
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-20T23:12:30.877354+00:00
-- url     : https://prove2.me/submissions/5112fcc0-0c63-4f47-8b70-29327b2a8906

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityPrimitiveCampaign_reach_source_q5_3738277295413674_strict
open scoped Classical
set_option autoImplicit false

theorem solution : SensitivityCampaign.AchievesExponent
    (Real.log (1522813785050025472152230187890625 : ℝ) / Real.log (3738277295413674 : ℝ)) := by
  have semantic_equivalence :
      ((∀ ε : ℝ, 0 < ε → ∀ S : ℕ, 2 ≤ S →
        ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
          let flipBits : (Fin n → Bool) → Finset (Fin n) → (Fin n → Bool) :=
            fun x B i => if i ∈ B then !(x i) else x i
          let s : ℕ := Finset.univ.sup (fun x : Fin n → Bool =>
            (Finset.univ.filter fun i : Fin n => f (flipBits x {i}) ≠ f x).card)
          let bs : ℕ := Finset.univ.sup (fun x : Fin n → Bool =>
            Finset.univ.sup (fun blocks : Finset (Finset (Fin n)) =>
              if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
                  (∀ B ∈ blocks, B.Nonempty ∧ f (flipBits x B) ≠ f x)
              then blocks.card else 0))
          S ≤ s ∧ (s : ℝ) ^ ((Real.log (1522813785050025472152230187890625 : ℝ) / Real.log (3738277295413674 : ℝ)) - ε) ≤ (bs : ℝ)) ∧
      (Real.log (1522813785050025472152230187890625 : ℝ) /
          Real.log (3738289747988852 : ℝ) < (Real.log (1522813785050025472152230187890625 : ℝ) / Real.log (3738277295413674 : ℝ)))) ↔
      (SensitivityCampaign.AchievesExponent (Real.log (1522813785050025472152230187890625 : ℝ) / Real.log (3738277295413674 : ℝ)) ∧
        (Real.log (1522813785050025472152230187890625 : ℝ) /
          Real.log (3738289747988852 : ℝ) < Real.log (1522813785050025472152230187890625 : ℝ) / Real.log (3738277295413674 : ℝ))) := by
      simp only [SensitivityCampaign.AchievesExponent, OAI.Paper320.sensitivity,
        OAI.Paper320.blockSensitivity]
      congr! <;> simp only [OAI.Paper320.sensitivityAt, OAI.Paper320.blockSensitivityAt] <;>
        congr! <;> simp only [OAI.Paper320.flip] <;> congr!
  exact (semantic_equivalence.mp
    SensitivityPrimitiveCampaign.reach_source_q5_3738277295413674_strict).1
#print axioms solution

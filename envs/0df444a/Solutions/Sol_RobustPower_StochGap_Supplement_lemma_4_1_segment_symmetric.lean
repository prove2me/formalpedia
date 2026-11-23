-- Prove2me | solution 1 for RobustPower.StochGap.Supplement.lemma_4_1_segment_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T21:13:18.590431+00:00
-- url     : https://prove2.me/submissions/f9caf5e4-4388-4b05-89aa-0e61b611efff

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
namespace RobustPower.StochGap.Supplement

/-- Lemma 4.1 (p. 25): the segment `{b ∈ ℝ²₊ | b₁ + b₂ = 1}` is symmetric (Definition 1.2)
with centre `u⁰ = (1/2, 1/2)`. -/

theorem lemma_4_1_segment_symmetric :
    RobustPower.StochGap.IsSymmetricAbout {v : Fin 2 → ℝ | 0 ≤ v ∧ v 0 + v 1 = 1}
      (fun _ => (1 / 2 : ℝ)) := by
  refine ⟨⟨fun i => by norm_num, by norm_num⟩, fun z => ?_⟩
  simp only [Set.mem_setOf_eq, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Fin.forall_fin_two]
  constructor <;> rintro ⟨⟨h0, h1⟩, h⟩ <;> exact ⟨⟨by linarith, by linarith⟩, by linarith⟩


end RobustPower.StochGap.Supplement

open RobustPower.StochGap.Supplement in
theorem solution :
    RobustPower.StochGap.IsSymmetricAbout {v : Fin 2 → ℝ | 0 ≤ v ∧ v 0 + v 1 = 1}
      (fun _ => (1 / 2 : ℝ)) := by
  refine ⟨⟨fun i => by norm_num, by norm_num⟩, fun z => ?_⟩
  simp only [Set.mem_setOf_eq, Pi.le_def, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Fin.forall_fin_two]
  constructor <;> rintro ⟨⟨h0, h1⟩, h⟩ <;> exact ⟨⟨by linarith, by linarith⟩, by linarith⟩


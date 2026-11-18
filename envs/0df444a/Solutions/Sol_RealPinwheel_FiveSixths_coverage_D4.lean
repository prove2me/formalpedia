-- Prove2me | solution 1 for RealPinwheel.FiveSixths.coverage_D4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:07.35109+00:00
-- url     : https://prove2.me/submissions/95fa1f5b-dc27-44c9-af9a-037d0cb1c233

import Theorems.Thm_RealPinwheel_FiveSixths_linearCoverCheck_sound
import Theorems.Thm_RealPinwheel_FiveSixths_checked_linear_D4_0000
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0

theorem solution (d : Fin 4 → ℝ) (hpos : ∀ i, 0 < d i) (hord : Antitone d)
    (hsum : (∑ i : Fin 4, d i) ≤ (5 : ℝ) / 6) :
    ∃ k : Fin certificateD4.size, codeBox certificateD4[k.val] d := by
  have hs : (∑ i, if i.val < 4 then d i else 0) ≤ (5 : ℝ) / 6 := by
    simpa only [Fin.is_lt, ↓reduceIte] using hsum
  obtain ⟨j, hb⟩ := linearCoverCheck_sound 4 69 codeFunctionD4 linearTreeD4_0000
    RealPinwheel.FiveSixths.checked_linear_D4_0000 d hpos hord hs
  have he (i : Fin 69) : codeFunctionD4 i.val = certificateD4[i.val]'(by change i.val < 69; exact i.isLt) := by
    fin_cases i <;> rfl
  refine ⟨⟨j.val, by change j.val < 69; exact j.isLt⟩, ?_⟩
  simpa only [he j] using hb

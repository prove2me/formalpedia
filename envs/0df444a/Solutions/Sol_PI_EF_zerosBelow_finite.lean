-- Prove2me | solution 1 for PI.EF.zerosBelow_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:46.697539+00:00
-- url     : https://prove2.me/submissions/ec0f0655-fe0e-4567-bd8b-304a88889e41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open DirichletCharacter
namespace PI.EF
theorem _root_.solution {C : ℝ} (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (T : ℝ) : (ZerosBelow χ T).Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.Icc (-⌈T⌉) ⌈T⌉).finite_toSet
    (fun n _ => (hC N χ hχ (n : ℝ)).1)) ?_
  intro ρ hρ
  obtain ⟨h0, h1, him, hL⟩ := hρ
  have hb := abs_lt.1 him
  refine Set.mem_biUnion (x := ⌊ρ.im⌋) (Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨?_, ?_⟩))
    ⟨h0, h1, ?_, hL⟩
  · have h := Int.floor_mono hb.1.le
    rw [Int.floor_neg] at h
    exact h
  · exact (Int.floor_mono hb.2.le).trans (Int.floor_le_ceil T)
  · rw [abs_le]
    constructor <;> linarith [Int.floor_le ρ.im, Int.sub_one_lt_floor ρ.im]
end PI.EF

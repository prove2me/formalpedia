-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_blockForms_isFormSystem_13915fe0a620
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:10:27.936188+00:00
-- url     : https://prove2.me/submissions/46ce3a9c-623c-4655-b80f-f83d0ebb951b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_whole_isLive_21de13e30d11

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : (blockAddData n k₀).IsFormSystem 1 (blockForms n k₀) where
  pos _ := le_rfl
  nonneg k := by
    have : (0 : ℤ) ≤ (Pi.single k₀ 1 : ι → ℤ) k := by
      by_cases h : k = k₀
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    change (0 : ℤ) ≤ ((1 : ι → ℕ) k : ℤ) + (Pi.single k₀ 1 : ι → ℤ) k
    simp only [Pi.one_apply, Nat.cast_one]
    linarith
  homog c j := ⟨1 + (Pi.single k₀ 1 : ι → ℕ),
    (isWeightedHomogeneous_chartMonomial c 1).mul (isWeightedHomogeneous_X ℤ (coordDeg n) _),
    fun k ↦ by
      change (((1 : ι → ℕ) + (Pi.single k₀ 1 : ι → ℕ)) k : ℤ) = ((1 : ι → ℕ) k : ℤ) + (Pi.single k₀ 1 : ι → ℤ) k
      rw [Pi.add_apply, Nat.cast_add, single_cast]⟩
  value c _ j := by simp only [blockForms, map_mul]; rfl
  dead c hc := absurd (ArithVariety.whole_isLive n c) hc
end GroundTheory.Heights₂.Heights

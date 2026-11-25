-- Prove2me | solution 1 for P2M_GlobalTheory_HilbertSamuelPS_lexOrder_sub_smul__a846a0077eea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:42.117236+00:00
-- url     : https://prove2.me/submissions/59b9e7ad-3734-46fc-a129-7709c19b45f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries
variable {D : ℕ}
namespace GlobalTheory.HilbertSamuelPS
theorem _root_.solution {g h : MvPowerSeries (Fin D) ℂ} (hg : g ≠ 0)
    (heq : lexOrder g = lexOrder h) : ∃ c : ℂ, lexOrder g < lexOrder (g - c • h) := by
  obtain ⟨d, hd⟩ := exists_finsupp_eq_lexOrder_of_ne_zero hg
  have hhd := coeff_ne_zero_of_lexOrder (hd.symm.trans heq)
  refine ⟨coeff d g / coeff d h, lt_of_le_of_ne ?_ ?_⟩
  · rw [le_lexOrder_iff]
    intro d' hd'
    have h1 := coeff_eq_zero_of_lt_lexOrder hd'
    have h2 := coeff_eq_zero_of_lt_lexOrder (heq ▸ hd')
    simp [h1, h2]
  · intro heq2
    apply coeff_ne_zero_of_lexOrder (hd.symm.trans heq2)
    simp [div_mul_cancel₀ _ hhd]
end GlobalTheory.HilbertSamuelPS

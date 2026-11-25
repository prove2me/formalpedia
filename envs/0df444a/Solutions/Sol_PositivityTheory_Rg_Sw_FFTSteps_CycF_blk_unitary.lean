-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.blk_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:39:00.507546+00:00
-- url     : https://prove2.me/submissions/98f65336-be71-4283-a2e8-79e7a1ae33e9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTA
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_sum_rw
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_blk_block
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_blk_of
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_blk_of_not

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} (ε : Fin m → Bool)
variable {ε}
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
theorem _root_.solution (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (hv : v ∈ Matrix.unitaryGroup (Rw ε β) ℂ) :
    blk ε β v ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hv ⊢
  ext a c
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.star_apply]
  by_cases ha : ε a = β
  · by_cases hc : ε c = β
    · have key := congrFun (congrFun hv ⟨a, ha⟩) ⟨c, hc⟩
      rw [Matrix.mul_apply, Matrix.one_apply] at key
      simp only [Matrix.star_apply] at key
      have e1 : ∀ b, blk ε β v a b * star (blk ε β v c b) =
          if h : ε b = β then v ⟨a, ha⟩ ⟨b, h⟩ * star (v ⟨c, hc⟩ ⟨b, h⟩) else 0 := by
        intro b
        rw [blk_of β v ha, blk_of β v hc]
        by_cases hb : ε b = β
        · rw [dif_pos hb, dif_pos hb, dif_pos hb]
        · rw [dif_neg hb, dif_neg hb, dif_neg hb, zero_mul]
      rw [Finset.sum_congr rfl (fun b _ => e1 b), sum_rw β (fun j => v ⟨a, ha⟩ j * star (v ⟨c, hc⟩ j)), key]
      by_cases hac : a = c
      · subst hac; simp
      · rw [if_neg (fun h => hac (congrArg Subtype.val h)), if_neg hac]
    · have e1 : ∀ b, blk ε β v a b * star (blk ε β v c b) = if c = b then blk ε β v a b else 0 := by
        intro b
        rw [blk_of_not β v hc b]
        by_cases hcb : c = b
        · rw [if_pos hcb, if_pos hcb, star_one, mul_one]
        · rw [if_neg hcb, if_neg hcb, star_zero, mul_zero]
      rw [Finset.sum_congr rfl (fun b _ => e1 b), Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      rw [blk_block β v a c (by rw [ha]; exact fun h => hc h.symm), if_neg (by rintro rfl; exact hc ha)]
  · have e1 : ∀ b, blk ε β v a b * star (blk ε β v c b) = if a = b then star (blk ε β v c b) else 0 := by
      intro b
      rw [blk_of_not β v ha b]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab, one_mul]
      · rw [if_neg hab, if_neg hab, zero_mul]
    rw [Finset.sum_congr rfl (fun b _ => e1 b), Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    by_cases hc : ε c = β
    · rw [blk_block β v c a (by rw [hc]; exact fun h => ha h.symm), star_zero,
        if_neg (by rintro rfl; exact ha hc)]
    · rw [blk_of_not β v hc a]
      by_cases hca : c = a
      · subst hca; simp
      · rw [if_neg hca, star_zero, if_neg (fun h => hca h.symm)]
end PositivityTheory.Rg.Sw.FFTSteps.CycF

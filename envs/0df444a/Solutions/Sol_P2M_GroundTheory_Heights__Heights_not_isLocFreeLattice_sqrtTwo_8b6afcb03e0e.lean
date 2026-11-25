-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_not_isLocFreeLattice_sqrtTwo_8b6afcb03e0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:36.647592+00:00
-- url     : https://prove2.me/submissions/bbe09b84-4bd3-4cc5-9968-ef78e4534ed6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_ratsInReal_of_mem_locPrimeTo_5ce87b3c663b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sqrt_two_not_mem_ratsInReal_55d20139eb84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_one_mem_sqrtTwoLattice_095e75f5c692
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sqrtTwo_mem_sqrtTwoLattice_5b389195a178

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
open IndefiniteRowSideFullHecke.Antisym
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (r : ℕ) :
    ¬ IsLocFreeLattice (locPrimeTo chartOne 2) r sqrtTwoLattice.toAddSubgroup := by
  rintro ⟨-, k, f, c, hf, -, hsum, hfr⟩
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hsum
  obtain ⟨b, hli, -, hiff⟩ := hfr l
  have hr : r ≤ 1 := by simpa using hli.fintype_card_le_finrank
  have hrat : ∀ a : ℝ, (∃ n : ℕ, f l ^ n * a ∈ locPrimeTo chartOne 2) → a ∈ ratsInReal := by
    rintro a ⟨n, hn⟩
    have hfn : f l ^ n ≠ 0 := pow_ne_zero _ hl
    have : a = f l ^ n * a / f l ^ n := by field_simp
    rw [this]
    exact div_mem (mem_ratsInReal_of_mem_locPrimeTo hn)
      (pow_mem (mem_ratsInReal_of_mem_locPrimeTo (hf l)) n)
  obtain ⟨a, ha, h1⟩ := (hiff 1).1 ⟨0, by simpa using one_mem_sqrtTwoLattice⟩
  obtain ⟨a', ha', h2⟩ := (hiff √2).1 ⟨0, by simpa using sqrtTwo_mem_sqrtTwoLattice⟩
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
  · simp at h1
  · simp only [Fin.sum_univ_one, smul_eq_mul] at h1 h2
    have ha0 : a 0 ≠ 0 := by rintro h; rw [h, zero_mul] at h1; exact one_ne_zero h1
    apply sqrt_two_not_mem_ratsInReal
    have : √2 = a' 0 / a 0 := by
      rw [eq_div_iff ha0, h2, mul_assoc, mul_comm (b 0), ← h1, mul_one]
    rw [this]
    exact div_mem (hrat _ (ha' 0)) (hrat _ (ha 0))
end GroundTheory.Heights₂.Heights

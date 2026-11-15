-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.canonicalSecondLowerRanks
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T19:14:36.92645+00:00
-- url     : https://prove2.me/submissions/4b96f1ca-a2b3-4ea9-b50b-969732db6719

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_secondCanonicalLowerRegion1
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_secondCanonicalLowerRegion2
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_secondCanonicalLowerRegion3
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_secondCanonicalLowerRegion4
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_secondCanonicalLowerRegion5
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace StableVotingDistortion.Lemma9Reduction
open Set PaperCurve PaperMiddle PaperBox
private def OnBox (a A b B c C : ℚ) : Prop :=
  ∀ {p q z : ℝ}, p∈Icc (16/25:ℝ) (99/100) → q∈Icc (0:ℝ) PaperCurve.lam → z∈Icc p 1 →
    (a:ℝ)≤p → p≤(A:ℝ) → (b:ℝ)≤q → q≤(B:ℝ) → (c:ℝ)≤z → z≤(C:ℝ) →
    highSecond PaperCurve.lam score (canonical score p) 1 (-(canonical score p*(1-p))) p q z 1 ≤ 0
private theorem cut0 {a A b B c C : ℚ} (u : ℚ)
    (left : OnBox a u b B c C) (right : OnBox u A b B c C) : OnBox a A b B c C := by
  intro p q z hp hq hz a0 a1 b0 b1 c0 c1
  by_cases h : p≤(u:ℝ)
  · exact left hp hq hz a0 h b0 b1 c0 c1
  · exact right hp hq hz (le_of_not_ge h) a1 b0 b1 c0 c1
private theorem cut1 {a A b B c C : ℚ} (u : ℚ)
    (left : OnBox a A b u c C) (right : OnBox a A u B c C) : OnBox a A b B c C := by
  intro p q z hp hq hz a0 a1 b0 b1 c0 c1
  by_cases h : q≤(u:ℝ)
  · exact left hp hq hz a0 a1 b0 h c0 c1
  · exact right hp hq hz a0 a1 (le_of_not_ge h) b1 c0 c1
private theorem cut2 {a A b B c C : ℚ} (u : ℚ)
    (left : OnBox a A b B c u) (right : OnBox a A b B u C) : OnBox a A b B c C := by
  intro p q z hp hq hz a0 a1 b0 b1 c0 c1
  by_cases h : z≤(u:ℝ)
  · exact left hp hq hz a0 a1 b0 b1 c0 h
  · exact right hp hq hz a0 a1 b0 b1 (le_of_not_ge h) c1
private theorem verified : OnBox (16/25) (99/100) 0 (703/2500) (16/25) 1 :=
  (cut2 (41/50) (by
    intro p q z hp hq hz a0 a1 b0 b1 c0 c1
    apply secondCanonicalLowerRegion1 hp hq hz
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro a0 a1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro b0 b1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro c0 c1) (cut0 (163/200) (cut2 (91/100) (by
    intro p q z hp hq hz a0 a1 b0 b1 c0 c1
    apply secondCanonicalLowerRegion2 hp hq hz
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro a0 a1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro b0 b1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro c0 c1) (cut1 (703/5000) (by
    intro p q z hp hq hz a0 a1 b0 b1 c0 c1
    apply secondCanonicalLowerRegion3 hp hq hz
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro a0 a1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro b0 b1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro c0 c1) (by
    intro p q z hp hq hz a0 a1 b0 b1 c0 c1
    apply secondCanonicalLowerRegion4 hp hq hz
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro a0 a1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro b0 b1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro c0 c1))) (by
    intro p q z hp hq hz a0 a1 b0 b1 c0 c1
    apply secondCanonicalLowerRegion5 hp hq hz
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro a0 a1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro b0 b1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using And.intro c0 c1)))
end StableVotingDistortion.Lemma9Reduction
open Set StableVotingDistortion StableVotingDistortion.PaperCurve StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperBox StableVotingDistortion.Lemma9Reduction
theorem solution {p q z : ℝ} (hp : p ∈ Icc (16/25:ℝ) (99/100)) (hq : q ∈ Icc (0:ℝ) (703/2500:ℝ)) (hz : z ∈ Icc p 1) : highSecond PaperCurve.lam score (canonical score p) 1 (-(canonical score p*(1-p))) p q z 1 ≤ 0 := by
  have hqa : q ∈ Icc (0:ℝ) PaperCurve.lam := ⟨hq.1,hq.2.trans (by norm_num [PaperCurve.lam,PaperCurve.lamQ])⟩
  apply verified hp hqa hz
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using hp.1
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using hp.2
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using hq.1
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using hq.2
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using hp.1.trans hz.1
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using hz.2

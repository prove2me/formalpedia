-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.canonicalFirstUpperRanks
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:58:54.31567+00:00
-- url     : https://prove2.me/submissions/e0fab035-3e91-46d3-9635-6e09d12434e2

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalUpperBox1
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalUpperBox2
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalUpperBox3
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalUpperBox4
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalUpperBox5
namespace StableVotingDistortion.Lemma9Reduction
open Set PaperCurve PaperMiddle PaperBox
private def OnBox (p P q Q : ℚ) : Prop :=
  ∀ {x y : ℝ}, (p:ℝ)≤x → x≤(P:ℝ) → (q:ℝ)≤y → y≤(Q:ℝ) →
    y+PaperMiddle.canonical PaperCurve.score x*deltaP PaperCurve.score x y≤PaperCurve.lam

private theorem cutP {p P q Q : ℚ} (u : ℚ) (a : OnBox p u q Q) (b : OnBox u P q Q) : OnBox p P q Q := by
  intro x y hp hP hq hQ
  by_cases h : x≤(u:ℝ)
  · exact a hp h hq hQ
  · exact b (le_of_not_ge h) hP hq hQ
private theorem cutQ {p P q Q : ℚ} (u : ℚ) (a : OnBox p P q u) (b : OnBox p P u Q) : OnBox p P q Q := by
  intro x y hp hP hq hQ
  by_cases h : y≤(u:ℝ)
  · exact a hp hP hq h
  · exact b hp hP (le_of_not_ge h) hQ


private theorem verified : OnBox (16/25) (99/100) (703/2500) (703/1250) := (cutP (163/200) (by intro x y a b c d; apply canonicalUpperBox1 <;> constructor <;> first | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using a | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using b | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using c | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using d) (cutQ (2109/5000) (cutP (361/400) (by intro x y a b c d; apply canonicalUpperBox2 <;> constructor <;> first | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using a | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using b | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using c | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using d) (cutQ (703/2000) (by intro x y a b c d; apply canonicalUpperBox3 <;> constructor <;> first | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using a | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using b | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using c | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using d) (by intro x y a b c d; apply canonicalUpperBox4 <;> constructor <;> first | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using a | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using b | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using c | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using d))) (by intro x y a b c d; apply canonicalUpperBox5 <;> constructor <;> first | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using a | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using b | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using c | simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero] using d)))
end StableVotingDistortion.Lemma9Reduction
open Set StableVotingDistortion StableVotingDistortion.PaperCurve StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperBox StableVotingDistortion.Lemma9Reduction
theorem solution {p q : ℝ} (hp : p ∈ Icc (16/25:ℝ) (99/100)) (hq : q ∈ Icc ((703/2500):ℝ) PaperCurve.lam) : q+PaperMiddle.canonical score p*deltaP score p q ≤ PaperCurve.lam := by
  apply verified
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using hp.1
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using hp.2
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,PaperCurve.lam,PaperCurve.lamQ] using hq.1
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,PaperCurve.lam,PaperCurve.lamQ] using hq.2

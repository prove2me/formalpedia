-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.canonicalUpperBox4
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:55:00.401679+00:00
-- url     : https://prove2.me/submissions/0b0a7239-5bfe-4614-a4fc-0a7ed1149110

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalRectangleBound
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperCurve PaperMiddle PaperBox PaperBox.Bounds
private def accepts (b c : Bounds) : Bool :=
    let select (val : PaperCurve.Piece → ℚ → ℚ) (last : ℚ) (q : ℚ) := PaperCurve.pieces.foldr (fun (row : PaperCurve.Piece) rest => if q≤row.hi then val row q else rest) last
    let vq (q : ℚ) := if q∈Icc 0 1 then PaperCurve.quickScore q else select PaperCurve.Piece.qvalue PaperCurve.endKnot.y q
    let jq (q : ℚ) := if q∈Icc 0 1 then PaperCurve.quickJ q else select PaperCurve.Piece.qprimitive PaperCurve.endKnot.j q
    let meet01 (i : Bounds) : Bounds := ⟨max i.lo 0,min i.hi 1⟩
    let v (i : Bounds) := PaperBox.decreasingRange (fun z => point (vq z)) (meet01 i)
    let j (i : Bounds) := PaperBox.unimodalRange (fun z => point (jq z)) PaperCurve.lamQ (meet01 i)
    let x := ((point 1).minus b).plus c
    let e : ℚ := 1+1/20000
    let s := (((point e).times ((j x).minus (j c))).minus (((point e).times b).times (v x))).minus (((point PaperCurve.lamQ).minus c).times (v b))
    let t := (((point e).times b).times ((v x).minus (v c))).plus (j b)
    let d := PaperCurve.anchor b s
    let z := PaperCurve.anchor c t
    decide (((16/25:ℚ)≤b.lo ∧ b.hi≤(99/100:ℚ) ∧ 0≤c.lo ∧ c.hi≤PaperCurve.lamQ) ∧
      e*d*(jq (1-d+z)-jq z)-(PaperCurve.lamQ-z)*jq d+PaperCurve.deviation b s+PaperCurve.deviation c t≤0)

private def OnBox (p P q Q : ℚ) : Prop :=
  ∀ {x y : ℝ}, (p:ℝ)≤x → x≤(P:ℝ) → (q:ℝ)≤y → y≤(Q:ℝ) →
    y+PaperMiddle.canonical PaperCurve.score x*deltaP PaperCurve.score x y≤PaperCurve.lam

private theorem atLeaf {p P q Q : ℚ} (h : accepts ⟨p,P⟩ ⟨q,Q⟩=true) : OnBox p P q Q := by
  intro x y a b c d
  exact canonicalRectangleBound (b:=⟨p,P⟩) (c:=⟨q,Q⟩) h ⟨a,b⟩ ⟨c,d⟩

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

private inductive Partition where
  | leaf | x (a b : Partition) | y (a b : Partition)
private def passes : Partition → ℚ → ℚ → ℚ → ℚ → Bool
  | .leaf,p,P,q,Q => accepts ⟨p,P⟩ ⟨q,Q⟩
  | .x a b,p,P,q,Q => passes a p ((p+P)/2) q Q && passes b ((p+P)/2) P q Q
  | .y a b,p,P,q,Q => passes a p P q ((q+Q)/2) && passes b p P ((q+Q)/2) Q
private theorem certify (t : Partition) {p P q Q : ℚ} (h : passes t p P q Q=true) : OnBox p P q Q := by
  induction t generalizing p P q Q with
  | leaf => exact atLeaf h
  | x l r il ir => exact cutP _ (il (Bool.and_eq_true_iff.mp h).1) (ir (Bool.and_eq_true_iff.mp h).2)
  | y l r il ir => exact cutQ _ (il (Bool.and_eq_true_iff.mp h).1) (ir (Bool.and_eq_true_iff.mp h).2)
private theorem certBlock0 : OnBox (361/400) (757/800) (703/2000) (2109/5000) := certify (.y (.x (.y (.x .leaf .leaf) (.x .leaf .leaf)) (.y (.x (.y .leaf .leaf) (.y (.x .leaf .leaf) .leaf)) (.x .leaf (.y .leaf .leaf)))) (.x (.y .leaf .leaf) (.y (.x .leaf (.y .leaf .leaf)) (.x .leaf .leaf)))) (by decide +kernel)

private theorem certBlock1 : OnBox (757/800) (1549/1600) (703/2000) (7733/20000) := certify (.y (.x (.y (.x .leaf .leaf) (.x .leaf .leaf)) (.y (.x (.y .leaf .leaf) (.y .leaf .leaf)) (.x .leaf (.y .leaf .leaf)))) (.x (.y (.x .leaf .leaf) .leaf) (.y (.x .leaf (.y .leaf .leaf)) (.x .leaf .leaf)))) (by decide +kernel)

private theorem certBlock2 : OnBox (1549/1600) (3133/3200) (703/2000) (14763/40000) := certify (.y (.x (.y (.x .leaf .leaf) (.x .leaf .leaf)) (.y (.x .leaf (.y .leaf .leaf)) (.x .leaf .leaf))) (.x (.y (.x .leaf .leaf) .leaf) (.y (.x .leaf .leaf) (.x .leaf .leaf)))) (by decide +kernel)

private theorem certBlock3 : OnBox (3133/3200) (99/100) (703/2000) (28823/80000) := certify (.x (.y (.x (.y .leaf .leaf) (.y (.x .leaf .leaf) .leaf)) (.x (.y .leaf .leaf) (.y .leaf .leaf))) (.y (.x (.y (.x .leaf .leaf) (.x .leaf .leaf)) (.y (.x (.y .leaf .leaf) (.y .leaf .leaf)) (.x .leaf (.y .leaf .leaf)))) (.x (.y (.x .leaf .leaf) (.x .leaf .leaf)) (.y (.x .leaf (.y .leaf .leaf)) (.x .leaf (.y .leaf .leaf)))))) (by decide +kernel)

private theorem certBlock4 : OnBox (3133/3200) (99/100) (28823/80000) (14763/40000) := certify (.x (.y (.x (.y .leaf .leaf) (.y .leaf .leaf)) (.x .leaf (.y .leaf .leaf))) (.y (.x (.y (.x .leaf .leaf) (.x .leaf .leaf)) (.y (.x .leaf .leaf) (.x .leaf .leaf))) (.x (.y (.x .leaf .leaf) .leaf) (.y (.x .leaf .leaf) (.x .leaf .leaf))))) (by decide +kernel)

private theorem certBlock5 : OnBox (1549/1600) (3133/3200) (14763/40000) (7733/20000) := certify (.y (.x (.y .leaf .leaf) (.y (.x .leaf .leaf) (.x .leaf .leaf))) (.x (.y .leaf .leaf) (.y (.x .leaf .leaf) (.x .leaf .leaf)))) (by decide +kernel)

private theorem certBlock6 : OnBox (3133/3200) (99/100) (14763/40000) (30229/80000) := certify (.x (.y (.x .leaf (.y .leaf .leaf)) (.x .leaf (.y .leaf .leaf))) (.y (.x (.y .leaf .leaf) (.y (.x .leaf .leaf) (.x .leaf .leaf))) (.x (.y .leaf .leaf) (.y (.x .leaf .leaf) (.x .leaf .leaf))))) (by decide +kernel)

private theorem certBlock7 : OnBox (3133/3200) (99/100) (30229/80000) (7733/20000) := certify (.x (.y (.x .leaf (.x .leaf .leaf)) (.x .leaf .leaf)) (.y (.x (.y .leaf .leaf) (.y (.x .leaf .leaf) (.x .leaf .leaf))) (.x (.y .leaf .leaf) (.y (.x .leaf .leaf) (.x .leaf .leaf))))) (by decide +kernel)

private theorem certBlock8 : OnBox (757/800) (1549/1600) (7733/20000) (2109/5000) := certify (.y (.x (.y .leaf .leaf) (.y (.x .leaf .leaf) (.x .leaf .leaf))) (.x (.y .leaf .leaf) (.y (.x .leaf .leaf) (.x .leaf .leaf)))) (by decide +kernel)

private theorem certBlock9 : OnBox (1549/1600) (3133/3200) (7733/20000) (16169/40000) := certify (.y (.x (.y .leaf .leaf) (.y .leaf .leaf)) (.x (.y .leaf .leaf) (.y .leaf .leaf))) (by decide +kernel)

private theorem certBlock10 : OnBox (3133/3200) (99/100) (7733/20000) (16169/40000) := certify (.y (.x (.y (.x .leaf .leaf) (.x .leaf .leaf)) (.y (.x (.x .leaf .leaf) (.y (.x .leaf .leaf) (.x .leaf .leaf))) (.x (.x .leaf .leaf) (.y .leaf .leaf)))) (.x (.y (.x .leaf .leaf) (.x .leaf .leaf)) (.y (.x (.x .leaf .leaf) (.y .leaf .leaf)) (.x (.x .leaf .leaf) (.y .leaf .leaf))))) (by decide +kernel)

private theorem certBlock11 : OnBox (1549/1600) (99/100) (16169/40000) (2109/5000) := certify (.x (.y (.x .leaf (.y .leaf .leaf)) (.x .leaf (.x .leaf .leaf))) (.y (.x (.y (.x .leaf .leaf) (.x .leaf .leaf)) (.y (.x .leaf (.x .leaf (.y .leaf .leaf))) (.x .leaf (.x .leaf .leaf)))) (.x (.y (.x .leaf .leaf) (.x .leaf .leaf)) (.y (.x .leaf (.x .leaf .leaf)) (.x .leaf (.x .leaf .leaf)))))) (by decide +kernel)
private theorem verified : OnBox (361/400) (99/100) (703/2000) (2109/5000) := (cutP (757/800) certBlock0 (cutQ (7733/20000) (cutP (1549/1600) certBlock1 (cutQ (14763/40000) (cutP (3133/3200) certBlock2 (cutQ (28823/80000) certBlock3 certBlock4)) (cutP (3133/3200) certBlock5 (cutQ (30229/80000) certBlock6 certBlock7)))) (cutP (1549/1600) certBlock8 (cutQ (16169/40000) (cutP (3133/3200) certBlock9 certBlock10) certBlock11))))
end StableVotingDistortion.Lemma9Reduction
open StableVotingDistortion StableVotingDistortion.Lemma9Reduction Set
theorem solution {p q : ℝ} (hp : p∈Icc ((361/400):ℝ) ((99/100):ℝ)) (hq : q∈Icc ((703/2000):ℝ) ((2109/5000):ℝ)) : q+PaperMiddle.canonical PaperCurve.score p*deltaP PaperCurve.score p q ≤ PaperCurve.lam := by
  apply verified
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using hp.1
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using hp.2
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,PaperCurve.lam,PaperCurve.lamQ] using hq.1
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,PaperCurve.lam,PaperCurve.lamQ] using hq.2

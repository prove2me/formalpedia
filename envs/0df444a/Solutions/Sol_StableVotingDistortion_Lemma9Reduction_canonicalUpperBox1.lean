-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.canonicalUpperBox1
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:54:55.404605+00:00
-- url     : https://prove2.me/submissions/bba988c8-d812-42e9-a53b-80b639050cd1

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
private theorem certBlock0 : OnBox (16/25) (163/200) (703/2500) (703/1250) := certify (.y (.x (.y .leaf .leaf) (.y (.x .leaf (.y (.x .leaf .leaf) .leaf)) (.x .leaf .leaf))) (.x (.y .leaf .leaf) (.y .leaf .leaf))) (by decide +kernel)
private theorem verified : OnBox (16/25) (163/200) (703/2500) (703/1250) := certBlock0
end StableVotingDistortion.Lemma9Reduction
open StableVotingDistortion StableVotingDistortion.Lemma9Reduction Set
theorem solution {p q : ℝ} (hp : p∈Icc ((16/25):ℝ) ((163/200):ℝ)) (hq : q∈Icc ((703/2500):ℝ) ((703/1250):ℝ)) : q+PaperMiddle.canonical PaperCurve.score p*deltaP PaperCurve.score p q ≤ PaperCurve.lam := by
  apply verified
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using hp.1
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using hp.2
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,PaperCurve.lam,PaperCurve.lamQ] using hq.1
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,PaperCurve.lam,PaperCurve.lamQ] using hq.2

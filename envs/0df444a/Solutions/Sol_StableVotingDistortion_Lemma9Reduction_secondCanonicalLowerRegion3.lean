-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.secondCanonicalLowerRegion3
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T19:08:30.596601+00:00
-- url     : https://prove2.me/submissions/94cb52e7-3775-4e7f-9978-5336c54875a2

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_secondCanonicalRectangleBound
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace StableVotingDistortion.Lemma9Reduction
open Set PaperCurve PaperMiddle PaperBox PaperBox.Bounds
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
private def slopeAt (d : Bounds) : Bounds :=
    let i := clampBox d
    let localBound (r : Piece) : Bounds :=
      let dx := (⟨max i.lo r.lo,min i.hi r.hi⟩ : Bounds).minus (point r.lo)
      r.slopeCoeffs.foldr (fun a acc => (point a).plus (dx.times acc)) (point 0)
    let acc (row : Piece) (rest : Option Bounds) : Option Bounds :=
      if i.lo ≤ row.hi ∧ row.lo ≤ i.hi then
        match rest with
        | none => some (localBound row)
        | some t => some ⟨min (localBound row).lo t.lo,max (localBound row).hi t.hi⟩
      else rest
    ((pieces.foldr acc none).getD (point 0)).times (clampSlopeBox d)
private def accept (b c d D : Bounds) : Bool :=
    let x := (d.minus b).plus c
    let e : ℚ := 1+1/20000
    let a := ((c.plus d).plus (quickTotalScoreBox d)).minus (point lamQ)
    let k := ((quickTotalPrimitiveBox x).minus (quickTotalPrimitiveBox d)).minus (quickTotalPrimitiveBox c)
    let s := ((a.times (quickTotalPrimitiveSlope b)).plus ((point e).times k)).minus (((point e).times b).times (quickTotalPrimitiveSlope x))
    let t := (quickTotalPrimitiveBox b).plus (((point e).times b).times ((quickTotalPrimitiveSlope x).minus (quickTotalPrimitiveSlope c)))
    let v := ((quickTotalPrimitiveBox b).times ((point 1).plus D)).plus (((point e).times b).times ((quickTotalPrimitiveSlope x).minus (quickTotalPrimitiveSlope d)))
    let m := anchor b s
    let j := anchor c t
    let y := anchor d v
    let residual := (j+y+quickTotalScore y-lamQ)*quickTotalJ m+e*m*(quickTotalJ (y-m+j)-quickTotalJ y-quickTotalJ j)
    decide (d.hi<b.lo ∨ (d.hi=1 ∧ 0 ≤ v.lo) ∨ residual+deviation b s+deviation c t+deviation d v≤0)
private theorem atLeaf {a A b B c C : ℚ} {D : Bounds}
    (hd : D=slopeAt ⟨c,C⟩) (ht : accept ⟨a,A⟩ ⟨b,B⟩ ⟨c,C⟩ D=true) : OnBox a A b B c C := by
  intro p q z hp hq hz ap pA bq qB cz zC
  exact secondCanonicalRectangleBound (b:=⟨a,A⟩) (c:=⟨b,B⟩) (d:=⟨c,C⟩) (D:=D) hd ht hp hq hz ⟨ap,pA⟩ ⟨bq,qB⟩ ⟨cz,zC⟩
private theorem bound0 : ⟨(-6152618776404925167/1302642688000000000),(-1371069185480906073/325660672000000000)⟩=slopeAt ⟨(91/100),(373/400)⟩ := by decide +kernel
private theorem bound1 : ⟨(-3410480405443113021/651321344000000000),(-6152618776404925167/1302642688000000000)⟩=slopeAt ⟨(373/400),(191/200)⟩ := by decide +kernel
private theorem bound2 : ⟨(-3410480405443113021/651321344000000000),(-1371069185480906073/325660672000000000)⟩=slopeAt ⟨(91/100),(191/200)⟩ := by decide +kernel
private theorem bound3 : ⟨(-14310263656253752959/2605285376000000000),(-3410480405443113021/651321344000000000)⟩=slopeAt ⟨(191/200),(773/800)⟩ := by decide +kernel
private theorem bound4 : ⟨(-7489302845367526917/1302642688000000000),(-14310263656253752959/2605285376000000000)⟩=slopeAt ⟨(773/800),(391/400)⟩ := by decide +kernel
private theorem bound5 : ⟨(-15646947725216354709/2605285376000000000),(-7489302845367526917/1302642688000000000)⟩=slopeAt ⟨(391/400),(791/800)⟩ := by decide +kernel
private theorem bound6 : ⟨(-11857041976524459/1893376000000000),(-15646947725216354709/2605285376000000000)⟩=slopeAt ⟨(791/800),1⟩ := by decide +kernel
private theorem bound7 : ⟨(-31962237484914010293/5210570752000000000),(-15646947725216354709/2605285376000000000)⟩=slopeAt ⟨(791/800),(1591/1600)⟩ := by decide +kernel
private theorem bound8 : ⟨(-11857041976524459/1893376000000000),(-31962237484914010293/5210570752000000000)⟩=slopeAt ⟨(1591/1600),1⟩ := by decide +kernel
private theorem bound9 : ⟨(-11857041976524459/1893376000000000),(-7489302845367526917/1302642688000000000)⟩=slopeAt ⟨(391/400),1⟩ := by decide +kernel
private theorem bound10 : ⟨(-7489302845367526917/1302642688000000000),(-3410480405443113021/651321344000000000)⟩=slopeAt ⟨(191/200),(391/400)⟩ := by decide +kernel
private theorem bound11 : ⟨(-11857041976524459/1893376000000000),(-3410480405443113021/651321344000000000)⟩=slopeAt ⟨(191/200),1⟩ := by decide +kernel
private theorem verified : OnBox (16/25) (163/200) 0 (703/5000) (91/100) 1 := (cut2 (191/200) (cut0 (291/400) (cut0 (547/800) (cut1 (703/10000) (cut2 (373/400) (atLeaf bound0 (by decide +kernel)) (cut0 (1059/1600) (atLeaf bound1 (by decide +kernel)) (atLeaf bound1 (by decide +kernel)))) (cut2 (373/400) (cut0 (1059/1600) (atLeaf bound0 (by decide +kernel)) (atLeaf bound0 (by decide +kernel))) (cut0 (1059/1600) (cut1 (2109/20000) (atLeaf bound1 (by decide +kernel)) (atLeaf bound1 (by decide +kernel))) (atLeaf bound1 (by decide +kernel))))) (cut2 (373/400) (atLeaf bound0 (by decide +kernel)) (cut1 (703/10000) (atLeaf bound1 (by decide +kernel)) (cut0 (1129/1600) (atLeaf bound1 (by decide +kernel)) (atLeaf bound1 (by decide +kernel)))))) (cut0 (617/800) (cut2 (373/400) (atLeaf bound0 (by decide +kernel)) (cut1 (703/10000) (atLeaf bound1 (by decide +kernel)) (atLeaf bound1 (by decide +kernel)))) (atLeaf bound2 (by decide +kernel)))) (cut0 (291/400) (cut1 (703/10000) (cut2 (391/400) (cut0 (547/800) (cut0 (1059/1600) (cut2 (773/800) (atLeaf bound3 (by decide +kernel)) (cut1 (703/20000) (atLeaf bound4 (by decide +kernel)) (atLeaf bound4 (by decide +kernel)))) (cut2 (773/800) (atLeaf bound3 (by decide +kernel)) (atLeaf bound4 (by decide +kernel)))) (cut2 (773/800) (atLeaf bound3 (by decide +kernel)) (cut0 (1129/1600) (atLeaf bound4 (by decide +kernel)) (atLeaf bound4 (by decide +kernel))))) (cut0 (547/800) (cut1 (703/20000) (cut2 (791/800) (cut0 (1059/1600) (atLeaf bound5 (by decide +kernel)) (atLeaf bound5 (by decide +kernel))) (atLeaf bound6 (by decide +kernel))) (cut2 (791/800) (cut0 (1059/1600) (atLeaf bound5 (by decide +kernel)) (atLeaf bound5 (by decide +kernel))) (cut0 (1059/1600) (cut1 (2109/40000) (cut2 (1591/1600) (atLeaf bound7 (by decide +kernel)) (atLeaf bound8 (by decide +kernel))) (atLeaf bound6 (by decide +kernel))) (atLeaf bound6 (by decide +kernel))))) (atLeaf bound9 (by decide +kernel)))) (cut2 (391/400) (cut0 (547/800) (cut1 (2109/20000) (cut0 (1059/1600) (atLeaf bound10 (by decide +kernel)) (atLeaf bound10 (by decide +kernel))) (cut2 (773/800) (atLeaf bound3 (by decide +kernel)) (atLeaf bound4 (by decide +kernel)))) (cut0 (1129/1600) (cut2 (773/800) (atLeaf bound3 (by decide +kernel)) (atLeaf bound4 (by decide +kernel))) (atLeaf bound10 (by decide +kernel)))) (cut0 (547/800) (cut1 (2109/20000) (cut2 (791/800) (cut0 (1059/1600) (atLeaf bound5 (by decide +kernel)) (atLeaf bound5 (by decide +kernel))) (cut0 (1059/1600) (atLeaf bound6 (by decide +kernel)) (atLeaf bound6 (by decide +kernel)))) (cut0 (1059/1600) (atLeaf bound9 (by decide +kernel)) (cut2 (791/800) (atLeaf bound5 (by decide +kernel)) (atLeaf bound6 (by decide +kernel))))) (cut2 (791/800) (cut1 (2109/20000) (cut0 (1129/1600) (atLeaf bound5 (by decide +kernel)) (atLeaf bound5 (by decide +kernel))) (atLeaf bound5 (by decide +kernel))) (atLeaf bound6 (by decide +kernel)))))) (atLeaf bound11 (by decide +kernel))))
end StableVotingDistortion.Lemma9Reduction
open Set StableVotingDistortion StableVotingDistortion.PaperCurve StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperBox StableVotingDistortion.PaperBox.Bounds StableVotingDistortion.Lemma9Reduction
theorem solution {p q z : ℝ} (hp : p∈Icc (16/25:ℝ) (99/100)) (hq : q∈Icc (0:ℝ) PaperCurve.lam) (hz : z∈Icc p 1) (bp : p∈Icc ((16/25):ℝ) ((163/200):ℝ)) (bq : q∈Icc (0:ℝ) ((703/5000):ℝ)) (bz : z∈Icc ((91/100):ℝ) (1:ℝ)) : highSecond PaperCurve.lam score (canonical score p) 1 (-(canonical score p*(1-p))) p q z 1 ≤ 0 := by
  apply verified hp hq hz
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using bp.1
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using bp.2
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using bq.1
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using bq.2
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using bz.1
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one,PaperCurve.lam,PaperCurve.lamQ,Set.mem_Icc] using bz.2

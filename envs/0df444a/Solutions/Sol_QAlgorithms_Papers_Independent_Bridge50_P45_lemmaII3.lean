-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P45.lemmaII3
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-07T13:43:22.595204+00:00
-- url     : https://prove2.me/submissions/fac44f14-3f7c-4173-b14e-13dd95d24146

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P45
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith

open Set QAlgorithms.Papers.Independent.Bridge50.P45

private lemma real_height_le (e : EReal) (r : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → e ≤ ((r + ε : ℝ) : EReal)) : e ≤ (r : EReal) := by
  cases e with
  | bot => exact bot_le
  | top => exact (not_le_of_gt (EReal.coe_lt_top (r + 1)) (h 1 zero_lt_one)).elim
  | coe x =>
    apply EReal.coe_le_coe
    by_contra hn
    have hp : 0 < (x - r) / 2 := by linarith
    have hx := EReal.coe_le_coe_iff.mp (h _ hp)
    linarith

theorem solution :
    (∀ (V Y : Type) [AddCommGroup V] [Module ℝ V] (S : Set V) (f : V → Y → ℝ),
      Convex ℝ S → (∀ y, ConvexOn ℝ S (fun x => f x y)) →
      EConvexOn S (fun x => ⨆ y, (f x y : EReal))) ∧
    (∀ (V W : Type) [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
      (S : Set V) (T : Set W) (f : V × W → ℝ),
      Convex ℝ S → Convex ℝ T → ConvexOn ℝ (S ×ˢ T) f →
      EConvexOn S (fun x => ⨅ y : T, (f (x,y.1) : EReal))) := by
  constructor
  · intro V Y _ _ S f hS hf
    refine ⟨hS, ?_⟩
    intro p hp q hq a b ha hb hab
    change a • p.1 + b • q.1 ∈ S ∧
      (⨆ y, (f (a • p.1 + b • q.1) y : EReal)) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
    refine ⟨hS hp.1 hq.1 ha hb hab, iSup_le fun y => ?_⟩
    have hp' : f p.1 y ≤ p.2 := EReal.coe_le_coe_iff.mp ((le_iSup _ y).trans hp.2)
    have hq' : f q.1 y ≤ q.2 := EReal.coe_le_coe_iff.mp ((le_iSup _ y).trans hq.2)
    apply EReal.coe_le_coe
    exact ((hf y).2 hp.1 hq.1 ha hb hab).trans
      (add_le_add (mul_le_mul_of_nonneg_left hp' ha) (mul_le_mul_of_nonneg_left hq' hb))
  · intro V W _ _ _ _ S T f hS hT hf
    refine ⟨hS, ?_⟩
    intro p hp q hq a b ha hb hab
    change a • p.1 + b • q.1 ∈ S ∧
      (⨅ y : T, (f (a • p.1 + b • q.1,y.1) : EReal)) ≤
        ((a * p.2 + b * q.2 : ℝ) : EReal)
    refine ⟨hS hp.1 hq.1 ha hb hab, real_height_le _ _ ?_⟩
    intro ε hε
    have hpl : (⨅ y : T, (f (p.1,y.1) : EReal)) < ((p.2 + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hp.2 (EReal.coe_lt_coe (by linarith))
    have hql : (⨅ y : T, (f (q.1,y.1) : EReal)) < ((q.2 + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hq.2 (EReal.coe_lt_coe (by linarith))
    obtain ⟨y, hy⟩ := iInf_lt_iff.mp hpl
    obtain ⟨z, hz⟩ := iInf_lt_iff.mp hql
    have hy' := (EReal.coe_lt_coe_iff.mp hy).le
    have hz' := (EReal.coe_lt_coe_iff.mp hz).le
    let w : T := ⟨a • y.val + b • z.val, hT y.property z.property ha hb hab⟩
    have hc := hf.2 (show (p.1,y.val) ∈ S ×ˢ T from ⟨hp.1,y.property⟩)
      (show (q.1,z.val) ∈ S ×ˢ T from ⟨hq.1,z.property⟩) ha hb hab
    change f (a • p.1 + b • q.1, w.val) ≤ a * f (p.1,y.val) + b * f (q.1,z.val) at hc
    refine (iInf_le _ w).trans (EReal.coe_le_coe (hc.trans ?_))
    have hh := add_le_add (mul_le_mul_of_nonneg_left hy' ha) (mul_le_mul_of_nonneg_left hz' hb)
    nlinarith [hab]

#print axioms solution

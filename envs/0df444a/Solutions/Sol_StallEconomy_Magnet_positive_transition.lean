-- Prove2me | solution 1 for StallEconomy.Magnet.positive_transition
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:09:12.644042+00:00
-- url     : https://prove2.me/submissions/212bf2fb-f086-4588-a9c4-125d9a09a933

import Mathlib
import Definitions.Def_StallEconomy_Magnet_Setting

namespace StallEconomy.Magnet

/-- Arrow-head coordinate (before any type-2 rotation). -/
def aOf (h : ℕ) (a b : ℤ) : ℤ :=
  if a + h < b then b - h else if b < a - h then b + h else b

/-- Coordinate rule of the magnet map for a pair that is not both-near. -/
def cOf (k h : ℕ) (a b : ℤ) : ℤ :=
  if a + h < b then b - h else if b < a - h then b + h
  else if (h : ℤ) ≤ b ∧ b ≤ (k : ℤ) - h then b else a

lemma ah0 (h : ℕ) (z : ℤ × ℤ) : arrowHead h 0 z = (z.1 - h, z.2 - h) := rfl
lemma ah1 (h : ℕ) (z : ℤ × ℤ) : arrowHead h 1 z = (z.1 - h, z.2) := rfl
lemma ah2 (h : ℕ) (z : ℤ × ℤ) : arrowHead h 2 z = (z.1 - h, z.2 + h) := rfl
lemma ah3 (h : ℕ) (z : ℤ × ℤ) : arrowHead h 3 z = (z.1, z.2 + h) := rfl
lemma ah4 (h : ℕ) (z : ℤ × ℤ) : arrowHead h 4 z = (z.1 + h, z.2 + h) := rfl
lemma ah5 (h : ℕ) (z : ℤ × ℤ) : arrowHead h 5 z = (z.1 + h, z.2) := rfl
lemma ah6 (h : ℕ) (z : ℤ × ℤ) : arrowHead h 6 z = (z.1 + h, z.2 - h) := rfl
lemma ah7 (h : ℕ) (z : ℤ × ℤ) : arrowHead h 7 z = (z.1, z.2 - h) := rfl

lemma arrowHead_regionIndex (h : ℕ) (zo zc : ℤ × ℤ)
    (hfar : ¬ ((zo.1 - h ≤ zc.1 ∧ zc.1 ≤ zo.1 + h) ∧ (zo.2 - h ≤ zc.2 ∧ zc.2 ≤ zo.2 + h))) :
    arrowHead h (regionIndex h zo zc) zc = (aOf h zo.1 zc.1, aOf h zo.2 zc.2) := by
  obtain ⟨xo, yo⟩ := zo
  obtain ⟨xc, yc⟩ := zc
  simp only at hfar ⊢
  unfold regionIndex
  simp only
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;>
    refine Prod.ext ?_ ?_ <;> simp only [ah0, ah1, ah2, ah3, ah4, ah5, ah6, ah7, aOf] <;> split_ifs <;> omega


lemma magnet_eq (k h : ℕ) (zo zc : ℤ × ℤ) (hzo : zo ∈ inner k h) (hzc : zc ∈ grid k) :
    magnet k h zo zc =
      if (zo.1 - h ≤ zc.1 ∧ zc.1 ≤ zo.1 + h) ∧ (zo.2 - h ≤ zc.2 ∧ zc.2 ≤ zo.2 + h) then zo
      else (cOf k h zo.1 zc.1, cOf k h zo.2 zc.2) := by
  have hsd : zc ∈ smallDiamond h zo ↔
      ((zo.1 - h ≤ zc.1 ∧ zc.1 ≤ zo.1 + h) ∧ (zo.2 - h ≤ zc.2 ∧ zc.2 ≤ zo.2 + h)) := by
    simp [smallDiamond, Finset.mem_product, Finset.mem_Icc]
  simp only [magnet]
  by_cases hn : ((zo.1 - h ≤ zc.1 ∧ zc.1 ≤ zo.1 + h) ∧ (zo.2 - h ≤ zc.2 ∧ zc.2 ≤ zo.2 + h))
  · rw [if_pos (hsd.2 hn), if_pos hn]
  rw [if_neg (fun hh => hn (hsd.1 hh)), if_neg hn, arrowHead_regionIndex h zo zc hn]
  obtain ⟨xo, yo⟩ := zo
  obtain ⟨xc, yc⟩ := zc
  simp only [inner, type1, grid, Finset.mem_product, Finset.mem_Icc] at hzo hzc hn ⊢
  by_cases a1 : xo + (h : ℤ) < xc <;> by_cases a2 : xc < xo - (h : ℤ) <;>
  by_cases b1 : yo + (h : ℤ) < yc <;> by_cases b2 : yc < yo - (h : ℤ) <;>
  simp only [aOf, cOf, a1, a2, b1, b2, if_true, if_false] <;>
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

lemma rule_valid' (k h : ℕ) (hkh : 2 * h ≤ k)
    (zo zc : ℤ × ℤ) (hzo : zo ∈ inner k h) (hzc : zc ∈ grid k) :
    magnet k h zo zc ∈ inner k h ∧
      (zc ∉ smallDiamond h zo →
        max |zc.1 - (magnet k h zo zc).1|
          |zc.2 - (magnet k h zo zc).2| = (h : ℤ)) := by
  rw [magnet_eq k h zo zc hzo hzc]
  obtain ⟨xo, yo⟩ := zo
  obtain ⟨xc, yc⟩ := zc
  simp only [inner, grid, smallDiamond, Finset.mem_product, Finset.mem_Icc] at hzo hzc ⊢
  by_cases a1 : xo + (h : ℤ) < xc <;> by_cases a2 : xc < xo - (h : ℤ) <;>
  by_cases b1 : yo + (h : ℤ) < yc <;> by_cases b2 : yc < yo - (h : ℤ) <;>
  simp only [cOf, a1, a2, b1, b2, if_true, if_false] <;>
  split_ifs <;> simp only [abs_eq_max_neg, max_def] <;> split_ifs <;> omega

/-- Encoding coordinate: the second component of the bijection. -/
def dOf (k h : ℕ) (a b : ℤ) : ℤ :=
  if a + h < b then a - h else if b < a - h then a + h
  else if (h : ℤ) ≤ b ∧ b ≤ (k : ℤ) - h then a else b

def eo (k h : ℕ) (d w : ℤ) : ℤ :=
  if w < d - h then w + h else if d + h < w then w - h
  else if (h : ℤ) ≤ w ∧ w ≤ (k : ℤ) - h then w else d

def ec (k h : ℕ) (d w : ℤ) : ℤ :=
  if w < d - h then d + h else if d + h < w then d - h
  else if (h : ℤ) ≤ w ∧ w ≤ (k : ℤ) - h then d else w

def psi (k h : ℕ) (p : (ℤ × ℤ) × (ℤ × ℤ)) : ℤ × ℤ :=
  if (p.1.1 - h ≤ p.2.1 ∧ p.2.1 ≤ p.1.1 + h) ∧ (p.1.2 - h ≤ p.2.2 ∧ p.2.2 ≤ p.1.2 + h)
  then p.2 else (dOf k h p.1.1 p.2.1, dOf k h p.1.2 p.2.2)

def Psi (k h : ℕ) (zd w : ℤ × ℤ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  if (zd.1 - h ≤ w.1 ∧ w.1 ≤ zd.1 + h) ∧ (zd.2 - h ≤ w.2 ∧ w.2 ≤ zd.2 + h)
  then (zd, w) else ((eo k h zd.1 w.1, eo k h zd.2 w.2), (ec k h zd.1 w.1, ec k h zd.2 w.2))

lemma Psi_mem (k h : ℕ) (hkh : 2 * h ≤ k) (zd w : ℤ × ℤ) (hzd : zd ∈ inner k h)
    (hw : w ∈ grid k) : (Psi k h zd w).1 ∈ inner k h ∧ (Psi k h zd w).2 ∈ grid k := by
  obtain ⟨xd, yd⟩ := zd
  obtain ⟨xw, yw⟩ := w
  simp only [inner, grid, Finset.mem_product, Finset.mem_Icc] at hzd hw ⊢
  simp only [Psi, eo, ec]
  split_ifs <;> simp only <;> omega

lemma magnet_Psi (k h : ℕ) (hkh : 2 * h ≤ k) (zd w : ℤ × ℤ) (hzd : zd ∈ inner k h)
    (hw : w ∈ grid k) : magnet k h (Psi k h zd w).1 (Psi k h zd w).2 = zd := by
  obtain ⟨h1, h2⟩ := Psi_mem k h hkh zd w hzd hw
  rw [magnet_eq k h _ _ h1 h2]
  clear h1 h2
  obtain ⟨xd, yd⟩ := zd
  obtain ⟨xw, yw⟩ := w
  simp only [inner, grid, Finset.mem_product, Finset.mem_Icc] at hzd hw
  by_cases a1 : xw < xd - (h : ℤ) <;> by_cases a2 : xd + (h : ℤ) < xw <;>
  by_cases b1 : yw < yd - (h : ℤ) <;> by_cases b2 : yd + (h : ℤ) < yw <;>
  simp only [Psi, eo, ec, a1, a2, b1, b2, if_true, if_false] <;>
  split_ifs <;> simp only [cOf, Prod.mk.injEq] at * <;> (try split_ifs) <;> (try simp only [Prod.mk.injEq, and_true, true_and]) <;> omega

lemma psi_Psi (k h : ℕ) (hkh : 2 * h ≤ k) (zd w : ℤ × ℤ) (hzd : zd ∈ inner k h)
    (hw : w ∈ grid k) : psi k h (Psi k h zd w) = w := by
  obtain ⟨xd, yd⟩ := zd
  obtain ⟨xw, yw⟩ := w
  simp only [inner, grid, Finset.mem_product, Finset.mem_Icc] at hzd hw
  by_cases a1 : xw < xd - (h : ℤ) <;> by_cases a2 : xd + (h : ℤ) < xw <;>
  by_cases b1 : yw < yd - (h : ℤ) <;> by_cases b2 : yd + (h : ℤ) < yw <;>
  simp only [Psi, eo, ec, a1, a2, b1, b2, if_true, if_false] <;>
  split_ifs <;> simp only [psi, dOf, Prod.mk.injEq] at * <;> (try split_ifs) <;> (try simp only [Prod.mk.injEq, and_true, true_and]) <;> omega

set_option maxHeartbeats 4000000 in
lemma Psi_psi (k h : ℕ) (hkh : 2 * h ≤ k) (zo zc : ℤ × ℤ) (hzo : zo ∈ inner k h)
    (hzc : zc ∈ grid k) : Psi k h (magnet k h zo zc) (psi k h (zo, zc)) = (zo, zc) := by
  rw [magnet_eq k h zo zc hzo hzc]
  obtain ⟨xo, yo⟩ := zo
  obtain ⟨xc, yc⟩ := zc
  simp only [inner, grid, Finset.mem_product, Finset.mem_Icc] at hzo hzc
  by_cases a1 : xo + (h : ℤ) < xc <;> by_cases a2 : xc < xo - (h : ℤ) <;>
  by_cases b1 : yo + (h : ℤ) < yc <;> by_cases b2 : yc < yo - (h : ℤ) <;>
  simp only [psi, cOf, dOf, a1, a2, b1, b2, if_true, if_false] <;>
  split_ifs <;> simp only [Psi, eo, ec, Prod.mk.injEq] at * <;> (try split_ifs) <;> (try simp only [Prod.mk.injEq, and_true, true_and]) <;> omega

lemma psi_mem (k h : ℕ) (hkh : 2 * h ≤ k) (zo zc : ℤ × ℤ) (hzo : zo ∈ inner k h)
    (hzc : zc ∈ grid k) : psi k h (zo, zc) ∈ grid k := by
  obtain ⟨xo, yo⟩ := zo
  obtain ⟨xc, yc⟩ := zc
  simp only [inner, grid, Finset.mem_product, Finset.mem_Icc] at hzo hzc ⊢
  simp only [psi, dOf]
  split_ifs <;> simp only <;> omega

lemma grid_card (k : ℕ) : (grid k).card = (k + 1) ^ 2 := by
  simp only [grid, Finset.card_product, Int.card_Icc]
  have : ((k : ℤ) + 1 - 0).toNat = k + 1 := by omega
  rw [this]; ring

lemma column_count' (k h : ℕ) (hkh : 2 * h ≤ k)
    (zd : ℤ × ℤ) (hzd : zd ∈ inner k h) :
    ∑ zo : inner k h, (A k h zo.1 zd).card = (k + 1) ^ 2 := by
  have e1 : ∑ zo : inner k h, (A k h zo.1 zd).card =
      ((inner k h ×ˢ grid k).filter (fun p => magnet k h p.1 p.2 = zd)).card := by
    rw [Finset.card_filter, Finset.sum_product,
      Finset.sum_coe_sort (inner k h) (fun zo => (A k h zo zd).card)]
    refine Finset.sum_congr rfl (fun zo _ => ?_)
    simp only [A, Finset.card_filter]
  rw [e1, ← grid_card k]
  refine Finset.card_nbij' (fun p => psi k h p) (fun w => Psi k h zd w) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp
    obtain ⟨⟨h1, h2⟩, -⟩ := hp
    exact psi_mem k h hkh p.1 p.2 h1 h2
  · intro w hw
    have hw' : w ∈ grid k := hw
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq]
    exact ⟨Psi_mem k h hkh zd w hzd hw', magnet_Psi k h hkh zd w hzd hw'⟩
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    have := Psi_psi k h hkh p.1 p.2 h1 h2
    rw [h3] at this
    exact this
  · intro w hw
    exact psi_Psi k h hkh zd w hzd hw

lemma row_count' (k h : ℕ) (hkh : 2 * h ≤ k)
    (zo : ℤ × ℤ) (hzo : zo ∈ inner k h) :
    ∑ zd : inner k h, (A k h zo zd.1).card = (k + 1) ^ 2 := by
  rw [Finset.sum_coe_sort (inner k h) (fun zd => (A k h zo zd).card), ← grid_card k]
  symm
  exact Finset.card_eq_sum_card_fiberwise
    (fun zc hzc => (rule_valid' k h hkh zo zc hzo hzc).1)

lemma self_loop_count' (k h : ℕ) (hkh : 2 * h ≤ k)
    (zd : ℤ × ℤ) (hzd : zd ∈ inner k h) :
    (A k h zd zd).card = (2 * h + 1) ^ 2 := by
  have e : A k h zd zd = smallDiamond h zd := by
    ext zc
    simp only [A, Finset.mem_filter]
    constructor
    · rintro ⟨hzc, hm⟩
      rw [magnet_eq k h zd zc hzd hzc] at hm
      obtain ⟨xd, yd⟩ := zd
      obtain ⟨xc, yc⟩ := zc
      simp only [inner, grid, smallDiamond, Finset.mem_product, Finset.mem_Icc] at hzd hzc ⊢
      revert hm
      split_ifs with hn
      · intro _; exact hn
      · simp only [cOf, Prod.mk.injEq]
        split_ifs <;> omega
    · intro hzc
      have hg : zc ∈ grid k := by
        obtain ⟨xd, yd⟩ := zd
        obtain ⟨xc, yc⟩ := zc
        simp only [inner, grid, smallDiamond, Finset.mem_product, Finset.mem_Icc] at hzd hzc ⊢
        omega
      refine ⟨hg, ?_⟩
      simp only [magnet, if_pos hzc]
  rw [e]
  simp only [smallDiamond, Finset.card_product, Int.card_Icc]
  have : (zd.1 + (h : ℤ) + 1 - (zd.1 - h)).toNat = 2 * h + 1 := by omega
  have h2 : (zd.2 + (h : ℤ) + 1 - (zd.2 - h)).toNat = 2 * h + 1 := by omega
  rw [this, h2]; ring

def wit (h : ℕ) (a d : ℤ) : ℤ := if a < d then d + h else if d < a then d - h else d

lemma positive_transition' (k h : ℕ) (hkh : 2 * h ≤ k)
    (zo zd : inner k h) :
    0 < (A k h zo.1 zd.1).card := by
  obtain ⟨⟨xo, yo⟩, hzo⟩ := zo
  obtain ⟨⟨xd, yd⟩, hzd⟩ := zd
  have hzc : (wit h xo xd, wit h yo yd) ∈ grid k := by
    simp only [inner, grid, Finset.mem_product, Finset.mem_Icc] at hzo hzd ⊢
    simp only [wit]
    split_ifs <;> omega
  refine Finset.card_pos.2 ⟨(wit h xo xd, wit h yo yd), ?_⟩
  simp only [A, Finset.mem_filter]
  refine ⟨hzc, ?_⟩
  rw [magnet_eq k h _ _ hzo hzc]
  simp only [inner, grid, Finset.mem_product, Finset.mem_Icc] at hzo hzd hzc
  simp only [wit, cOf]
  split_ifs <;> simp only [Prod.mk.injEq, and_true, true_and] at * <;> omega

end StallEconomy.Magnet

open StallEconomy.Magnet

theorem solution (k h : ℕ) (hkh : 2 * h ≤ k)
    (zo zd : inner k h) :
    0 < (A k h zo.1 zd.1).card :=
  positive_transition' k h hkh zo zd

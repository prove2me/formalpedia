-- Prove2me | solution 1 for SherbrookeMetric.ConvexHull.lowerHull_slopes
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:52:01.598606+00:00
-- url     : https://prove2.me/submissions/2f6b6424-78a2-4b28-837c-b649edaa2b60

import Mathlib
import Definitions.Def_SherbrookeMetric_ConvexHull_LowerHull

set_option autoImplicit false
open SherbrookeMetric.ConvexHull ServiceParts.StockLevels

namespace SMCAux

lemma fdiff2_eq (f : ℕ → ℝ) (m : ℕ) :
    fdiff2 f m = f (m + 2) - 2 * f (m + 1) + f m := by
  unfold fdiff2 fdiff
  have : m + 1 + 1 = m + 2 := rfl
  rw [this]; ring

lemma fdiff_mono {g : ℕ → ℝ} (hg : DiscreteConvex g) : Monotone (fdiff g) :=
  monotone_nat_of_le_succ (fun m => by
    have := hg m
    unfold fdiff2 at this
    linarith)

lemma fdiff_nonpos_of_bdd {g : ℕ → ℝ} (hg : DiscreteConvex g) {C : ℝ}
    (hC : ∀ m, g m ≤ C) (m : ℕ) : fdiff g m ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  have hmono := fdiff_mono hg
  have key : ∀ n : ℕ, g m + n * fdiff g m ≤ g (m + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : fdiff g m ≤ fdiff g (m + n) := hmono (by omega)
      have h2 : g (m + n + 1) = g (m + n) + fdiff g (m + n) := by unfold fdiff; ring
      have : m + (n + 1) = m + n + 1 := by omega
      rw [this, h2]; push_cast; linarith
  obtain ⟨n, hn⟩ := Archimedean.arch (C - g m + 1) hpos
  have := key n
  have := hC (m + n)
  simp only [nsmul_eq_mul] at hn
  linarith

lemma exists_lb {Ξ : ℕ → ℝ} (hbdd : BddBelow (Set.range Ξ)) : ∃ b : ℝ, ∀ k, b ≤ Ξ k := by
  obtain ⟨b, hb⟩ := hbdd
  exact ⟨b, fun k => hb (Set.mem_range_self k)⟩

lemma const_convex (b : ℝ) : DiscreteConvex (fun _ : ℕ => b) := by
  intro m; simp [fdiff2, fdiff]

lemma fam_nonempty {Ξ : ℕ → ℝ} (hbdd : BddBelow (Set.range Ξ)) :
    Nonempty {g : ℕ → ℝ // DiscreteConvex g ∧ ∀ k : ℕ, g k ≤ Ξ k} := by
  obtain ⟨b, hb⟩ := exists_lb hbdd
  exact ⟨⟨fun _ => b, const_convex b, hb⟩⟩

lemma le_hull {Ξ : ℕ → ℝ} {g : ℕ → ℝ} (hg : DiscreteConvex g) (hle : ∀ k, g k ≤ Ξ k) (m : ℕ) :
    g m ≤ lowerHull Ξ m := by
  unfold lowerHull
  refine le_ciSup (f := fun g : {g : ℕ → ℝ // DiscreteConvex g ∧ ∀ k : ℕ, g k ≤ Ξ k} => g.1 m)
    ⟨Ξ m, ?_⟩ ⟨g, hg, hle⟩
  rintro _ ⟨g', rfl⟩
  exact g'.2.2 m

lemma hull_le {Ξ : ℕ → ℝ} (hbdd : BddBelow (Set.range Ξ)) (m : ℕ) : lowerHull Ξ m ≤ Ξ m := by
  haveI := fam_nonempty hbdd
  exact ciSup_le (fun g => g.2.2 m)

lemma hull_convex {Ξ : ℕ → ℝ} (hbdd : BddBelow (Set.range Ξ)) : DiscreteConvex (lowerHull Ξ) := by
  haveI := fam_nonempty hbdd
  intro m
  rw [fdiff2_eq]
  have : lowerHull Ξ (m + 1) ≤ (lowerHull Ξ m + lowerHull Ξ (m + 2)) / 2 := by
    refine ciSup_le (fun g => ?_)
    have h1 := g.2.1 m
    rw [fdiff2_eq] at h1
    have h2 : g.1 m ≤ lowerHull Ξ m := le_hull g.2.1 g.2.2 m
    have h3 : g.1 (m + 2) ≤ lowerHull Ξ (m + 2) := le_hull g.2.1 g.2.2 (m + 2)
    linarith
  linarith

lemma hull_lb {Ξ : ℕ → ℝ} {b : ℝ} (hb : ∀ k, b ≤ Ξ k) (m : ℕ) : b ≤ lowerHull Ξ m :=
  le_hull (const_convex b) hb m

lemma hull_fdiff_nonpos {Ξ : ℕ → ℝ} (hanti : Antitone Ξ) (hbdd : BddBelow (Set.range Ξ)) (m : ℕ) :
    fdiff (lowerHull Ξ) m ≤ 0 :=
  fdiff_nonpos_of_bdd (hull_convex hbdd) (C := Ξ 0)
    (fun k => (hull_le hbdd k).trans (hanti (Nat.zero_le k))) m

lemma hull_tendsto {Ξ : ℕ → ℝ} (hanti : Antitone Ξ) (hbdd : BddBelow (Set.range Ξ)) :
    Filter.Tendsto (fdiff (lowerHull Ξ)) Filter.atTop (nhds 0) := by
  obtain ⟨b, hb⟩ := exists_lb hbdd
  have hmono := fdiff_mono (hull_convex hbdd)
  have hnp := hull_fdiff_nonpos hanti hbdd
  have hlb := hull_lb hb
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- some N with fdiff H N > -ε
  have : ∃ N, -ε < fdiff (lowerHull Ξ) N := by
    by_contra hcon
    push_neg at hcon
    have key : ∀ n : ℕ, lowerHull Ξ 0 - n * ε ≥ lowerHull Ξ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have := hcon n
        have h2 : lowerHull Ξ (n + 1) = lowerHull Ξ n + fdiff (lowerHull Ξ) n := by unfold fdiff; ring
        rw [h2]; push_cast; linarith
    obtain ⟨n, hn⟩ := Archimedean.arch (lowerHull Ξ 0 - b + 1) hε
    simp only [nsmul_eq_mul] at hn
    have := key n
    have := hlb n
    linarith
  obtain ⟨N, hN⟩ := this
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hmono hn
  have h2 := hnp n
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith


lemma slopes_antitone {Ξ : ℕ → ℝ} (hanti : Antitone Ξ) (hbdd : BddBelow (Set.range Ξ)) :
    Antitone (lowerHull Ξ) :=
  antitone_nat_of_succ_le (fun m => by
    have := hull_fdiff_nonpos hanti hbdd m
    unfold fdiff at this
    linarith)

end SMCAux

open SMCAux

theorem solution (Ξ : ℕ → ℝ) (hanti : Antitone Ξ)
    (hbdd : BddBelow (Set.range Ξ)) :
    Antitone (lowerHull Ξ) ∧
      (∀ b : ℝ, (∀ k : ℕ, b ≤ Ξ k) → ∀ m : ℕ, b ≤ lowerHull Ξ m) ∧
      (∀ m : ℕ, ServiceParts.StockLevels.fdiff (lowerHull Ξ) m ≤ 0) ∧
      Filter.Tendsto (ServiceParts.StockLevels.fdiff (lowerHull Ξ))
        Filter.atTop (nhds 0) :=
  ⟨slopes_antitone hanti hbdd, fun _ hb m => hull_lb hb m, hull_fdiff_nonpos hanti hbdd,
    hull_tendsto hanti hbdd⟩

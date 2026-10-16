-- Prove2me | solution 1 for PrizeAlloc.Interval.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T08:18:07.738984+00:00
-- url     : https://prove2.me/submissions/40164a6f-6b6d-4d10-89a8-5f0f76cf59d6

import Mathlib
import Definitions.Def_PrizeAlloc_Interval_Setting

set_option autoImplicit false
open PrizeAlloc.Interval

namespace PrizeResearch

theorem coordinate_le {U : Type*} [DecidableEq U] (φ ψ : List U → ℝ → U → ℝ)
    (hφ : IsPrizeRule φ) (hψ : IsPrizeRule ψ)
    (hφEM : EndowmentMonotone φ) (hφCons : Consistent φ)
    (hψCons : Consistent ψ)
    (h2 : ∀ (l : List U) (E : ℝ), IsRanking l → l.length = 2 → 0 ≤ E →
      ∀ i ∈ l, φ l E i = ψ l E i)
    (l : List U) (E : ℝ) (hl : IsRanking l) (hE : 0 ≤ E) (i : U) (hi : i ∈ l) :
    φ l E i ≤ ψ l E i := by
  classical
  by_contra hnot
  have hilt : ψ l E i < φ l E i := lt_of_not_ge hnot
  obtain ⟨j,hj,hjlt⟩ : ∃ j ∈ l, φ l E j < ψ l E j := by
    by_contra! h
    have hs := Finset.sum_lt_sum
      (s := l.toFinset) (f := ψ l E) (g := φ l E)
      (fun j hj => h j (List.mem_toFinset.mp hj)) ⟨i,List.mem_toFinset.mpr hi,hilt⟩
    rw [(hφ l E hl hE).2,(hψ l E hl hE).2] at hs
    exact lt_irrefl _ hs
  have hij : i ≠ j := by intro h; subst j; linarith
  let S : Finset U := {i,j}
  have hS : S ⊆ l.toFinset := by
    intro x hx
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr hi
    · exact List.mem_toFinset.mpr hj
  have hSne : S.Nonempty := ⟨i,by simp [S]⟩
  have hfin : (sub l S).toFinset = S := by
    ext x
    simp only [List.mem_toFinset,sub,List.mem_filter,decide_eq_true_eq]
    exact and_iff_right_of_imp (fun hx => List.mem_toFinset.mp (hS hx))
  have hlen : (sub l S).length = 2 := by
    rw [←List.toFinset_card_of_nodup (show (sub l S).Nodup from hl.1.filter _),hfin]
    simp [S,hij]
  have hrank : IsRanking (sub l S) := ⟨hl.1.filter _,by intro h; simp [h] at hlen⟩
  have hiS : i ∈ S := by simp [S]
  have hjS : j ∈ S := by simp [S]
  have hisub : i ∈ sub l S := List.mem_toFinset.mp (hfin.symm ▸ hiS)
  have hjsub : j ∈ sub l S := List.mem_toFinset.mp (hfin.symm ▸ hjS)
  let A : ℝ := ∑ k ∈ S, φ l E k
  let B : ℝ := ∑ k ∈ S, ψ l E k
  have hA : 0 ≤ A := Finset.sum_nonneg (fun k hk => (hφ l E hl hE).1 k
    (List.mem_toFinset.mp (hS hk)))
  have hB : 0 ≤ B := Finset.sum_nonneg (fun k hk => (hψ l E hl hE).1 k
    (List.mem_toFinset.mp (hS hk)))
  have hcφ (k) (hk : k ∈ S) : φ l E k = φ (sub l S) A k := hφCons l E hl hE S hS hSne k hk
  have hcψ (k) (hk : k ∈ S) : ψ l E k = φ (sub l S) B k := by
    rw [hψCons l E hl hE S hS hSne k hk]
    exact (h2 (sub l S) B hrank hlen hB k (List.mem_toFinset.mp (hfin.symm ▸ hk))).symm
  have hm {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (k) (hk : k ∈ sub l S) :
      φ (sub l S) a k ≤ φ (sub l S) b k := by
    rcases hab.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact hφEM _ a b hrank ha hlt k hk
  rcases le_total A B with hab | hba
  · have hh := hm hA hab i hisub
    rw [←hcφ i hiS,←hcψ i hiS] at hh
    linarith
  · have hh := hm hB hba j hjsub
    rw [←hcψ j hjS,←hcφ j hjS] at hh
    linarith

end PrizeResearch

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Dietzenbacher and Kondratev, arXiv:2008.08985v2, Lemma 3.
theorem solution {U : Type*} [DecidableEq U] (φ ψ : List U → ℝ → U → ℝ)
    (hφ : IsPrizeRule φ) (hψ : IsPrizeRule ψ)
    (hφEM : EndowmentMonotone φ) (hφCons : Consistent φ)
    (hψEM : EndowmentMonotone ψ) (hψCons : Consistent ψ)
    (h2 : ∀ (l : List U) (E : ℝ), IsRanking l → l.length = 2 → 0 ≤ E →
      ∀ i ∈ l, φ l E i = ψ l E i) :
    ∀ (l : List U) (E : ℝ), IsRanking l → 0 ≤ E → ∀ i ∈ l, φ l E i = ψ l E i := by
  intro l E hl hE i hi
  exact le_antisymm (PrizeResearch.coordinate_le φ ψ hφ hψ hφEM hφCons hψCons h2 l E hl hE i hi)
    (PrizeResearch.coordinate_le ψ φ hψ hφ hψEM hψCons hφCons
      (fun l E hl hn hE i hi => (h2 l E hl hn hE i hi).symm) l E hl hE i hi)

#print axioms solution

-- Prove2me | solution 1 for OpenPitMIP.Hourglass.most_violated_set
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:44:00.919077+00:00
-- url     : https://prove2.me/submissions/5517f927-efb6-4ee7-a7fa-90a7306d3823

import Mathlib
import Definitions.Def_OpenPitMIP_Hourglass_Setting
set_option autoImplicit false
open OpenPitMIP.Hourglass

open Classical in
theorem solution {B D C : Type} [Fintype B] [Fintype D] [Fintype C]
    [DecidableEq B] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing)
    (w : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) (cbar : C) (d : D)
    (t₁ t : Fin T) (ht : t₁ ≤ t) :
    let viol : Finset B → ℝ := fun S =>
      (I.qBlocks (S ∪ I.blocksOf {cbar}) - I.Ucum d t₁ t) * w cbar t
        + ∑ b ∈ I.blocksOf (I.rcl cbar \ {cbar}), I.q b * PCPSPC.ySum y b d t₁ t
        - ∑ b ∈ S ∪ I.blocksOf {cbar}, I.q b * (w (I.clu b) t - PCPSPC.ySum y b d t₁ t)
    let Sstar : Finset B := Finset.univ.filter
      (fun b => I.cprec (I.clu b) cbar ∧ w (I.clu b) t - PCPSPC.ySum y b d t₁ t < w cbar t)
    Sstar ⊆ I.blocksOf (I.cl cbar \ {cbar}) ∧
      ∀ S ⊆ I.blocksOf (I.cl cbar \ {cbar}), viol S ≤ viol Sstar := by
  intro viol Sstar
  haveI := hI.strictOrder
  have hirr : ∀ c, ¬ I.cprec c c := fun c => irrefl_of I.cprec c
  have memAl : ∀ b, b ∈ I.blocksOf (I.cl cbar \ {cbar}) ↔ I.cprec (I.clu b) cbar := by
    intro b
    simp only [PCPSPC.blocksOf, PCPSPC.cl, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact h1
    · intro h
      exact ⟨Or.inr h, fun h' => hirr cbar (h' ▸ h)⟩
  have memB0 : ∀ b, b ∈ I.blocksOf {cbar} ↔ I.clu b = cbar := by
    intro b
    simp [PCPSPC.blocksOf]
  have hdis : ∀ S ⊆ I.blocksOf (I.cl cbar \ {cbar}), Disjoint S (I.blocksOf {cbar}) := by
    intro S hS
    rw [Finset.disjoint_left]
    intro b hb hb0
    have h1 := (memAl b).1 (hS hb)
    rw [(memB0 b).1 hb0] at h1
    exact hirr _ h1
  have hviol : ∀ S ⊆ I.blocksOf (I.cl cbar \ {cbar}), viol S = viol ∅ +
      ∑ b ∈ S, I.q b * (w cbar t - (w (I.clu b) t - PCPSPC.ySum y b d t₁ t)) := by
    intro S hS
    have hd := hdis S hS
    simp only [viol, PCPSPC.qBlocks, Finset.empty_union, Finset.sum_union hd]
    simp only [add_mul, sub_mul, mul_sub, Finset.sum_mul, Finset.sum_sub_distrib]
    ring
  have hSsub : Sstar ⊆ I.blocksOf (I.cl cbar \ {cbar}) := by
    intro b hb
    simp only [Sstar, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact (memAl b).2 hb.1
  refine ⟨hSsub, fun S hS => ?_⟩
  rw [hviol S hS, hviol Sstar hSsub]
  have hq := hI.q_nonneg
  have hle : ∀ b ∈ S, I.q b * (w cbar t - (w (I.clu b) t - PCPSPC.ySum y b d t₁ t)) ≤
      if b ∈ Sstar then I.q b * (w cbar t - (w (I.clu b) t - PCPSPC.ySum y b d t₁ t)) else 0 := by
    intro b hb
    by_cases hbS : b ∈ Sstar
    · rw [if_pos hbS]
    · rw [if_neg hbS]
      have hc := (memAl b).1 (hS hb)
      have : ¬ (w (I.clu b) t - PCPSPC.ySum y b d t₁ t < w cbar t) := fun h => hbS (by
        simp only [Sstar, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hc, h⟩)
      push_neg at this
      exact mul_nonpos_of_nonneg_of_nonpos (hq b) (by linarith)
  have h1 := Finset.sum_le_sum hle
  rw [Finset.sum_ite_mem] at h1
  have h2 : ∑ b ∈ S ∩ Sstar, I.q b * (w cbar t - (w (I.clu b) t - PCPSPC.ySum y b d t₁ t)) ≤
      ∑ b ∈ Sstar, I.q b * (w cbar t - (w (I.clu b) t - PCPSPC.ySum y b d t₁ t)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    intro b hb _
    simp only [Sstar, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact mul_nonneg (hq b) (by linarith [hb.2])
  linarith

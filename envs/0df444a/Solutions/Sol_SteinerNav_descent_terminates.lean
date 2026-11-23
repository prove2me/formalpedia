-- Prove2me | solution 1 for SteinerNav.descent_terminates
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:54:56.508546+00:00
-- url     : https://prove2.me/submissions/30983d24-4c44-4e4c-9d3e-c558cfcca46d

import Mathlib
import Definitions.Def_SteinerNav_GreedyRun

open SteinerNav

namespace AuxDescent

lemma run_above_card {d : ℕ} {V : Finset (Pt d)} {E : Finset (Pt d × Pt d)}
    (hE : ∀ x y, (x, y) ∈ E → x ∈ V ∧ y ∈ V) {q x₀ : Pt d} (hx₀ : x₀ ∈ V)
    {k : ℕ} {x : Pt d} (hrun : GreedyRun E q x₀ k x) :
    x ∈ V ∧ k + 1 ≤ (V.filter fun v => dist x q ≤ dist v q).card := by
  induction hrun with
  | start =>
    refine ⟨hx₀, ?_⟩
    have hmem : x₀ ∈ V.filter (fun v => dist x₀ q ≤ dist v q) :=
      Finset.mem_filter.mpr ⟨hx₀, le_rfl⟩
    exact Finset.card_pos.mpr ⟨x₀, hmem⟩
  | @step k x y _ hstep ih =>
    obtain ⟨_, hcard⟩ := ih
    have hyV : y ∈ V := (hE x y hstep.1).2
    have hyx : dist y q < dist x q := hstep.2.1
    refine ⟨hyV, ?_⟩
    have hssub : V.filter (fun v => dist x q ≤ dist v q) ⊂
        V.filter (fun v => dist y q ≤ dist v q) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨y, Finset.mem_filter.mpr ⟨hyV, le_rfl⟩, ?_⟩
        rw [Finset.mem_filter]
        intro hcontra
        exact not_lt_of_ge hcontra.2 hyx
      · intro v hv
        rw [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, le_trans (le_of_lt hyx) hv.2⟩
    have hlt : (V.filter fun v => dist x q ≤ dist v q).card <
        (V.filter fun v => dist y q ≤ dist v q).card :=
      Finset.card_lt_card hssub
    omega

lemma exists_localMin_aux {d : ℕ} (V : Finset (Pt d)) (E : Finset (Pt d × Pt d))
    (hE : ∀ x y, (x, y) ∈ E → x ∈ V ∧ y ∈ V) (q x₀ : Pt d) :
    ∀ (m k : ℕ) (x : Pt d), x ∈ V →
      (V.filter fun v => dist v q < dist x q).card ≤ m →
      GreedyRun E q x₀ k x →
      ∃ k' y, GreedyRun E q x₀ k' y ∧ GreedyLocalMin E q y := by
  intro m
  induction m with
  | zero =>
    intro k x hxV hbelow hrun
    by_cases hloc : GreedyLocalMin E q x
    · exact ⟨k, x, hrun, hloc⟩
    · exfalso
      unfold GreedyLocalMin at hloc
      push_neg at hloc
      obtain ⟨z, hzE, hzx⟩ := hloc
      have hzV : z ∈ V := (hE x z hzE).2
      have hzmem : z ∈ V.filter (fun v => dist v q < dist x q) :=
        Finset.mem_filter.mpr ⟨hzV, hzx⟩
      have hpos : 0 < (V.filter fun v => dist v q < dist x q).card :=
        Finset.card_pos.mpr ⟨z, hzmem⟩
      omega
  | succ m ih =>
    intro k x _ hbelow hrun
    by_cases hloc : GreedyLocalMin E q x
    · exact ⟨k, x, hrun, hloc⟩
    · unfold GreedyLocalMin at hloc
      push_neg at hloc
      obtain ⟨z₀, hz₀E, hz₀x⟩ := hloc
      let outN : Finset (Pt d) := (E.filter fun e => e.1 = x).image Prod.snd
      have hz₀_mem : z₀ ∈ outN :=
        Finset.mem_image.mpr ⟨(x, z₀), Finset.mem_filter.mpr ⟨hz₀E, rfl⟩, rfl⟩
      obtain ⟨y, hy_mem, hy_min⟩ := outN.exists_min_image (fun z => dist z q) ⟨z₀, hz₀_mem⟩
      obtain ⟨⟨x', y'⟩, hxy_filt, rfl⟩ := Finset.mem_image.mp hy_mem
      obtain ⟨hxyE, rfl⟩ := Finset.mem_filter.mp hxy_filt
      dsimp only at hy_min hbelow ⊢
      have hyV : y' ∈ V := (hE x' y' hxyE).2
      have hyq : dist y' q < dist x' q := lt_of_le_of_lt (hy_min z₀ hz₀_mem) hz₀x
      have hstep : GreedyStep E q x' y' := by
        refine ⟨hxyE, hyq, ?_⟩
        intro z hzE
        exact hy_min z (Finset.mem_image.mpr ⟨(x', z), Finset.mem_filter.mpr ⟨hzE, rfl⟩, rfl⟩)
      have hssub : V.filter (fun v => dist v q < dist y' q) ⊂
          V.filter (fun v => dist v q < dist x' q) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨y', Finset.mem_filter.mpr ⟨hyV, hyq⟩, ?_⟩
          rw [Finset.mem_filter]
          intro hc
          exact lt_irrefl _ hc.2
        · intro v hv
          rw [Finset.mem_filter] at hv ⊢
          exact ⟨hv.1, lt_trans hv.2 hyq⟩
      have hlt : (V.filter fun v => dist v q < dist y' q).card <
          (V.filter fun v => dist v q < dist x' q).card :=
        Finset.card_lt_card hssub
      exact ih (k + 1) y' hyV (by omega) (GreedyRun.step hrun hstep)

end AuxDescent

theorem solution {d : ℕ} (V : Finset (Pt d)) (E : Finset (Pt d × Pt d))
    (hE : ∀ x y, (x, y) ∈ E → x ∈ V ∧ y ∈ V) (q x₀ : Pt d) (hx₀ : x₀ ∈ V) :
    (∀ k x, GreedyRun E q x₀ k x → k < V.card) ∧
      ∃ k x, GreedyRun E q x₀ k x ∧ GreedyLocalMin E q x := by
  constructor
  · intro k x hrun
    have hcard := (AuxDescent.run_above_card hE hx₀ hrun).2
    have hle : (V.filter fun v => dist x q ≤ dist v q).card ≤ V.card :=
      Finset.card_filter_le V _
    omega
  · exact AuxDescent.exists_localMin_aux V E hE q x₀
      (V.filter fun v => dist v q < dist x₀ q).card 0 x₀ hx₀ le_rfl GreedyRun.start

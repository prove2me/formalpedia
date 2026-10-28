-- Prove2me | solution 1 for PigeonholeDesign.Upper.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:08:04.351387+00:00
-- url     : https://prove2.me/submissions/989b752a-8a1f-47ce-b271-c0a59f67c4c1

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting
import Definitions.Def_PigeonholeDesign_Upper_Stopping
import Theorems.Thm_PigeonholeDesign_Upper_assign_balanced
import Theorems.Thm_PigeonholeDesign_Upper_unmatched_imbalance
import Theorems.Thm_PigeonholeDesign_Upper_component_1
import Theorems.Thm_PigeonholeDesign_Upper_component_2

open PigeonholeDesign.Upper

namespace PHU3Aux

lemma disc_split {E : Type*} [PseudoMetricSpace E] {T : ℕ} (x : Fin T → E) (w : Fin T → Bool)
    (M : Finset (Fin T))
    (h1 : Fintype.card {t // t ∈ M ∧ w t = false} = Fintype.card {t // t ∈ M ∧ w t = true})
    (h2 : Fintype.card {t // t ∈ Finset.univ \ M ∧ w t = false} =
      Fintype.card {t // t ∈ Finset.univ \ M ∧ w t = true}) :
    discrepancy x w ≤ discrepancyOn x w M + discrepancyOn x w (Finset.univ \ M) := by
  obtain ⟨e1'⟩ := Fintype.card_eq.1 h1
  obtain ⟨e2'⟩ := Fintype.card_eq.1 h2
  have hM : ∀ t, t ∈ Finset.univ \ M ↔ t ∉ M := by simp
  have key : ∀ (e1 : {t // t ∈ M ∧ w t = false} ≃ {t // t ∈ M ∧ w t = true})
      (e2 : {t // t ∈ Finset.univ \ M ∧ w t = false} ≃ {t // t ∈ Finset.univ \ M ∧ w t = true}),
      discrepancy x w ≤ (∑ a, dist (x a.1) (x (e1 a).1)) + ∑ a, dist (x a.1) (x (e2 a).1) := by
    intro e1 e2
    let f : {t // w t = false} → {t // w t = true} := fun a =>
      if h : a.1 ∈ M then ⟨(e1 ⟨a.1, h, a.2⟩).1, (e1 ⟨a.1, h, a.2⟩).2.2⟩
      else ⟨(e2 ⟨a.1, (hM _).2 h, a.2⟩).1, (e2 ⟨a.1, (hM _).2 h, a.2⟩).2.2⟩
    let g : {t // w t = true} → {t // w t = false} := fun b =>
      if h : b.1 ∈ M then ⟨(e1.symm ⟨b.1, h, b.2⟩).1, (e1.symm ⟨b.1, h, b.2⟩).2.2⟩
      else ⟨(e2.symm ⟨b.1, (hM _).2 h, b.2⟩).1, (e2.symm ⟨b.1, (hM _).2 h, b.2⟩).2.2⟩
    have hfg : ∀ a, g (f a) = a := by
      intro a
      by_cases h : a.1 ∈ M
      · have hm : (e1 ⟨a.1, h, a.2⟩).1 ∈ M := (e1 ⟨a.1, h, a.2⟩).2.1
        simp only [f, g, dif_pos h, dif_pos hm]
        apply Subtype.ext; simp
      · have hm : (e2 ⟨a.1, (hM _).2 h, a.2⟩).1 ∉ M := (hM _).1 (e2 ⟨a.1, (hM _).2 h, a.2⟩).2.1
        simp only [f, g, dif_neg h, dif_neg hm]
        apply Subtype.ext; simp
    have hgf : ∀ b, f (g b) = b := by
      intro b
      by_cases h : b.1 ∈ M
      · have hm : (e1.symm ⟨b.1, h, b.2⟩).1 ∈ M := (e1.symm ⟨b.1, h, b.2⟩).2.1
        simp only [f, g, dif_pos h, dif_pos hm]
        apply Subtype.ext; simp
      · have hm : (e2.symm ⟨b.1, (hM _).2 h, b.2⟩).1 ∉ M :=
          (hM _).1 (e2.symm ⟨b.1, (hM _).2 h, b.2⟩).2.1
        simp only [f, g, dif_neg h, dif_neg hm]
        apply Subtype.ext; simp
    let e : {t // w t = false} ≃ {t // w t = true} := ⟨f, g, hfg, hgf⟩
    have hle : discrepancy x w ≤ ∑ a, dist (x a.1) (x (e a).1) :=
      ciInf_le ⟨0, by rintro _ ⟨e', rfl⟩; exact Finset.sum_nonneg (fun _ _ => dist_nonneg)⟩ e
    refine hle.trans (le_of_eq ?_)
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : {t // w t = false} => a.1 ∈ M)]
    congr 1
    · refine Finset.sum_bij' (fun a ha => ⟨a.1, (Finset.mem_filter.1 ha).2, a.2⟩)
        (fun a _ => ⟨a.1, a.2.2⟩) (by simp) (fun a _ => by simpa using a.2.1) (by simp) (by simp) ?_
      intro a ha
      have h := (Finset.mem_filter.1 ha).2
      simp only [e, Equiv.coe_fn_mk, f, dif_pos h]
    · refine Finset.sum_bij' (fun a ha => ⟨a.1, (hM _).2 (Finset.mem_filter.1 ha).2, a.2⟩)
        (fun a _ => ⟨a.1, a.2.2⟩) (by simp) (fun a _ => by simpa using ((hM _).1 a.2.1))
        (by simp) (by simp) ?_
      intro a ha
      have h := (Finset.mem_filter.1 ha).2
      simp only [e, Equiv.coe_fn_mk, f, dif_neg h]
  have hb : ∀ e2 : {t // t ∈ Finset.univ \ M ∧ w t = false} ≃
      {t // t ∈ Finset.univ \ M ∧ w t = true},
      discrepancy x w - ∑ a, dist (x a.1) (x (e2 a).1) ≤ discrepancyOn x w M := by
    intro e2
    have : Nonempty ({t // t ∈ M ∧ w t = false} ≃ {t // t ∈ M ∧ w t = true}) := ⟨e1'⟩
    exact le_ciInf (fun e1 => by linarith [key e1 e2])
  have : Nonempty ({t // t ∈ Finset.univ \ M ∧ w t = false} ≃
      {t // t ∈ Finset.univ \ M ∧ w t = true}) := ⟨e2'⟩
  have : discrepancy x w - discrepancyOn x w M ≤ discrepancyOn x w (Finset.univ \ M) :=
    le_ciInf (fun e2 => by linarith [hb e2])
  linarith

end PHU3Aux

open PHU3Aux in
theorem solution (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ x : Fin T → ℝ, (∀ t, x t ∈ Set.Icc (0 : ℝ) 1) →
        phdExp (uniformHole ⌈(T : ℝ) ^ η⌉₊) x
          ≤ C * ((T : ℝ) ^ (1 / 2 - η / 2) + (T : ℝ) ^ (η / 2) * Real.sqrt (Real.log T)) := by
  obtain ⟨C1, hC1, h1⟩ := PigeonholeDesign.Upper.component_1
  obtain ⟨C2, hC2, T₂, h2⟩ := PigeonholeDesign.Upper.component_2 η hη0 hη1
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, max T₂ 1, ?_⟩
  intro T hT hTe x hx
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  set K := ⌈(T : ℝ) ^ η⌉₊ with hK
  set hole := uniformHole K with hhole
  have hsplit : ∀ coin : Fin T → Bool,
      discrepancy x (assign hole x coin) ≤
        discrepancyOn x (assign hole x coin) (matched hole x coin) +
          discrepancyOn x (assign hole x coin) (matched hole x coin)ᶜ := by
    intro coin
    set w := assign hole x coin with hw
    set M := matched hole x coin with hM
    have hU := PigeonholeDesign.Upper.unmatched_imbalance η hη0 hη1 T hT1 hTe x hx coin
    have hbal := PigeonholeDesign.Upper.assign_balanced hTe hole x coin
    have hmb : ∀ b : Bool, (M.filter (fun t => w t = b)).card =
        ∑ k ∈ Finset.range K, (M.filter (fun s => hole (x s) = k ∧ w s = b)).card := by
      intro b
      rw [Finset.card_eq_sum_card_fiberwise (f := fun s => hole (x s)) (t := Finset.range K)]
      · apply Finset.sum_congr rfl; intro k _
        rw [Finset.filter_filter]; congr 1; ext s; simp; tauto
      · intro s _
        simp only [Finset.coe_range, Set.mem_Iio, hhole, uniformHole]
        have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
        have hpos : 0 < (T : ℝ) ^ η := by positivity
        have hK1 : 1 ≤ K := Nat.ceil_pos.2 hpos
        have := min_le_right ⌊x s * K⌋₊ (K - 1)
        omega
    have h1' : Fintype.card {t // t ∈ M ∧ w t = false} = Fintype.card {t // t ∈ M ∧ w t = true} := by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      have e : ∀ b : Bool, Finset.univ.filter (fun t => t ∈ M ∧ w t = b) = M.filter (fun t => w t = b) := by
        intro b; ext t; simp
      rw [e, e, hmb, hmb]
      apply Finset.sum_congr rfl; intro k _
      exact hU.2.1 k
    have hb : ∀ b : Bool, Fintype.card {t // t ∈ Finset.univ \ M ∧ w t = b} +
        Fintype.card {t // t ∈ M ∧ w t = b} =
          (Finset.univ.filter (fun t => w t = b)).card := by
      intro b
      rw [Fintype.card_subtype, Fintype.card_subtype,
        ← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun t => w t = b))
          (fun t => t ∉ M), Finset.filter_filter, Finset.filter_filter]
      congr 1 <;> (congr 1; ext t; simp; try tauto)
    have h2' : Fintype.card {t // t ∈ Finset.univ \ M ∧ w t = false} =
        Fintype.card {t // t ∈ Finset.univ \ M ∧ w t = true} := by
      have hf : (Finset.univ.filter (fun t => w t = false)).card = T / 2 := hbal.1
      have ht : (Finset.univ.filter (fun t => w t = true)).card = T / 2 := hbal.2
      have := hb false; have := hb true; clear hU hmb; omega
    have := disc_split x w M h1' h2'
    rwa [← Finset.compl_eq_univ_sdiff] at this
  have hc1 := h1 η hη0 hη1 T hT1 hTe x hx
  have hc2 := h2 T (le_trans (le_max_left _ _) hT) hTe x hx
  have hpow : (0 : ℝ) < 2 ^ T := by positivity
  rw [div_le_iff₀ hpow] at hc1 hc2
  unfold phdExp
  rw [div_le_iff₀ hpow]
  have hsum := Finset.sum_le_sum (fun coin (_ : coin ∈ (Finset.univ : Finset (Fin T → Bool))) =>
    hsplit coin)
  rw [Finset.sum_add_distrib] at hsum
  have hA : 0 ≤ (T : ℝ) ^ (1 / 2 - η / 2) := by positivity
  have hB : 0 ≤ (T : ℝ) ^ (η / 2) * Real.sqrt (Real.log T) := by positivity
  have e1 := mul_le_mul_of_nonneg_right (le_max_left C1 C2) hA
  have e2 := mul_le_mul_of_nonneg_right (le_max_right C1 C2) hB
  have hfin : C1 * (T : ℝ) ^ (1 / 2 - η / 2) + C2 * ((T : ℝ) ^ (η / 2) * Real.sqrt (Real.log T)) ≤
      max C1 C2 * ((T : ℝ) ^ (1 / 2 - η / 2) + (T : ℝ) ^ (η / 2) * Real.sqrt (Real.log T)) := by
    rw [mul_add]; linarith
  have := mul_le_mul_of_nonneg_right hfin hpow.le
  nlinarith

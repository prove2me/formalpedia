-- Prove2me | solution 1 for RobustMNL.SizeCon.rectangular_reduction
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:48:25.14259+00:00
-- url     : https://prove2.me/submissions/13066108-fe44-4e1b-b7bb-604aa668d0e6

import Mathlib
import Definitions.Def_RobustMNL_SizeCon_Model

open RobustMNL.SizeCon RobustMNL.Static
open scoped BigOperators

private noncomputable def phi {n : ℕ} (r : Fin n → ℝ) (S : Finset (Fin n))
    (lam : ℝ) (p : ℝ × (Fin n → ℝ)) : ℝ :=
  (1 / p.1) * ∑ i ∈ S, p.2 i * (r i - lam)

private lemma cont_phi {n : ℕ} (r : Fin n → ℝ) (S : Finset (Fin n)) (lam : ℝ)
    (V : Set (ℝ × (Fin n → ℝ))) (hpos : ∀ p ∈ V, IsPos p) :
    ContinuousOn (phi r S lam) V := by
  unfold phi
  apply ContinuousOn.mul
  · exact continuousOn_const.div continuous_fst.continuousOn
      (fun p hp => ne_of_gt (hpos p hp).1)
  · exact (by fun_prop : Continuous (fun p : ℝ × (Fin n → ℝ) =>
      ∑ i ∈ S, p.2 i * (r i - lam))).continuousOn

private lemma box_pos {n : ℕ} (l₀ u₀ : ℝ) (l u : Fin n → ℝ) (hl₀ : 0 < l₀)
    (hl : ∀ i, 0 < l i) : ∀ p ∈ box l₀ u₀ l u, IsPos p := by
  rintro p ⟨hp0, hp⟩
  exact ⟨hl₀.trans_le hp0.1, fun i => (hl i).trans_le (hp.1 i)⟩

theorem solution {n : ℕ} (l₀ u₀ : ℝ) (l u : Fin n → ℝ) (hl₀ : 0 < l₀)
    (hlu₀ : l₀ ≤ u₀) (hl : ∀ i, 0 < l i) (hlu : l ≤ u) (r : Fin n → ℝ) (K : ℕ) (lam : ℝ) :
    paramValue (box l₀ u₀ l u) r K lam =
      (sizeFeasible n K).sup' (sizeFeasible_nonempty n K)
        (fun S => (1 / u₀) * ∑ i ∈ S, l i * (r i - lam)) := by
  let V := box l₀ u₀ l u
  have hq : (u₀, l) ∈ V := ⟨⟨hlu₀, le_rfl⟩, ⟨le_rfl, hlu⟩⟩
  have hc : IsCompact V := isCompact_Icc.prod isCompact_Icc
  have hpos := box_pos l₀ u₀ l u hl₀ hl
  have hu₀ := hl₀.trans_le hlu₀
  unfold paramValue
  apply le_antisymm
  · apply Finset.sup'_le
    intro S hS
    have hbound := csInf_le ((hc.image_of_continuousOn (cont_phi r S lam V hpos)).bddBelow)
      (show phi r S lam (u₀, l) ∈ (phi r S lam) '' V from ⟨_, hq, rfl⟩)
    exact hbound.trans (Finset.le_sup' (fun S => (1 / u₀) * ∑ i ∈ S, l i * (r i - lam)) hS)
  · apply Finset.sup'_le
    intro S hS
    let A := S.filter (fun i => 0 ≤ r i - lam)
    have hAS : A ⊆ S := Finset.filter_subset _ _
    have hA : A ∈ sizeFeasible n K := by
      have hcard := Finset.card_le_card hAS
      simp only [sizeFeasible, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      omega
    have hApos : ∀ i ∈ A, 0 ≤ r i - lam := by intro i hi; exact (Finset.mem_filter.mp hi).2
    have hnonneg : 0 ≤ ∑ i ∈ A, l i * (r i - lam) :=
      Finset.sum_nonneg (fun i hi => mul_nonneg (hl i).le (hApos i hi))
    have hsum : (∑ i ∈ S, l i * (r i - lam)) ≤ ∑ i ∈ A, l i * (r i - lam) := by
      simp only [A, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro i hi
      split_ifs with h
      · exact le_rfl
      · exact (mul_neg_of_pos_of_neg (hl i) (lt_of_not_ge h)).le
    have hbelow : phi r A lam (u₀, l) ≤ sInf ((phi r A lam) '' V) := by
      apply le_csInf ((show V.Nonempty from ⟨(u₀, l), hq⟩).image (phi r A lam))
      rintro _ ⟨p, hp, rfl⟩
      have hnum : (∑ i ∈ A, l i * (r i - lam)) ≤ ∑ i ∈ A, p.2 i * (r i - lam) :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hp.2.1 i) (hApos i hi))
      have hinv : 1 / u₀ ≤ 1 / p.1 := one_div_le_one_div_of_le (hpos p hp).1 hp.1.2
      exact mul_le_mul hinv hnum hnonneg (one_div_pos.mpr (hpos p hp).1).le
    exact (mul_le_mul_of_nonneg_left hsum (one_div_pos.mpr hu₀).le).trans
      (hbelow.trans (Finset.le_sup' (fun S => sInf ((phi r S lam) '' V)) hA))

-- Prove2me | solution 1 for RobustMNL.SizeCon.rectangular_unconstrained
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:48:28.977419+00:00
-- url     : https://prove2.me/submissions/c62f943b-b626-40c5-a843-e1902bc3b815

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

private lemma den_pos {n : ℕ} (S : Finset (Fin n)) (p : ℝ × (Fin n → ℝ))
    (hp : IsPos p) : 0 < (∑ i ∈ S, p.2 i) + p.1 := by
  exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ => (hp.2 i).le)) hp.1

private lemma cont_rev {n : ℕ} (r : Fin n → ℝ) (S : Finset (Fin n))
    (V : Set (ℝ × (Fin n → ℝ))) (hpos : ∀ p ∈ V, IsPos p) :
    ContinuousOn (rev r S) V := by
  unfold rev ChoiceCDLP.MNL.mnlObjective
  apply ContinuousOn.div
  · exact (by fun_prop : Continuous (fun p : ℝ × (Fin n → ℝ) =>
      ∑ i ∈ S, r i * p.2 i)).continuousOn
  · exact (by fun_prop : Continuous (fun p : ℝ × (Fin n → ℝ) =>
      (∑ i ∈ S, p.2 i) + p.1)).continuousOn
  · intro p hp
    exact ne_of_gt (den_pos S p (hpos p hp))

private lemma inf_threshold {α : Type*} [TopologicalSpace α] (V : Set α)
    (hc : IsCompact V) (hne : V.Nonempty) (f : α → ℝ) (hf : ContinuousOn f V) (lam : ℝ) :
    lam ≤ sInf (f '' V) ↔ ∀ p ∈ V, lam ≤ f p := by
  have hb := (hc.image_of_continuousOn hf).bddBelow
  constructor
  · intro h p hp
    exact h.trans (csInf_le hb ⟨p, hp, rfl⟩)
  · intro h
    apply le_csInf (hne.image f)
    rintro _ ⟨p, hp, rfl⟩
    exact h p hp

private lemma rev_threshold {n : ℕ} (r : Fin n → ℝ) (S : Finset (Fin n))
    (lam : ℝ) (p : ℝ × (Fin n → ℝ)) (hp : IsPos p) :
    lam ≤ rev r S p ↔ lam ≤ phi r S lam p := by
  have hd := den_pos S p hp
  have hid : (∑ i ∈ S, p.2 i * (r i - lam)) =
      (∑ i ∈ S, r i * p.2 i) - lam * ∑ i ∈ S, p.2 i := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
  unfold rev ChoiceCDLP.MNL.mnlObjective phi
  rw [show (1 / p.1) * (∑ i ∈ S, p.2 i * (r i - lam)) =
      (∑ i ∈ S, p.2 i * (r i - lam)) / p.1 by ring]
  rw [le_div_iff₀ hd, le_div_iff₀ hp.1, hid]
  constructor <;> intro h <;> nlinarith

private lemma param_threshold {n : ℕ} (V : Set (ℝ × (Fin n → ℝ))) (hc : IsCompact V)
    (hne : V.Nonempty) (hpos : ∀ p ∈ V, IsPos p) (r : Fin n → ℝ) (K : ℕ) (lam : ℝ) :
    lam ≤ paramValue V r K lam ↔ lam ≤ Ystar V r K := by
  unfold paramValue Ystar
  rw [Finset.le_sup'_iff, Finset.le_sup'_iff]
  apply exists_congr
  intro S
  apply and_congr_right
  intro hS
  change (lam ≤ sInf ((phi r S lam) '' V)) ↔ lam ≤ sInf ((rev r S) '' V)
  rw [inf_threshold V hc hne _ (cont_phi r S lam V hpos),
      inf_threshold V hc hne _ (cont_rev r S V hpos)]
  exact forall_congr' (fun p => forall_congr' (fun hp => (rev_threshold r S lam p (hpos p hp)).symm))

theorem parametric_aux {n : ℕ} (V : Set (ℝ × (Fin n → ℝ))) (hVc : IsCompact V)
    (hVne : V.Nonempty) (hVpos : ∀ p ∈ V, IsPos p) (r : Fin n → ℝ) (K : ℕ) :
    IsGreatest {lam : ℝ | lam ≤ paramValue V r K lam} (Ystar V r K) := by
  exact ⟨(param_threshold V hVc hVne hVpos r K _).mpr le_rfl,
    fun lam hlam => (param_threshold V hVc hVne hVpos r K lam).mp hlam⟩

theorem known_parametric_aux {n : ℕ} (u₀ : ℝ) (l : Fin n → ℝ) (hu₀ : 0 < u₀)
    (hl : ∀ i, 0 < l i) (r : Fin n → ℝ) (K : ℕ) :
    IsGreatest {lam : ℝ | lam ≤ (sizeFeasible n K).sup' (sizeFeasible_nonempty n K)
      (fun S => (1 / u₀) * ∑ i ∈ S, l i * (r i - lam))} (knownMax r K (u₀, l)) := by
  have h := parametric_aux ({(u₀, l)} : Set (ℝ × (Fin n → ℝ))) isCompact_singleton
    (Set.singleton_nonempty _) (by intro p hp; rcases hp with rfl; exact ⟨hu₀, hl⟩) r K
  have hw : worst ({(u₀, l)} : Set (ℝ × (Fin n → ℝ))) r = fun S => rev r S (u₀, l) := by
    funext S
    simp [worst]
  simpa only [paramValue, Ystar, hw, Set.image_singleton, csInf_singleton, knownMax] using h

private lemma box_pos {n : ℕ} (l₀ u₀ : ℝ) (l u : Fin n → ℝ) (hl₀ : 0 < l₀)
    (hl : ∀ i, 0 < l i) : ∀ p ∈ box l₀ u₀ l u, IsPos p := by
  rintro p ⟨hp0, hp⟩
  exact ⟨hl₀.trans_le hp0.1, fun i => (hl i).trans_le (hp.1 i)⟩

theorem rectangular_aux {n : ℕ} (l₀ u₀ : ℝ) (l u : Fin n → ℝ) (hl₀ : 0 < l₀)
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

theorem main_aux {n : ℕ} (l₀ u₀ : ℝ) (l u : Fin n → ℝ) (hl₀ : 0 < l₀)
    (hlu₀ : l₀ ≤ u₀) (hl : ∀ i, 0 < l i) (hlu : l ≤ u) (r : Fin n → ℝ) (K : ℕ) :
    Ystar (box l₀ u₀ l u) r K = knownMax r K (u₀, l) := by
  have ha := parametric_aux (box l₀ u₀ l u) (isCompact_Icc.prod isCompact_Icc)
    ⟨(u₀, l), ⟨⟨hlu₀, le_rfl⟩, ⟨le_rfl, hlu⟩⟩⟩ (box_pos l₀ u₀ l u hl₀ hl) r K
  have hb := known_parametric_aux u₀ l (hl₀.trans_le hlu₀) hl r K
  simp only [rectangular_aux l₀ u₀ l u hl₀ hlu₀ hl hlu r K] at ha
  exact ha.unique hb

theorem solution {n : ℕ} (l₀ u₀ : ℝ) (l u : Fin n → ℝ) (hl₀ : 0 < l₀)
    (hlu₀ : l₀ ≤ u₀) (hl : ∀ i, 0 < l i) (hlu : l ≤ u) (r : Fin n → ℝ) :
    Zstar (box l₀ u₀ l u) r =
      (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty
        (fun S => rev r S (u₀, l)) := by
  have hsf : sizeFeasible n n = Finset.univ := by
    ext S
    simp only [sizeFeasible, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)
  have h := main_aux l₀ u₀ l u hl₀ hlu₀ hl hlu r n
  simpa only [Ystar, knownMax, hsf, Zstar] using h

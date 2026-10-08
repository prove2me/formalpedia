-- Prove2me | solution 1 for RobustMNL.SizeCon.known_weights_parametric
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:48:26.831197+00:00
-- url     : https://prove2.me/submissions/1403206d-20b7-4e2b-8bae-bcf995233e65

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

theorem solution {n : ℕ} (u₀ : ℝ) (l : Fin n → ℝ) (hu₀ : 0 < u₀)
    (hl : ∀ i, 0 < l i) (r : Fin n → ℝ) (K : ℕ) :
    IsGreatest {lam : ℝ | lam ≤ (sizeFeasible n K).sup' (sizeFeasible_nonempty n K)
      (fun S => (1 / u₀) * ∑ i ∈ S, l i * (r i - lam))} (knownMax r K (u₀, l)) := by
  have h := parametric_aux ({(u₀, l)} : Set (ℝ × (Fin n → ℝ))) isCompact_singleton
    (Set.singleton_nonempty _) (by intro p hp; rcases hp with rfl; exact ⟨hu₀, hl⟩) r K
  have hw : worst ({(u₀, l)} : Set (ℝ × (Fin n → ℝ))) r = fun S => rev r S (u₀, l) := by
    funext S
    simp [worst]
  simpa only [paramValue, Ystar, hw, Set.image_singleton, csInf_singleton, knownMax] using h

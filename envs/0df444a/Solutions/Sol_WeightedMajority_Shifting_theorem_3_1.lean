-- Prove2me | solution 1 for WeightedMajority.Shifting.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:54:46.397108+00:00
-- url     : https://prove2.me/submissions/2bcba408-e71f-48ba-82b7-f8767532c448

import Mathlib
import Theorems.Thm_WeightedMajority_Shifting_lemma_3_1

open WeightedMajority.Shifting
open Finset
open scoped BigOperators

private lemma block_weight_pos {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β)
    {x : Fin T → Fin n → Bool} {ρ : Fin T → Bool} {w : ℕ → Fin n → ℝ} {lam : Fin T → Bool}
    (hrun : IsWMLRun β γ x ρ w lam) : ∀ k, k ≤ T → ∀ i, 0 < w k i := by
  intro k
  induction k with
  | zero => intro _ i; exact hrun.init_pos i
  | succ k ih =>
    intro hk i
    have := hrun.update ⟨k, by omega⟩
    simp only at this
    rw [this]
    have h := ih (by omega) i
    unfold wmlUpdate
    split_ifs
    · positivity
    · exact h

private lemma block_weight_mono {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {x : Fin T → Fin n → Bool} {ρ : Fin T → Bool} {w : ℕ → Fin n → ℝ} {lam : Fin T → Bool}
    (hrun : IsWMLRun β γ x ρ w lam) (t : Fin T) (i : Fin n) :
    β * w t i ≤ w ((t : ℕ) + 1) i ∧ w ((t : ℕ) + 1) i ≤ w t i := by
  have hp := block_weight_pos hβ0 hrun t (by omega) i
  rw [hrun.update t]
  unfold wmlUpdate
  split_ifs
  · exact ⟨le_rfl, by nlinarith⟩
  · exact ⟨by nlinarith, le_rfl⟩

private lemma block_floor {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ)
    {x : Fin T → Fin n → Bool} {ρ : Fin T → Bool} {w : ℕ → Fin n → ℝ} {lam : Fin T → Bool}
    (hrun : IsWMLRun β γ x ρ w lam)
    (hfloor : ∀ i, β * γ / (n : ℝ) * totalWeight (w 0) ≤ w 0 i) :
    ∀ k, k ≤ T → ∀ i, β * γ / (n : ℝ) * totalWeight (w k) ≤ w k i := by
  intro k
  induction k with
  | zero => intro _; exact hfloor
  | succ k ih =>
    intro hk i
    have hkT : k < T := by omega
    set t : Fin T := ⟨k, hkT⟩
    have hWle : totalWeight (w (k+1)) ≤ totalWeight (w k) :=
      Finset.sum_le_sum (fun j _ => (block_weight_mono hβ0 hβ1 hrun t j).2)
    have hc : 0 ≤ β * γ / (n : ℝ) := by positivity
    have h0 := ih (by omega) i
    have hupd := hrun.update t
    have hi : w (k+1) i = wmlUpdate β γ (w k) (x t) (ρ t) (lam t) i := by
      rw [hupd]
    rw [hi]
    unfold wmlUpdate
    split_ifs with hcond
    · have h3 := hcond.2.2
      have : β * (γ / (n:ℝ) * totalWeight (w k)) < β * w k i := by nlinarith
      calc β * γ / (n : ℝ) * totalWeight (w (k+1)) ≤ β * γ / (n : ℝ) * totalWeight (w k) :=
            mul_le_mul_of_nonneg_left hWle hc
        _ = β * (γ / (n:ℝ) * totalWeight (w k)) := by ring
        _ ≤ _ := this.le
    · calc β * γ / (n : ℝ) * totalWeight (w (k+1)) ≤ β * γ / (n : ℝ) * totalWeight (w k) :=
            mul_le_mul_of_nonneg_left hWle hc
        _ ≤ _ := h0

private def segIndex {T : ℕ} (a b : ℕ) (hb : b ≤ T) (t : Fin (b-a)) : Fin T :=
  ⟨a + t.val, by have := t.isLt; omega⟩

private lemma segment_card {T : ℕ} (P : Fin T → Prop) [DecidablePred P]
    (a b : ℕ) (hb : b ≤ T) :
    (univ.filter (fun t : Fin (b-a) => P (segIndex a b hb t))).card =
      (univ.filter (fun t : Fin T => a ≤ t.val ∧ t.val < b ∧ P t)).card := by
  apply Finset.card_bij (fun t _ => segIndex a b hb t)
  · intro t ht
    have hp := (mem_filter.mp ht).2
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨by simp [segIndex], by have := t.isLt; simp only [segIndex]; omega, hp⟩
  · intro t ht s hs heq
    apply Fin.ext
    have heq' := congrArg Fin.val heq
    simp only [segIndex] at heq'
    omega
  · intro t ht
    obtain ⟨ha, hb', hp⟩ := (mem_filter.mp ht).2
    let s : Fin (b-a) := ⟨t.val-a, by omega⟩
    have heq : segIndex a b hb s = t := by apply Fin.ext; simp only [segIndex, s]; omega
    exact ⟨s, by simp only [mem_filter, mem_univ, true_and]; rw [heq]; exact hp, heq⟩

private lemma segment_run {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β)
    {x : Fin T → Fin n → Bool} {ρ : Fin T → Bool} {w : ℕ → Fin n → ℝ} {lam : Fin T → Bool}
    (hrun : IsWMLRun β γ x ρ w lam) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ T) :
    IsWMLRun β γ (fun t => x (segIndex a b hb t)) (fun t => ρ (segIndex a b hb t))
      (fun k => w (a+k)) (fun t => lam (segIndex a b hb t)) := by
  constructor
  · intro i
    simpa using block_weight_pos hβ0 hrun a (hab.trans hb) i
  · intro t
    exact hrun.predict (segIndex a b hb t)
  · intro t
    simpa only [segIndex, Nat.add_assoc] using hrun.update (segIndex a b hb t)

private lemma segment_best {n T : ℕ} (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool)
    (a b : ℕ) (hb : b ≤ T) :
    bestMistakesOn (fun t => x (segIndex a b hb t)) (fun t => ρ (segIndex a b hb t)) 0 (b-a) =
      bestMistakesOn x ρ a b := by
  unfold bestMistakesOn
  congr 1
  funext i
  unfold memberMistakesOn
  simpa only [Nat.zero_le, Fin.is_lt, true_and] using
    segment_card (fun t => x t i ≠ ρ t) a b hb

private lemma segment_bound {n T : ℕ} (hn : 0 < n) {β γ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1/2)
    (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool)
    (hrun : IsWMLRun β γ x ρ w lam)
    (hfloor : ∀ i, β*γ/(n:ℝ)*totalWeight (w 0) ≤ w 0 i)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ T) :
    ((univ.filter (fun t : Fin T => a ≤ t.val ∧ t.val < b ∧ lam t ≠ ρ t)).card : ℝ) ≤
      min ((b-a : ℕ) : ℝ)
        ((Real.log ((n:ℝ)/(β*γ)) + (bestMistakesOn x ρ a b : ℝ)*Real.log (1/β)) /
          Real.log (1/uFactor β γ)) := by
  have hs := segment_run hβ0 hrun a b hab hb
  have hf : ∀ i, β*γ/(n:ℝ)*totalWeight ((fun k => w (a+k)) 0) ≤ (fun k => w (a+k)) 0 i := by
    simpa only [Nat.add_zero] using block_floor hβ0 hβ1 hγ0.le hrun hfloor a (hab.trans hb)
  have h := (lemma_3_1 hn hβ0 hβ1 hγ0 hγ1 _ _ _ _ hs hf).1
  rw [segment_best x ρ a b hb] at h
  have heq := segment_card (fun t => lam t ≠ ρ t) a b hb
  unfold masterMistakes at h
  rw [heq] at h
  apply le_min _ h
  rw [← heq]
  exact_mod_cast (Finset.card_filter_le (univ : Finset (Fin (b-a)))
    (fun t => lam (segIndex a b hb t) ≠ ρ (segIndex a b hb t))).trans_eq (Fintype.card_fin (b-a))

private lemma prefix_add_segment {T : ℕ} (P : Fin T → Prop) [DecidablePred P]
    (a b : ℕ) (hab : a ≤ b) :
    (univ.filter (fun t : Fin T => t.val < a ∧ P t)).card +
      (univ.filter (fun t : Fin T => a ≤ t.val ∧ t.val < b ∧ P t)).card =
      (univ.filter (fun t : Fin T => t.val < b ∧ P t)).card := by
  have hd : Disjoint (univ.filter (fun t : Fin T => t.val < a ∧ P t))
      (univ.filter (fun t : Fin T => a ≤ t.val ∧ t.val < b ∧ P t)) := by
    apply Finset.disjoint_left.mpr
    intro t ht hu
    have ht := (mem_filter.mp ht).2
    have hu := (mem_filter.mp hu).2
    omega
  rw [← Finset.card_union_of_disjoint hd]
  congr 1
  ext t
  simp only [mem_union, mem_filter, mem_univ, true_and]
  constructor
  · rintro (⟨ha, hp⟩ | ⟨ha, hb, hp⟩)
    · exact ⟨ha.trans_le hab, hp⟩
    · exact ⟨hb, hp⟩
  · rintro ⟨hb, hp⟩
    by_cases ha : t.val < a
    · exact Or.inl ⟨ha, hp⟩
    · exact Or.inr ⟨by omega, hb, hp⟩

private lemma partition_card {T : ℕ} (P : Fin T → Prop) [DecidablePred P]
    (k : ℕ) (b : Fin (k+1) → ℕ) (hb_mono : Monotone b) (hb0 : b 0 = 0)
    (hbk : b (Fin.last k) = T) :
    ((univ.filter P).card : ℝ) =
      ∑ i : Fin k, ((univ.filter (fun t : Fin T =>
        b i.castSucc ≤ t.val ∧ t.val < b i.succ ∧ P t)).card : ℝ) := by
  let c : Fin (k+1) → ℝ := fun i => ((univ.filter (fun t : Fin T => t.val < b i ∧ P t)).card : ℝ)
  have hdiff : ∀ i : Fin k,
      ((univ.filter (fun t : Fin T => b i.castSucc ≤ t.val ∧ t.val < b i.succ ∧ P t)).card : ℝ) =
      c i.succ - c i.castSucc := by
    intro i
    have heq := prefix_add_segment P (b i.castSucc) (b i.succ) (hb_mono i.castSucc_lt_succ.le)
    have heq' : c i.castSucc + ((univ.filter (fun t : Fin T =>
        b i.castSucc ≤ t.val ∧ t.val < b i.succ ∧ P t)).card : ℝ) = c i.succ := by
      dsimp only [c]
      exact_mod_cast heq
    linarith
  simp_rw [hdiff]
  rw [Finset.sum_sub_distrib]
  have hfirst : c 0 = 0 := by simp [c, hb0]
  have hlast : c (Fin.last k) = ((univ.filter P).card : ℝ) := by simp [c, hbk]
  have h₁ := Fin.sum_univ_succ c
  have h₂ := Fin.sum_univ_castSucc c
  linarith

theorem solution {n T : ℕ} (hn : 0 < n) {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2)
    (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool)
    (hrun : IsWMLRun β γ x ρ w lam)
    (hfloor : ∀ i, β * γ / (n : ℝ) * totalWeight (w 0) ≤ w 0 i)
    (k : ℕ) (b : Fin (k + 1) → ℕ) (hb_mono : Monotone b) (hb0 : b 0 = 0)
    (hbk : b (Fin.last k) = T) :
    (masterMistakes ρ lam : ℝ) ≤
      ∑ i : Fin k, min ((b i.succ - b i.castSucc : ℕ) : ℝ)
        ((Real.log ((n : ℝ) / (β * γ)) +
            (bestMistakesOn x ρ (b i.castSucc) (b i.succ) : ℝ) * Real.log (1 / β)) /
          Real.log (1 / uFactor β γ)) := by
  unfold masterMistakes
  rw [partition_card (fun t => lam t ≠ ρ t) k b hb_mono hb0 hbk]
  apply Finset.sum_le_sum
  intro i hi
  apply segment_bound hn hβ0 hβ1 hγ0 hγ1 x ρ w lam hrun hfloor
  · exact hb_mono i.castSucc_lt_succ.le
  · rw [← hbk]
    exact hb_mono (Fin.le_last _)



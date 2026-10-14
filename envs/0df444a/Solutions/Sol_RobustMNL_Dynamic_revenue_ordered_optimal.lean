-- Prove2me | solution 1 for RobustMNL.Dynamic.revenue_ordered_optimal
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:30:27.031182+00:00
-- url     : https://prove2.me/submissions/975172c6-5dcf-4c81-8e49-2af0ed314377

import Mathlib
import Definitions.Def_RobustMNL_Dynamic_ValueFunction
import Theorems.Thm_RobustMNL_Static_incremental_value_bounds
import Theorems.Thm_RobustMNL_Static_revenue_ordered_robust
import Theorems.Thm_RobustMNL_Static_incremental_revenue_larger
import Theorems.Thm_RobustMNL_Static_larger_uncertainty

open scoped BigOperators
open RobustMNL.Static RobustMNL.Dynamic

private lemma dm_cont {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hp : ∀ p ∈ V, IsPos p) (S : Finset (Fin n)) : ContinuousOn (rev r S) V := by
  unfold rev ChoiceCDLP.MNL.mnlObjective
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro p h
    exact ne_of_gt (add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => (hp p h).2 i |>.le) (hp p h).1)

private lemma dm_min {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hc : IsCompact V) (hn : V.Nonempty) (hp : ∀ p ∈ V, IsPos p) (S : Finset (Fin n)) :
    ∃ p ∈ V, worst V r S = rev r S p ∧ ∀ q ∈ V, rev r S p ≤ rev r S q := by
  exact hc.exists_sInf_image_eq_and_le hn (dm_cont r V hp S)

private lemma dm_prob {n : ℕ} (r : Fin n → ℝ) (S : Finset (Fin n))
    (p : ℝ × (Fin n → ℝ)) : (∑ i ∈ S, choiceProb S p i * r i) = rev r S p := by
  classical
  unfold rev ChoiceCDLP.MNL.mnlObjective
  calc
    (∑ i ∈ S, choiceProb S p i * r i) = ∑ i ∈ S, (r i * p.2 i) / (p.1 + ∑ ℓ ∈ S, p.2 ℓ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [choiceProb, if_pos hi]
      ring
    _ = _ := by rw [Finset.sum_div]; rw [add_comm p.1]

private lemma dm_point {n : ℕ} (r : Fin n → ℝ) (a b : ℝ) (S : Finset (Fin n))
    (p : ℝ × (Fin n → ℝ)) :
    (∑ i ∈ S, choiceProb S p i * (r i + a)) + (1 - ∑ i ∈ S, choiceProb S p i) * b =
      rev (fun i => r i - (b - a)) S p + b := by
  rw [← dm_prob]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

private lemma dm_stage {n : ℕ} (V : Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ)
    (hc : IsCompact V) (hn : V.Nonempty) (hp : ∀ p ∈ V, IsPos p) (a b : ℝ) (S : Finset (Fin n)) :
    stageValue V r a b S = worst V (fun i => r i - (b - a)) S + b := by
  obtain ⟨p, hpm, he, hl⟩ := dm_min (fun i => r i - (b-a)) V hc hn hp S
  unfold stageValue
  simp_rw [dm_point]
  rw [he]
  apply IsLeast.csInf_eq
  exact ⟨⟨p, hpm, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact add_le_add (hl q hq) le_rfl⟩

private lemma dm_sup_add {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (b : ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => f i + b) =
      Finset.univ.sup' Finset.univ_nonempty f + b := by
  classical
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty f
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun j hj => add_le_add (Finset.le_sup' f hj) le_rfl)
  · rw [he]
    exact Finset.le_sup' (fun i => f i + b) hi

private lemma dm_step {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (s x : ℕ) (hs : s < T) :
    Jgo T V r (s+1) (x+1) = Jgo T V r s (x+1) +
      Zstar (V (T-s)) (fun i => r i - (Jgo T V r s (x+1) - Jgo T V r s x)) := by
  obtain ⟨hc, hn, hp⟩ := hV (T-s) (by omega) (by omega)
  rw [Jgo]
  simp_rw [dm_stage _ _ hc hn hp]
  rw [dm_sup_add]
  exact add_comm _ _

private lemma dm_nonneg {n : ℕ} (V : Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ)
    (hn : V.Nonempty) : 0 ≤ Zstar V r := by
  have he : worst V r ∅ = 0 := by
    have him : (fun _ : ℝ × (Fin n → ℝ) => (0 : ℝ)) '' V = {0} := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩; rfl
      · intro hz; obtain ⟨p, hp⟩ := hn; exact ⟨p, hp, (Set.mem_singleton_iff.mp hz).symm⟩
    simpa only [worst, rev, ChoiceCDLP.MNL.mnlObjective, Finset.sum_empty, zero_div, him, csInf_singleton]
  rw [← he]
  exact Finset.le_sup' _ (Finset.mem_univ ∅)

private lemma dm_bounds {n : ℕ} (V : Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ)
    (hc : IsCompact V) (hn : V.Nonempty) (hp : ∀ p ∈ V, IsPos p) (a b : ℝ) (hab : a ≤ b) :
    Zstar V (fun i => r i - b) ≤ Zstar V (fun i => r i - a) ∧
    Zstar V (fun i => r i - a) ≤ Zstar V (fun i => r i - b) + (b-a) := by
  have h := RobustMNL.Static.incremental_value_bounds (fun i => r i - b) V hc hn hp (b-a) (sub_nonneg.mpr hab)
  have he : (fun i => r i - b + (b-a)) = (fun i => r i - a) := by funext i; ring
  rw [he] at h
  exact ⟨h.1, by linarith [h.2]⟩

private noncomputable def dm_d {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (s x : ℕ) : ℝ := Jgo T V r s (x+1) - Jgo T V r s x

private lemma dm_zero {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (s : ℕ) : Jgo T V r s 0 = 0 := by cases s <;> rfl

private lemma dm_transition {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (s : ℕ) (hs : s < T)
    (hdec : ∀ x, dm_d T V r s (x+1) ≤ dm_d T V r s x) :
    (∀ x, dm_d T V r s x ≤ dm_d T V r (s+1) x) ∧
    (∀ x, dm_d T V r (s+1) (x+1) ≤ dm_d T V r s x) := by
  obtain ⟨hc, hn, hp⟩ := hV (T-s) (by omega) (by omega)
  have he (x : ℕ) : dm_d T V r (s+1) (x+1) = dm_d T V r s (x+1) +
      Zstar (V (T-s)) (fun i => r i - dm_d T V r s (x+1)) -
      Zstar (V (T-s)) (fun i => r i - dm_d T V r s x) := by
    unfold dm_d
    rw [dm_step T V r hV s (x+1) hs, dm_step T V r hV s x hs]
    ring
  have hb (x : ℕ) := dm_bounds (V (T-s)) r hc hn hp _ _ (hdec x)
  constructor
  · intro x
    cases x with
    | zero =>
      unfold dm_d
      rw [dm_step T V r hV s 0 hs, dm_zero, dm_zero]
      have h := dm_nonneg (V (T-s)) (fun i => r i - (Jgo T V r s 1 - Jgo T V r s 0)) hn
      rw [dm_zero] at h
      linarith
    | succ x => rw [he]; linarith [(hb x).1]
  · intro x
    rw [he]
    linarith [(hb x).2]

private lemma dm_properties {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (s : ℕ) (hs : s ≤ T) :
    (∀ x, 0 ≤ dm_d T V r s x ∧ dm_d T V r s (x+1) ≤ dm_d T V r s x) ∧
      (∀ x, dm_d T V r (s-1) x ≤ dm_d T V r s x) := by
  induction s with
  | zero => simp [dm_d, Jgo]
  | succ s ih =>
    have hi := ih (by omega)
    have ht := dm_transition T V r hV s (by omega) (fun x => (hi.1 x).2)
    refine ⟨fun x => ⟨(hi.1 x).1.trans (ht.1 x), (ht.2 x).trans (ht.1 x)⟩, ?_⟩
    simpa using ht.1

private lemma dm_marginal {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (t x : ℕ) (hx : 1 ≤ x) :
    marginalValue T V r t x = dm_d T V r (T+1-t) (x-1) := by
  unfold marginalValue J dm_d
  rw [Nat.sub_add_cancel hx]

private lemma dm_bellman {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (hx : 1 ≤ x) :
    J T V r t x = J T V r (t+1) x + Zstar (V t) (fun i => r i - marginalValue T V r (t+1) x) := by
  have he := dm_step T V r hV (T-t) (x-1) (by omega)
  have h1 : T-(T-t)=t := by omega
  have h2 : T-t+1=T+1-t := by omega
  have h3 : T+1-(t+1)=T-t := by omega
  rw [Nat.sub_add_cancel hx, h1, h2] at he
  simpa only [J, marginalValue, h3] using he

private lemma dm_obj {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T)
    (S : Finset (Fin n)) : bellmanObj T V r t x S =
      worst (V t) (fun i => r i - marginalValue T V r (t+1) x) S + J T V r (t+1) x := by
  obtain ⟨hc, hn, hp⟩ := hV t ht htT
  exact dm_stage (V t) r hc hn hp _ _ S

private lemma dm_opts {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T)
    (S : Finset (Fin n)) : IsOptAssort T V r t x S ↔
      IsSmallestOptimal (V t) (fun i => r i - marginalValue T V r (t+1) x) S := by
  unfold IsOptAssort IsSmallestOptimal Zstar
  simp_rw [dm_obj T V r hV t x ht htT, dm_sup_add]
  simp only [add_left_inj]

private lemma dm_capacity {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (t x : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ T+1) (hx : 1 ≤ x) :
    marginalValue T V r t (x+1) ≤ marginalValue T V r t x := by
  rw [dm_marginal T V r t (x+1) (by omega), dm_marginal T V r t x hx]
  have h := ((dm_properties T V r hV (T+1-t) (by omega)).1 (x-1)).2
  simpa only [Nat.add_sub_cancel, Nat.sub_add_cancel hx] using h

private lemma dm_time {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (t x : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ T) (hx : 1 ≤ x) :
    marginalValue T V r (t+1) x ≤ marginalValue T V r t x := by
  rw [dm_marginal T V r (t+1) x hx, dm_marginal T V r t x hx]
  have h := (dm_properties T V r hV (T+1-t) (by omega)).2 (x-1)
  have he : T+1-t-1=T+1-(t+1) := by omega
  simpa only [he] using h

private lemma dm_inclusion {n : ℕ} (V : Set (ℝ × (Fin n → ℝ))) (r : Fin n → ℝ)
    (hc : IsCompact V) (hn : V.Nonempty) (hp : ∀ p ∈ V, IsPos p)
    (a b : ℝ) (hab : b ≤ a) (S S' : Finset (Fin n))
    (hS : IsSmallestOptimal V (fun i => r i - a) S)
    (hS' : IsSmallestOptimal V (fun i => r i - b) S') : S ⊆ S' := by
  have he : (fun i => r i - a + (a-b)) = (fun i => r i - b) := by funext i; ring
  apply RobustMNL.Static.incremental_revenue_larger (fun i => r i - a) V hc hn hp (a-b)
    (sub_nonneg.mpr hab) S S' hS
  simpa only [he] using hS'


 theorem solution {n : ℕ} (T : ℕ) (V : ℕ → Set (ℝ × (Fin n → ℝ)))
    (r : Fin n → ℝ) (hV : IsUncertaintySeq T V) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (hx : 1 ≤ x)
    (S : Finset (Fin n)) :
    IsOptAssort T V r t x S ↔
      S = Finset.univ.filter (fun i => J T V r t x - J T V r (t + 1) (x - 1) < r i) := by
  classical
  obtain ⟨hc, hn, hp⟩ := hV t ht htT
  rw [dm_opts T V r hV t x ht htT S,
    RobustMNL.Static.revenue_ordered_robust _ (V t) hc hn hp S]
  have he : Finset.univ.filter (fun i => Zstar (V t) (fun i => r i - marginalValue T V r (t+1) x)
      < r i - marginalValue T V r (t+1) x) =
      Finset.univ.filter (fun i => J T V r t x - J T V r (t+1) (x-1) < r i) := by
    apply Finset.filter_congr
    intro i hi
    have hb := dm_bellman T V r hV t x ht htT hx
    unfold marginalValue at *
    constructor <;> intro h <;> linarith
  rw [he]
#print axioms solution

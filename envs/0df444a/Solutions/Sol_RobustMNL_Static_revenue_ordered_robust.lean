-- Prove2me | solution 1 for RobustMNL.Static.revenue_ordered_robust
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:50:05.64841+00:00
-- url     : https://prove2.me/submissions/2993df63-4958-4e63-80f2-4dfd4cb7d299

import Mathlib
import Definitions.Def_RobustMNL_Static_Model

open scoped BigOperators
open RobustMNL.Static

private lemma rm_den {n : ℕ} (p : ℝ × (Fin n → ℝ)) (hp : IsPos p)
    (S : Finset (Fin n)) : 0 < (∑ i ∈ S, p.2 i) + p.1 := by
  exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => (hp.2 i).le) hp.1

private lemma rm_cont {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hp : ∀ p ∈ V, IsPos p) (S : Finset (Fin n)) : ContinuousOn (rev r S) V := by
  unfold rev ChoiceCDLP.MNL.mnlObjective
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro p h
    exact ne_of_gt (rm_den p (hp p h) S)

private lemma rm_min {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hc : IsCompact V) (hn : V.Nonempty) (hp : ∀ p ∈ V, IsPos p) (S : Finset (Fin n)) :
    ∃ p ∈ V, worst V r S = rev r S p ∧ ∀ q ∈ V, rev r S p ≤ rev r S q := by
  exact hc.exists_sInf_image_eq_and_le hn (rm_cont r V hp S)

private lemma rm_low {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hc : IsCompact V) (hn : V.Nonempty) (hp : ∀ p ∈ V, IsPos p) (S : Finset (Fin n))
    (q : ℝ × (Fin n → ℝ)) (hq : q ∈ V) : worst V r S ≤ rev r S q := by
  obtain ⟨p, _, he, hl⟩ := rm_min r V hc hn hp S
  rw [he]
  exact hl q hq

private lemma rm_le_worst {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hc : IsCompact V) (hn : V.Nonempty) (hp : ∀ p ∈ V, IsPos p) (S : Finset (Fin n))
    (z : ℝ) (hz : ∀ q ∈ V, z ≤ rev r S q) : z ≤ worst V r S := by
  obtain ⟨p, hm, he, _⟩ := rm_min r V hc hn hp S
  rw [he]
  exact hz p hm

private lemma rm_max {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (S : Finset (Fin n)) : worst V r S ≤ Zstar V r := by
  exact Finset.le_sup' (worst V r) (Finset.mem_univ S)

private lemma rm_exists {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ))) :
    ∃ S, IsSmallestOptimal V r S := by
  classical
  obtain ⟨S, _, he⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Finset (Fin n)))) Finset.univ_nonempty (worst V r)
  have hs : worst V r S = Zstar V r := he.symm
  let opts := (Finset.univ : Finset (Finset (Fin n))).filter (fun T => worst V r T = Zstar V r)
  have ho : opts.Nonempty := ⟨S, by simp [opts, hs]⟩
  obtain ⟨T, ht, hmin⟩ := opts.exists_min_image Finset.card ho
  refine ⟨T, (Finset.mem_filter.mp ht).2, ?_⟩
  intro U hu
  exact hmin U (by simp [opts, hu])

private lemma rm_mul {n : ℕ} (r : Fin n → ℝ) (p : ℝ × (Fin n → ℝ))
    (hp : IsPos p) (S : Finset (Fin n)) :
    rev r S p * ((∑ i ∈ S, p.2 i) + p.1) = ∑ i ∈ S, r i * p.2 i := by
  exact div_mul_cancel₀ _ (ne_of_gt (rm_den p hp S))

private lemma rm_insert_mul {n : ℕ} (r : Fin n → ℝ) (p : ℝ × (Fin n → ℝ))
    (hp : IsPos p) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    rev r (insert i S) p * (p.2 i + (∑ j ∈ S, p.2 j) + p.1) =
      r i * p.2 i + rev r S p * ((∑ j ∈ S, p.2 j) + p.1) := by
  simpa [Finset.sum_insert hi, rm_mul r p hp S] using rm_mul r p hp (insert i S)

private lemma rm_character {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hc : IsCompact V) (hn : V.Nonempty) (hp : ∀ p ∈ V, IsPos p) (S : Finset (Fin n))
    (hS : IsSmallestOptimal V r S) : S = Finset.univ.filter (fun i => Zstar V r < r i) := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    by_contra hb
    have hz : r i ≤ Zstar V r := le_of_not_gt hb
    have hw : Zstar V r ≤ worst V r (S.erase i) := by
      apply rm_le_worst r V hc hn hp
      intro p hpm
      have hp' := hp p hpm
      have hden := rm_den p hp' (S.erase i)
      have hm := rm_insert_mul r p hp' (S.erase i) i (Finset.notMem_erase i S)
      rw [Finset.insert_erase hi] at hm
      have hv := rm_low r V hc hn hp S p hpm
      rw [hS.1] at hv
      have hpos := hp'.2 i
      nlinarith
    have he := le_antisymm (rm_max r V (S.erase i)) hw
    have hcard := hS.2 (S.erase i) he
    have hlt := Finset.card_erase_lt_of_mem hi
    omega
  · intro hi
    by_contra hb
    obtain ⟨p, hpm, he, _⟩ := rm_min r V hc hn hp (insert i S)
    have hp' := hp p hpm
    have hd := rm_den p hp' S
    have hm := rm_insert_mul r p hp' S i hb
    have hv := rm_low r V hc hn hp S p hpm
    rw [hS.1] at hv
    have hmax := rm_max r V (insert i S)
    rw [he] at hmax
    have hpos := hp'.2 i
    nlinarith

theorem solution {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hV : IsCompact V) (hne : V.Nonempty) (hpos : ∀ p ∈ V, IsPos p) (S : Finset (Fin n)) :
    IsSmallestOptimal V r S ↔ S = Finset.univ.filter (fun i => Zstar V r < r i) := by
  constructor
  · exact rm_character r V hV hne hpos S
  · intro he
    obtain ⟨T, ht⟩ := rm_exists r V
    have ht' := rm_character r V hV hne hpos T ht
    have hst : S = T := he.trans ht'.symm
    simpa [hst] using ht

#print axioms solution

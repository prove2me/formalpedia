-- Prove2me | solution 1 for RobustMNL.Static.incremental_value_bounds
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:01:14.430251+00:00
-- url     : https://prove2.me/submissions/653d12c9-5cdc-469f-b362-2103eeb43ccf

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


 theorem solution {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hV : IsCompact V) (hne : V.Nonempty) (hpos : ∀ p ∈ V, IsPos p) (δ : ℝ) (hδ : 0 ≤ δ) :
    Zstar V r ≤ Zstar V (fun i => r i + δ) ∧ Zstar V (fun i => r i + δ) ≤ δ + Zstar V r := by
  have hpt : ∀ S : Finset (Fin n), ∀ p ∈ V,
      rev r S p ≤ rev (fun i => r i + δ) S p ∧
        rev (fun i => r i + δ) S p ≤ δ + rev r S p := by
    intro S p hpm
    have hp := hpos p hpm
    have hd := rm_den p hp S
    have hs : 0 ≤ ∑ i ∈ S, p.2 i := Finset.sum_nonneg fun i _ => (hp.2 i).le
    have hr := rm_mul r p hp S
    have hr' := rm_mul (fun i => r i + δ) p hp S
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at hr'
    constructor <;> nlinarith [mul_nonneg hδ hs, mul_nonneg hδ hp.1.le]
  have hw : ∀ S, worst V r S ≤ worst V (fun i => r i + δ) S ∧
      worst V (fun i => r i + δ) S ≤ δ + worst V r S := by
    intro S
    constructor
    · apply rm_le_worst (fun i => r i + δ) V hV hne hpos S
      intro p hp
      exact (rm_low r V hV hne hpos S p hp).trans (hpt S p hp).1
    · obtain ⟨p, hp, he, _⟩ := rm_min r V hV hne hpos S
      rw [he]
      exact (rm_low (fun i => r i + δ) V hV hne hpos S p hp).trans (hpt S p hp).2
  constructor
  · exact Finset.sup'_le _ _ (fun S _ => (hw S).1.trans (rm_max _ _ S))
  · exact Finset.sup'_le _ _ (fun S _ => (hw S).2.trans (add_le_add le_rfl (rm_max r V S)))
#print axioms solution

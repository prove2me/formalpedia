-- Prove2me | solution 1 for RobustMNL.Static.adding_product_iff
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:59:16.233457+00:00
-- url     : https://prove2.me/submissions/2046a4e9-fde6-4a89-864d-392c7c0fa842

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


 theorem solution {n : ℕ} (r : Fin n → ℝ) (p : ℝ × (Fin n → ℝ)) (hp : IsPos p)
    (A : Finset (Fin n)) (i : Fin n) (hi : i ∉ A) :
    List.TFAE [r i > rev r A p, rev r (insert i A) p > rev r A p,
      r i > rev r (insert i A) p] := by
  have hd := rm_den p hp A
  have hi0 := hp.2 i
  have hm := rm_insert_mul r p hp A i hi
  tfae_have 1 ↔ 2 := by constructor <;> intro h <;> nlinarith
  tfae_have 1 ↔ 3 := by constructor <;> intro h <;> nlinarith
  tfae_finish
#print axioms solution

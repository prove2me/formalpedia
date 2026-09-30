-- Prove2me | solution 1 for SupplyChainTheory.pcenter_set_cover
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T22:42:32.13722+00:00
-- url     : https://prove2.me/submissions/36602e49-eac9-48f1-a507-26bb8524c9d9

import Mathlib
import Definitions.Def_SupplyChainTheory_location

open SupplyChainTheory

theorem solution {n m : ℕ} (c : Fin n → Fin m → ℝ) (p : ℕ) (hp : 1 ≤ p) (hpm : p ≤ m)
    (r : ℝ) (hr : 0 ≤ r) :
    pCenterValue c p ≤ r ↔ ∃ S : Finset (Fin m), S.card ≤ p ∧ ∀ i, ∃ j ∈ S, c i j ≤ r := by
  classical
  set A := {r' | ∃ S : Finset (Fin m), S.card = p ∧ ∀ i, ∃ j ∈ S, c i j ≤ r'} with hA
  -- Any cover by at most `p` sites extends to one by exactly `p` sites.
  have hpad : ∀ S : Finset (Fin m), S.card ≤ p → ∃ S' : Finset (Fin m), S ⊆ S' ∧ S'.card = p := by
    intro S hS
    obtain ⟨S', h1, -, h2⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ S) hS
      (by rw [Finset.card_univ, Fintype.card_fin]; exact hpm)
    exact ⟨S', h1, h2⟩
  constructor
  · intro hle
    by_contra hno
    push Not at hno
    -- Some `p`-set exists, and every `p`-set leaves some customer farther than `r`.
    obtain ⟨S₀, -, hS₀⟩ := hpad ∅ (Nat.zero_le _)
    have hS₀ne : S₀.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀, hi₀⟩ := hno S₀ hS₀.le
    obtain ⟨j₀, hj₀⟩ := hS₀ne
    set D := (Finset.univ ×ˢ Finset.univ).filter (fun q : Fin n × Fin m => r < c q.1 q.2) with hD
    have hDne : D.Nonempty := ⟨(i₀, j₀), by simp [hD, hi₀ j₀ hj₀]⟩
    set δ := D.inf' hDne (fun q => c q.1 q.2 - r) with hδ
    have hδpos : 0 < δ := by
      rw [hδ, Finset.lt_inf'_iff]
      intro q hq; simp only [hD, Finset.mem_filter] at hq; linarith [hq.2]
    -- Every feasible radius is at least `r + δ`.
    have hAlb : ∀ r' ∈ A, r + δ ≤ r' := by
      rintro r' ⟨S, hS, hcov⟩
      obtain ⟨i, hi⟩ := hno S hS.le
      obtain ⟨j, hj, hjr⟩ := hcov i
      have hq : (i, j) ∈ D := by simp [hD, hi j hj]
      have := Finset.inf'_le (fun q : Fin n × Fin m => c q.1 q.2 - r) hq
      rw [← hδ] at this
      simp only at this
      linarith
    have hAne : A.Nonempty := by
      refine ⟨∑ i, ∑ j, |c i j|, S₀, hS₀, fun i => ⟨j₀, ‹j₀ ∈ S₀›, ?_⟩⟩
      calc c i j₀ ≤ |c i j₀| := le_abs_self _
        _ ≤ ∑ j, |c i j| := Finset.single_le_sum (fun j _ => abs_nonneg (c i j)) (Finset.mem_univ j₀)
        _ ≤ ∑ i, ∑ j, |c i j| := Finset.single_le_sum (f := fun i => ∑ j, |c i j|)
            (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ i)
    have := le_csInf hAne hAlb
    change sInf A ≤ r at hle
    linarith
  · rintro ⟨S, hS, hcov⟩
    obtain ⟨S', hSS', hS'⟩ := hpad S hS
    have hrA : r ∈ A := ⟨S', hS', fun i => by
      obtain ⟨j, hj, hjr⟩ := hcov i; exact ⟨j, hSS' hj, hjr⟩⟩
    by_cases hbdd : BddBelow A
    · exact csInf_le hbdd hrA
    · change sInf A ≤ r
      rw [Real.sInf_of_not_bddBelow hbdd]; exact hr

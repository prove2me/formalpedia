-- Prove2me | solution 1 for SpectralSparsify.Decomp.per_level_cut_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:30:28.101502+00:00
-- url     : https://prove2.me/submissions/c487168d-f054-4b28-aab9-429010933903

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_vol
import Definitions.Def_SpectralSparsify_Decomp_cutEdges
import Definitions.Def_SpectralSparsify_Decomp_cond

set_option autoImplicit false
open SpectralSparsify.Decomp

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) (φ : ℝ) (hφ : 0 ≤ φ)
    {ι : Type*} [Fintype ι] (B S : ι → Finset V)
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j)) (hSB : ∀ j, S j ⊂ B j)
    (hC1 : ∀ j, vol G (S j) ≤ vol G (B j) / 2) (hC2 : ∀ j, condRel G (B j) (S j) ≤ φ) :
    ∑ j, (cutEdges G (S j) (B j \ S j) : ℝ) ≤ φ * (G.edgeFinset.card : ℝ) := by
  have hvol_pos : ∀ T : Finset V, T.Nonempty → 0 < vol G T := by
    intro T hT
    unfold vol
    exact Finset.sum_pos (fun i _ => by exact_mod_cast hdeg i) hT
  have hterm : ∀ j, (cutEdges G (S j) (B j \ S j) : ℝ) ≤ φ * vol G (S j) := by
    intro j
    by_cases h : S j = ∅
    · simp [h, cutEdges, vol]
    · have hne : (S j).Nonempty := Finset.nonempty_iff_ne_empty.mpr h
      have hpos := hvol_pos _ hne
      have hdiff : vol G (B j \ S j) = vol G (B j) - vol G (S j) := by
        unfold vol
        have := Finset.sum_sdiff (f := fun i => (G.degree i : ℝ)) (hSB j).subset
        linarith
      have hmin : min (vol G (S j)) (vol G (B j \ S j)) = vol G (S j) := by
        apply min_eq_left
        rw [hdiff]
        linarith [hC1 j]
      have := hC2 j
      unfold condRel at this
      rw [if_neg h, hmin, div_le_iff₀ hpos] at this
      exact this
  have hsum_vol : ∑ j, vol G (B j) ≤ 2 * (G.edgeFinset.card : ℝ) := by
    have h1 : ∑ j, vol G (B j) = vol G (Finset.univ.biUnion B) := by
      unfold vol
      rw [Finset.sum_biUnion]
      intro a _ b _ hab
      exact hdisj hab
    have h2 : vol G (Finset.univ.biUnion B) ≤ vol G Finset.univ := by
      unfold vol
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => Nat.cast_nonneg _)
    have h3 : vol G Finset.univ = 2 * (G.edgeFinset.card : ℝ) := by
      unfold vol
      have := G.sum_degrees_eq_twice_card_edges
      exact_mod_cast this
    linarith
  calc ∑ j, (cutEdges G (S j) (B j \ S j) : ℝ) ≤ ∑ j, φ * vol G (S j) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = φ * ∑ j, vol G (S j) := by rw [Finset.mul_sum]
    _ ≤ φ * ((G.edgeFinset.card : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hφ
        have : ∑ j, vol G (S j) ≤ ∑ j, vol G (B j) / 2 := Finset.sum_le_sum (fun j _ => hC1 j)
        rw [← Finset.sum_div] at this
        linarith

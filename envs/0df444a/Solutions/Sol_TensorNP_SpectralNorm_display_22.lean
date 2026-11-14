-- Prove2me | solution 1 for TensorNP.SpectralNorm.display_22
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T04:44:02.753727+00:00
-- url     : https://prove2.me/submissions/67df2de3-0d5b-4dc0-9ee1-398121ee5ae0

import Definitions.Def_TensorNP_SpectralNorm_CliqueTensor
import Theorems.Thm_TensorNP_SpectralNorm_theorem_6_7
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators
open TensorNP.SpectralNorm Matrix

private theorem weighted_darts {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (w : Sym2 (Fin v) → ℝ) :
    (∑ d : G.Dart, w d.edge) = 2 * ∑ e ∈ G.edgeFinset, w e := by
  classical
  have hf := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset G.Dart)) (t := G.edgeFinset)
    (g := SimpleGraph.Dart.edge) (fun d _ => G.mem_edgeFinset.mpr d.edge_mem) w
  rw [← hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [Finset.sum_const, nsmul_eq_mul, G.dart_edge_fiber_card e (G.mem_edgeFinset.mp he), Nat.cast_ofNat]

private theorem ordered_dart_sum {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (f : Fin v → Fin v → ℝ) :
    (∑ i, ∑ j, if G.Adj i j then f i j else 0) = ∑ d : G.Dart, f d.fst d.snd := by
  classical
  rw [← Fintype.sum_prod_type (fun p : Fin v × Fin v => if G.Adj p.1 p.2 then f p.1 p.2 else 0)]
  rw [← Finset.sum_filter]
  exact Finset.sum_bij (fun p hp => (⟨p, (Finset.mem_filter.mp hp).2⟩ : G.Dart))
    (fun _ _ => Finset.mem_univ _)
    (fun _ _ _ _ h => congrArg SimpleGraph.Dart.toProd h)
    (fun d _ => ⟨d.toProd, Finset.mem_filter.mpr ⟨Finset.mem_univ _, d.adj⟩, rfl⟩)
    (fun _ _ => rfl)

theorem ordered_edge_sum {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (x : Fin v → ℝ) :
    (∑ i, ∑ j, if G.Adj i j then x i * x j else 0) =
      2 * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun i j => x i * x j, fun _ _ => mul_comm _ _⟩ e := by
  exact (ordered_dart_sum G (fun i j => x i * x j)).trans
    (weighted_darts G (Sym2.lift ⟨fun i j => x i * x j, fun _ _ => mul_comm _ _⟩))

private theorem q_on_simplex {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (l : ℕ) (x : Fin v → ℝ) (hx : x ∈ stdSimplex ℝ (Fin v)) :
    x ⬝ᵥ (Qmat G l *ᵥ x) =
      2 * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun i j => x i * x j, fun _ _ => mul_comm _ _⟩ e + 1 / (l : ℝ) := by
  rw [Qmat, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
    G.dotProduct_mulVec_adjMatrix, ordered_edge_sum]
  simp [dotProduct, mulVec, hx.2]

theorem solution {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (l : ℕ) (hl : 1 ≤ l) :
    IsGreatest ((fun x : Fin v → ℝ => x ⬝ᵥ (Qmat G l *ᵥ x)) '' stdSimplex ℝ (Fin v))
        (1 + ((G.cliqueNum : ℝ) - l) / ((l : ℝ) * G.cliqueNum)) ∧
      Mval G l = 1 + ((G.cliqueNum : ℝ) - l) / ((l : ℝ) * G.cliqueNum) ∧
      (l = G.cliqueNum → Mval G l = 1) ∧
      (l < G.cliqueNum → 1 < Mval G l) ∧
      (G.cliqueNum < l → Mval G l < 1)  := by
  have hωnat : 1 ≤ G.cliqueNum := by
    have hc : G.IsClique (↑({⟨0, hv⟩} : Finset (Fin v)) : Set (Fin v)) := by simp
    simpa using hc.card_le_cliqueNum
  have hpos : (0 : ℝ) < l ∧ (0 : ℝ) < G.cliqueNum :=
    ⟨Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hl),
      Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hωnat)⟩
  have hshift : (1 - 1 / (G.cliqueNum : ℝ)) + 1 / (l : ℝ) =
      1 + ((G.cliqueNum : ℝ) - l) / ((l : ℝ) * G.cliqueNum) := by
    field_simp
    ring
  have hMS := theorem_6_7 hv G
  have hgreat : IsGreatest
      ((fun x : Fin v → ℝ => x ⬝ᵥ (Qmat G l *ᵥ x)) '' stdSimplex ℝ (Fin v))
      (1 + ((G.cliqueNum : ℝ) - l) / ((l : ℝ) * G.cliqueNum)) := by
    constructor
    · rcases hMS.1 with ⟨x, hx, heq⟩
      refine ⟨x, hx, ?_⟩
      simpa only [q_on_simplex G l x hx, heq] using hshift
    · rintro z ⟨x, hx, rfl⟩
      simpa only [q_on_simplex G l x hx, hshift] using
        add_le_add (hMS.2 ⟨x, hx, rfl⟩) (le_refl (1 / (l : ℝ)))
  have hsup : Mval G l = 1 + ((G.cliqueNum : ℝ) - l) / ((l : ℝ) * G.cliqueNum) :=
    hgreat.csSup_eq
  refine ⟨hgreat, hsup, ?_, ?_, ?_⟩
  · exact fun h => by simpa [h] using hsup
  · intro h
    rw [hsup]
    exact lt_add_of_pos_right 1
      (div_pos (sub_pos.mpr (Nat.cast_lt.mpr h)) (mul_pos hpos.1 hpos.2))
  · intro h
    rw [hsup]
    exact add_lt_of_neg_right 1
      (div_neg_of_neg_of_pos (sub_neg.mpr (Nat.cast_lt.mpr h)) (mul_pos hpos.1 hpos.2))

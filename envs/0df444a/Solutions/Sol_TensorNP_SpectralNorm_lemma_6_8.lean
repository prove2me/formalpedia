-- Prove2me | solution 1 for TensorNP.SpectralNorm.lemma_6_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T04:52:27.210002+00:00
-- url     : https://prove2.me/submissions/5b617ab4-cd44-4f38-9c3b-2e0b51f5ba83

import Definitions.Def_TensorNP_SpectralNorm_CliqueTensor
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

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

private theorem edge_quad_mk {v : ℕ} (a b : Fin v) (hab : a ≠ b) (u : Fin v → ℝ) :
    u ⬝ᵥ (edgeMatrix ℝ s(a, b) *ᵥ u) = u a * u b := by
  simp only [edgeMatrix, dotProduct, mulVec, of_apply, Sym2.eq_iff]
  have he : ∀ i j : Fin v,
      (if i = a ∧ j = b ∨ i = b ∧ j = a then (1 / 2 : ℝ) else 0) =
      (if i = a then if j = b then (1 / 2 : ℝ) else 0 else 0) +
        (if i = b then if j = a then (1 / 2 : ℝ) else 0 else 0) := by
    intro i j
    grind
  simp_rw [he]
  simp [add_mul, Finset.sum_add_distrib, mul_add, mul_ite, ite_mul]
  ring

private theorem edge_quad_sq {v : ℕ} (s : Sym2 (Fin v)) (hs : ¬s.IsDiag) (u : Fin v → ℝ) :
    (u ⬝ᵥ (edgeMatrix ℝ s *ᵥ u)) ^ 2 =
      Sym2.lift ⟨fun i j => u i ^ 2 * u j ^ 2, fun _ _ => mul_comm _ _⟩ s := by
  induction s using Sym2.ind with
  | _ a b =>
    rw [edge_quad_mk a b (mt Sym2.mk_isDiag_iff.mpr hs) u, Sym2.lift_mk]
    exact mul_pow _ _ _

private theorem edge_enum_sum {v e : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (ε : Fin e ≃ G.edgeSet) (f : Sym2 (Fin v) → ℝ) :
    (∑ k : Fin e, f (ε k)) = ∑ s ∈ G.edgeFinset, f s := by
  simpa only [Finset.sum_set_coe, SimpleGraph.edgeFinset] using
    ε.sum_comp (fun s : G.edgeSet => f s)

private theorem norm_first {v : ℕ} (l : ℕ) (hl : 1 ≤ l) (u : Fin v → ℝ)
    (hu : l2norm u = 1) :
    (∑ _i : Fin l, (u ⬝ᵥ (((1 / (l : ℝ)) • (1 : Matrix (Fin v) (Fin v) ℝ)) *ᵥ u)) ^ 2) =
      1 / (l : ℝ) := by
  have hs : (∑ i, u i ^ 2) = 1 := Real.sqrt_eq_one.mp hu
  simp_rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
  simp [dotProduct, ← sq, hs]
  field_simp

private theorem q_on_simplex {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (l : ℕ) (x : Fin v → ℝ) (hx : x ∈ stdSimplex ℝ (Fin v)) :
    x ⬝ᵥ (Qmat G l *ᵥ x) =
      2 * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun i j => x i * x j, fun _ _ => mul_comm _ _⟩ e + 1 / (l : ℝ) := by
  rw [Qmat, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
    G.dotProduct_mulVec_adjMatrix, ordered_edge_sum]
  simp [dotProduct, mulVec, hx.2]


private theorem norm_value {v e : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (hl : 1 ≤ l) (u : Fin v → ℝ)
    (hu : l2norm u = 1) :
    (∑ _i : Fin l, (u ⬝ᵥ (((1 / (l : ℝ)) • (1 : Matrix (Fin v) (Fin v) ℝ)) *ᵥ u)) ^ 2 +
      2 * ∑ k : Fin e, (u ⬝ᵥ (edgeMatrix ℝ (ε k : Sym2 (Fin v)) *ᵥ u)) ^ 2) =
      (fun i => u i ^ 2) ⬝ᵥ (Qmat G l *ᵥ (fun i => u i ^ 2)) := by
  have hx : (fun i => u i ^ 2) ∈ stdSimplex ℝ (Fin v) :=
    ⟨fun i => sq_nonneg _, Real.sqrt_eq_one.mp hu⟩
  rw [norm_first l hl u hu, q_on_simplex G l _ hx]
  have heq (k : Fin e) := edge_quad_sq (ε k : Sym2 (Fin v))
    (G.not_isDiag_of_mem_edgeSet (ε k).property) u
  simp_rw [heq]
  rw [edge_enum_sum G ε, add_comm]

theorem solution {v e : ℕ} (_hv : 0 < v) (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (hl : 1 ≤ l) :
    Mval G l = Nval G ε l := by
  unfold Mval Nval
  apply congrArg sSup
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    let u : Fin v → ℝ := fun i => Real.sqrt (x i)
    have hsquare : (fun i => u i ^ 2) = x := funext (fun i => Real.sq_sqrt (hx.1 i))
    have hu : l2norm u = 1 := by
      simpa only [l2norm, hsquare, Real.sqrt_eq_one] using hx.2
    exact ⟨u, hu, (norm_value G ε l hl u hu).trans
      (congrArg (fun z : Fin v → ℝ => z ⬝ᵥ (Qmat G l *ᵥ z)) hsquare)⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(fun i => u i ^ 2), ⟨fun i => sq_nonneg _, Real.sqrt_eq_one.mp hu⟩,
      (norm_value G ε l hl u hu).symm⟩

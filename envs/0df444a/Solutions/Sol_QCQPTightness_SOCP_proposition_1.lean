-- Prove2me | solution 1 for QCQPTightness.SOCP.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:37:32.34621+00:00
-- url     : https://prove2.me/submissions/37dd635b-54a4-45b9-90ef-6db1d474cd00

import Mathlib
import Definitions.Def_QCQPTightness_SOCP_QCQP
import Definitions.Def_QCQPTightness_SOCP_Relaxation

namespace RRAux_QCQPTightness_SOCP_proposition_1

open Matrix QCQPTightness.ConvHull

lemma trace_eq {N : ℕ} (a b x : Fin N → ℝ) (c : ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    (liftQ (diagonal a) b c * liftY x X).trace = a ⬝ᵥ (fun j => X j j) + 2 * (b ⬝ᵥ x) + c := by
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_sum_type, liftQ, liftY, dotProduct,
    diagonal_apply, Matrix.fromBlocks, ite_mul, Finset.sum_add_distrib]
  ring

lemma sq_le_diag {N : ℕ} (x : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ)
    (h : (liftY x X).PosSemidef) (j : Fin N) : x j ^ 2 ≤ X j j := by
  have h2 := (h.submatrix ![Sum.inl 0, Sum.inr j]).dotProduct_mulVec_nonneg ![-x j, 1]
  simp [dotProduct, mulVec, Fin.sum_univ_two, liftY, Matrix.fromBlocks] at h2
  nlinarith [h2]

def Xof {N : ℕ} (x y : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  vecMulVec x x + diagonal (fun j => y j - x j ^ 2)

lemma Xof_diag {N : ℕ} (x y : Fin N → ℝ) : (fun j => Xof x y j j) = y := by
  funext j; simp [Xof, vecMulVec_apply]; ring

lemma Xof_symm {N : ℕ} (x y : Fin N → ℝ) : (Xof x y).IsSymm := by
  ext i j
  simp [Xof, vecMulVec_apply, diagonal, transpose_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij, mul_comm]

lemma Xof_psd {N : ℕ} (x y : Fin N → ℝ) (hy : ∀ j, x j ^ 2 ≤ y j) :
    (liftY x (Xof x y)).PosSemidef := by
  have e : liftY x (Xof x y) =
      vecMulVec (Sum.elim (fun _ : Fin 1 => (1:ℝ)) x) (star (Sum.elim (fun _ : Fin 1 => (1:ℝ)) x))
      + diagonal (Sum.elim (fun _ : Fin 1 => (0:ℝ)) (fun j => y j - x j ^ 2)) := by
    ext (i | i) (j | j) <;> simp [liftY, Xof, vecMulVec_apply, diagonal_apply, Matrix.fromBlocks]
  rw [e]
  refine (posSemidef_vecMulVec_self_star _).add (PosSemidef.diagonal ?_)
  intro i
  rcases i with i | i
  · simp
  · simp; linarith [hy i]

end RRAux_QCQPTightness_SOCP_proposition_1

open RRAux_QCQPTightness_SOCP_proposition_1 in
open QCQPTightness.SOCP in
open Matrix in
theorem solution {N m : ℕ} (P : QCQP N m) (hm : 1 ≤ m)
    (a₀ : Fin N → ℝ) (a : Fin m → Fin N → ℝ) (hdiag : P.IsDiagonalQCQP a₀ a) :
    P.DSOCP a₀ a = P.DSDP ∧ P.OptSOCP a₀ a = P.OptSDP := by
  obtain ⟨h0, hi⟩ := hdiag
  -- forward map
  have fwd : ∀ x y, (x, y) ∈ P.socpFeasible a →
      (x, Xof x y) ∈ P.sdpFeasible ∧
      (QCQPTightness.ConvHull.liftQ P.A₀ P.b₀ P.c₀ *
        QCQPTightness.ConvHull.liftY x (Xof x y)).trace
        = a₀ ⬝ᵥ y + 2 * (P.b₀ ⬝ᵥ x) + P.c₀ := by
    intro x y hxy
    obtain ⟨hc, hy⟩ := hxy
    refine ⟨⟨Xof_symm x y, Xof_psd x y hy, fun i => ?_⟩, ?_⟩
    · simp only [hi i, trace_eq, Xof_diag]
      exact hc i
    · rw [h0, trace_eq, Xof_diag]
  have bwd : ∀ x X, (x, X) ∈ P.sdpFeasible →
      (x, fun j => X j j) ∈ P.socpFeasible a ∧
      (QCQPTightness.ConvHull.liftQ P.A₀ P.b₀ P.c₀ *
        QCQPTightness.ConvHull.liftY x X).trace
        = a₀ ⬝ᵥ (fun j => X j j) + 2 * (P.b₀ ⬝ᵥ x) + P.c₀ := by
    intro x X hxX
    obtain ⟨_, hpsd, hc⟩ := hxX
    refine ⟨⟨fun i => ?_, sq_le_diag x X hpsd⟩, ?_⟩
    · have := hc i
      simp only [hi i, trace_eq] at this
      exact this
    · rw [h0, trace_eq]
  refine ⟨?_, ?_⟩
  · ext ⟨x, t⟩
    constructor
    · rintro ⟨y, hy, hobj⟩
      obtain ⟨hf, he⟩ := fwd x y hy
      exact ⟨Xof x y, hf, he ▸ hobj⟩
    · rintro ⟨X, hX, hobj⟩
      obtain ⟨hf, he⟩ := bwd x X hX
      exact ⟨_, hf, he ▸ hobj⟩
  · apply le_antisymm
    · refine le_iInf₂ fun p hp => ?_
      obtain ⟨hf, he⟩ := bwd p.1 p.2 hp
      refine iInf₂_le_of_le (p.1, fun j => p.2 j j) hf (le_of_eq ?_)
      simp only [he]
    · refine le_iInf₂ fun p hp => ?_
      obtain ⟨hf, he⟩ := fwd p.1 p.2 hp
      refine iInf₂_le_of_le (p.1, Xof p.1 p.2) hf (le_of_eq ?_)
      simp only [he]

#print axioms solution

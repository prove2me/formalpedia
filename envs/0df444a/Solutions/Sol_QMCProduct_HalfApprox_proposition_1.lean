-- Prove2me | solution 1 for QMCProduct.HalfApprox.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T23:23:57.92675+00:00
-- url     : https://prove2.me/submissions/61ad2b40-5f71-4fee-b41e-3ad524cb0d81

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QMCProduct_HalfApprox_Basic

set_option autoImplicit false

namespace Aux_QMCHAp1
open QMCProduct.HalfApprox Matrix
open scoped ComplexOrder

lemma kronAll_herm {n : ℕ} (M : Fin n → Matrix Bool Bool ℂ) (hM : ∀ q, (M q).IsHermitian) :
    (QAlgorithms.kronAll M).IsHermitian := by
  show (QAlgorithms.kronAll M)ᴴ = QAlgorithms.kronAll M
  ext y z
  simp only [QAlgorithms.kronAll, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [Complex.star_def, map_prod]
  apply Finset.prod_congr rfl
  intro q _
  rw [← Complex.star_def]
  exact (hM q).apply (y q) (z q)

lemma pauli1_herm (a : Fin 4) : (pauli1 a).IsHermitian := by
  show (pauli1 a)ᴴ = pauli1 a
  fin_cases a
  · simp [pauli1]
  all_goals
    ext i j
    cases i <;> cases j <;>
      simp [pauli1, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
        Matrix.conjTranspose_apply]

lemma pauliPoly_herm {n : ℕ} (k : ℕ) (P : Op n) (hP : IsPauliPoly k P) : P.IsHermitian := by
  obtain ⟨c, _, rfl⟩ := hP
  show (∑ s, (c s : ℂ) • pauliOp s)ᴴ = ∑ s, (c s : ℂ) • pauliOp s
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hs : (pauliOp s)ᴴ = pauliOp s := (kronAll_herm _ (fun q => pauli1_herm (s q))).eq
  rw [Matrix.conjTranspose_smul, hs]
  congr 1
  rw [Complex.star_def, Complex.conj_ofReal]

lemma density_pseudo {n : ℕ} (k : ℕ) (σ : Op n) (hσ : QAlgorithms.IsDensityMatrix σ) :
    IsPseudoDensity k σ := by
  refine ⟨hσ.1.isHermitian, hσ.2, ?_⟩
  intro P hP
  have hH := pauliPoly_herm k P hP
  have hpsd : (P * σ * Pᴴ).PosSemidef := hσ.1.mul_mul_conjTranspose_same P
  rw [hH.eq] at hpsd
  have htr : (σ * P * P).trace = (P * σ * P).trace := by
    rw [Matrix.trace_mul_comm (σ * P) P, ← Matrix.mul_assoc]
  rw [htr]
  exact (Complex.le_def.1 hpsd.trace_nonneg).1

lemma trace_H {n : ℕ} (E : Finset (Fin n × Fin n)) (w : Fin n × Fin n → ℝ) (S : Fin n × Fin n → Op n)
    (M : Op n) :
    ((∑ e ∈ E, (w e : ℂ) • S e) * M).trace.re = ∑ e ∈ E, w e * (S e * M).trace.re := by
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma trace_sq {n : ℕ} (c0 : ℝ) (c : Fin 3 → Fin 3 → ℝ) (i j : Fin n) (M : Op n) :
    (sqTerm c0 c i j * M).trace.re = c0 * M.trace.re + ∑ a : Fin 3, ∑ b : Fin 3,
      c a b * ((onSite i (pauli1 a.succ) * onSite j (pauli1 b.succ)) * M).trace.re := by
  simp only [sqTerm, add_mul, Finset.sum_mul, smul_mul_assoc, Matrix.one_mul, Matrix.trace_add,
    Matrix.trace_sum, Matrix.trace_smul, Complex.add_re, Complex.re_sum, smul_eq_mul,
    Complex.re_ofReal_mul]

end Aux_QMCHAp1

open QMCProduct.HalfApprox Aux_QMCHAp1 in
open scoped ComplexOrder in
theorem solution {n : ℕ} (k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → Fin n → ℝ) (hw : ∀ e ∈ edges G, 0 ≤ w e.1 e.2)
    (c0 : Fin n → Fin n → ℝ) (c : Fin n → Fin n → Fin 3 → Fin 3 → ℝ)
    (hpsd : ∀ e ∈ edges G, (sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2).PosSemidef)
    (ρt : Op n)
    (hopt : IsOptimalLk k
      (∑ e ∈ edges G, (w e.1 e.2 : ℂ) • sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2) ρt)
    (ρ : Op n) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hedge : ∀ e ∈ edges G,
      α * (c0 e.1 e.2 + ∑ a : Fin 3, ∑ b : Fin 3, c e.1 e.2 a b *
          val ρt (onSite e.1 (pauli1 a.succ) * onSite e.2 (pauli1 b.succ))) ≤
        (sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2 * ρ).trace.re) :
    ∀ σ : Op n, QAlgorithms.IsDensityMatrix σ →
      α * ((∑ e ∈ edges G, (w e.1 e.2 : ℂ) • sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2) *
          σ).trace.re ≤
        ((∑ e ∈ edges G, (w e.1 e.2 : ℂ) • sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2) *
          ρ).trace.re := by
  intro σ hσ
  have h1 := hopt.2 σ (density_pseudo k σ hσ)
  have htr1 : ρt.trace.re = 1 := by rw [hopt.1.2.1]; simp
  have hρt : ((∑ e ∈ edges G, (w e.1 e.2 : ℂ) • sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2) *
      ρt).trace.re = ∑ e ∈ edges G, w e.1 e.2 * (c0 e.1 e.2 + ∑ a : Fin 3, ∑ b : Fin 3,
        c e.1 e.2 a b * val ρt (onSite e.1 (pauli1 a.succ) * onSite e.2 (pauli1 b.succ))) := by
    rw [trace_H (edges G) (fun e => w e.1 e.2) (fun e => sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2)]
    apply Finset.sum_congr rfl
    intro e _
    rw [trace_sq, htr1, mul_one]
    congr 2
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [val, Matrix.trace_mul_comm]
  have hρ' : ((∑ e ∈ edges G, (w e.1 e.2 : ℂ) • sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2) *
      ρ).trace.re = ∑ e ∈ edges G, w e.1 e.2 *
        (sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2 * ρ).trace.re :=
    trace_H (edges G) (fun e => w e.1 e.2) (fun e => sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2) ρ
  have h2 : α * ((∑ e ∈ edges G, (w e.1 e.2 : ℂ) • sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2) *
      ρt).trace.re ≤ ((∑ e ∈ edges G, (w e.1 e.2 : ℂ) • sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2) *
      ρ).trace.re := by
    rw [hρt, hρ', Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    calc α * (w e.1 e.2 * _) = w e.1 e.2 * (α * _) := by ring
      _ ≤ w e.1 e.2 * (sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2 * ρ).trace.re :=
          mul_le_mul_of_nonneg_left (hedge e he) (hw e he)
  calc α * _ ≤ α * ((∑ e ∈ edges G, (w e.1 e.2 : ℂ) • sqTerm (c0 e.1 e.2) (c e.1 e.2) e.1 e.2) *
      ρt).trace.re := mul_le_mul_of_nonneg_left h1 hα0.le
    _ ≤ _ := h2

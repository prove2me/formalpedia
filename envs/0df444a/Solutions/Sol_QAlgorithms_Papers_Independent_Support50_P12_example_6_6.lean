-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.example_6_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:36:25.551915+00:00
-- url     : https://prove2.me/submissions/cf6779ad-aea8-40ef-8b19-63f69dadc7bd

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12
noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]


open scoped MatrixOrder

lemma S169G_cfc_diag {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  set A := Matrix.diagonal (fun i => (d i : ℂ)) with hA
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, hA, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  set S : Finset ℝ := Finset.univ.image d
  let p : Polynomial ℝ := Lagrange.interpolate S id f
  have hp : ∀ i, p.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f) (i := d i)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    exact this
  have hspec : ∀ x ∈ spectrum ℝ A, ∃ i, d i = x := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, hA, spectrum_diagonal,
      Set.mem_range] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by rw [Complex.coe_algebraMap] at hi; exact_mod_cast hi⟩
  have h1 : cfc f A = cfc p.eval A := by
    apply cfc_congr
    intro x hx
    obtain ⟨i, rfl⟩ := hspec x hx
    exact (hp i).symm
  rw [h1, cfc_polynomial p A]
  rw [hA, show Matrix.diagonal (fun i => (d i : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) from rfl, Polynomial.aeval_algHom_apply]
  rw [show Matrix.diagonal (fun i => (f (d i) : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (f (d i) : ℂ)) from rfl]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply₂]
  rw [show ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval, hp]
  rfl

lemma S169G_sp (d : Fin 3 → ℝ) (t : ℝ) :
    supportPower (Matrix.diagonal (fun i => (d i : ℂ))) t =
      Matrix.diagonal (fun i => ((if d i = 0 then 0 else Real.rpow (d i) t : ℝ) : ℂ)) := by
  unfold supportPower; exact S169G_cfc_diag d _

def S169G_r : Fin 3 → ℝ := ![2/3, 1/3, 0]
def S169G_s : Fin 3 → ℝ := ![1/6, 1/3, 1/2]
def S169G_mr : Fin 3 → ℝ := ![1, 0, 0]
def S169G_ms : Fin 3 → ℝ := ![1/2, 0, 1/2]

lemma S169G_rho : exampleRho = Matrix.diagonal (fun i => (S169G_r i : ℂ)) := by
  unfold exampleRho; congr 1; funext i; fin_cases i <;> simp [S169G_r]
lemma S169G_sigma : exampleSigma = Matrix.diagonal (fun i => (S169G_s i : ℂ)) := by
  unfold exampleSigma; congr 1; funext i; fin_cases i <;> simp [S169G_s]
lemma S169G_mrho : merge exampleRho = Matrix.diagonal (fun i => (S169G_mr i : ℂ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [merge, exampleRho, S169G_mr] <;> norm_num
lemma S169G_msigma : merge exampleSigma = Matrix.diagonal (fun i => (S169G_ms i : ℂ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [merge, exampleSigma, S169G_ms] <;> norm_num

lemma S169G_tr1 (a : ℝ) : tr (supportPower exampleRho a * supportPower exampleSigma (1 - a)) =
    (2 + Real.rpow 4 a) / 6 := by
  rw [S169G_rho, S169G_sigma, S169G_sp, S169G_sp, Matrix.diagonal_mul_diagonal]
  simp only [tr, Matrix.trace_diagonal, Fin.sum_univ_three, S169G_r, S169G_s]
  simp
  have h1 : (2/3 : ℝ) ^ a * (6⁻¹ : ℝ) ^ (1 - a) = 4 ^ a / 6 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, ← mul_div_assoc, mul_comm, mul_div_assoc,
      ← Real.div_rpow (by norm_num) (by norm_num)]
    norm_num; ring
  have h2 : (3⁻¹ : ℝ) ^ a * (3⁻¹ : ℝ) ^ (1 - a) = 3⁻¹ := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  rw [h1, h2]; ring

lemma S169G_tr2 (a : ℝ) : tr (supportPower (merge exampleRho) a * supportPower (merge exampleSigma) (1 - a)) =
    Real.rpow 2 (a - 1) := by
  rw [S169G_mrho, S169G_msigma, S169G_sp, S169G_sp, Matrix.diagonal_mul_diagonal]
  simp only [tr, Matrix.trace_diagonal, Fin.sum_univ_three, S169G_mr, S169G_ms]
  simp
  rw [Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
  ring_nf

lemma S169G_chernoff_merge : chernoff (merge exampleRho) (merge exampleSigma) = (Real.log 2 : EReal) := by
  unfold chernoff logOverlap
  apply IsGreatest.csSup_eq
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∀ a : ℝ, -logNonnegativeExtended (Real.rpow 2 (a - 1)) = (((1 - a) * Real.log 2 : ℝ) : EReal) := by
    intro a
    unfold logNonnegativeExtended
    rw [if_pos (show (0:ℝ) < Real.rpow 2 (a - 1) from Real.rpow_pos_of_pos (by norm_num) _)]
    rw [show Real.rpow 2 (a - 1) = (2:ℝ) ^ (a - 1) from rfl, Real.log_rpow (by norm_num), ← EReal.coe_neg]
    congr 1; ring
  refine ⟨⟨0, le_refl _, by norm_num, ?_⟩, ?_⟩
  · rw [S169G_tr2, key]; norm_num
  · rintro v ⟨a, ha0, ha1, rfl⟩
    rw [S169G_tr2, key]
    exact EReal.coe_le_coe_iff.mpr (by nlinarith)

lemma S169G_chernoff : chernoff exampleRho exampleSigma = (Real.log 2 : EReal) := by
  unfold chernoff logOverlap
  apply IsGreatest.csSup_eq
  have key : ∀ a : ℝ, -logNonnegativeExtended ((2 + Real.rpow 4 a) / 6) =
      ((-Real.log ((2 + Real.rpow 4 a) / 6) : ℝ) : EReal) := by
    intro a
    unfold logNonnegativeExtended
    rw [if_pos (by have := Real.rpow_pos_of_pos (show (0:ℝ) < 4 by norm_num) a; positivity), EReal.coe_neg]
  refine ⟨⟨0, le_refl _, by norm_num, ?_⟩, ?_⟩
  · rw [S169G_tr1, key]
    congr 1
    rw [show Real.rpow 4 0 = 1 from Real.rpow_zero 4]
    rw [show (2 + 1 : ℝ) / 6 = 2⁻¹ by norm_num, Real.log_inv]; ring
  · rintro v ⟨a, ha0, ha1, rfl⟩
    rw [S169G_tr1, key]
    apply EReal.coe_le_coe_iff.mpr
    have h4 : (1:ℝ) ≤ Real.rpow 4 a := Real.one_le_rpow (by norm_num) ha0
    have : Real.log (2⁻¹) ≤ Real.log ((2 + Real.rpow 4 a) / 6) :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_inv] at this
    linarith

lemma S169G_petzRenyi_merge : petzRenyi 0 (merge exampleRho) (merge exampleSigma) = (Real.log 2 : EReal) := by
  unfold petzRenyi
  rw [if_pos (Or.inr (by norm_num))]
  have := S169G_tr2 0
  rw [show (1:ℝ) - 0 = 1 - 0 from rfl, this]
  unfold logNonnegativeExtended
  rw [if_pos (show (0:ℝ) < Real.rpow 2 (0 - 1) from Real.rpow_pos_of_pos (by norm_num) _),
    ← EReal.coe_mul]
  congr 1
  rw [show Real.rpow 2 (0 - 1) = (2:ℝ) ^ ((0:ℝ) - 1) from rfl, Real.log_rpow (by norm_num)]
  norm_num

lemma S169G_petzRenyi : petzRenyi 0 exampleRho exampleSigma = (Real.log 2 : EReal) := by
  unfold petzRenyi
  rw [if_pos (Or.inr (by norm_num))]
  rw [S169G_tr1 0]
  unfold logNonnegativeExtended
  rw [show Real.rpow 4 0 = 1 from Real.rpow_zero 4, if_pos (by norm_num), ← EReal.coe_mul]
  congr 1
  rw [show (2 + 1 : ℝ) / 6 = 2⁻¹ by norm_num, Real.log_inv]; norm_num

lemma S169G_adj (Y : Mat (Fin 3)) :
    channelAdjoint merge Y = Matrix.diagonal ![Y 0 0, Y 0 0, Y 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [channelAdjoint, merge, Fin.sum_univ_three, Matrix.single_apply, Matrix.diagonal_apply]

lemma S169G_petz : petz exampleSigma merge (merge exampleRho) =
    Matrix.diagonal ![(1 / 3 : ℂ), 2 / 3, 0] := by
  unfold petz
  simp only []
  rw [S169G_msigma, S169G_mrho, S169G_sigma, S169G_cfc_diag, S169G_cfc_diag, S169G_adj]
  ext i j
  have h6 : Real.sqrt (1/6) * Real.sqrt (1/6) = 1/6 := Real.mul_self_sqrt (by norm_num)
  have h3 : Real.sqrt (1/3) * Real.sqrt (1/3) = 1/3 := Real.mul_self_sqrt (by norm_num)
  have h2 : (Real.sqrt (1/2))⁻¹ * (Real.sqrt (1/2))⁻¹ = 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, S169G_s, S169G_ms, S169G_mr]
  · rw [show (Real.sqrt 6 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) * (Real.sqrt 6 : ℂ)⁻¹ =
        (((Real.sqrt 6)⁻¹ * (Real.sqrt 6)⁻¹ * (Real.sqrt 2 * Real.sqrt 2) : ℝ) : ℂ) by push_cast; ring]
    rw [Real.mul_self_sqrt (by norm_num), ← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  · rw [show (Real.sqrt 3 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) * (Real.sqrt 3 : ℂ)⁻¹ =
        (((Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ * (Real.sqrt 2 * Real.sqrt 2) : ℝ) : ℂ) by push_cast; ring]
    rw [Real.mul_self_sqrt (by norm_num), ← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num

def S169G_V (n : ℕ) (s t : Fin 3) : Matrix (Fin n × Fin 3) (Fin n × Fin 3) ℂ :=
  fun w u => if w.1 = u.1 ∧ w.2 = s ∧ u.2 = t then 1 else 0

lemma S169G_V_apply (n : ℕ) (s t : Fin 3) (X : Mat (Fin n × Fin 3)) (u v : Fin n × Fin 3) :
    ((S169G_V n s t)ᴴ * X * S169G_V n s t) u v =
      if u.2 = t ∧ v.2 = t then X (u.1, s) (v.1, s) else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, S169G_V, Fintype.sum_prod_type]
  by_cases hu : u.2 = t <;> by_cases hv : v.2 = t <;>
    simp [hu, hv, ite_and, apply_ite (starRingEnd ℂ), Finset.sum_ite_eq', Finset.sum_ite_eq]

lemma S169G_CP : AlgebraCompletelyPositive (diagonalAlgebra (Fin 3)) merge := by
  intro n X _ hX
  have e : amp merge n X = (S169G_V n 0 0)ᴴ * X * S169G_V n 0 0 +
      (S169G_V n 1 0)ᴴ * X * S169G_V n 1 0 + (S169G_V n 2 2)ᴴ * X * S169G_V n 2 2 := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [Matrix.add_apply, S169G_V_apply, amp, merge, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;> simp
  rw [e]
  exact ((hX.conjTranspose_mul_mul_same _).add (hX.conjTranspose_mul_mul_same _)).add
    (hX.conjTranspose_mul_mul_same _)

lemma S169G_TP : AlgebraTracePreserving (diagonalAlgebra (Fin 3)) merge := by
  intro X _
  simp [merge, Matrix.trace, Fin.sum_univ_three]

lemma S169G_dens (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i) (h1 : d 0 + d 1 + d 2 = 1) :
    AlgebraDensity (diagonalAlgebra (Fin 3)) (Matrix.diagonal (fun i => (d i : ℂ))) := by
  refine ⟨fun i j h => Matrix.diagonal_apply_ne _ h, ?_, ?_⟩
  · rw [Matrix.posSemidef_diagonal_iff]
    intro i; exact_mod_cast hd i
  · simp only [tr, Matrix.trace_diagonal, Fin.sum_univ_three]
    simp only [Complex.add_re, Complex.ofReal_re]; exact h1

lemma S169G_notrev : ¬ Reversible (diagonalAlgebra (Fin 3)) (diagonalAlgebra (Fin 3)) merge
    exampleRho exampleSigma := by
  rintro ⟨Ψ, ⟨⟨_, hsch⟩, _⟩, h1, h2⟩
  have hE : AlgebraDensity (diagonalAlgebra (Fin 3)) (merge exampleRho) := by
    rw [S169G_mrho]; exact S169G_dens _ (fun i => by fin_cases i <;> simp [S169G_mr])
      (by simp [S169G_mr])
  have hP := hsch.2.1 _ hE.1 hE.2.1
  have hd := hP.diag_nonneg (i := 2)
  have e : Matrix.single (2 : Fin 3) (2 : Fin 3) (1 : ℂ) = (2 : ℂ) • merge exampleSigma - merge exampleRho := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [merge, exampleSigma, exampleRho, Matrix.single_apply]
      <;> norm_num
  have hΨ : Ψ (Matrix.single (2 : Fin 3) (2 : Fin 3) (1 : ℂ)) = (2 : ℂ) • exampleSigma - exampleRho := by
    rw [e, map_sub, map_smul, h1, h2]
  have hval : channelAdjoint Ψ (merge exampleRho) 2 2 = -1/3 := by
    simp only [channelAdjoint, hΨ, S169G_mrho]
    simp [Fin.sum_univ_three, Matrix.diagonal_apply, S169G_mr, exampleSigma, exampleRho]
    simp only [map_ofNat]; norm_num
  rw [hval] at hd
  have := (Complex.nonneg_iff.mp hd).1
  norm_num at this

theorem S169G_main :
    AlgebraCompletelyPositive (diagonalAlgebra (Fin 3)) merge ∧ AlgebraTracePreserving (diagonalAlgebra (Fin 3)) merge ∧
    AlgebraDensity (diagonalAlgebra (Fin 3)) exampleRho ∧ AlgebraDensity (diagonalAlgebra (Fin 3)) exampleSigma ∧
    merge exampleRho = Matrix.diagonal ![(1 : ℂ), 0, 0] ∧
    merge exampleSigma = Matrix.diagonal ![(1 / 2 : ℂ), 0, 1 / 2] ∧
    (∀ a : ℝ, tr (supportPower exampleRho a * supportPower exampleSigma (1 - a)) =
      (2 + Real.rpow 4 a) / 6) ∧
    (∀ a : ℝ, tr (supportPower (merge exampleRho) a * supportPower (merge exampleSigma) (1 - a)) =
      Real.rpow 2 (a - 1)) ∧
    chernoff (merge exampleRho) (merge exampleSigma) = (Real.log 2 : EReal) ∧
    chernoff exampleRho exampleSigma = (Real.log 2 : EReal) ∧
    petzRenyi 0 (merge exampleRho) (merge exampleSigma) = (Real.log 2 : EReal) ∧
    petzRenyi 0 exampleRho exampleSigma = (Real.log 2 : EReal) ∧
    petz exampleSigma merge (merge exampleRho) = Matrix.diagonal ![(1 / 3 : ℂ), 2 / 3, 0] ∧
    petz exampleSigma merge (merge exampleRho) ≠ exampleRho ∧
    ¬ Reversible (diagonalAlgebra (Fin 3)) (diagonalAlgebra (Fin 3)) merge exampleRho exampleSigma := by
  refine ⟨S169G_CP, S169G_TP, ?_, ?_, ?_, ?_, S169G_tr1, S169G_tr2, S169G_chernoff_merge,
    S169G_chernoff, S169G_petzRenyi_merge, S169G_petzRenyi, S169G_petz, ?_, S169G_notrev⟩
  · rw [S169G_rho]; exact S169G_dens _ (fun i => by fin_cases i <;> simp [S169G_r] <;> norm_num)
      (by simp [S169G_r]; norm_num)
  · rw [S169G_sigma]; exact S169G_dens _ (fun i => by fin_cases i <;> simp [S169G_s] <;> norm_num)
      (by simp [S169G_s]; norm_num)
  · rw [S169G_mrho]; congr 1; funext i; fin_cases i <;> simp [S169G_mr]
  · rw [S169G_msigma]; congr 1; funext i; fin_cases i <;> simp [S169G_ms]
  · rw [S169G_petz]; intro h
    have := congrFun (congrFun h 0) 0
    simp [exampleRho] at this
    norm_num at this

end QAlgorithms.Papers.Independent.Support50.P12

end

open QAlgorithms.Papers.Independent.Support50.P12
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr)
open QAlgorithms.Papers.Independent.Dependency50.P21 (petz)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

theorem solution :
    AlgebraCompletelyPositive (diagonalAlgebra (Fin 3)) merge ∧ AlgebraTracePreserving (diagonalAlgebra (Fin 3)) merge ∧
    AlgebraDensity (diagonalAlgebra (Fin 3)) exampleRho ∧ AlgebraDensity (diagonalAlgebra (Fin 3)) exampleSigma ∧
    merge exampleRho = Matrix.diagonal ![(1 : ℂ), 0, 0] ∧
    merge exampleSigma = Matrix.diagonal ![(1 / 2 : ℂ), 0, 1 / 2] ∧
    (∀ a : ℝ, tr (supportPower exampleRho a * supportPower exampleSigma (1 - a)) =
      (2 + Real.rpow 4 a) / 6) ∧
    (∀ a : ℝ, tr (supportPower (merge exampleRho) a * supportPower (merge exampleSigma) (1 - a)) =
      Real.rpow 2 (a - 1)) ∧
    chernoff (merge exampleRho) (merge exampleSigma) = (Real.log 2 : EReal) ∧
    chernoff exampleRho exampleSigma = (Real.log 2 : EReal) ∧
    petzRenyi 0 (merge exampleRho) (merge exampleSigma) = (Real.log 2 : EReal) ∧
    petzRenyi 0 exampleRho exampleSigma = (Real.log 2 : EReal) ∧
    petz exampleSigma merge (merge exampleRho) = Matrix.diagonal ![(1 / 3 : ℂ), 2 / 3, 0] ∧
    petz exampleSigma merge (merge exampleRho) ≠ exampleRho ∧
    ¬ Reversible (diagonalAlgebra (Fin 3)) (diagonalAlgebra (Fin 3)) merge exampleRho exampleSigma :=
  S169G_main

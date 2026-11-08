-- Prove2me | solution 1 for WildeQIT.Activation.property_13_6_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:30:32.77675+00:00
-- url     : https://prove2.me/submissions/3a8508ac-657d-471a-b3ce-71f59fb0d97b

import Definitions.Def_WildeQIT_Activation_privateInfoChannel

open scoped ComplexOrder Kronecker
namespace Aux_WQ_1361
open WildeQIT WildeQIT.Degradable WildeQIT.Activation Matrix

noncomputable def reStar {b c : Type} [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    (e : b ≃ c) : Matrix b b ℂ →⋆ₐ[ℂ] Matrix c c ℂ :=
  { (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom with
    map_star' := fun M => by
      ext i j
      simp [Matrix.reindexAlgEquiv_apply, Matrix.star_apply] }

theorem reStar_apply {b c : Type} [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    (e : b ≃ c) (M : Matrix b b ℂ) : reStar e M = Matrix.reindex e e M := rfl

theorem hcont : Continuous (fun x : ℝ => x * Real.logb 2 x) := by
  have := Real.continuous_mul_log.div_const (Real.log 2)
  convert this using 1
  funext x
  simp [Real.logb, mul_div_assoc]

theorem trace_reindex' {b c : Type} [Fintype b] [Fintype c] (e : b ≃ c) (M : Matrix b b ℂ) :
    (Matrix.reindex e e M).trace = M.trace := by
  unfold Matrix.trace
  simp only [Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

theorem entropy_reindex {b c : Type} [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    (e : b ≃ c) (σ : Matrix b b ℂ) :
    QAlgorithms.vnEntropy (Matrix.reindex e e σ) = QAlgorithms.vnEntropy σ := by
  unfold QAlgorithms.vnEntropy
  by_cases h : IsSelfAdjoint σ
  · have h' : IsSelfAdjoint (reStar e σ) := by
      unfold IsSelfAdjoint
      rw [← map_star, h.star_eq]
    rw [← reStar_apply, ← StarAlgHom.map_cfc (reStar e) (fun x : ℝ => x * Real.logb 2 x) σ
      hcont.continuousOn (by
        show Continuous fun M : Matrix b b ℂ => Matrix.reindex e e M
        exact continuous_id.matrix_reindex e e) h h', reStar_apply, trace_reindex']
  · have h' : ¬ IsSelfAdjoint (Matrix.reindex e e σ) := by
      intro hh
      apply h
      unfold IsSelfAdjoint at hh ⊢
      have : Matrix.reindex e e (star σ) = Matrix.reindex e e σ := by
        rw [← hh]; ext i j; simp [Matrix.star_apply]
      exact (Matrix.reindex e e).injective this
    rw [cfc_apply_of_not_predicate _ h, cfc_apply_of_not_predicate _ h']
    simp

def eqv (c : Type) : c ≃ Fin 1 × c where
  toFun k := (0, k)
  invFun p := p.2
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨i, k⟩
    rw [Fin.fin_one_eq_zero i]

theorem M_eq {c : Type} [Fintype c] [DecidableEq c] (σ : Matrix c c ℂ) :
    cqState (fun _ : Fin 1 => (1 : ℝ)) (fun _ => σ) = Matrix.reindex (eqv c) (eqv c) σ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
  simp [cqState, eqv, Matrix.kroneckerMap_apply]

theorem L_eq {c : Type} [Fintype c] [DecidableEq c] (σ : Matrix c c ℂ) :
    partialTraceLeft (cqState (fun _ : Fin 1 => (1 : ℝ)) (fun _ => σ)) = σ := by
  ext k l
  simp [partialTraceLeft, cqState, Matrix.kroneckerMap_apply]

theorem R_eq {c : Type} [Fintype c] [DecidableEq c] (σ : Matrix c c ℂ) :
    partialTraceRight (cqState (fun _ : Fin 1 => (1 : ℝ)) (fun _ => σ)) =
      Matrix.of fun _ _ => σ.trace := by
  ext i j
  rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
  simp [partialTraceRight, cqState, Matrix.kroneckerMap_apply, Matrix.trace]

theorem qMI_single {c : Type} [Fintype c] [DecidableEq c] (σ : Matrix c c ℂ) :
    WildeQIT.AFW.qMutualInfo (cqState (fun _ : Fin 1 => (1 : ℝ)) (fun _ => σ)) =
      QAlgorithms.vnEntropy (Matrix.of fun (_ _ : Fin 1) => σ.trace) := by
  unfold WildeQIT.AFW.qMutualInfo
  rw [R_eq, L_eq, M_eq, entropy_reindex]
  ring

theorem tr_apply {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b)
    (ρ : Matrix a a ℂ) : (N.apply ρ).trace = ρ.trace := by
  unfold QChannel.apply
  calc (∑ i, N.K i * ρ * (N.K i)ᴴ).trace = ∑ i, ((N.K i)ᴴ * N.K i * ρ).trace := by
        rw [Matrix.trace_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    _ = ((∑ i, (N.K i)ᴴ * N.K i) * ρ).trace := by rw [Finset.sum_mul, Matrix.trace_sum]
    _ = ρ.trace := by rw [N.complete, Matrix.one_mul]

theorem tr_compl {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b)
    (ρ : Matrix a a ℂ) : (complementaryApply N ρ).trace = ρ.trace := by
  unfold complementaryApply
  have hpt : ∀ X : Matrix (b × N.ι) (b × N.ι) ℂ, (partialTraceLeft X).trace = X.trace := by
    intro X
    simp only [Matrix.trace, partialTraceLeft, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  have hV : (isometricExtension N)ᴴ * isometricExtension N = 1 := by
    rw [← N.complete]
    ext x x'
    simp only [isometricExtension, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.sum_apply]
    rw [Finset.sum_comm]
  rw [hpt, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]

end Aux_WQ_1361

open WildeQIT WildeQIT.Degradable WildeQIT.Activation Aux_WQ_1361 in
theorem solution {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a] (N : QChannel a b) :
    0 ≤ privateInfoChannel N := by
  classical
  obtain ⟨i0⟩ := ‹Nonempty a›
  let ρ0 : Matrix a a ℂ := Matrix.diagonal (fun j => if j = i0 then 1 else 0)
  have hρ0 : IsDensityOperator ρ0 := by
    constructor
    · rw [Matrix.posSemidef_diagonal_iff]
      intro j
      split_ifs <;> simp
    · simp [ρ0, Matrix.trace_diagonal]
  let E₁ : CQInput a := ⟨1, ⟨fun _ => 1, fun _ => zero_le_one, by simp⟩, fun _ => ρ0, fun _ => hρ0⟩
  have h0 : privateInfoEnsemble N E₁ = 0 := by
    unfold privateInfoEnsemble
    show WildeQIT.AFW.qMutualInfo (cqState (fun _ : Fin 1 => (1 : ℝ)) (fun _ => N.apply ρ0)) -
      WildeQIT.AFW.qMutualInfo (cqState (fun _ : Fin 1 => (1 : ℝ))
        (fun _ => complementaryApply N ρ0)) = 0
    rw [qMI_single, qMI_single, tr_apply, tr_compl, sub_self]
  unfold privateInfoChannel
  by_cases hb : BddAbove (Set.range (fun E => privateInfoEnsemble N E))
  · rw [← h0]; exact le_ciSup hb E₁
  · rw [Real.iSup_of_not_bddAbove hb]

-- Prove2me | solution 1 for WildeQIT.Degradable.property_13_5_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:25:33.611908+00:00
-- url     : https://prove2.me/submissions/86ea0257-35c0-41a9-9e73-8d6446ea6ef5

import Definitions.Def_WildeQIT_Degradable_coherentInfoChannel

namespace Aux_WQ_1351
open WildeQIT WildeQIT.Degradable Matrix
open scoped ComplexOrder

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


theorem Y_eq {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : QChannel a b) (X : Matrix (Fin 1 × a) (Fin 1 × a) ℂ) :
    QAlgorithms.idTensorSuperop (R := Fin 1) N.apply X =
      Matrix.reindex (eqv b) (eqv b) (N.apply (Matrix.of fun i i' => X (0, i) (0, i'))) := by
  ext ⟨p, k⟩ ⟨q, l⟩
  rw [Fin.fin_one_eq_zero p, Fin.fin_one_eq_zero q]
  rfl

theorem ptl_eq {b : Type} [Fintype b] [DecidableEq b] (σ : Matrix b b ℂ) :
    partialTraceLeft (Matrix.reindex (eqv b) (eqv b) σ) = σ := by
  ext k l
  simp [partialTraceLeft, eqv]

end Aux_WQ_1351

open WildeQIT WildeQIT.Degradable Aux_WQ_1351 in
theorem solution {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a]
    (N : QChannel a b) :
    0 ≤ coherentInfoChannel N := by
  obtain ⟨i0⟩ := ‹Nonempty a›
  let φ : PureInput a := ⟨1, EuclideanSpace.single (0, i0) 1, by simp⟩
  have h0 : coherentInfoState (QAlgorithms.idTensorSuperop (R := Fin φ.m) N.apply
      (QAlgorithms.pureDensity φ.ψ)) = 0 := by
    show coherentInfoState (QAlgorithms.idTensorSuperop (R := Fin 1) N.apply
      (QAlgorithms.pureDensity φ.ψ)) = 0
    unfold coherentInfoState
    rw [Y_eq, ptl_eq, entropy_reindex, sub_self]
  unfold coherentInfoChannel
  by_cases hb : BddAbove (Set.range (fun φ : PureInput a => coherentInfoState
      (QAlgorithms.idTensorSuperop (R := Fin φ.m) N.apply (QAlgorithms.pureDensity φ.ψ))))
  · rw [← h0]; exact le_ciSup hb φ
  · rw [Real.iSup_of_not_bddAbove hb]

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P50.j1_identity_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:04:02.51037+00:00
-- url     : https://prove2.me/submissions/99282d7f-23d2-43b8-9c40-d29179026c17

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace X6P50J1

open QAlgorithms.Papers.Independent.Dependency50.P50

lemma av_apply (p : Fin 2 × Fin 2) :
    antisymmetricVector p =
      (if p = (0, 1) then 1 else 0) - (if p = (1, 0) then 1 else 0) := by
  obtain ⟨a, b⟩ := p
  fin_cases a <;> fin_cases b <;>
    simp [antisymmetricVector, QAlgorithms.tensorVec, QAlgorithms.ket]

lemma act_av : QAlgorithms.act (j1 (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ))) antisymmetricVector = (-1 : ℂ) • antisymmetricVector := by
  ext p
  obtain ⟨a, b⟩ := p
  simp only [QAlgorithms.act, j1, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_two, LinearMap.id_apply, PiLp.smul_apply, smul_eq_mul]
  fin_cases a <;> fin_cases b <;> simp [av_apply, Matrix.single_apply]

lemma inner_av : inner ℂ antisymmetricVector
    (QAlgorithms.act (j1 (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ]
      Matrix (Fin 2) (Fin 2) ℂ))) antisymmetricVector) = (-2 : ℂ) := by
  rw [act_av]
  simp only [PiLp.inner_apply, PiLp.smul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    av_apply, smul_eq_mul]
  simp
  norm_num

lemma sn_av : schmidtNumber antisymmetricVector = 2 := by
  unfold schmidtNumber
  have hM : (Matrix.of fun (i : Fin 2) (j : Fin 2) => antisymmetricVector (i, j)) =
      !![0, 1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [av_apply]
  rw [hM]
  have hu : IsUnit (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]
    norm_num
  rw [Matrix.rank_of_isUnit _ hu]
  simp

lemma id_cp : QAlgorithms.Entanglement.IsCompletelyPositive
    (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)) := by
  intro r X hX
  have : QAlgorithms.idTensorSuperop (R := Fin r)
      (⇑(LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ))) X = X := by
    ext p q; rfl
  rw [this]; exact hX

end X6P50J1

open QAlgorithms.Papers.Independent.Dependency50.P50 X6P50J1 in
theorem solution :
    QAlgorithms.Entanglement.IsCompletelyPositive (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)) ∧
      QAlgorithms.act (j1 (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ))) antisymmetricVector =
        (-1 : ℂ) • antisymmetricVector ∧
      schmidtNumber antisymmetricVector = 2 ∧
      inner ℂ antisymmetricVector
        (QAlgorithms.act (j1 (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ))) antisymmetricVector) = (-2 : ℂ) ∧
      ¬ (∀ v : Bipartite 2 2, schmidtNumber v ≤ 2 →
        0 ≤ inner ℂ v (QAlgorithms.act (j1 (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ))) v)) := by
  refine ⟨id_cp, act_av, sn_av, inner_av, fun h => ?_⟩
  have := h antisymmetricVector (le_of_eq sn_av)
  rw [inner_av] at this
  norm_num [Complex.nonneg_iff] at this

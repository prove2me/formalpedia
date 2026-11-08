-- Prove2me | solution 1 for WildeQIT.DiamondDist.proposition_9_1_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:35:02.031816+00:00
-- url     : https://prove2.me/submissions/b53cbfdc-86be-473c-a4a2-83d463744c9c

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Matrix MatrixOrder ComplexOrder

namespace WildeQIT.DiamondDist.Aux_TN

theorem eig_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {S S' : E →ₗ[ℂ] E} (h : S = S') (hS : S.IsSymmetric)
    (hS' : S'.IsSymmetric) {d : ℕ} (hn : Module.finrank ℂ E = d) :
    hS.eigenvalues hn = hS'.eigenvalues hn := by
  subst h; rfl

end WildeQIT.DiamondDist.Aux_TN

open WildeQIT WildeQIT.DiamondDist.Aux_TN in
theorem solution {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) :
    traceNorm M = (Matrix.toEuclideanLin M).singularValues.sum (fun _ σ => σ) := by
  classical
  have hA : (Mᴴ * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hnn : 0 ≤ Mᴴ * M :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self M)
  have h1 : traceNorm M = ∑ i, Real.sqrt (hA.eigenvalues i) := by
    unfold traceNorm
    rw [CFC.sqrt_eq_real_sqrt _ hnn, cfcₙ_eq_cfc (hf0 := by simp), hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal,
      Complex.re_sum]
    simp
  have h2 : ∑ i, Real.sqrt (hA.eigenvalues i) =
      ∑ j, Real.sqrt (hA.eigenvalues₀ j) := by
    unfold Matrix.IsHermitian.eigenvalues
    exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun j => Real.sqrt (hA.eigenvalues₀ j))
  set T := Matrix.toEuclideanLin M with hTdef
  have hn : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := finrank_euclideanSpace
  have hlin : Matrix.toEuclideanLin (Mᴴ * M) = T.adjoint ∘ₗ T := by
    rw [hTdef, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    exact Matrix.toLpLin_mul_same _ _ _
  have h3 : ∀ j, hA.eigenvalues₀ j = T.isSymmetric_adjoint_comp_self.eigenvalues hn j := by
    intro j
    unfold Matrix.IsHermitian.eigenvalues₀
    rw [eig_congr hlin _ T.isSymmetric_adjoint_comp_self]
  have hsub : T.singularValues.support ⊆ Finset.range (Fintype.card n) := by
    intro i hi
    rw [Finset.mem_range]
    by_contra h
    push_neg at h
    rw [Finsupp.mem_support_iff] at hi
    exact hi (T.singularValues_of_finrank_le (by rw [hn]; exact h))
  rw [h1, h2, Finsupp.sum_of_support_subset _ hsub _ (fun _ _ => rfl),
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [T.singularValues_fin hn j, h3 j]

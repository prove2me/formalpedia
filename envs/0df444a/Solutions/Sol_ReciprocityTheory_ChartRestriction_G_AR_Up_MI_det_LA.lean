-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.det_LA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:46.799794+00:00
-- url     : https://prove2.me/submissions/708765dd-7dab-403f-90ed-86e776e9bfdb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (A : ι → Matrix (Fin r) (Fin r) ℂ) :
    LinearMap.det (LA A) = ∏ τ, (A τ).det ^ r := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ix ι r)), ← Matrix.det_reindex_self (eB ι r)]
  have hM : Matrix.reindex (eB ι r) (eB ι r)
      (LinearMap.toMatrix (Pi.basisFun ℂ (Ix ι r)) (Pi.basisFun ℂ (Ix ι r)) (LA A)) =
      Matrix.blockDiagonal (fun k : ι × Fin r => A k.1) := by
    ext ⟨a, τ, b⟩ ⟨c, τ', d⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
      Pi.basisFun_apply, Pi.basisFun_repr, Matrix.blockDiagonal_apply]
    simp only [eB, Equiv.coe_fn_symm_mk, LA, LinearMap.coe_mk, AddHom.coe_mk, Mt, Matrix.mul_apply,
      Matrix.of_apply]
    by_cases h : (τ, b) = (τ', d)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [if_pos rfl, Finset.sum_eq_single c]
      · simp
      · intro k _ hk
        simp [Pi.single_apply, hk]
      · simp
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : ((τ, k, b) : Ix ι r) ≠ (τ', c, d) := by
        intro he
        apply h
        simp only [Prod.mk.injEq] at he ⊢
        exact ⟨he.1, he.2.2⟩
      simp [Pi.single_apply, this]
  rw [hM, Matrix.det_blockDiagonal, Fintype.prod_prod_type]
  simp [Finset.prod_const]
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI

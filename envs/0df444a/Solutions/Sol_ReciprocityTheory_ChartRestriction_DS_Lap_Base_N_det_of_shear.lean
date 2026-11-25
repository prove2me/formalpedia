-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.det_of_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:12:51.528366+00:00
-- url     : https://prove2.me/submissions/85aba676-2d69-4b63-9b26-10aedac081fe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (G : ℕ → Submodule ℝ E) (L : ℕ) (hG0 : G 0 = ⊤) (hL : G L = ⊥)
    (D : E →L[ℝ] E) (hD : ∀ j, ∀ x ∈ G j, D x - x ∈ G (j + 1)) : D.det = 1 := by
  let b := Module.finBasis ℝ E
  let N : E →ₗ[ℝ] E := (D : E →ₗ[ℝ] E) - LinearMap.id
  have hNpow : ∀ k, ∀ x, (N ^ k) x ∈ G k := by
    intro k
    induction k with
    | zero => intro x; rw [hG0]; exact Submodule.mem_top
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply]
      exact hD k _ (ih x)
  have hnil : IsNilpotent N := by
    refine ⟨L, LinearMap.ext fun x => ?_⟩
    have h := hNpow L x
    rw [hL, Submodule.mem_bot] at h
    rw [LinearMap.zero_apply]
    exact h
  have hpowM : ∀ k, (LinearMap.toMatrix b b N) ^ k = LinearMap.toMatrix b b (N ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero]; exact (LinearMap.toMatrix_one b).symm
    | succ k ih => rw [pow_succ, pow_succ, LinearMap.toMatrix_mul, ih]
  have hM : IsNilpotent (LinearMap.toMatrix b b N) := by
    obtain ⟨k, hk⟩ := hnil
    exact ⟨k, by rw [hpowM, hk, map_zero]⟩
  have key : ∀ M : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ,
      IsNilpotent M → (1 + M).det = 1 := by
    intro M hM
    have hch : M.charpoly = Polynomial.X ^ Fintype.card (Fin (Module.finrank ℝ E)) :=
      sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM).eq_zero
    have hmat : (Matrix.charmatrix M).map (Polynomial.eval (-1 : ℝ)) = -(1 + M) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp only [Matrix.map_apply, Matrix.charmatrix_apply, Matrix.diagonal_apply_eq,
          Matrix.neg_apply, Matrix.add_apply, Matrix.one_apply_eq, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
        ring
      · simp only [Matrix.map_apply, Matrix.charmatrix_apply, Matrix.diagonal_apply_ne _ h,
          Matrix.neg_apply, Matrix.add_apply, Matrix.one_apply_ne h, Polynomial.eval_sub,
          Polynomial.eval_zero, Polynomial.eval_C]
        ring
    have hev : Polynomial.eval (-1 : ℝ) M.charpoly = (-(1 + M)).det := by
      rw [← hmat, Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det,
        RingHom.mapMatrix_apply]
    rw [hch, Matrix.det_neg, Polynomial.eval_pow, Polynomial.eval_X] at hev
    have hne : ((-1 : ℝ)) ^ Fintype.card (Fin (Module.finrank ℝ E)) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    exact mul_left_cancel₀ hne (hev.symm.trans (mul_one _).symm)
  have hD' : LinearMap.toMatrix b b (D : E →ₗ[ℝ] E) = 1 + LinearMap.toMatrix b b N := by
    rw [← LinearMap.toMatrix_id b, ← map_add]
    congr 1
    ext x
    simp [N]
  show LinearMap.det (D : E →ₗ[ℝ] E) = 1
  rw [← LinearMap.det_toMatrix b, hD']
  exact key _ hM
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

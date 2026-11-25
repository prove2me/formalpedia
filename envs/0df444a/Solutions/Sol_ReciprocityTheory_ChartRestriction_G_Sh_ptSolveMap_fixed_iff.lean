-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptSolveMap_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:20.426502+00:00
-- url     : https://prove2.me/submissions/6fe08510-29f6-4894-88e7-f8f5f5d6a817

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}
section Solve
variable {d : ℕ} {σ τ : Type*} [Finite σ]
  (A : (Fin d → MvPowerSeries τ C) → σ → MvPowerSeries τ C)
  (K : Fin d → MvPowerSeries σ C) (M N : Matrix (Fin d) (Fin d) C)
  (f : Fin d → MvPowerSeries τ C)
private lemma sum_smul_sum_smul_eq_of_mul_eq_one (P Q : Matrix (Fin d) (Fin d) C) (hPQ : P * Q = 1)
    (z : Fin d → MvPowerSeries τ C) (c : Fin d) : ∑ b, Q b c • ∑ a, P a b • z a = z c := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have e : ∀ a, ∑ b, Q b c * P a b = (P * Q) a c := fun a => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  simp_rw [e, hPQ, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp
variable {A K}
end Solve
end
end ReciprocityTheory.ChartRestriction.G.Sh
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}
variable {d : ℕ} {σ τ : Type*} [Finite σ]
  (A : (Fin d → MvPowerSeries τ C) → σ → MvPowerSeries τ C)
  (K : Fin d → MvPowerSeries σ C) (M N : Matrix (Fin d) (Fin d) C)
  (f : Fin d → MvPowerSeries τ C)
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution (hNM : N * M = 1) (hMN : M * N = 1)
    (x : Fin d → MvPowerSeries τ C) :
    ptSolveMap A K N f x = x ↔ ∀ b, ∑ a, M a b • x a + subst (A x) (K b) = f b := by
  constructor
  · intro hx b
    have e := sum_smul_sum_smul_eq_of_mul_eq_one N M hNM (fun c => f c - subst (A x) (K c)) b
    have hx' : ∀ a, ∑ c, N c a • (f c - subst (A x) (K c)) = x a := fun a => congrFun hx a
    simp_rw [hx'] at e
    rw [e]
    abel
  · intro h
    funext c
    have hy : ∀ b, f b - subst (A x) (K b) = ∑ a, M a b • x a := fun b => by
      rw [← h b]
      abel
    simp only [ptSolveMap]
    simp_rw [hy]
    exact sum_smul_sum_smul_eq_of_mul_eq_one M N hMN x c
end ReciprocityTheory.ChartRestriction.G.Sh

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.UUA.reps_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:00.207621+00:00
-- url     : https://prove2.me/submissions/7c49e57b-3d6d-419e-b0b0-af46fbc2af5a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsCeil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA
theorem _root_.solution {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ) (hk : 1 ≤ k) :
    ∃ rep : (Fin (Module.finrank ℤ X) → Fin k) → X,
      (∀ χ : X, ∃ a μ, rep a + k • μ = χ) ∧
      (∀ a a' (μ μ' : X), rep a + k • μ = rep a' + k • μ' → a = a') ∧
      (∀ x y : X, k • x = k • y → x = y) := by
  classical
  let b := Module.finBasis ℤ X
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨fun a => b.equivFun.symm (fun i => ((a i : ℕ) : ℤ)), ?_, ?_, ?_⟩
  · intro χ
    refine ⟨fun i => ⟨(b.equivFun χ i % k).toNat, ?_⟩, b.equivFun.symm (fun i => b.equivFun χ i / k), ?_⟩
    · rw [Int.toNat_lt (Int.emod_nonneg _ hk0.ne')]
      exact Int.emod_lt_of_pos _ hk0
    · apply b.equivFun.injective
      funext i
      simp only [map_add, map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, nsmul_eq_mul]
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hk0.ne')]
      exact Int.emod_add_mul_ediv _ _
  · intro a a' μ μ' h
    funext i
    have e := congrFun (congrArg b.equivFun h) i
    simp only [map_add, map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, nsmul_eq_mul, Pi.mul_apply,
      Pi.natCast_apply] at e
    have e' := congrArg (fun t => t % (k : ℤ)) e
    rw [Int.add_mul_emod_self_left, Int.add_mul_emod_self_left] at e'
    have e1 : ((a i : ℕ) : ℤ) % k = (a i : ℕ) :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (a i).isLt)
    have e2 : ((a' i : ℕ) : ℤ) % k = (a' i : ℕ) :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (a' i).isLt)
    rw [e1, e2] at e'
    exact Fin.ext (by exact_mod_cast e')
  · intro x y hxy
    apply b.equivFun.injective
    funext i
    have e := congrFun (congrArg b.equivFun hxy) i
    simp only [map_nsmul, Pi.smul_apply, nsmul_eq_mul] at e
    exact mul_left_cancel₀ hk0.ne' e
end ReciprocityTheory.ChartRestriction.G.DVR.UUA

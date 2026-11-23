-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_Up__T_E_26bb633a7916
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:13.890798+00:00
-- url     : https://prove2.me/submissions/951c5236-3df9-44ed-a4f3-15c55387d205

import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthFrobeniusStatement
import Definitions.Def_ReciprocityTheory_DualLattices_FrobEqOfLe
import Definitions.Def_ReciprocityTheory_DualLattices_StdJForm
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section Unram
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
private lemma cj_cj_dual_lattices (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) : U.cj (U.cj i) = i := by
  by_contra h
  obtain ⟨a, ha⟩ := U.distinct _ _ h
  rw [U.conj (U.cj i) a, U.conj i (σ a), hS.invol a, sub_self, map_zero, map_zero] at ha
  exact zero_ne_one ha
private lemma isUnit_of_valuation_eq_one' (hS : HodgeTateSetting p v R O σ cp) {x : R} (hx : v (algebraMap R C x) = 1) :
    IsUnit x := by
  refine hS.integers.isUnit_of_one ?_ hx
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, map_zero] at hx
  exact zero_ne_one hx
private lemma E_block_zero (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (k j : Fin U.m) (hkj : U.cj j ≠ k) :
    (U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j = 0 := by
  have hinv : ∀ a, ((H.ρ a).map (algebraMap ℤ_[p] R))ᵀ * H.E.map (algebraMap ℤ_[p] R) =
      H.E.map (algebraMap ℤ_[p] R) * (H.ρ (σ a)).map (algebraMap ℤ_[p] R) := by
    intro a
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, H.E_equivariant a]
  have key : ∀ a, U.sg k a • ((U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j) =
      U.sg (U.cj j) a • ((U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j) := by
    intro a
    have h1 : (U.εT k)ᵀ * ((H.ρ a).map (algebraMap ℤ_[p] R))ᵀ = U.sg k a • (U.εT k)ᵀ := by
      rw [← Matrix.transpose_mul, U.εT_eig a k, Matrix.transpose_smul]
    calc U.sg k a • ((U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j)
        = (U.sg k a • (U.εT k)ᵀ) * H.E.map (algebraMap ℤ_[p] R) * U.εT j := by
          rw [Matrix.smul_mul, Matrix.smul_mul]
      _ = (U.εT k)ᵀ * ((H.ρ a).map (algebraMap ℤ_[p] R))ᵀ * H.E.map (algebraMap ℤ_[p] R) *
            U.εT j := by rw [h1]
      _ = (U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) *
            ((H.ρ (σ a)).map (algebraMap ℤ_[p] R) * U.εT j) := by
          rw [Matrix.mul_assoc ((U.εT k)ᵀ), hinv a]
          simp only [Matrix.mul_assoc]
      _ = U.sg (U.cj j) a • ((U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j) := by
          rw [U.εT_eig (σ a) j, ← U.conj j a, Matrix.mul_smul]
  obtain ⟨a, ha⟩ := U.distinct k (U.cj j) (Ne.symm hkj)
  have hu := isUnit_of_valuation_eq_one' hS ha
  have h2 := key a
  rw [← sub_eq_zero, ← sub_smul] at h2
  exact hu.smul_eq_zero.mp h2
end Unram
end ReciprocityTheory.PGsh.Up
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) :
    (U.εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) = H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by
  calc (U.εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R)
        = (U.εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) * 1 := (Matrix.mul_one _).symm
    _ = ∑ j, (U.εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j := by
        rw [← U.εT_sum, Matrix.mul_sum]
    _ = (U.εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by
        refine Finset.sum_eq_single (U.cj i) (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)
        refine E_block_zero hS H U i b (fun h => hb ?_)
        rw [← h, cj_cj_dual_lattices hS U b]
    _ = ∑ k, (U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by
        symm
        refine Finset.sum_eq_single i (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)
        refine E_block_zero hS H U b (U.cj i) ?_
        rw [cj_cj_dual_lattices hS U i]
        exact Ne.symm hb
    _ = (∑ k, U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by
        rw [Matrix.transpose_sum, Matrix.sum_mul, Matrix.sum_mul]
    _ = H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by
        rw [U.εT_sum, Matrix.transpose_one, Matrix.one_mul]
end ReciprocityTheory.PGsh.Up

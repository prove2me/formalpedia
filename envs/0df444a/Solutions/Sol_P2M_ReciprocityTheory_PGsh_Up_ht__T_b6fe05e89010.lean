-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_Up_ht__T_b6fe05e89010
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:37.14056+00:00
-- url     : https://prove2.me/submissions/af48afe2-5a8b-4555-861e-093eb37cc80a

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
private lemma epsL_transpose_mul_Ht_mul_epsT_eq_zero_of_ne (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (k i : Fin U.m) (hki : U.cj k ≠ i) :
    (U.εL k)ᵀ * H.Ht * U.εT i = 0 := by
  have key : ∀ a, U.sg i a • ((U.εL k)ᵀ * H.Ht * U.εT i) =
      U.sg (U.cj k) a • ((U.εL k)ᵀ * H.Ht * U.εT i) := by
    intro a
    have h1 : (U.εL k)ᵀ * (H.ρL (σ a))ᵀ = U.sg (U.cj k) a • (U.εL k)ᵀ := by
      rw [← Matrix.transpose_mul, U.εL_eig (σ a) k, Matrix.transpose_smul, ← U.conj k a]
    calc U.sg i a • ((U.εL k)ᵀ * H.Ht * U.εT i)
        = (U.εL k)ᵀ * H.Ht * ((H.ρ a).map (algebraMap ℤ_[p] R) * U.εT i) := by
          rw [U.εT_eig a i, Matrix.mul_smul]
      _ = (U.εL k)ᵀ * (H.Ht * (H.ρ a).map (algebraMap ℤ_[p] R)) * U.εT i := by
          simp only [Matrix.mul_assoc]
      _ = (U.εL k)ᵀ * (H.ρL (σ a))ᵀ * H.Ht * U.εT i := by
          rw [H.Ht_equivariant.1 a]
          simp only [Matrix.mul_assoc]
      _ = U.sg (U.cj k) a • ((U.εL k)ᵀ * H.Ht * U.εT i) := by
          rw [h1, Matrix.smul_mul, Matrix.smul_mul]
  obtain ⟨a, ha⟩ := U.distinct i (U.cj k) (Ne.symm hki)
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
    H.Ht * U.εT i = (U.εL (U.cj i))ᵀ * H.Ht := by
  calc H.Ht * U.εT i = (1 : Matrix (Fin g) (Fin g) R) * H.Ht * U.εT i := by rw [Matrix.one_mul]
    _ = (∑ k, U.εL k)ᵀ * H.Ht * U.εT i := by rw [U.εL_sum, Matrix.transpose_one]
    _ = ∑ k, (U.εL k)ᵀ * H.Ht * U.εT i := by
        rw [Matrix.transpose_sum, Matrix.sum_mul, Matrix.sum_mul]
    _ = (U.εL (U.cj i))ᵀ * H.Ht * U.εT i := by
        refine Finset.sum_eq_single (U.cj i) (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)
        refine epsL_transpose_mul_Ht_mul_epsT_eq_zero_of_ne hS H U b i (fun h => hb ?_)
        rw [← h, cj_cj_dual_lattices hS U b]
    _ = ∑ j, (U.εL (U.cj i))ᵀ * H.Ht * U.εT j := by
        symm
        refine Finset.sum_eq_single i (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)
        refine epsL_transpose_mul_Ht_mul_epsT_eq_zero_of_ne hS H U (U.cj i) b ?_
        rw [cj_cj_dual_lattices hS U i]
        exact Ne.symm hb
    _ = (U.εL (U.cj i))ᵀ * H.Ht := by rw [← Matrix.mul_sum, U.εT_sum, Matrix.mul_one]
end ReciprocityTheory.PGsh.Up

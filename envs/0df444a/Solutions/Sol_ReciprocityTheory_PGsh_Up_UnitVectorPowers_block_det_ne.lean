-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.UnitVectorPowers.block_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:27:15.150827+00:00
-- url     : https://prove2.me/submissions/552ba005-d531-4c90-abea-1e9ea39d90e6

import Definitions.Def_ReciprocityTheory_DualLattices_ProdPowUnitVectorVal
import Definitions.Def_ReciprocityTheory_DualLattices_FormMonomialUnitVector
import Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_Mk_det
import Theorems.Thm_ReciprocityTheory_PGsh_Up_UnitVectorPowers_Mk_off

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.UnitVectorPowers
open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
variable [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers
theorem _root_.solution (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (i : Fin U.m) (e : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i}) :
    (Matrix.of fun j l : {j // D.κ j = i} => Mk D j.1 (e l).1).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  let W : Ix g → IsLocalRing.ResidueField R := fun j => if hj : D.κ j = i then w ⟨j, hj⟩ else 0
  apply Mk_det D
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  refine ⟨W, ?_, ?_⟩
  · intro hW
    apply hw0
    funext j
    have h1 := congrFun hW j.1
    simpa [W, j.2] using h1
  · funext l
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    by_cases hl : D.κ l = U.φ i
    · have h1 := congrFun hw (e.symm ⟨l, hl⟩)
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Equiv.apply_symm_apply,
        Pi.zero_apply] at h1
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => D.κ j = i)]
      have h2 : ∑ j : {j // ¬ D.κ j = i}, W j.1 * Mk D j.1 l = 0 :=
        Finset.sum_eq_zero fun j _ => by simp [W, j.2]
      have h3 : ∑ j : {j // D.κ j = i}, W j.1 * Mk D j.1 l = ∑ j, w j * Mk D j.1 l :=
        Finset.sum_congr rfl fun j _ => by simp [W, j.2]
      rw [h2, h3, add_zero]
      exact h1
    · refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : D.κ j = i
      · rw [Mk_off hv hp1 D j l (by rw [hj]; exact hl), mul_zero]
      · simp [W, hj]
end ReciprocityTheory.PGsh.Up.UnitVectorPowers

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.log_relIndex_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:38:46.029383+00:00
-- url     : https://prove2.me/submissions/cd6a6192-b78f-487b-b683-5bb4176153b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsMPrimeFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_RelIndexNeZeroOfMulMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mul_mem_of_forall
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_relIndex_ne_zero_of_mul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_relIndex_chain
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sec_zero__b0dd91851335
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Module
variable {Ω : Type} [Field Ω] [CharZero Ω]
variable {κ : Type} [Fintype κ]
private theorem sec_eq_sec_one_pow (x : κ → Ω) (n : ℕ) : sec ℤ x n = sec ℤ x 1 ^ n := by
  unfold sec
  rw [← MvPolynomial.homogeneousSubmodule_one_pow (σ := κ) (R := ℤ) (n := n), Submodule.map_pow]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Module
variable {Ω : Type} [Field Ω] [CharZero Ω]
variable {κ : Type} [Fintype κ]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x x' : κ → Ω) (hle : sec ℤ x 1 ≤ sec ℤ x' 1)
    (hfin : ∃ M : ℕ, 0 < M ∧ ∀ s ∈ sec ℤ x' 1, (M : Ω) * s ∈ sec ℤ x 1) (n : ℕ) :
    Real.log ((sec ℤ x n).toAddSubgroup.relIndex (sec ℤ x' n).toAddSubgroup) =
      ∑ j ∈ Finset.range n,
      Real.log ((sec ℤ x (n - j) * sec ℤ x' j).toAddSubgroup.relIndex
        (sec ℤ x (n - j - 1) * sec ℤ x' (j + 1)).toAddSubgroup) := by
  obtain ⟨M, hM0, hM⟩ := hfin
  simp only [Nat.sub_sub]
  have hfgs : ∀ (y : κ → Ω) (k : ℕ), (sec ℤ y k).FG := fun y k => Module.Finite.iff_fg.mp inferInstance
  have e1 : ∀ j < n, sec ℤ x (n - j) = sec ℤ x (n - (j + 1)) * sec ℤ x 1 := by
    intro j hj
    rw [sec_eq_sec_one_pow x (n - j), sec_eq_sec_one_pow x (n - (j + 1)), ← pow_succ]
    congr 1
    omega
  have e2 : ∀ j, sec ℤ x' (j + 1) = sec ℤ x' j * sec ℤ x' 1 := by
    intro j
    rw [sec_eq_sec_one_pow x' (j + 1), sec_eq_sec_one_pow x' j, pow_succ]
  have hstep : ∀ j < n, sec ℤ x (n - j) * sec ℤ x' j ≤ sec ℤ x (n - (j + 1)) * sec ℤ x' (j + 1) := by
    intro j hj
    rw [e1 j hj, e2 j, mul_right_comm, ← mul_assoc]
    exact Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul ha (hle hb)
  have hne : ∀ j < n, (sec ℤ x (n - j) * sec ℤ x' j).toAddSubgroup.relIndex
      (sec ℤ x (n - (j + 1)) * sec ℤ x' (j + 1)).toAddSubgroup ≠ 0 := by
    intro j hj
    refine relIndex_ne_zero_of_mul_mem ((hfgs x _).mul (hfgs x' _)) hM0 fun u hu => ?_
    rw [e2 j, ← mul_assoc] at hu
    have h := mul_mem_of_forall hM (sec ℤ x (n - (j + 1)) * sec ℤ x' j) u hu
    rw [e1 j hj, mul_right_comm]
    exact h
  have chain := (relIndex_chain (fun j => (sec ℤ x (n - j) * sec ℤ x' j).toAddSubgroup) n
    (fun j hj => hstep j hj) n le_rfl).1
  simp only [Nat.sub_zero, Nat.sub_self, sec_zero', mul_one, one_mul] at chain
  rw [chain, Nat.cast_prod, Real.log_prod]
  intro j hj
  exact Nat.cast_ne_zero.mpr (hne j (Finset.mem_range.mp hj))
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

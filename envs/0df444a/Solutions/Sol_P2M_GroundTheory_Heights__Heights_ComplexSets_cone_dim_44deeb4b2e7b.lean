-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_cone_dim_44deeb4b2e7b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:56:19.94887+00:00
-- url     : https://prove2.me/submissions/d3f82826-0c04-4311-b10a-abb3d85d6d83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_coneEq_ne_zero_df5d0619dfe6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_cone_isPrime_a6929b93aaa1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_withBot_le_two_of_add_one_le_755902c62a52
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_X_zero_not_mem_coneIdeal_a1ec09729f1b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution :
    ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ) := by
  have hup : ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) ≤ 2 := by
    apply withBot_le_two_of_add_one_le
    have h3 : ringKrullDim (MvPolynomial (Fin 3) ℂ) = 3 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      simp
    rw [← h3]
    exact ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_of_ne_zero coneEq_ne_zero)

  let ψ1 : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ := aeval ![0, 0, X 0]
  let ψ2 : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] ℂ := aeval (fun _ => 0)
  have c2 : ψ2 = (aeval (fun _ => (0 : ℂ))).comp ψ1 := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [ψ1, ψ2]
  have l2 : RingHom.ker ψ1 ≤ RingHom.ker ψ2 := by
    intro p hp
    rw [RingHom.mem_ker] at hp ⊢
    rw [c2, AlgHom.comp_apply, hp, map_zero]
  have l1 : coneIdeal ≤ RingHom.ker ψ1 := by
    rw [coneIdeal, Ideal.span_le, Set.singleton_subset_iff]
    show ψ1 coneEq = 0
    simp [ψ1, coneEq]
  have : (RingHom.ker ψ1).IsPrime := RingHom.ker_isPrime _
  have : (RingHom.ker ψ2).IsPrime := RingHom.ker_isPrime _
  let p0 : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin 3) ℂ) (coneIdeal : Set _) :=
    ⟨⟨coneIdeal, cone_isPrime⟩, (show (coneIdeal : Set (MvPolynomial (Fin 3) ℂ)) ⊆ coneIdeal from subset_rfl)⟩
  let p1 : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin 3) ℂ) (coneIdeal : Set _) :=
    ⟨⟨RingHom.ker ψ1, inferInstance⟩, (show (coneIdeal : Set (MvPolynomial (Fin 3) ℂ)) ⊆ RingHom.ker ψ1 from l1)⟩
  let p2 : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin 3) ℂ) (coneIdeal : Set _) :=
    ⟨⟨RingHom.ker ψ2, inferInstance⟩, (show (coneIdeal : Set (MvPolynomial (Fin 3) ℂ)) ⊆ RingHom.ker ψ2 from l1.trans l2)⟩
  have h01 : p0 < p1 := by
    refine lt_of_le_not_ge (show coneIdeal ≤ RingHom.ker ψ1 from l1) fun h => ?_
    have hx : (X 0 : MvPolynomial (Fin 3) ℂ) ∈ RingHom.ker ψ1 := by
      rw [RingHom.mem_ker]; simp [ψ1]
    exact X_zero_not_mem_coneIdeal ((show RingHom.ker ψ1 ≤ coneIdeal from h) hx)
  have h12 : p1 < p2 := by
    refine lt_of_le_not_ge (show RingHom.ker ψ1 ≤ RingHom.ker ψ2 from l2) fun h => ?_
    have hx : (X 2 : MvPolynomial (Fin 3) ℂ) ∈ RingHom.ker ψ2 := by
      rw [RingHom.mem_ker]; simp [ψ2]
    have hx' := (show RingHom.ker ψ2 ≤ RingHom.ker ψ1 from h) hx
    rw [RingHom.mem_ker] at hx'
    simp [ψ1] at hx'
  let s : LTSeries (PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin 3) ℂ) (coneIdeal : Set _)) :=
    { length := 2
      toFun := ![p0, p1, p2]
      step := fun i => by fin_cases i; exacts [h01, h12] }
  have hlow : (2 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) := by
    rw [ringKrullDim_quotient]
    exact Order.LTSeries.length_le_krullDim s
  rw [le_antisymm hup hlow]
  rfl
end GroundTheory.Heights₂.Heights.ComplexSets

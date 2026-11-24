-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ReesAlgebraDim_proof_1bf2fe786d2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:07:10.227805+00:00
-- url     : https://prove2.me/submissions/529c61f3-4799-4bf7-82ec-eb5095d577c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PReesAlgebraDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open Polynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace ReesAlgebraDim
theorem _root_.solution (h₁ : DimensionInequality.Statement.{u, u}) :
    ReesAlgebraDim.Statement.{u} := by
  intro A _ _ _ I hI n hn
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hinj : Function.Injective (algebraMap A (reesAlgebra I)) := by
    intro x y h
    have := congrArg (fun r : reesAlgebra I => (r : A[X])) h
    simpa using this
  apply le_antisymm
  · rw [ringKrullDim_le_iff_height_le]
    intro P hP
    have key := h₁ A (reesAlgebra I) hinj P
    have htd : Algebra.trdeg A (reesAlgebra I) ≤ 1 := by
      calc Algebra.trdeg A (reesAlgebra I) ≤ Algebra.trdeg A A[X] :=
            trdeg_le_of_injective (reesAlgebra I).val Subtype.val_injective
        _ = 1 := Polynomial.trdeg_of_isDomain
    have hp : (P.under A).height ≤ n := by
      have := Ideal.height_le_ringKrullDim_of_ne_top (inferInstance : (P.under A).IsPrime).ne_top
      rw [hn] at this
      exact_mod_cast this
    have hc : Cardinal.ofENat P.height ≤ Cardinal.ofENat ((n + 1 : ℕ) : ℕ∞) := by
      calc Cardinal.ofENat P.height
          ≤ Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (reesAlgebra I ⧸ P) :=
            le_self_add
        _ ≤ Cardinal.ofENat (P.under A).height + Algebra.trdeg A (reesAlgebra I) := key
        _ ≤ Cardinal.ofENat (n : ℕ∞) + 1 := by gcongr
        _ = Cardinal.ofENat ((n + 1 : ℕ) : ℕ∞) := by simp
    have : P.height ≤ ((n + 1 : ℕ) : ℕ∞) := Cardinal.ofENat_le_ofENat.mp hc
    exact_mod_cast this
  · let f : reesAlgebra I →+* A := (Polynomial.constantCoeff).comp (reesAlgebra I).val.toRingHom
    have hf : Function.Surjective f := fun x => ⟨algebraMap A (reesAlgebra I) x, by simp [f]⟩
    let r : reesAlgebra I := ⟨monomial 1 a, reesAlgebra.monomial_mem.mpr (by simpa using haI)⟩
    have hr0 : r ≠ 0 := by
      intro h
      have := congrArg (fun s : reesAlgebra I => (s : A[X])) h
      simp [r] at this
      exact ha0 this
    have h := ringKrullDim_succ_le_of_surjective f hf (mem_nonZeroDivisors_of_ne_zero hr0)
      (by simp [f, r])
    rw [hn] at h
    exact_mod_cast h
end ReesAlgebraDim
end GroundTheory.Heights₂.Heights.NumbersDVR

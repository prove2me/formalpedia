-- Prove2me | solution 1 for PermanentRollout.criticalLinearSliceIdeal_radical_eq_idealOfVars_of_dimension_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/3b939194-7cbe-4a0a-9980-1dd5179ddd15

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_rollout_minimalPrime_isHomogeneous
import Theorems.Thm_PermanentRollout_permanent_rollout_homogeneousPrime_le_idealOfVars
import Theorems.Thm_PermanentRollout_permanent_rollout_idealOfVars_isMaximal
import Theorems.Thm_PermanentRollout_permanent_rollout_homogeneous_linear_slice_ideal_isHomogeneous
import Theorems.Thm_PermanentRollout_criticalGradientIdeal_isHomogeneous
import Theorems.Thm_PermanentRollout_criticalGradientIdeal_ne_top

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {m n d : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (hd : 2 ≤ d) (hP : P.IsHomogeneous d)
    (c : Fin n → Fin m → ℂ)
    (hdimension :
      ringKrullDim
        (MvPolynomial (Fin m) ℂ ⧸
          permanentRolloutHomogeneousLinearSliceIdeal
            (homogeneousMapIdeal
              (fun i : Fin m => MvPolynomial.pderiv i P)) c) ≤
        (0 : WithBot ℕ∞)) :
    (permanentRolloutHomogeneousLinearSliceIdeal
      (homogeneousMapIdeal
        (fun i : Fin m => MvPolynomial.pderiv i P)) c).radical =
      MvPolynomial.idealOfVars (Fin m) ℂ := by
  let I : Ideal (MvPolynomial (Fin m) ℂ) :=
    homogeneousMapIdeal (fun i : Fin m => MvPolynomial.pderiv i P)
  let J : Ideal (MvPolynomial (Fin m) ℂ) :=
    permanentRolloutHomogeneousLinearSliceIdeal I c
  have hIproper : I ≠ ⊤ := criticalGradientIdeal_ne_top P hd hP
  obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_minimalPrimes hIproper
  have hIvertex : I ≤ MvPolynomial.idealOfVars (Fin m) ℂ :=
    hQ.le.trans
      (permanent_rollout_homogeneousPrime_le_idealOfVars Q hQ.isPrime
        (permanent_rollout_minimalPrime_isHomogeneous
          (criticalGradientIdeal_isHomogeneous P hP) hQ))
  have hJvertex : J ≤ MvPolynomial.idealOfVars (Fin m) ℂ := by
    apply sup_le hIvertex
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    change (∑ i, c j i • MvPolynomial.X i) ∈
      MvPolynomial.idealOfVars (Fin m) ℂ
    apply Ideal.sum_mem
    intro i _
    rw [Algebra.smul_def]
    exact (MvPolynomial.idealOfVars (Fin m) ℂ).mul_mem_left _
      (Ideal.subset_span (Set.mem_range_self i))
  have hvertexproper : MvPolynomial.idealOfVars (Fin m) ℂ ≠ ⊤ :=
    (permanent_rollout_idealOfVars_isMaximal m).ne_top
  have hJproper : J ≠ ⊤ := by
    intro htop
    apply hvertexproper
    apply top_unique
    rw [← htop]
    exact hJvertex
  have hJhomogeneous :
      J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) ℂ) :=
    permanent_rollout_homogeneous_linear_slice_ideal_isHomogeneous
      I (criticalGradientIdeal_isHomogeneous P hP) c
  have hzero : Ring.KrullDimLE 0 (MvPolynomial (Fin m) ℂ ⧸ J) :=
    Ring.krullDimLE_iff.mpr hdimension
  have hallmaximal : ∀ p ∈ J.minimalPrimes, p.IsMaximal :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mp
      hzero
  change J.radical = MvPolynomial.idealOfVars (Fin m) ℂ
  rw [← J.sInf_minimalPrimes]
  apply le_antisymm
  · obtain ⟨⟨p, hp⟩⟩ := Ideal.nonempty_minimalPrimes hJproper
    have hpvertex : p ≤ MvPolynomial.idealOfVars (Fin m) ℂ :=
      permanent_rollout_homogeneousPrime_le_idealOfVars p hp.isPrime
        (permanent_rollout_minimalPrime_isHomogeneous hJhomogeneous hp)
    have hpeq : p = MvPolynomial.idealOfVars (Fin m) ℂ :=
      (hallmaximal p hp).eq_of_le hvertexproper hpvertex
    rw [← hpeq]
    exact sInf_le hp
  · apply le_sInf
    intro p hp
    have hpvertex : p ≤ MvPolynomial.idealOfVars (Fin m) ℂ :=
      permanent_rollout_homogeneousPrime_le_idealOfVars p hp.isPrime
        (permanent_rollout_minimalPrime_isHomogeneous hJhomogeneous hp)
    have hpeq : p = MvPolynomial.idealOfVars (Fin m) ℂ :=
      (hallmaximal p hp).eq_of_le hvertexproper hpvertex
    exact hpeq.symm.le
end PermanentRollout

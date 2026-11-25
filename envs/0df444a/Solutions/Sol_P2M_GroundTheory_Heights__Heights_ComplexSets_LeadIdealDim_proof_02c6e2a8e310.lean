-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_LeadIdealDim_proof_02c6e2a8e310
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:18:08.416555+00:00
-- url     : https://prove2.me/submissions/ae7e91d4-1883-486d-ab62-10378a5c0f45

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_algebraicIndependent_mk_X_iff_0a51e0acb677
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_rename_mem_of_leadIdeal_79b057493084
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_quotient_dim_le_of_minimalPrimes_b2ad850cbdc7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_exists_vars_isTranscendenceBasis_40c8cc02b5cb
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_exists_ringKrullDim_eq_trdeg


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
open MvPolynomial
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace LeadIdealDim
theorem _root_.solution : LeadIdealDim.Statement := by
  intro n J
  apply quotient_dim_le_of_minimalPrimes
  intro P hP
  have _ : P.IsPrime := hP.1.1
  obtain ⟨u, hu, hcard⟩ := exists_vars_isTranscendenceBasis P
  have hJ : ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ J → q = 0 :=
    rename_mem_of_leadIdeal J u fun q hq => (algebraicIndependent_mk_X_iff P u).mp hu q (hP.1.2 hq)

  let M : Submonoid (MvPolynomial (Fin n) ℂ) :=
    (nonZeroDivisors (MvPolynomial u ℂ)).map (rename (R := ℂ) (Subtype.val : u → Fin n))
  have hdis : Disjoint (J : Set (MvPolynomial (Fin n) ℂ)) M := by
    rw [Set.disjoint_left]
    rintro _ hJf ⟨q, hq, rfl⟩
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hq) (hJ q hJf)
  obtain ⟨Q, hQ, hJQ, hQM⟩ := Ideal.exists_le_prime_disjoint J M hdis
  have hQu : AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk Q (X (i : Fin n))) := by
    rw [algebraicIndependent_mk_X_iff]
    intro q hq
    by_contra hq0
    exact Set.disjoint_left.mp hQM hq ⟨q, mem_nonZeroDivisors_of_ne_zero hq0, rfl⟩
  obtain ⟨a, haP, htP⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg ℂ (A := MvPolynomial (Fin n) ℂ ⧸ P)
  obtain ⟨b, hbQ, htQ⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg ℂ (A := MvPolynomial (Fin n) ℂ ⧸ Q)
  have hab : a ≤ b := by
    have h := hQu.cardinalMk_le_trdeg
    rw [hcard, htP, htQ] at h
    exact_mod_cast h
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = a := haP
    _ ≤ b := by exact_mod_cast hab
    _ = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) := hbQ.symm
    _ ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJQ) (Ideal.Quotient.factor_surjective hJQ)
end LeadIdealDim
end GroundTheory.Heights₂.Heights.ComplexSets

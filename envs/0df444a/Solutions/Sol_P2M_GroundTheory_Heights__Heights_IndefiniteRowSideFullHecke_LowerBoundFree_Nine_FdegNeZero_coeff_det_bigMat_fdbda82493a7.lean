-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_coeff_det_bigMat_fdbda82493a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:10.948861+00:00
-- url     : https://prove2.me/submissions/e95e93fd-0380-4bf2-8669-350c1936aec6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PTwinFdegNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_rho_apply_0a0148cd7cde
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_rho_mem_70265bcf8127
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_prod_bigMat_of_9a5918927180
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_sum_single_apply_d25b8e844fff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_Nine_FdegNeZero_sum_single_rho_8bb9a79f8d56

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
open MvPolynomial Matrix Equiv
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero
variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero
theorem _root_.solution (j : ℕ) (hj : j ≤ N) :
    coeff (delta0 j) (bigMat (Ψ := Ψ) (N := N) j).det = ((Perm.sign (rho (Ψ := Ψ) j hj) : ℤ) : ℚ) := by
  rw [det_apply, coeff_sum, Finset.sum_eq_single (rho j hj)]
  · rw [Units.smul_def, coeff_smul, prod_bigMat_of j _ (rho_mem j hj), coeff_monomial,
      if_pos (sum_single_rho j hj)]
    simp
  · intro σ _ hne
    rw [Units.smul_def, coeff_smul]
    by_cases hσ : ∀ l, (σ l).1 = l.1 ∧ (((σ l).2 : ℕ) < j ↔ (l.2 : ℕ) < j)
    · rw [prod_bigMat_of j σ hσ, coeff_monomial, if_neg, smul_zero]
      intro hm
      apply hne
      refine Equiv.ext fun l => Prod.ext ?_ (Fin.ext ?_)
      · rw [(hσ l).1, rho_apply]
      · have h1 := congrArg (fun m : Ψ × Fin N →₀ ℕ => m (σ l)) hm
        have h2 := (hσ l).2
        rw [sum_single_apply] at h1
        simp only [delta0, Finsupp.coe_equivFunOnFinite_symm, colExp] at h1
        simp only [rho_apply, rev]
        have h3 := (σ l).2.2
        have h4 := l.2.2
        split_ifs at h1 ⊢ <;> omega
    · obtain ⟨l, hl⟩ := not_forall.mp hσ
      rw [Finset.prod_eq_zero (Finset.mem_univ l) (by simp only [bigMat, of_apply, if_neg hl]), coeff_zero,
        smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FdegNeZero

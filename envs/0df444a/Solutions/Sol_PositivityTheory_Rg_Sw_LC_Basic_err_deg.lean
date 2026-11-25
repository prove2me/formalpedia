-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.err_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:33.086838+00:00
-- url     : https://prove2.me/submissions/b97995d4-83db-41b6-845e-ece431b23811

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_X_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_monomial
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_Basic_degree_add__88e784869794
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_sub
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_mono
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_X_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_DegLT_pderiv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_Sm_succ
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_Sm_deg
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fockMono_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Basic
theorem _root_.solution (c : ℝ) : ∀ d : ℕ, ∀ s : Ix m n →₀ ℕ, s.degree = d → DegLT d (err c s) := by
  intro d
  induction d with
  | zero =>
    intro s hs
    have : s = 0 := (Finsupp.degree_eq_zero_iff s).mp hs
    subst this
    simp [err, Sm, fockMono_zero, DegLT.zero]
  | succ d ih =>
    intro s hs
    have hs0 : s ≠ 0 := by
      intro h; subst h; simp at hs
    obtain ⟨k, hk⟩ : ∃ k, s k ≠ 0 := by
      by_contra h; push_neg at h; exact hs0 (Finsupp.ext h)
    have hle : Finsupp.single k 1 ≤ s := by
      intro i
      by_cases hi : i = k
      · subst hi; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hi]
    set s' := s - Finsupp.single k 1 with hs'
    have hsplit : s = s' + Finsupp.single k 1 := (tsub_add_cancel_of_le hle).symm
    have hd' : s'.degree = d := by
      have := degree_add' s' (Finsupp.single k 1)
      rw [← hsplit, Finsupp.degree_single] at this
      omega
    have hrec : fockMono c s = cr c k (fockMono c s') := by
      rw [← fock_monomial, ← fock_monomial, hsplit, add_comm, monomial_single_add, pow_one, fock_X_mul]
    have e : err c s = (2 * c : ℂ) • (X (flp k) * err c s') - pderiv k (Sm c s' + err c s') := by
      rw [err, hrec, cr_apply, hsplit, Sm_succ, err]
      simp only [sub_add_cancel, mul_sub, smul_sub]
      abel
    rw [e]
    refine DegLT.sub (DegLT.smul _ (DegLT.X_mul _ (ih s' hd'))) (DegLT.pderiv _ (DegLT.add ?_ ((ih s' hd').mono (by omega))))
    have := Sm_deg c s'
    rwa [hd'] at this
end PositivityTheory.Rg.Sw.LC.Basic

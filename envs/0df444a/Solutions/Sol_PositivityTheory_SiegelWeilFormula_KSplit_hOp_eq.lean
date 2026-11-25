-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.hOp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:37.462806+00:00
-- url     : https://prove2.me/submissions/1ce350ea-fb43-4f95-8678-be272177a1e2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dY_X
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dsum_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KSplit
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.SiegelWeilFormula.KSplit
theorem _root_.solution (c : ℝ) (a b : Fin m) (P : PX m n) : hOp (fun _ => true) c a b P = dY (single a b 1) P := by
  set D' : Derivation ℂ (PX m n) (PX m n) := ∑ i, ((X (b, i, false) : PX m n) • pderiv (a, i, false) -
    (X (a, i, true) : PX m n) • pderiv (b, i, true))
  have h1 : hOp (fun _ => true) c a b P = D' P := by
    simp only [D', dsum_apply, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, hOp, sgn, if_true, mul_one,
      sub_self, mul_zero, map_zero, zero_mul, sub_zero, C_1, one_mul]
  have h2 : D' = dY (single a b 1) := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a', i', b'⟩
    rw [dY_X]
    simp only [D', dsum_apply, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, pderiv_X, Pi.single_apply,
      Prod.mk.injEq]
    cases b'
    · simp only [lf, dm, Bool.false_eq_true, if_false, and_false, mul_zero, sub_zero, single_apply]
      by_cases ha : a' = a
      · subst ha
        rw [Finset.sum_eq_single b (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
        rw [Finset.sum_eq_single i' (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
        simp
      · simp [Ne.symm ha, ha]
    · simp only [lf, dm, if_true, and_false, and_true, mul_zero, zero_sub, single_apply, Matrix.neg_apply,
        transpose_apply]
      by_cases hb : a' = b
      · subst hb
        rw [Finset.sum_eq_single a (fun c _ hc => by simp [hc, Ne.symm hc]) (by simp)]
        rw [Finset.sum_eq_single i' (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
        simp
      · simp [Ne.symm hb, hb]
  rw [h1, h2]
end PositivityTheory.SiegelWeilFormula.KSplit

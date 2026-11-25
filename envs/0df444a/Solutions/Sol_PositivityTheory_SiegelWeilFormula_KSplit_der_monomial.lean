-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.der_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:56:41.264882+00:00
-- url     : https://prove2.me/submissions/4e103751-0e87-4ded-8202-3dacdde01836

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial

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
theorem _root_.solution (D : Derivation ℂ (PX m n) (PX m n)) (w : Fin m × Fin n × Bool → ℂ)
    (hD : ∀ k, D (X k) = C (w k) * X k) (s : Fin m × Fin n × Bool →₀ ℕ) :
    D (monomial s 1) = C (s.sum fun k e => (e : ℂ) * w k) * monomial s 1 := by
  induction s using Finsupp.induction with
  | zero => simp
  | single_add k e s _ _ ih =>
    have e1 : (monomial (Finsupp.single k e + s) (1 : ℂ) : PX m n) = X k ^ e * monomial s 1 := by
      rw [X_pow_eq_monomial (R := ℂ), monomial_mul, one_mul]
    rw [e1, Derivation.leibniz, Derivation.leibniz_pow, hD, ih, Finsupp.sum_add_index' (fun _ => by simp)
      (fun _ _ _ => by push_cast; ring), Finsupp.sum_single_index (by simp)]
    simp only [smul_eq_mul, nsmul_eq_mul, map_add, map_mul, map_natCast]
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · subst h0; simp
    · have : (X k : PX m n) ^ e = X k ^ (e - 1) * X k := by
        rw [← pow_succ, Nat.sub_add_cancel hpos]
      rw [this]; ring
end PositivityTheory.SiegelWeilFormula.KSplit

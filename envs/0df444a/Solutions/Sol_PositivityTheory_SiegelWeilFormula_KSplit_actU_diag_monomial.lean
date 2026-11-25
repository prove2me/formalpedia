-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.actU_diag_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:34.468811+00:00
-- url     : https://prove2.me/submissions/9b48aa7a-dce1-48e9-aed3-470ef7006a26

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_actU_X

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
theorem _root_.solution (ζ : Fin m → ℂ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    actU (diagonal ζ) (monomial s 1) =
      C (s.prod fun k e => (if k.2.2 then star (ζ k.1) else ζ k.1) ^ e) * monomial s (1 : ℂ) := by
  have hX : ∀ k : Fin m × Fin n × Bool, actU (n := n) (diagonal ζ) (X k) =
      C (if k.2.2 then star (ζ k.1) else ζ k.1) * X k := by
    rintro ⟨a, i, b⟩
    rw [actU_X]
    cases b
    · simp only [lf, am, Bool.false_eq_true, if_false]
      rw [Finset.sum_eq_single a (fun c _ hc => by rw [diagonal_apply_ne _ (Ne.symm hc)]; simp) (by simp)]
      simp
    · simp only [lf, am, if_true]
      rw [Finset.sum_eq_single a (fun c _ hc => by rw [map_apply, diagonal_apply_ne _ (Ne.symm hc)]; simp) (by simp)]
      simp
  simp only [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod, map_pow, hX, mul_pow, ← Finset.prod_mul_distrib]
end PositivityTheory.SiegelWeilFormula.KSplit

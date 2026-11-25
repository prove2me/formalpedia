-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.kill_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:18:01.071785+00:00
-- url     : https://prove2.me/submissions/4d0876cf-7b40-473c-b134-eb1d6bf72b55

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_dY_X
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_der_monomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_kill_charged
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_sum_weight

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
theorem _root_.solution (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ u ∈ unitaryGroup (Fin m) ℂ, ∀ P, Λ (actU u P) = Λ P)
    (d : Fin m → ℂ) (P : PX m n) : Λ (dY (diagonal d) P) = 0 := by
  have hD : ∀ k : Fin m × Fin n × Bool, dY (diagonal d) (X k) = C (if k.2.2 then -d k.1 else d k.1) * X k := by
    rintro ⟨a, i, b⟩
    rw [dY_X]
    cases b
    · simp only [lf, dm, Bool.false_eq_true, if_false]
      rw [Finset.sum_eq_single a (fun c _ hc => by rw [diagonal_apply_ne _ (Ne.symm hc)]; simp) (by simp)]
      simp
    · simp only [lf, dm, if_true]
      rw [Finset.sum_eq_single a (fun c _ hc => by
        rw [Matrix.neg_apply, transpose_apply, diagonal_apply_ne _ hc]; simp) (by simp)]
      simp
  have hmon : ∀ s, Λ (dY (diagonal d) (monomial s 1)) = 0 := fun s => by
    rw [der_monomial _ _ hD, C_mul', map_smul, smul_eq_mul, sum_weight]
    by_cases h : ∀ a, chg a s = 0
    · rw [Finset.sum_eq_zero fun a _ => by rw [h a]; simp, zero_mul]
    · push Not at h
      obtain ⟨a, ha⟩ := h
      rw [kill_charged Λ hΛ s a ha, mul_zero]
  rw [P.as_sum, map_sum, map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [show (monomial s (coeff s P) : PX m n) = coeff s P • monomial s 1 by rw [smul_monomial, smul_eq_mul, mul_one],
    (dY (diagonal d)).map_smul, map_smul, hmon, smul_zero]
end PositivityTheory.SiegelWeilFormula.KSplit

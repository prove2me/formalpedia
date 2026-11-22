-- Prove2me | solution 1 for PI.WeylForKInhab.diag_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:54.440073+00:00
-- url     : https://prove2.me/submissions/699ee643-f36b-4435-9745-224f6f0eae1e

import Definitions.Def_Formalism_PeriodIntegrals_WeylForK
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UpqRep Matrix
noncomputable section
open PI PI.WeylForKInhab
namespace PI.WeylForKInhab
theorem _root_.solution {N : ℕ} (ε : Fin N → Bool) (θ : Fin N → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by
  simp only [Kset, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    first
      | simp [← Complex.exp_conj, ← Complex.exp_add]
      | (rw [Pi.star_apply, ← Complex.exp_conj, ← Complex.exp_add]
         simp [Complex.conj_ofReal])
      | (rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Complex.norm_exp_ofReal_mul_I]
         simp)
  · simp only [Jm, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring
end PI.WeylForKInhab

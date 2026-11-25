-- Prove2me | solution 1 for PI.KerDetFinW.det_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:43.119304+00:00
-- url     : https://prove2.me/submissions/8cbf1a06-d733-487a-b237-0a36824a133a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
import Theorems.Thm_PI_KerDetFinW_det_mem_of_entries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerDetFinW
open PI.KerIso
namespace PI.KerDetFinW
theorem _root_.solution {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (A : Matrix ι ι K) (u : ι → ℕ) (hu : ∀ j, Nat.Coprime (u j) p)
    (hA : ∀ i j, (u j : K) * A i j ∈ (algebraMap (𝓞 K) K).range) :
    ∃ U : ℕ, Nat.Coprime U p ∧ (U : K) * A.det ∈ (algebraMap (𝓞 K) K).range := by
  refine ⟨∏ j, u j, Nat.Coprime.prod_left (fun j _ => hu j), ?_⟩
  have h1 : ((∏ j, u j : ℕ) : K) * A.det = (A * Matrix.diagonal (fun j => (u j : K))).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    push_cast
    ring
  rw [h1]
  apply det_mem_of_entries
  intro i j
  rw [Matrix.mul_diagonal, mul_comm]
  exact hA i j
end PI.KerDetFinW

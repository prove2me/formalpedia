-- Prove2me | solution 1 for PIQnLT.sum_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:58:56.319529+00:00
-- url     : https://prove2.me/submissions/f82c1afb-21ab-4776-b3c2-ee658ff595c3

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzOutRight
import Theorems.Thm_PIQnLT_lev_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PIQnLT
theorem _root_.solution {M : Type*} [AddCommMonoid M] (f : Fin (2 * (i + r') + k + 1) → M)
    (h : ∀ p : Fin (2 * (i + r') + k + 1), ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) → f p = 0) :
    ∑ p, f p = ∑ j : Fin (2 * r' + k + 1), f (levPos k i r' j) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := levPos k i r') (fun x _ y _ e => lev_inj e)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro p _ hp
  apply h
  intro hc
  apply hp
  refine Finset.mem_image.2 ⟨⟨p.val - i, by omega⟩, Finset.mem_univ _, ?_⟩
  apply Fin.ext
  show p.val - i + i = p.val
  omega
end PIQnLT

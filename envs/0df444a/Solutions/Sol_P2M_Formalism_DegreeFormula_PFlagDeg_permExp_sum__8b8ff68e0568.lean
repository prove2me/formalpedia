-- Prove2me | solution 1 for P2M_Formalism_DegreeFormula_PFlagDeg_permExp_sum__8b8ff68e0568
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:46.623375+00:00
-- url     : https://prove2.me/submissions/77a1dd7e-4491-4a3a-9cde-62a01441be2a

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg
import Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_sum_perm_rev
import Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_permExp_apply

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
open Formalism Formalism.DegreeFormula
open Formalism.DegreeFormula.PFlagDeg
namespace Formalism.DegreeFormula.PFlagDeg
theorem _root_.solution {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) :
    ∑ x : ι × Fin N, permExp σ x = dimFl ι N := by
  rw [Fintype.sum_prod_type]
  simp only [permExp_apply, sum_perm_rev]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id, Finset.sum_const,
    Finset.card_univ, smul_eq_mul]
  rfl
end Formalism.DegreeFormula.PFlagDeg

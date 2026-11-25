-- Prove2me | solution 1 for PI.TOW.LiftW.main_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:45.480061+00:00
-- url     : https://prove2.me/submissions/15389305-b070-41f8-aece-9200fbeb12aa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_NotMemVarsEmbS
import Theorems.Thm_PI_TOW_LiftW_pderiv_prod_ne
import Theorems.Thm_PI_TOW_LiftW_opWord_liftW
import Theorems.Thm_PI_TOW_LiftW_opWord_append

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW PI.TOW.LiftW
open PI.TO PI.TOW
variable {K : Type} [CommRing K] {n' k : ℕ}
namespace PI.TOW.LiftW
theorem _root_.solution (w : Fin n' → List (Fin k × Fin k)) (G : Fin n' → MvPolynomial (Fin k) K)
    (ts : List (Fin n')) (hts : ts.Nodup) :
    opWord (ts.flatMap fun t => liftW t (w t)) (∏ s, embS K s (G s)) =
      ∏ s, embS K s (if s ∈ ts then word1 (w s) (G s) else G s) := by
  classical
  induction ts with
  | nil => simp [opWord]
  | cons t ts ih =>
    rw [List.nodup_cons] at hts
    rw [List.flatMap_cons, opWord_append, ih hts.2]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t),
      ← Finset.mul_prod_erase Finset.univ
        (fun s => embS K s (if s ∈ t :: ts then word1 (w s) (G s) else G s)) (Finset.mem_univ t)]
    simp only [if_neg hts.1, List.mem_cons, true_or, if_true]
    rw [opWord_liftW t (w t) (G t) _ (fun b' => pderiv_prod_ne t b' _ (Finset.notMem_erase t _) _)]
    congr 1
    refine Finset.prod_congr rfl fun s hs => ?_
    have hne : s ≠ t := Finset.ne_of_mem_erase hs
    simp [hne]
end PI.TOW.LiftW

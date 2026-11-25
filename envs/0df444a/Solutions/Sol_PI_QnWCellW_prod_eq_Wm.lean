-- Prove2me | solution 1 for PI.QnWCellW.prod_eq_Wm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:05.09457+00:00
-- url     : https://prove2.me/submissions/8ad0470c-51ac-4752-98db-b359ec858d9d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell
import Theorems.Thm_PI_QnWCellW_cN_val
import Theorems.Thm_PI_QnWCellW_Wm_empty
import Theorems.Thm_PI_QnWCellW_reflection_mul_weyl_cell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.QnWCellW.cN_val

set_option autoImplicit false
open Matrix Finset
open PI PI.QnWCellW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace PI.QnWCellW
theorem _root_.solution (k r : ℕ) (c : Fin r → ℂ) : ∀ L : List (Fin r), L.Nodup →
    (L.map fun a => w1 k r a (c a)).prod = Wm k r (L.map Fin.val).toFinset c
  | [], _ => by simpa using (Wm_empty k r c).symm
  | a :: L, h => by
      rw [List.map_cons, List.prod_cons, solution k r c L (List.nodup_cons.1 h).2, List.map_cons,
        List.toFinset_cons]
      apply reflection_mul_weyl_cell
      intro hm
      simp only [List.mem_toFinset, List.mem_map] at hm
      obtain ⟨b, hb, hba⟩ := hm
      have hba' : b = a := Fin.ext hba
      subst hba'
      exact (List.nodup_cons.1 h).1 hb
end PI.QnWCellW

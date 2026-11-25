-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.prod_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:20.145455+00:00
-- url     : https://prove2.me/submissions/a9e842e7-b169-410e-8e24-478884888e50

import Definitions.Def_Formalism_PeriodIntegrals_QmDefs
import Definitions.Def_Formalism_PeriodIntegrals_QmMove
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
import Theorems.Thm_Formalism_REAL_drop_ofFn_congr
import Theorems.Thm_Formalism_REAL_prod_ofFn_split_pair
import Theorems.Thm_Formalism_REAL_take_ofFn_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmMove
namespace PI.UnitaryGroupMassFormula.QmMove
theorem _root_.solution {A : Type*} [Ring A] {t : ℕ} (f g : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → g k = f k) :
    (List.ofFn f).prod - (List.ofFn g).prod =
      ((List.ofFn f).take i).prod *
        (f ⟨i, by omega⟩ * f ⟨i + 1, hi⟩ - g ⟨i, by omega⟩ * g ⟨i + 1, hi⟩) *
        ((List.ofFn f).drop (i + 2)).prod := by
  rw [prod_ofFn_split_pair f i hi, prod_ofFn_split_pair g i hi, take_ofFn_congr g f i (fun k hk => h k (by omega) (by omega)),
    drop_ofFn_congr g f (i + 2) (fun k hk => h k (by omega) (by omega))]
  noncomm_ring
end PI.UnitaryGroupMassFormula.QmMove

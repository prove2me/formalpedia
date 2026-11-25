-- Prove2me | solution 1 for QmCapCommW.hpart2_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:11.253077+00:00
-- url     : https://prove2.me/submissions/b2fb6dcd-1c7c-497d-b550-2130ad12402c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_CapelliOperatorCongruence
import Theorems.Thm_QmCapCommW_hpart2_skew
import Theorems.Thm_QmCapCommW_hpk_zero
import Theorems.Thm_QmCapCommW_col_zero
import Theorems.Thm_QmCapCommW_hpart_col
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open QmCapCommW
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace QmCapCommW
theorem _root_.solution {k r : ℕ} (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  refine ⟨hpart2_skew _ _ (hpkFacts k r).1 (hpkFacts k r).2.1, fun a' ha' => ⟨?_, ?_⟩⟩
  all_goals
    refine col_zero _ _ fun j => ?_
    unfold hpart2
    rw [Matrix.smul_apply, ← one_smul ℂ ((Hpk k r)⁻¹ * _ * _)]
  · rw [hpart_col a b _ (by simp only [posL, eI, ne_eq, Fin.ext_iff]; omega) (hpk_zero i a a' ha').1, smul_zero]
  · rw [hpart_col a b _ (by simp only [posL, esI, ne_eq, Fin.ext_iff]; have := b.isLt; unfold mdim at this; omega)
      (hpk_zero i a a' ha').2, smul_zero]
end QmCapCommW

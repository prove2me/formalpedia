-- Prove2me | solution 1 for PI.StabSplit.UnipW.herm_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:52.383612+00:00
-- url     : https://prove2.me/submissions/3eab18ab-635c-4397-8b55-c2326a911d45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.UnipW
namespace PI.StabSplit.UnipW
theorem _root_.solution {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (y z : Fin m → ℂ) (c : ℂ) :
    herm H (y - c • z) (y - c • z) =
      herm H y y - star c * herm H y z - c * herm H z y + c * star c * herm H z z := by
  unfold herm
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul, dotProduct_sub,
    sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring
end PI.StabSplit.UnipW

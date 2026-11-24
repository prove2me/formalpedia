-- Prove2me | solution 1 for PI.FJMS.idxN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:44.557862+00:00
-- url     : https://prove2.me/submissions/238a0178-98c0-48d4-bc39-cb56387aa68c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
import Theorems.Thm_PI_FJMS_neg_iff_nN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMS
open PI.FJM PI.FJMP
namespace PI.FJMS
theorem _root_.solution {n : ℕ} (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0)
    (i : Fin n) (h : f i < 0) : ∃ x : Fin (nN f), Fin.rev (Fin.castLE (nN_le f) x) = i := by
  have h1 := (neg_iff_nN f hseg i).1 h
  have h2 := i.isLt
  refine ⟨⟨n - 1 - i.val, by omega⟩, Fin.ext ?_⟩
  simp only [Fin.val_rev, Fin.val_castLE]
  omega
end PI.FJMS

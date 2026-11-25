-- Prove2me | solution 1 for PI.OmLocU.Nrm.norm_le_of_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:01:24.937042+00:00
-- url     : https://prove2.me/submissions/f604c7fb-67db-4fa8-a578-267e4c3d2b9d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LandherrUnitNorm_UnitNormLoc
import Definitions.Def_Lemmata_GeneralBFactLeft_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_NormLeOfNear
import Theorems.Thm_P2M_PI_Landherr__unitNormLoc_add_le_19ca89b64b37


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open PI.Landherr₃
open PI PI.OmLocU PI.OmLocU.Nrm
namespace PI.OmLocU.Nrm
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {z y₀ : K} (h : ‖z - y₀‖ < 1)
    (h0 : ‖y₀‖ ≤ 1) : ‖z‖ ≤ 1 := by
  have e : z = (z - y₀) + y₀ := by ring
  rw [e]; exact unitNormLoc_add_le h.le h0
end PI.OmLocU.Nrm

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionSmall_mkF_den_ne_zero_3d31e6ab25c8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:49.199818+00:00
-- url     : https://prove2.me/submissions/94f1392f-e70f-4de5-932b-8bd8c9867873

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PSectionSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionSmall
namespace GroundTheory.Heights₂.Heights.SectionSmall
theorem _root_.solution {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a) :
    P.mkF s.den ≠ 0 := fun h ↦ s.den_not_mem ((P.mkF_eq_zero_iff _).mp h)
end GroundTheory.Heights₂.Heights.SectionSmall

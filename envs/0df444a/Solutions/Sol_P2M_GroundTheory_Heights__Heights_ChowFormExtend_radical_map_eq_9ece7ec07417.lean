-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormExtend_radical_map_eq_9ece7ec07417
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:28.47891+00:00
-- url     : https://prove2.me/submissions/b61e9634-66db-43f1-bacb-df3bc6b85105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend

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
open GroundTheory.Heights₂.Heights.ChowFormExtend
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChowFormExtend
theorem _root_.solution (h : RadicalBaseChange.Statement) {K L : Type} [Field K] [PerfectField K]
    [Field L] (σ : K →+* L) {ι : Type} (J : Ideal (MvPolynomial ι K)) :
    (J.map (MvPolynomial.map σ)).radical = J.radical.map (MvPolynomial.map σ) :=
  le_antisymm
    ((h K L σ ι J.radical (Ideal.radical_isRadical J)).radical_le_iff.2
      (Ideal.map_mono Ideal.le_radical))
    (Ideal.map_radical_le _)
end GroundTheory.Heights₂.Heights.ChowFormExtend

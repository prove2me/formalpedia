-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormExtend_incidenceIdeal_map_8d93a5362789
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:24.128217+00:00
-- url     : https://prove2.me/submissions/61e61767-c97b-4e67-af06-7e0f6a66a27e

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
theorem _root_.solution {K L : Type*} [Field K] [Field L] (σ : K →+* L)
    (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ) :
    incidenceIdeal (I.map (MvPolynomial.map σ)) k =
      (incidenceIdeal I k).map (MvPolynomial.map σ) := by
  rw [incidenceIdeal, incidenceIdeal, Ideal.map_sup, Ideal.map_span]
  congr 1
  · rw [← Ideal.map_coe (rename Sum.inr), ← Ideal.map_coe (rename Sum.inr), Ideal.map_map, Ideal.map_map]
    congr 1
    apply ringHom_ext <;> intro <;> simp
  · congr 1
    ext p
    simp
end GroundTheory.Heights₂.Heights.ChowFormExtend

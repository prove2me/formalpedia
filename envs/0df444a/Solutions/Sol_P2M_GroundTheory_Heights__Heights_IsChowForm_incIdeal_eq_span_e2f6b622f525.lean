-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsChowForm_incIdeal_eq_span_e2f6b622f525
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:00.903861+00:00
-- url     : https://prove2.me/submissions/13cc5a62-7896-4f65-b798-049f9a0bc129

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PConeDimOfChowForm

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
namespace GroundTheory.Heights₂.Heights
namespace IsChowForm
theorem _root_.solution {F : Type*} [Field F] {n k : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm P k f) : incIdeal P k = Ideal.span {f} := by
  ext g
  rw [Ideal.mem_span_singleton, ← hf.2 g]
  simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker]
end IsChowForm
end GroundTheory.Heights₂.Heights

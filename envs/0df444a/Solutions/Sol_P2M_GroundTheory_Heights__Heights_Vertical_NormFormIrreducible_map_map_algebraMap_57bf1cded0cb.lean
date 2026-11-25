-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_map_map_algebraMap_57bf1cded0cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:23:27.821007+00:00
-- url     : https://prove2.me/submissions/1be0ac04-095a-4a38-9178-677c18834ede

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
variable {E L K : Type*} [Field E] [Field L] [Field K] [Algebra E L] [Algebra E K] {n : ℕ}
  {x : Fin n → L} {t : Fin n → E}
namespace GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
theorem _root_.solution (τ : K →ₐ[E] K) (p : MvPolynomial (Fin n) E) :
    (p.map (algebraMap E K)).map (τ : K →+* K) = p.map (algebraMap E K) := by
  rw [MvPolynomial.map_map, AlgHom.comp_algebraMap]
end GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible

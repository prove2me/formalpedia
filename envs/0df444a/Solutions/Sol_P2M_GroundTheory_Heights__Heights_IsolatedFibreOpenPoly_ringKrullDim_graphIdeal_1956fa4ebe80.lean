-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_ringKrullDim_graphIdeal_1956fa4ebe80
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:56:36.52985+00:00
-- url     : https://prove2.me/submissions/243b6a71-5eb2-42c2-a3d2-d739b64086a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphSubst_surjective_da448e31549d

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
open MvPolynomial Topology Filter Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
theorem _root_.solution (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + d)) ℂ ⧸ graphIdeal P p) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := by
  set f : MvPolynomial (Fin (n + d)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ P :=
    (Ideal.Quotient.mk P).comp (graphSubst p).toRingHom with hf
  have hsurj : Function.Surjective f :=
    Ideal.Quotient.mk_surjective.comp (graphSubst_surjective p)
  have hker : graphIdeal P p = RingHom.ker f := by
    rw [hf, ← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  exact ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj))
end GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly

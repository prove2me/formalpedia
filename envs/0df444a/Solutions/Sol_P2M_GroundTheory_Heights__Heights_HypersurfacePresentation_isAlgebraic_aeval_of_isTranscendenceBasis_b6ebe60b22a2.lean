-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_isAlgebraic_aeval_of_isTranscendenceBasis_b6ebe60b22a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:52.290062+00:00
-- url     : https://prove2.me/submissions/ccf097d0-6980-4cba-9822-970da2d27e29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation

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
open GroundTheory.Heights₂.Heights.HypersurfacePresentation
namespace GroundTheory.Heights₂.Heights.HypersurfacePresentation
theorem _root_.solution {S A : Type} [CommRing S] [Nontrivial S] [CommRing A]
    [Algebra S A] {d : ℕ} {y : Fin d → A} (hb : IsTranscendenceBasis S y) :
    letI := (MvPolynomial.aeval (R := S) y).toRingHom.toAlgebra
    Algebra.IsAlgebraic (MvPolynomial (Fin d) S) A := by
  let _ : Algebra (MvPolynomial (Fin d) S) A := (MvPolynomial.aeval (R := S) y).toRingHom.toAlgebra
  have := hb.isAlgebraic
  have h : (algebraMap (MvPolynomial (Fin d) S) A).comp (hb.1.aevalEquiv.symm : _ →+* _) =
      (RingHom.id A).comp (algebraMap (Algebra.adjoin S (Set.range y)) A) := RingHom.ext fun z => by
    show MvPolynomial.aeval y (hb.1.aevalEquiv.symm z) = (z : A)
    rw [← hb.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
    rfl
  exact ⟨fun a => (isAlgebraic_ringHom_iff_of_comp_eq hb.1.aevalEquiv.symm (RingHom.id A)
    Function.injective_id h).2 (Algebra.IsAlgebraic.isAlgebraic a)⟩
end GroundTheory.Heights₂.Heights.HypersurfacePresentation

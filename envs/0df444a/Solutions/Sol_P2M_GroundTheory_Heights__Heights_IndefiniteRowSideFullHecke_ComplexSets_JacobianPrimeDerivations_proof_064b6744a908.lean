-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_JacobianPrimeDerivations_proof_064b6744a908
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:59:13.020805+00:00
-- url     : https://prove2.me/submissions/14bbbca5-b3d8-4ce1-9f05-7f198684b4c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StJacobianPrimeDerivations
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyDerivationsDetectSquare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCotangentBasisInPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationMinorOfDetection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGeneratorsClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PJacobianPrimeDerivations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace JacobianPrimeDerivations
theorem _root_.solution (hDetect : PolyDerivationsDetectSquare.Statement)
    (hBasis : CotangentBasisInPrime.Statement) (hMinor : DerivationMinorOfDetection.Statement)
    (hClear : LocalGeneratorsClearDenominators.Statement) : JacobianPrimeDerivations.Statement := by
  intro k _ n p hp
  obtain ⟨h, f, hfp, hspan, hind⟩ := hBasis (MvPolynomial (Fin n) k) p
  obtain ⟨D, hD⟩ := hMinor (MvPolynomial (Fin n) k) p h f hfp hind
    (fun g hg hDg => hDetect k n p g hg hDg)
  obtain ⟨s, hs, hsp⟩ := hClear (MvPolynomial (Fin n) k) p h f hfp hspan
  exact ⟨h, f, D, s, hfp, hs, hsp, hD⟩
end JacobianPrimeDerivations
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

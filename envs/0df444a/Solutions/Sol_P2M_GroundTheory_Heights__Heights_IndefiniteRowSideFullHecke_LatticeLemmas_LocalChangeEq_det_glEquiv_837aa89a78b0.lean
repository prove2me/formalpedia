-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LatticeLemmas_LocalChangeEq_det_glEquiv_837aa89a78b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:09.74663+00:00
-- url     : https://prove2.me/submissions/f6992df5-c9f2-4ba4-95c8-ca0f438178cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LatticeOfLocalisationsHyps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LocalChangeOfVectorSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct IsDedekindDomain
  GroundTheory.Heights₂.Heights.ComplexAt
universe u v
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas.LocalChangeEq
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {r : ℕ} (φ : V ≃ₗ[K] (Fin r → K))
variable (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas.LocalChangeEq
theorem _root_.solution (g : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
    LinearMap.det (glEquiv v g : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _) =
      (g : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det :=
  LinearMap.det_toLin' _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas.LocalChangeEq

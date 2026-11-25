-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_PrimesToPts_comap_toSpec__ae60923711e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:39.488644+00:00
-- url     : https://prove2.me/submissions/4294eb7c-f2b2-4619-81fb-204e1d7316e8

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_BasicOpenNormFibreIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesToPts
namespace GlobalTheory.CompanionTheory.PrimesToPts
theorem _root_.solution {P D : Scheme.{0}} (v : P ⟶ D) (z : P) :
    (P.toSpecΓ z : PrimeSpectrum Γ(P, ⊤)).asIdeal.comap v.appTop.hom =
      (D.toSpecΓ (v z) : PrimeSpectrum Γ(D, ⊤)).asIdeal := by
  have h : D.toSpecΓ (v z) = Spec.map v.appTop (P.toSpecΓ z) := by
    rw [← Scheme.Hom.comp_apply, Scheme.toSpecΓ_naturality, Scheme.Hom.comp_apply]
  rw [h]
  rfl
end GlobalTheory.CompanionTheory.PrimesToPts

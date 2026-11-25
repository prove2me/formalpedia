-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_PrimesToPts_mem_basicOpen_iff_toSpec__539c058bfd78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:41.087266+00:00
-- url     : https://prove2.me/submissions/39d81712-d969-400b-9a85-f73eec5cc7d5

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
theorem _root_.solution {X : Scheme.{0}} (f : Γ(X, ⊤)) (x : X) :
    x ∈ X.basicOpen f ↔ f ∉ (X.toSpecΓ x : PrimeSpectrum Γ(X, ⊤)).asIdeal := by
  rw [← X.toSpecΓ_preimage_basicOpen f]
  exact Iff.rfl
end GlobalTheory.CompanionTheory.PrimesToPts

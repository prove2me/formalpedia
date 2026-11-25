-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_localLattice_baseChange_37285dfb9883
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:36:54.207001+00:00
-- url     : https://prove2.me/submissions/db88826c-3208-4731-b0dd-8d48dafdb198

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples

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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (e : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V)
    (he : L.map (e.toLinearMap.restrictScalars (𝓞 K)) = L) :
    (localLattice v L : Set (v.adicCompletion K ⊗[K] V)) =
      e.baseChange K (v.adicCompletion K) V V '' localLattice v L := by
  set f := ((e.baseChange K (v.adicCompletion K) V V).toLinearMap.restrictScalars
    (v.adicCompletionIntegers K))
  have hf : ∀ x : V, f (toLocal v x) = toLocal v (e x) := fun x ↦ rfl
  change _ = (f : _ → _) '' _
  rw [← Submodule.map_coe, localLattice, Submodule.map_span, Set.image_image]
  simp only [hf]
  have hL : (e : V → V) '' (L : Set V) = L := by
    conv_rhs => rw [← he]
    rw [Submodule.map_coe]
    rfl
  rw [← Set.image_image (toLocal v) (e : V → V), hL]
end GroundTheory.Heights₂.Heights

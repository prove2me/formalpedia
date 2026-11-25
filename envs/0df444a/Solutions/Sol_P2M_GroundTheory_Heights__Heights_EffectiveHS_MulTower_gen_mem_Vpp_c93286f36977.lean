-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_gen_mem_Vpp_c93286f36977
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:26:37.084742+00:00
-- url     : https://prove2.me/submissions/76fcc34f-4c0d-48f7-8e1f-2bf86d052d80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision

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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (τ : MulTower R A)
variable {D : ℕ} {s : Fin D → A}
namespace GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
theorem _root_.solution {T a₀ : ℕ} (α : Fin D → ℕ) {k : ℕ} (w : Fin k → A)
    (hw : ∀ i, w i ∈ τ.W) {m : A} (hm : m ∈ τ.V 0) (hT : ∑ i, α i + k = T)
    (ha : ∑ i, α i ≤ a₀) : mono s α * (∏ i, w i) * m ∈ τ.Vpp D T a₀ s :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨α, k, w, m, hw, hm, hT, ha, rfl⟩)
end GroundTheory.Heights₂.Heights.EffectiveHS.MulTower

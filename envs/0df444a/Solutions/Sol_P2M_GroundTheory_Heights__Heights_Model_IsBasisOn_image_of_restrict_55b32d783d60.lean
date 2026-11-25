-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_image_of_restrict_55b32d783d60
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:03.529741+00:00
-- url     : https://prove2.me/submissions/0d4b0fd8-7977-409e-a666-4a138a413a96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.Model
namespace IsBasisOn
theorem _root_.solution {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) {W : Y.Opens} {n : ℕ} {s : Fin n → Γ(M.restrict f, W)}
    (hs : IsBasisOn (M.restrict f) W s) :
    IsBasisOn M (f ''ᵁ W) (fun i => (M.restrictAppIso f W).hom (s i)) := by
  intro V h
  obtain ⟨V', rfl⟩ : ∃ V' : Y.Opens, f ''ᵁ V' = V :=
    ⟨f ⁻¹ᵁ V, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right]
      exact h.trans (f.image_le_opensRange W)⟩
  have hV' : V' ≤ W := by
    rw [← f.preimage_image_eq V', ← f.preimage_image_eq W]
    exact f.preimage_mono h
  have key : (fun r : Fin n → Γ(X, f ''ᵁ V') =>
      ∑ i, r i • (M.presheaf.map (homOfLE h).op).hom ((M.restrictAppIso f W).hom (s i))) =
      (fun r' : Fin n → Γ(Y, V') =>
        ∑ i, r' i • ((M.restrict f).presheaf.map (homOfLE hV').op).hom (s i)) ∘
        (fun r i => (f.appIso V').hom.hom (r i)) := by
    funext r
    simp only [Function.comp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ = ((f.appIso V').inv.hom ((f.appIso V').hom.hom (r i)) : Γ(X, f ''ᵁ V')) •
      (M.presheaf.map (homOfLE h).op).hom ((M.restrictAppIso f W).hom (s i))
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  rw [key]
  refine (hs V' hV').comp ?_
  exact (Equiv.piCongrRight fun _ => (f.appIso V').commRingCatIsoToRingEquiv.toEquiv).bijective
end IsBasisOn
end GroundTheory.Heights₂.Heights.Model

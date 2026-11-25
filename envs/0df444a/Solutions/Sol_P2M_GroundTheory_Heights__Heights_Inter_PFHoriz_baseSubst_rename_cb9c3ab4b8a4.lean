-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_baseSubst_rename_cb9c3ab4b8a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:53:12.970981+00:00
-- url     : https://prove2.me/submissions/78684581-d499-46f4-97d5-c8d555b4b8ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFHoriz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PFHoriz
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
namespace GroundTheory.Heights₂.Heights.Inter.PFHoriz
theorem _root_.solution (hκv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι) :
    baseSubst κ G (rename v f) = C (aeval G.x f) := by
  have e : (baseSubst κ G).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom =
      (C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (((baseSubst κ G).comp
        (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom).comp C)
        (((C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp
          (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom).comp C)) a
    · have h1 : (v p).1 ∈ Set.range κ := ⟨p.1, (hκv.2.2.1 p).symm⟩
      have h2 : v p ∈ Set.range v := ⟨p, rfl⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, aeval_X]
      rw [baseSubst, eval₂Hom_X', dif_pos h1, dif_pos h2, hκv.2.1 h2.choose_spec]
  exact RingHom.congr_fun e f
end GroundTheory.Heights₂.Heights.Inter.PFHoriz

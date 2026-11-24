-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_baseSubst_rename_49ffc4fb7581
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:45.493844+00:00
-- url     : https://prove2.me/submissions/b4507678-3cfd-48f1-bb4d-f3598c7ab55d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreMult

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
omit [Fintype K'] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof
theorem _root_.solution (hv : IsBlockMap κ v) (G : GenFibre v P') (t : MRing ι) :
    baseSubst κ G (rename v t) = C (aeval G.x t) := by
  have h : (baseSubst κ G).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom =
      (C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [show (C r : MRing ι) = (r : MRing ι) from eq_intCast C r, map_intCast]
    · intro p
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, aeval_X]
      unfold baseSubst
      rw [eval₂Hom_X']
      have h1 : (v p).1 ∈ Set.range κ := ⟨p.1, (hv.2.2.1 p).symm⟩
      have h2 : v p ∈ Set.range v := ⟨p, rfl⟩
      rw [dif_pos h1, dif_pos h2, hv.2.1 h2.choose_spec]
  exact DFunLike.congr_fun h t
end GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof

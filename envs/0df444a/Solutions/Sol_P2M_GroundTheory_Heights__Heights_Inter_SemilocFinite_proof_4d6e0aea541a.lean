-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocFinite_proof_4d6e0aea541a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:02:33.621212+00:00
-- url     : https://prove2.me/submissions/2346f2be-16a8-4117-aef9-f9b1c31f8913

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingIntClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_semiLocRing_le_empty_1422200f6aab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
namespace GroundTheory.Heights₂.Heights.Inter
namespace SemilocFinite
theorem _root_.solution (h₁ : SemilocIntegral.Statement) (h₂ : LocRingIntClosureFinite.Statement)
    (h₃ : LocRingDimOne.Statement) : SemilocFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ hs hsQ hW
  have := hP'.2.1.1
  let _ := (locToSemiloc hv P' W).toAlgebra
  have hN : IsNoetherianRing (locRing (imageZ v P') W) := (h₃ K ι (imageZ v P') s α W hQ.2.1 hs hsQ hW).1
  have hint := h₁ K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW
  refine ⟨?_, ?_⟩
  · let _ := ((fracMapZ v P').comp (locRing (imageZ v P') W).subtype).toAlgebra
    let _ : Module (locRing (imageZ v P') W) (FractionRing (MRing ι' ⧸ P')) := Algebra.toModule
    obtain ⟨t, ht⟩ := h₂ K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW
    let g : semiLocRing P' (fibreOver v P' W) →ₗ[locRing (imageZ v P') W] FractionRing (MRing ι' ⧸ P') :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hg : ∀ b, g b ∈ Submodule.span (locRing (imageZ v P') W) (t : Set (FractionRing (MRing ι' ⧸ P'))) :=
      fun b => ht _ (semiLocRing_le_empty P' _ b.2)
        ((hint.isIntegral b).map_of_comp_eq (RingHom.id (locRing (imageZ v P') W)) (semiLocRing P' (fibreOver v P' W)).subtype
          (RingHom.ext fun _ => rfl))
    have : IsNoetherian (locRing (imageZ v P') W)
        (Submodule.span (locRing (imageZ v P') W) (t : Set (FractionRing (MRing ι' ⧸ P')))) :=
      isNoetherian_span_of_finite _ t.finite_toSet
    exact Module.Finite.of_injective (g.codRestrict _ hg)
      fun b c hbc => by
        have h := congrArg Subtype.val hbc
        exact Subtype.ext h
  · have := imageZ_isPrime_of_prime v P'
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro a b hab
    exact Subtype.val_injective ((fracMapZ v P').injective (congrArg Subtype.val hab))
end SemilocFinite
end GroundTheory.Heights₂.Heights.Inter

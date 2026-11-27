-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocIntegral_proof_45390e266a45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:50.394991+00:00
-- url     : https://prove2.me/submissions/7fedf78a-bc2b-4cc6-9359-aca6181e1718

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StValCentreZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StCentreOverW
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocIntegral

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
namespace SemilocIntegral
theorem _root_.solution (h₁ : ValCentreZ.Statement) (h₂ : CentreOverW.Statement) :
    SemilocIntegral.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hP hs hsP hW
  have := hP'.2.1.1
  letI := (locToSemiloc hv P' W).toAlgebra
  let f : locRing (imageZ v P') W →+* FractionRing (MRing ι' ⧸ P') :=
    (semiLocRing P' (fibreOver v P' W)).subtype.comp (locToSemiloc hv P' W)
  refine ⟨fun b => ?_⟩
  refine RingHom.IsIntegralElem.of_map (g := (semiLocRing P' (fibreOver v P' W)).subtype)
    Subtype.val_injective ?_
  have hmem : (b : FractionRing (MRing ι' ⧸ P')) ∈ ⨅ V : {V : ValuationSubring
      (FractionRing (MRing ι' ⧸ P')) // Set.range f ⊆ V.toSubring}, V.1.toSubring := by
    rw [Subring.mem_iInf]
    rintro ⟨V, hV⟩
    obtain ⟨y, hy⟩ := h₁ K' ι' P' hP'.2.1 V
    have hcase := h₂ K ι K' ι' κ v P' n s α W hv hP' hP hs hsP hW V
      (fun a ha => hV ⟨⟨a, ha⟩, rfl⟩) y hy
    have hle : semiLocRing P' (fibreOver v P' W) ≤ V.toSubring := by
      rw [semiLocRing, Subring.closure_le]
      rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
      have hwy : w ∉ y := by
        rcases hcase with rfl | hy'
        · exact fun h => nonZeroDivisors.ne_zero hw (Ideal.Quotient.eq_zero_iff_mem.mpr h)
        · exact hwW y hy'
      rw [SetLike.mem_coe, IsFractionRing.mk'_eq_div]
      exact (hy.2.2 a u w hu hwa hwy).1
    exact hle b.2
  rw [iInf_valuationSubring_superset, ← RingHom.coe_range, Subring.closure_eq] at hmem
  obtain ⟨p, hp, hpx⟩ := (hmem : IsIntegral f.range (b : FractionRing (MRing ι' ⧸ P')))
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts p).mpr
      (Polynomial.map_surjective f.rangeRestrict (fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩) p)) hp
  refine ⟨q, hqm, ?_⟩
  change Polynomial.eval₂ (f.range.subtype.comp f.rangeRestrict) (b : FractionRing _) q = 0
  rw [← Polynomial.eval₂_map, hq]
  exact hpx
end SemilocIntegral
end GroundTheory.Heights₂.Heights.Inter

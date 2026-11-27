-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionDivisorPushforward_proof_4a1db152f008
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:02:23.684535+00:00
-- url     : https://prove2.me/submissions/c7f49b55-d5af-4c76-9349-6556b1e32cb4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IdDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocLength
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_exists_form_notMem_9e34f112a8d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_locIdeal_eq_span_6d401f7ea2c7
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_dimOneTorsionFreeFormula
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_krullDimLE_one_of_krullDim_eq


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Inter
namespace ArithmeticIntersectionDivisorPushforward
theorem _root_.solution (hDeh : regularityDehomogenization_holds.Statement) (hLoc : LocRingDimOne.Statement)
    (hFin : SemilocFinite.Statement) (hRank : SemilocRank.Statement) (hLen : SemilocLength.Statement) :
    ArithmeticIntersectionDivisorPushforward.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J s α W E hv hP' hP hJ hs hsP hW hE
  have : P'.IsPrime := hP'.2.1.1
  have : (imageZ v P').IsPrime := hP.2.1.1

  obtain ⟨t, ht, htW⟩ := exists_form_notMem hW.2 hW.1.1.1 α
  have ht0 : algebraMap (MRing ι ⧸ imageZ v P') (FractionRing (MRing ι ⧸ imageZ v P'))
      (Ideal.Quotient.mk _ t) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => htW (hW.1.1.2 (Ideal.mem_sup_left h))
  set y : FractionRing (MRing ι ⧸ imageZ v P') := algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) /
    algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) with hy
  have hyt : y * algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) =
      algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) := div_mul_cancel₀ _ ht0
  obtain ⟨hyA, hm⟩ := hDeh K ι (imageZ v P') s t α W y hP.2.1 hs hsP hW ht htW hyt
  obtain ⟨hNoeth, hLocal, hDim⟩ := hLoc K ι (imageZ v P') s α W hP.2.1 hs hsP hW
  let _ : Algebra (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) := (locToSemiloc hv P' W).toAlgebra
  obtain ⟨hBf, hBt⟩ := hFin K ι K' ι' κ v P' n s α W hv hP' hP hs hsP hW
  have hrk := hRank K ι K' ι' κ v P' n G J s α W hv hP' hP hJ hs hsP hW
  obtain ⟨N, hlen, hN⟩ := hLen K ι K' ι' κ v P' n s t α W E hv hP' ⟨y, hyA⟩ hP hs ht hsP hW htW hyt hE
  have hy0 : (⟨y, hyA⟩ : locRing (imageZ v P') W) ≠ 0 := fun h => by
    have h' : y = 0 := congrArg Subtype.val h
    rw [hy, div_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h'
    exact h'.elim hsP ht0

  have := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hDim
  have key := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula _ (semiLocRing P' (fibreOver v P' W)) ⟨y, hyA⟩ hDim hy0
  have hord : Ring.ord (locRing (imageZ v P') W) ⟨y, hyA⟩ =
      (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℕ∞) := by
    have hfin := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hy0)
    rw [hm, locIdeal_eq_span hyA]
    exact (ENat.natCast_toNat hfin).symm
  rw [hlen, hord] at key
  have hNat : N = Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) *
      multAt (imageZ v P' ⊔ Ideal.span {s}) W := by
    exact_mod_cast key
  rw [← hN, hNat, ← hrk]
  push_cast
  rfl
end ArithmeticIntersectionDivisorPushforward
end GroundTheory.Heights₂.Heights.Inter

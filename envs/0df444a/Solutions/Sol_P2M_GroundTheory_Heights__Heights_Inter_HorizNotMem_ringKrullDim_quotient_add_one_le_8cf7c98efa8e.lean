-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_HorizNotMem_ringKrullDim_quotient_add_one_le_8cf7c98efa8e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:23.884807+00:00
-- url     : https://prove2.me/submissions/9cd3dfa7-987b-461a-9c8b-55bef8224a55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Inter
namespace HorizNotMem
theorem _root_.solution {R : Type*} [CommRing R] {W₀ W : Ideal R}
    [hW₀ : W₀.IsPrime] [hW : W.IsPrime] (hlt : W₀ < W) :
    ringKrullDim (R ⧸ W) + 1 ≤ ringKrullDim (R ⧸ W₀) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) W) :=
    ⟨⟨⟨W, hW⟩, fun _ h => h⟩⟩
  rw [← Order.krullDim_withBot]
  let f : WithBot (PrimeSpectrum.zeroLocus (R := R) W) → PrimeSpectrum.zeroLocus (R := R) W₀ :=
    fun x => WithBot.recBotCoe ⟨⟨W₀, hW₀⟩, fun _ h => h⟩ (fun q => ⟨q.1, fun _ h => q.2 (hlt.le h)⟩) x
  refine Order.krullDim_le_of_strictMono f ?_
  intro a b hab
  induction a using WithBot.recBotCoe with
  | bot =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd hab (lt_irrefl _)
    | coe q =>
      change (⟨⟨W₀, hW₀⟩, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩
      exact Subtype.mk_lt_mk.mpr ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp
        (hlt.trans_le (fun _ h => q.2 h)))
  | coe p =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd hab (WithBot.not_lt_bot _)
    | coe q =>
      change (⟨p.1, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩
      exact Subtype.mk_lt_mk.mpr (Subtype.mk_lt_mk.mp (WithBot.coe_lt_coe.mp hab))
end HorizNotMem
end GroundTheory.Heights₂.Heights.Inter

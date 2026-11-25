-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_not_lt_lt_9447da08df4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:57:51.913837+00:00
-- url     : https://prove2.me/submissions/7e61562a-d479-4f55-93b6-9d23d31100c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwapCyclesArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSwapCycles

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
  ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
namespace GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
theorem _root_.solution {R : Type*} [CommRing R] [IsNoetherianRing R] {V W W' : Ideal R} [V.IsPrime]
    [W'.IsPrime] {x : R} (hW : W ∈ (V ⊔ Ideal.span {x}).minimalPrimes) (hVW' : V < W')
    (hW'W : W' < W) : False := by
  have hWp : W.IsPrime := hW.isPrime
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  set q := Ideal.Quotient.mk V
  have hker : RingHom.ker q = V := Ideal.mk_ker
  have hW'm : (W'.map q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [hker]; exact hVW'.le)
  have hWm : (W.map q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [hker]; exact hVW'.le.trans hW'W.le)
  have hlt : W'.map q < W.map q := by
    refine lt_of_le_of_ne (Ideal.map_mono hW'W.le) fun he => hW'W.ne ?_
    have := congrArg (Ideal.comap q) he
    rwa [Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective, hker,
      sup_eq_left.mpr hVW'.le, sup_eq_left.mpr (hVW'.le.trans hW'W.le)] at this
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h0 : (W'.map q).height = 0 := by
    have h3 := h2.trans h1
    generalize (W'.map q).height = a at h3
    cases a with
    | top => simp at h3
    | coe a => norm_cast at h3 ⊢; omega
  haveI : IsDomain (R ⧸ V) := Ideal.Quotient.isDomain V
  rw [Ideal.height_eq_zero_iff_eq_bot] at h0
  apply hVW'.ne
  apply le_antisymm hVW'.le
  intro y hy
  have : q y ∈ W'.map q := Ideal.mem_map_of_mem q hy
  rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this
end GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt

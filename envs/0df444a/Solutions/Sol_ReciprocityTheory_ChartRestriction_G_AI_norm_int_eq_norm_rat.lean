-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.norm_int_eq_norm_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:31:24.805837+00:00
-- url     : https://prove2.me/submissions/caefa2f1-8c9c-4bb4-ac4b-668b8bf52675

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_IndexSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CardQuotEqNatAbsNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (O : Subring K)
    [Module.Free ℤ O] [Module.Finite ℤ O] (h : Module.finrank ℤ O = Module.finrank ℚ K)
    (f : O) : ((Algebra.norm ℤ f : ℤ) : ℚ) = Algebra.norm ℚ (f : K) := by
  classical
  let b := Module.Free.chooseBasis ℤ O
  have hli : LinearIndependent ℚ (fun i => ((b i : O) : K)) := by
    have h1 : LinearIndependent ℤ (fun i => ((b i : O) : K)) :=
      b.linearIndependent.map' (O.subtype.toIntAlgHom.toLinearMap)
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ O) = Module.finrank ℚ K := by
    rw [← h, Module.finrank_eq_card_chooseBasisIndex]
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℤ O) := by
    apply Fintype.card_pos_iff.mp
    rw [hcard]
    exact Module.finrank_pos
  let b' := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb' : ∀ i, b' i = ((b i : O) : K) := fun i => by
    simp only [b', coe_basisOfLinearIndependentOfCardEqFinrank]
  rw [Algebra.norm_eq_matrix_det b f, Algebra.norm_eq_matrix_det b' (f : K)]
  have hm := RingHom.map_det (Int.castRingHom ℚ) (Algebra.leftMulMatrix b f)
  rw [show ((Algebra.leftMulMatrix b f).det : ℚ) = (Int.castRingHom ℚ) (Algebra.leftMulMatrix b f).det from rfl, hm]
  congr 1
  ext i j
  have hx : (f : K) * b' j = ∑ k, ((b.repr (f * b j) k : ℤ) : ℚ) • b' k := by
    have e1 := congrArg (O.subtype.toIntAlgHom.toLinearMap) (b.sum_repr (f * b j))
    rw [map_sum] at e1
    simp only [map_zsmul] at e1
    simp only [hb', Int.cast_smul_eq_zsmul]
    exact e1.symm
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, eq_intCast]
  rw [hx, b'.repr_sum_self]
end ReciprocityTheory.ChartRestriction.G.AI

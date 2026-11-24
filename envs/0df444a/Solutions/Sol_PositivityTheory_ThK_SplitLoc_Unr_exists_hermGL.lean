-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.exists_hermGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:25:50.353912+00:00
-- url     : https://prove2.me/submissions/ec921464-8019-472a-b529-0566fa034275

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_GlobalTheory_SatakeBound_exists_hermMat
import Theorems.Thm_GlobalTheory_SatakeBound_val_hermGL
import Theorems.Thm_GlobalTheory_SplitWeil_iwasawa_blockTriangular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
open GlobalTheory.SatakeBound
omit [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {p : 𝒪[k]} (hp : Irreducible p) {n : ℕ} {g : GL (Fin n) k} (hg : ∀ i j, g.val i j ∈ 𝒪[k]) :
    ∃ (a : Fin n → ℕ) (c : HermIdx p a), (hermGL hp a c)⁻¹ * g ∈ KO k (Fin n) := by
  obtain ⟨b, hb, w, hw, e⟩ := iwasawa_blockTriangular k (Fin n) Fin.val g
  have hb' : ∀ i j, b.val i j ∈ 𝒪[k] := fun i j => by
    rw [eq_mul_inv_of_mul_eq e.symm, Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => mul_mem (hg _ _) (((mem_KO_iff _).1 hw).2 _ _)
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨b.val i j, hb' i j⟩
  have hB : b.val = (algebraMap 𝒪[k] k).mapMatrix B := rfl
  have h1 : ∀ i j, j < i → B i j = 0 := fun i j h => Subtype.ext (hb h)
  have hd : B.det ≠ 0 := fun h => b.det_ne_zero (by rw [hB, ← RingHom.map_det, h, map_zero])
  rw [Matrix.det_of_isUpperTriangular (M := B) fun _ _ h => h1 _ _ h, Finset.prod_ne_zero_iff] at hd
  obtain ⟨a, c, U, hU⟩ := exists_hermMat hp B h1 fun i => hd i (Finset.mem_univ i)
  have : hermGL hp a c = b * Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) U := by
    apply Units.ext
    rw [val_hermGL, hU, map_mul, ← hB]
    rfl
  refine ⟨a, c, ?_⟩
  rw [this, e, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  exact mul_mem (inv_mem (MonoidHom.mem_range.2 ⟨U, rfl⟩)) hw
end PositivityTheory.ThK.SplitLoc.Unr

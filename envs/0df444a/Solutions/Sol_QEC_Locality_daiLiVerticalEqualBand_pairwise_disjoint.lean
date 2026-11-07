-- Prove2me | solution 1 for QEC.Locality.daiLiVerticalEqualBand_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:27:20.438189+00:00
-- url     : https://prove2.me/submissions/fd1f7982-26d1-41b9-909f-e8396b02210b

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
omit [Fintype ι]
namespace QEC.Locality
theorem _root_.solution
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lower upper : ℝ} {m : Nat} (hM : 0 < m) (hSpan : 0 < upper - lower) :
    ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (daiLiVerticalEqualBand embedding region lower upper m) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro i hi j hj hij
  by_contra hneq
  obtain ⟨q, hq⟩ := hij
  have hqi := (Finset.mem_inter.mp hq).1
  have hqj := (Finset.mem_inter.mp hq).2
  have hStep : 0 < (upper - lower) / (m : ℝ) := by
    apply div_pos hSpan
    exact_mod_cast hM
  have hqiBounds := (Finset.mem_filter.mp hqi).2
  have hqjBounds := (Finset.mem_filter.mp hqj).2
  rcases lt_or_gt_of_ne hneq with hij | hji
  · have hIndexNat : i.val + 1 ≤ j.val := Nat.succ_le_iff.mpr hij
    have hIndex : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hIndexNat
    nlinarith
  · have hIndexNat : j.val + 1 ≤ i.val := Nat.succ_le_iff.mpr hji
    have hIndex : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hIndexNat
    nlinarith
end QEC.Locality

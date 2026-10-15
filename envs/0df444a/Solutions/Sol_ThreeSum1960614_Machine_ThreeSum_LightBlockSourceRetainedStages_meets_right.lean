-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages.meets_right
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:34:42.460614+00:00
-- url     : https://prove2.me/submissions/fe0cdbff-6026-47fa-9fc6-ccad3d748219

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BlockIndex_maskHash_right
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceRetainedStages_Procs_meets
import Theorems.Thm_ThreeSum_OneHotMask_eval_le

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightBlockSourceRetainedStages
end ThreeSum.LightBlockSourceRetainedStages
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.OneHotMask
end ThreeSum1960614.Machine.ThreeSum.OneHotMask
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram
open _root_.ThreeSum.LightHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





theorem count_le (key : ℕ → ℕ) (r i : ℕ) : _root_.ThreeSum.LightHistogram.count key r i ≤ i := by
  exact (Finset.card_filter_le _ _).trans (by simp)















end ThreeSum.LightHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues
open _root_.ThreeSum.LightResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (_root_.ThreeSum.LightResidues.residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

















end ThreeSum.LightResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask
open _root_.ThreeSum.OneHotMask


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false











@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    _root_.ThreeSum.OneHotMask.extend f i.val = f i := by simp [_root_.ThreeSum.OneHotMask.extend, i.isLt]









end ThreeSum.OneHotMask

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Reading constructed block coefficients in the flat mask order

The imperative coefficient constructor writes rows. The mask evaluator reads
one flat array. These lemmas identify the two layouts, including empty ground
sets, and specialize them to the unchanged schedule-occurrence encoding.
-/

namespace ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.BlockCoefficientRows


open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds





theorem flat_le {J L p U M : ℕ} {sel : ℕ → ℕ} {w : ℕ → ℕ → ℕ}
    (hp : 1 ≤ p) (hsel : ∀ j < J, sel j < M)
    (hbound : ∀ s < M, ∀ i < L, w s i ≤ U) {i : ℕ} (hi : i < J*L) :
    _root_.ThreeSum.BlockCoefficientRows.flat J L p sel w i ≤ p^J*U := by
  let c := (_root_.ThreeSum.BlockIndex.coordEquiv J L).symm ⟨i,hi⟩
  change (if h : i < J*L then _ else 0) ≤ _
  rw [dif_pos hi]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right hp (Nat.le_of_lt c.1.isLt))
    (hbound _ (hsel _ c.1.isLt) _ c.2.isLt)



@[simp] theorem occurrenceIndices_fin {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (i : Fin J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o i.val = (o i).val := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.extend_fin _ i



@[simp] theorem mapRow_fin {h : ℕ} (b : Bool) (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) (i : Fin (464*h)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h b s.val i.val = (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h s (i,b)).val := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow,s.isLt,dite_true,_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.extend_fin]

theorem occurrenceIndices_lt {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) {j : ℕ} (hj : j < J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o j < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h := by
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices_fin o ⟨j,hj⟩).trans_lt (o ⟨j,hj⟩).isLt

theorem mapRow_le {h : ℕ} (b : Bool) {s i : ℕ}
    (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (hi : i < 464*h) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h b s i ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow_fin b ⟨s,hs⟩ ⟨i,hi⟩]
  exact Nat.le_of_lt (ZMod.val_lt _)

theorem flat_coefficient {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (b : Bool) :
    _root_.ThreeSum.BlockCoefficientRows.flat J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h b) =
      _root_.ThreeSum.OneHotMask.extend (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.coefficient o b ∘ (_root_.ThreeSum.BlockIndex.coordEquiv J (464*h)).symm) := by
  unfold _root_.ThreeSum.BlockCoefficientRows.flat
  apply congrArg _root_.ThreeSum.OneHotMask.extend
  funext i
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices_fin,_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow_fin,Function.comp_apply,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.coefficient]



theorem eval_right {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J)
    (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :
    (_root_.ThreeSum.OneHotMask.eval
      (_root_.ThreeSum.BlockCoefficientRows.flat J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true))
      (_root_.ThreeSum.BlockCoefficientRows.flat J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false))
      (J*(464*h)) (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet S)) : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o S := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.flat_coefficient,_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.flat_coefficient]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.maskHash_right o S

end ThreeSum.BlockCoefficientRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues
open _root_.ThreeSum.LightSourceResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000



theorem key_cast {p m : ℕ} (hm : 0 < m) (shift x : ℤ) :
    (_root_.ThreeSum.LightSourceResidues.key p m shift x : ℤ) = (x % (p : ℤ) + shift) % (m : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightSourceResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.BlockSourceEncoding


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000

theorem key_eq_iff {p m : ℕ} (hm : 0 < m) (shift x endpoint : ℤ) :
    _root_.ThreeSum.LightSourceResidues.key p m shift x = _root_.ThreeSum.LightResidues.residue m 1 endpoint ↔
      (m : ℤ) ∣ x % (p : ℤ) + shift - endpoint := by
  rw [← Int.natCast_inj, _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.key_cast hm, _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hm, one_mul,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]

theorem count_eq_sum {p m : ℕ} (hm : 0 < m) (shift endpoint : ℤ)
    (values : ℕ → ℤ) (n : ℕ) :
    _root_.ThreeSum.LightHistogram.count (fun i => _root_.ThreeSum.LightSourceResidues.key p m shift (values i))
      (_root_.ThreeSum.LightResidues.residue m 1 endpoint) n =
        ∑ i ∈ range n, if (m : ℤ) ∣ values i % (p : ℤ) + shift - endpoint
          then 1 else 0 := by
  unfold _root_.ThreeSum.LightHistogram.count
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.key_eq_iff hm]

theorem count_eq_sum_of_equiv {β : Type*} [DecidableEq β]
    {p m n : ℕ} (hm : 0 < m) (shift endpoint : ℤ)
    (B : Finset β) (b : β → ℤ) (values : ℕ → ℤ)
    (e : Fin n ≃ B) (hvalues : ∀ i : Fin n, values i.val = b (e i)) :
    _root_.ThreeSum.LightHistogram.count (fun i => _root_.ThreeSum.LightSourceResidues.key p m shift (values i))
      (_root_.ThreeSum.LightResidues.residue m 1 endpoint) n =
        ∑ i ∈ B, if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then 1 else 0 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.count_eq_sum hm,← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : B, if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then 1 else 0 := by
      apply Fintype.sum_equiv e
      intro i
      rw [hvalues i]
    _ = _ := Finset.sum_coe_sort B
      (fun i : β => if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then (1 : ℕ) else 0)



theorem modulus_pos (h J : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J := pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) J

@[simp] theorem modulus_cast (h J : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]



theorem rightWeights_eq_histogram {h J n : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (p : ℕ) (shift : ℤ)
    (C : Finset β) (c : β → ℤ) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h)))
    (values : ℕ → ℤ) (e : Fin n ≃ C)
    (hvalues : ∀ i : Fin n, values i.val = c (e i)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights o (p : ℤ) shift C c S =
      if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o S then
        _root_.ThreeSum.LightHistogram.count (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift (values i))
          (_root_.ThreeSum.LightResidues.residue (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 1 (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o S)) n
      else 0 := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.count_eq_sum_of_equiv (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_pos h J) shift (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o S) C c values e hvalues]
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_cast]

end OriginalSources

end ThreeSum.BlockSourceEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original block-source multiplicities from the costed constructor

These contracts specialize the actual histogram-and-gather program to the
unchanged block encoding. Endpoint bounds follow from the constructed
coefficient rows; they are not extra semantic assumptions about the encoder.
The original input enumeration explicitly retains individual incidences.
-/

namespace ThreeSum.LightBlockSourceBuild
open _root_.ThreeSum.LightBlockSourceBuild


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

set_option maxHeartbeats 1500000



theorem flat_bound {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (b : Bool) {i : ℕ}
    (hi : i < J*(464*h)) :
    _root_.ThreeSum.BlockCoefficientRows.flat J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h b) i ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^J*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.flat_le (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) (fun _ hj => _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices_lt o hj)
    (fun _ hs _ hk => _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow_le b hs hk) hi



theorem endpointRight_abs_le {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J)
    (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :
    |_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o S| ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J : ℤ) := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.eval_right o S,Int.abs_natCast]
  exact Int.ofNat_le.mpr (_root_.ThreeSum.OneHotMask.eval_le
    (fun _ hi => _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.flat_bound o true hi) (fun _ hi => _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.flat_bound o false hi))



theorem right_value {β : Type*} [DecidableEq β] {h J N : ℕ}
    (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (p : ℕ) (shift : ℤ) (C : Finset β) (c : β → ℤ)
    (sets : ℕ → Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) (values : ℕ → ℤ)
    (e : Fin N ≃ C) (hvalues : ∀ i : Fin N, values i.val = c (e i)) (i : ℕ) :
    _root_.ThreeSum.LightSourceGather.value (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) (fun i => _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o (sets i))
      (fun i => if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o (sets i) then 1 else 0)
      (fun r => _root_.ThreeSum.LightHistogram.count
        (fun j => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift (values j)) r N) i =
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights o (p : ℤ) shift C c (sets i) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.rightWeights_eq_histogram o p shift C c (sets i) values e hvalues]
  unfold _root_.ThreeSum.LightSourceGather.value
  by_cases ha : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o (sets i) <;> simp [ha]

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightBlockSourceBuild

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact block source stages using the shared original-input histograms

The histogram read condition is the ordinary output of the already costed
`LightSourceHistogram` program. The physical array-index equivalence supplies
its semantic connection to the finite original input set. Once retained, this
same histogram supports every occurrence vector of the corresponding band.
-/

namespace ThreeSum.LightBlockSourceRetainedStages
open _root_.ThreeSum.LightBlockSourceRetainedStages


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild

set_option maxHeartbeats 1800000



theorem histogram_le (p m : ℕ) (shift : ℤ) (v : ℕ → ℤ) (N r : ℕ) :
    _root_.ThreeSum.LightBlockSourceRetainedStages.histogram p m shift v N r ≤ N := _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_le ..



theorem source_eq_right {β : Type*} [Fintype β] [DecidableEq β]
    {h J N : ℕ} (p : ℕ) (shift : ℤ) (B : Finset β) (b : β → ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hinput : ∀ i : Fin N, v i.val = b (e i)) :
    _root_.ThreeSum.LightSourceRetainedStages.source (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J)
      (fun S => _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockIndex.unindexSet S))
      (fun S => if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockIndex.unindexSet S) then 1 else 0)
      (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift v N) =
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource (p : ℤ) shift B b q := by
  funext S
  exact congrArg (fun n : ℕ => (n : ℤ))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.right_value (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) p shift B b (fun _ => _root_.ThreeSum.BlockIndex.unindexSet S) v e hinput 0)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightBlockSourceRetainedStages

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBlockSourceRetainedStages
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
set_option maxHeartbeats 1800000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages.meets_right__implementation_3ab4d6b733 {β : Type*} [Fintype β] [DecidableEq β] {pMain : ℕ}
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.Procs P pMain)
    {μ : ℕ → ℤ} {h J N raw flags p table base work cut maskBase : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(464*h)+8 ≤ lim.depth)
    (hcut : cut ≤ J*(464*h))
    (hraw : raw+_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ base)
    (hflags : flags+_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ base)
    (htable : table+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J ≤ base)
    (hdata : base+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ work)
    (hspace : _root_.ThreeSum.LightSourceRetainedStages.space work (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourceRetainedStages.word (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) N : ℤ) ≤ lim.word)
    (hinput : ∀ i : Fin N, v i.val = b (e i))
    (hhistRead : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J, μ (table+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift v N r : ℤ))
    (hrawRead : ∀ i < _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,
      μ (raw+i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout.sets h J cut i))
    (hflagRead : ∀ i < _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,
      μ (flags+i) = (if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout.sets h J cut i)
        then 1 else 0 : ℕ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [raw,flags,table,base,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,work,J*(464*h),cut,maskBase,_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut]
      μ (_root_.ThreeSum.LightSourceRetainedStages.time (J*(464*h)) cut (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J))
      (fun _ ν => _root_.ThreeSum.LightZetaStages.StoredThrough ν base cut
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource (p : ℤ) shift B b q) (J*(464*h)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν base) := by
  have run := C.meets (d := d) (μ := μ) (raw := raw) (flags := flags)
    (table := table) (base := base) (m := _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) (work := work)
    (L := J*(464*h)) (cut := cut) (maskBase := maskBase) (E := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) (B := N)
    (fun S => _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockIndex.unindexSet S))
    (fun S => if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockIndex.unindexSet S) then 1 else 0)
    (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift v N)
    hw hd (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_pos h J) hcut hraw hflags htable hdata hmasks hspace hword hrawRead
    (fun S _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointRight_abs_le (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockIndex.unindexSet S)) hflagRead
    (fun S _ => by split <;> omega) hhistRead (fun r _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages.histogram_le ..)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages.source_eq_right p shift B b q v e hinput] at run
  exact run
end

end

theorem solution.{u_implementation_0} : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages.meets_right__implementation_3ab4d6b733.{u_implementation_0}) := (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages.meets_right__implementation_3ab4d6b733.{u_implementation_0})

#print axioms solution

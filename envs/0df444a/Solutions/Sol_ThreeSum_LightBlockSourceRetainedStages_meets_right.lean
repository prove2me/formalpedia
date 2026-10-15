-- Prove2me | solution 1 for ThreeSum.LightBlockSourceRetainedStages.meets_right
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:48:20.752491+00:00
-- url     : https://prove2.me/submissions/20bef6da-cc3f-4d4c-9656-f1e06e92b981

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BlockIndex_maskHash_right
import Theorems.Thm_ThreeSum_LightSourceRetainedStages_Procs_meets
import Theorems.Thm_ThreeSum_OneHotMask_eval_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask

open Finset SubsetAddress LocalHashMoments
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

























































@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    extend f i.val = f i := by simp [extend, i.isLt]









































end ThreeSum.OneHotMask

end

section


/-!
# Reading constructed block coefficients in the flat mask order

The imperative coefficient constructor writes rows. The mask evaluator reads
one flat array. These lemmas identify the two layouts, including empty ground
sets, and specialize them to the unchanged schedule-occurrence encoding.
-/

namespace ThreeSum.BlockCoefficientRows

open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds




























theorem flat_le {J L p U M : ℕ} {sel : ℕ → ℕ} {w : ℕ → ℕ → ℕ}
    (hp : 1 ≤ p) (hsel : ∀ j < J, sel j < M)
    (hbound : ∀ s < M, ∀ i < L, w s i ≤ U) {i : ℕ} (hi : i < J*L) :
    flat J L p sel w i ≤ p^J*U := by
  let c := (coordEquiv J L).symm ⟨i,hi⟩
  change (if h : i < J*L then _ else 0) ≤ _
  rw [dif_pos hi]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right hp (Nat.le_of_lt c.1.isLt))
    (hbound _ (hsel _ c.1.isLt) _ c.2.isLt)




@[simp] theorem occurrenceIndices_fin {h J : ℕ} (o : Occurrences h J) (i : Fin J) :
    occurrenceIndices o i.val = (o i).val := by
  exact OneHotMask.extend_fin _ i






@[simp] theorem mapRow_fin {h : ℕ} (b : Bool) (s : Occurrence h) (i : Fin (512*h)) :
    mapRow h b s.val i.val = (mapAt h s (i,b)).val := by
  simp only [mapRow,s.isLt,dite_true,OneHotMask.extend_fin]

theorem occurrenceIndices_lt {h J : ℕ} (o : Occurrences h J) {j : ℕ} (hj : j < J) :
    occurrenceIndices o j < scheduleSize h := by
  exact (occurrenceIndices_fin o ⟨j,hj⟩).trans_lt (o ⟨j,hj⟩).isLt

theorem mapRow_le {h : ℕ} (b : Bool) {s i : ℕ}
    (hs : s < scheduleSize h) (hi : i < 512*h) : mapRow h b s i ≤ localPrime h := by
  rw [mapRow_fin b ⟨s,hs⟩ ⟨i,hi⟩]
  exact Nat.le_of_lt (ZMod.val_lt _)

theorem flat_coefficient {h J : ℕ} (o : Occurrences h J) (b : Bool) :
    flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h b) =
      OneHotMask.extend (coefficient o b ∘ (coordEquiv J (512*h)).symm) := by
  unfold flat
  apply congrArg OneHotMask.extend
  funext i
  simp only [occurrenceIndices_fin,mapRow_fin,Function.comp_apply,coefficient]










theorem eval_right {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) :
    (OneHotMask.eval
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h true))
      (flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h false))
      (J*(512*h)) (SubsetAddress.subsetMask (indexSet S)) : ℤ) = endpointRight o S := by
  rw [flat_coefficient,flat_coefficient]
  exact maskHash_right o S

end ThreeSum.BlockCoefficientRows

end

section


/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues

open Light

variable {lim : Limits} {P : Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')












































































































end ThreeSum.LightResidues

end

section


/-!
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000



theorem key_cast {p m : ℕ} (hm : 0 < m) (shift x : ℤ) :
    (key p m shift x : ℤ) = (x % (p : ℤ) + shift) % (m : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))






























variable {lim : Limits} {P : Program} {d : ℕ}

















































































































end ThreeSum.LightSourceResidues

end

section


/-!
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram

open Light Finset

variable {lim : Limits} {P : Program} {d : ℕ}







theorem count_le (key : ℕ → ℕ) (r i : ℕ) : count key r i ≤ i := by
  exact (Finset.card_filter_le _ _).trans (by simp)






































































































end ThreeSum.LightHistogram

end

section


/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding

open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators

set_option maxHeartbeats 1000000

theorem key_eq_iff {p m : ℕ} (hm : 0 < m) (shift x endpoint : ℤ) :
    key p m shift x = LightResidues.residue m 1 endpoint ↔
      (m : ℤ) ∣ x % (p : ℤ) + shift - endpoint := by
  rw [← Int.natCast_inj, key_cast hm, LightResidues.residue_cast hm, one_mul,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]

theorem count_eq_sum {p m : ℕ} (hm : 0 < m) (shift endpoint : ℤ)
    (values : ℕ → ℤ) (n : ℕ) :
    LightHistogram.count (fun i => key p m shift (values i))
      (LightResidues.residue m 1 endpoint) n =
        ∑ i ∈ range n, if (m : ℤ) ∣ values i % (p : ℤ) + shift - endpoint
          then 1 else 0 := by
  unfold LightHistogram.count
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [key_eq_iff hm]

theorem count_eq_sum_of_equiv {β : Type*} [DecidableEq β]
    {p m n : ℕ} (hm : 0 < m) (shift endpoint : ℤ)
    (B : Finset β) (b : β → ℤ) (values : ℕ → ℤ)
    (e : Fin n ≃ B) (hvalues : ∀ i : Fin n, values i.val = b (e i)) :
    LightHistogram.count (fun i => key p m shift (values i))
      (LightResidues.residue m 1 endpoint) n =
        ∑ i ∈ B, if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then 1 else 0 := by
  rw [count_eq_sum hm,← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : B, if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then 1 else 0 := by
      apply Fintype.sum_equiv e
      intro i
      rw [hvalues i]
    _ = _ := Finset.sum_coe_sort B
      (fun i : β => if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then (1 : ℕ) else 0)



theorem modulus_pos (h J : ℕ) : 0 < modulus h J := pow_pos (localPrime_pos h) J

@[simp] theorem modulus_cast (h J : ℕ) : (modulus h J : ℤ) = globalModulus h J := by
  simp only [modulus,globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]














theorem rightWeights_eq_histogram {h J n : ℕ} (o : Occurrences h J) (p : ℕ) (shift : ℤ)
    (C : Finset β) (c : β → ℤ) (S : Finset (BlockRows.Coord J (512*h)))
    (values : ℕ → ℤ) (e : Fin n ≃ C)
    (hvalues : ∀ i : Fin n, values i.val = c (e i)) :
    rightWeights o (p : ℤ) shift C c S =
      if RightAllowed o S then
        LightHistogram.count (fun i => key p (modulus h J) shift (values i))
          (LightResidues.residue (modulus h J) 1 (endpointRight o S)) n
      else 0 := by
  unfold rightWeights
  rw [count_eq_sum_of_equiv (modulus_pos h J) shift (endpointRight o S) C c values e hvalues]
  simp only [modulus_cast]

end OriginalSources

end ThreeSum.BlockSourceEncoding

end

section


/-!
# Original block-source multiplicities from the costed constructor

These contracts specialize the actual histogram-and-gather program to the
unchanged block encoding. Endpoint bounds follow from the constructed
coefficient rows; they are not extra semantic assumptions about the encoder.
The original input enumeration explicitly retains individual incidences.
-/

namespace ThreeSum.LightBlockSourceBuild

open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds

set_option maxHeartbeats 1500000



theorem flat_bound {h J : ℕ} (o : Occurrences h J) (b : Bool) {i : ℕ}
    (hi : i < J*(512*h)) :
    flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h b) i ≤
      localPrime h^J*localPrime h := by
  exact flat_le (localPrime_pos h) (fun _ hj => occurrenceIndices_lt o hj)
    (fun _ hs _ hk => mapRow_le b hs hk) hi








theorem endpointRight_abs_le {h J : ℕ} (o : Occurrences h J)
    (S : Finset (BlockRows.Coord J (512*h))) :
    |endpointRight o S| ≤ (endpointBound h J : ℤ) := by
  rw [← eval_right o S,Int.abs_natCast]
  exact Int.ofNat_le.mpr (OneHotMask.eval_le
    (fun _ hi => flat_bound o true hi) (fun _ hi => flat_bound o false hi))














theorem right_value {β : Type*} [DecidableEq β] {h J N : ℕ}
    (o : Occurrences h J) (p : ℕ) (shift : ℤ) (C : Finset β) (c : β → ℤ)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h))) (values : ℕ → ℤ)
    (e : Fin N ≃ C) (hvalues : ∀ i : Fin N, values i.val = c (e i)) (i : ℕ) :
    LightSourceGather.value (modulus h J) (fun i => endpointRight o (sets i))
      (fun i => if RightAllowed o (sets i) then 1 else 0)
      (fun r => LightHistogram.count
        (fun j => LightSourceResidues.key p (modulus h J) shift (values j)) r N) i =
      rightWeights o (p : ℤ) shift C c (sets i) := by
  rw [rightWeights_eq_histogram o p shift C c (sets i) values e hvalues]
  unfold LightSourceGather.value
  by_cases ha : RightAllowed o (sets i) <;> simp [ha]

variable {lim : Limits} {P : Program} {d : ℕ}
































































end ThreeSum.LightBlockSourceBuild

end

section


/-!
# Exact block source stages using the shared original-input histograms

The histogram read condition is the ordinary output of the already costed
`LightSourceHistogram` program. The physical array-index equivalence supplies
its semantic connection to the finite original input set. Once retained, this
same histogram supports every occurrence vector of the corresponding band.
-/

namespace ThreeSum.LightBlockSourceRetainedStages

open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild

set_option maxHeartbeats 1800000




theorem histogram_le (p m : ℕ) (shift : ℤ) (v : ℕ → ℤ) (N r : ℕ) :
    histogram p m shift v N r ≤ N := LightHistogram.count_le ..













theorem source_eq_right {β : Type*} [Fintype β] [DecidableEq β]
    {h J N : ℕ} (p : ℕ) (shift : ℤ) (B : Finset β) (b : β → ℤ)
    (q : GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hinput : ∀ i : Fin N, v i.val = b (e i)) :
    LightSourceRetainedStages.source (modulus h J)
      (fun S => endpointRight (outputOccurrences q) (unindexSet S))
      (fun S => if RightAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
      (histogram p (modulus h J) shift v N) =
      BlockIndexedQuery.rightSource (p : ℤ) shift B b q := by
  funext S
  exact congrArg (fun n : ℕ => (n : ℤ))
    (right_value (outputOccurrences q) p shift B b (fun _ => unindexSet S) v e hinput 0)

variable {lim : Limits} {P : Program} {d : ℕ}






































theorem meets_right_sourceProof {β : Type*} [Fintype β] [DecidableEq β] {pMain : ℕ}
    (C : LightSourceRetainedStages.Procs P pMain)
    {μ : ℕ → ℤ} {h J N raw flags p table base work cut maskBase : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+8 ≤ lim.depth)
    (hcut : cut ≤ J*(512*h))
    (hraw : raw+downsetCap (J*(512*h)) cut ≤ base)
    (hflags : flags+downsetCap (J*(512*h)) cut ≤ base)
    (htable : table+modulus h J ≤ base)
    (hdata : base+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ maskBase)
    (hmasks : maskBase+downsetCap (J*(512*h)) cut ≤ work)
    (hspace : LightSourceRetainedStages.space work (J*(512*h)) (endpointBound h J) ≤ lim.space)
    (hword : (LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) N : ℤ) ≤ lim.word)
    (hinput : ∀ i : Fin N, v i.val = b (e i))
    (hhistRead : ∀ r < modulus h J, μ (table+r) = (histogram p (modulus h J) shift v N r : ℤ))
    (hrawRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (raw+i) = endpointRight (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i))
    (hflagRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (flags+i) = (if RightAllowed (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i)
        then 1 else 0 : ℕ)) :
    Meets lim P pMain d
      [raw,flags,table,base,modulus h J,work,J*(512*h),cut,maskBase,downsetCap (J*(512*h)) cut]
      μ (LightSourceRetainedStages.time (J*(512*h)) cut (endpointBound h J))
      (fun _ ν => LightZetaStages.StoredThrough ν base cut
        (BlockIndexedQuery.rightSource (p : ℤ) shift B b q) (J*(512*h)) ∧ Kept μ ν base) := by
  have run := C.meets (d := d) (μ := μ) (raw := raw) (flags := flags)
    (table := table) (base := base) (m := modulus h J) (work := work)
    (L := J*(512*h)) (cut := cut) (maskBase := maskBase) (E := endpointBound h J) (B := N)
    (fun S => endpointRight (outputOccurrences q) (unindexSet S))
    (fun S => if RightAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
    (histogram p (modulus h J) shift v N)
    hw hd (modulus_pos h J) hcut hraw hflags htable hdata hmasks hspace hword hrawRead
    (fun S _ => endpointRight_abs_le (outputOccurrences q) (unindexSet S)) hflagRead
    (fun S _ => by split <;> omega) hhistRead (fun r _ => histogram_le ..)
  rw [source_eq_right p shift B b q v e hinput] at run
  exact run

end ThreeSum.LightBlockSourceRetainedStages

end

universe u_1

theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {β : Type u_1} [Fintype.{u_1} β] [DecidableEq.{u_1 + 1} β]
  {pMain : Nat} (C : ThreeSum.LightSourceRetainedStages.Procs P pMain) {μ : Nat → Int}
  {h J N raw flags p table base work cut maskBase : Nat} {shift : Int} (B : Finset.{u_1} β) (b : β → Int)
  (q : ThreeSum.GlobalEncoding.GlobalOutput h J) (v : Nat → Int) (e : Equiv.{1, u_1 + 1} (Fin N) ↥B),
  @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        lim.depth →
      @LE.le.{0} Nat instLENat cut
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw
              (ThreeSum.SubsetAddress.downsetCap
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                cut))
            base →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flags
                (ThreeSum.SubsetAddress.downsetCap
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                  cut))
              base →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) table
                  (ThreeSum.BlockSourceEncoding.modulus h J))
                base →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (ThreeSum.SubsetAddress.downsetCap
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                        cut)))
                  maskBase →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maskBase
                      (ThreeSum.SubsetAddress.downsetCap
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                        cut))
                    work →
                  @LE.le.{0} Nat instLENat
                      (ThreeSum.LightSourceRetainedStages.space work
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                        (ThreeSum.LightBlockSourceBuild.endpointBound h J))
                      lim.space →
                    @LE.le.{0} Int Int.instLEInt
                        (@Nat.cast.{0} Int instNatCastInt
                          (ThreeSum.LightSourceRetainedStages.word
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                            (ThreeSum.BlockSourceEncoding.modulus h J)
                            (ThreeSum.LightBlockSourceBuild.endpointBound h J) N))
                        lim.word →
                      (∀ (i : Fin N),
                          @Eq.{1} Int (v (@Fin.val N i))
                            (b
                              (@Subtype.val.{u_1 + 1} β
                                (fun (x : β) =>
                                  @Membership.mem.{u_1, u_1} β (Finset.{u_1} β)
                                    (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} β) β
                                      (@Finset.instSetLike.{u_1} β))
                                    B x)
                                (@DFunLike.coe.{u_1 + 1, 1, u_1 + 1} (Equiv.{1, u_1 + 1} (Fin N) ↥B) (Fin N)
                                  (fun (x : Fin N) => ↥B)
                                  (@EquivLike.toFunLike.{u_1 + 1, 1, u_1 + 1} (Equiv.{1, u_1 + 1} (Fin N) ↥B) (Fin N)
                                    (↥B) (@Equiv.instEquivLike.{1, u_1 + 1} (Fin N) ↥B))
                                  e i)))) →
                        (∀ (r : Nat),
                            @LT.lt.{0} Nat instLTNat r (ThreeSum.BlockSourceEncoding.modulus h J) →
                              @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) table r))
                                (@Nat.cast.{0} Int instNatCastInt
                                  (ThreeSum.LightBlockSourceRetainedStages.histogram p
                                    (ThreeSum.BlockSourceEncoding.modulus h J) shift v N r))) →
                          (∀ (i : Nat),
                              @LT.lt.{0} Nat instLTNat i
                                  (ThreeSum.SubsetAddress.downsetCap
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                    cut) →
                                @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw i))
                                  (@ThreeSum.BlockEncoding.endpointRight h J
                                    (@ThreeSum.BlockEncoding.outputOccurrences h J q)
                                    (ThreeSum.BlockSourceTableLayout.sets h J cut i))) →
                            (∀ (i : Nat),
                                @LT.lt.{0} Nat instLTNat i
                                    (ThreeSum.SubsetAddress.downsetCap
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                      cut) →
                                  @Eq.{1} Int
                                    (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flags i))
                                    (@Nat.cast.{0} Int instNatCastInt
                                      (@ite.{1} Nat
                                        (@ThreeSum.BlockEncoding.RightAllowed h J
                                          (@ThreeSum.BlockEncoding.outputOccurrences h J q)
                                          (ThreeSum.BlockSourceTableLayout.sets h J cut i))
                                        (@ThreeSum.BlockEncoding.instDecidableRightAllowed h J
                                          (@ThreeSum.BlockEncoding.outputOccurrences h J q)
                                          (ThreeSum.BlockSourceTableLayout.sets h J cut i))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) →
                              Light.Meets lim P pMain d
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt raw)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flags)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt table)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base)
                                        (@List.cons.{0} Int
                                          (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BlockSourceEncoding.modulus h J))
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                            (@List.cons.{0} Int
                                              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                                (@Nat.cast.{0} Int instNatCastInt J)
                                                (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                                                  (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512)))
                                                  (@Nat.cast.{0} Int instNatCastInt h)))
                                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maskBase)
                                                  (@List.cons.{0} Int
                                                    (@Nat.cast.{0} Int instNatCastInt
                                                      (ThreeSum.SubsetAddress.downsetCap
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          J
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                              (instOfNatNat (nat_lit 512)))
                                                            h))
                                                        cut))
                                                    (@List.nil.{0} Int)))))))))))
                                μ
                                (ThreeSum.LightSourceRetainedStages.time
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                  cut (ThreeSum.LightBlockSourceBuild.endpointBound h J))
                                fun (x : Int) (ν : Nat → Int) =>
                                And
                                  (@ThreeSum.LightZetaStages.StoredThrough
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                    ν base cut
                                    (@ThreeSum.BlockIndexedQuery.rightSource.{u_1} β h J
                                      (@Nat.cast.{0} Int instNatCastInt p) shift B b q)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                                  (Light.Kept μ ν base) := by
  exact @ThreeSum.LightBlockSourceRetainedStages.meets_right_sourceProof

#print axioms solution

-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixCatalogSetup.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:39:20.08929+00:00
-- url     : https://prove2.me/submissions/832061a7-3d60-4fb5-bd40-0f1fa4d66cfa

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
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
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
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
import Theorems.Thm_ThreeSum_LightBoxStages_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixTable_time_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostQueryBounds
end ThreeSum.ReportingHostQueryBounds
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# A rectangular Pascal table in the benchmark language

Every coefficient is built once by addition from the preceding row.
The row-major representation supports one multiplication and two additions
per later lookup. No recursive binomial-coefficient evaluation is used.
-/

namespace ThreeSum.LightPascal

open Light

variable {lim : Limits} {P : Program} {d : ℕ}






















































































































































theorem buildTime_bound (L : ℕ) : buildTime L ≤ 1000*(L+1)^2 := by
  unfold buildTime rowTime LightArray.linearTime
  simp only [fillTime]
  nlinarith

end ThreeSum.LightPascal

end

section


/-!
# A complete subset-rank program, including table construction

This fixed program constructs both lookup tables in scratch and then ranks
one valid mask. Its cost is quadratic in the bit width. The faster cached
rank contract remains available separately, but no supplied table correctness
assumption appears in the fixed-program result below.
-/

namespace ThreeSum.LightSubsetSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}
















































































theorem time_bound (L : ℕ) : time L ≤ 1200*(L+1)^2 := by
  have hb := buildTime_bound L
  unfold time powTableTime rankTime
  nlinarith

end ThreeSum.LightSubsetSetup

end

section


/-!
# Computing the compact downset size

The program builds a Pascal table, scans all preceding layers, and adds
the final binomial coefficient. The table stride used by the transform
is therefore computed by an actual fixed program.
-/

namespace ThreeSum.LightDownsetSize

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}



















































































theorem time_bound (L : ℕ) : time L ≤ 1400*(L+1)^2 := by
  have hh := LightSubsetSetup.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold time LightSubsetOffset.time
  nlinarith

end ThreeSum.LightDownsetSize

end

section


/-!
# Complete suffix-local box preprocessing, including its own shift factor

The program constructs the mask-lifting power, fills every local compact leaf
through the original global source reads, and builds every local prefix-zeta
stage. Its exponentially sized domain is the residual width V.
-/

namespace ThreeSum.LightReportingSuffixSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix

variable {lim : Limits}




































































































































































theorem coreTime_bound {W V cut : ℕ} (hV : V ≤ W) (hcut : cut ≤ V) :
    coreTime W V cut ≤ 19000*(W+1)^4*(downsetCap V cut+1) := by
  have hl := LightReportingSuffixTable.time_bound hV hcut
  have hb := LightBoxStages.time_bound hcut
  have hp : (W+1)^3 ≤ (W+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hv := Nat.pow_le_pow_left (Nat.succ_le_succ hV) 4
  have hm := Nat.mul_le_mul_right (downsetCap V cut+1) (Nat.mul_le_mul_left 12000 hp)
  have hn := Nat.mul_le_mul_right (downsetCap V cut+1) (Nat.mul_le_mul_left 6000 hv)
  have hpos : 1 ≤ (W+1)^4*(downsetCap V cut+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold coreTime
  nlinarith

theorem time_bound {W V cut offset : ℕ} (hfit : offset+V ≤ W) (hcut : cut ≤ V) :
    time W V cut offset ≤ 20000*(W+1)^4*(downsetCap V cut+1) := by
  have hc := coreTime_bound (by omega : V ≤ W) hcut
  have hp : W+1 ≤ (W+1)^4 := by
    simpa using (Nat.pow_le_pow_right (by omega : 1 ≤ W+1) (by decide : 1 ≤ 4))
  have hm := Nat.le_mul_of_pos_right ((W+1)^4) (by omega : 0 < downsetCap V cut+1)
  unfold time powTableTime
  nlinarith

end ThreeSum.LightReportingSuffixSetup

end

section


/-!
# Actual construction of a contiguous suffix-box catalog

Each input record is a physical pair of global prefix masks. The host invokes
complete suffix-local setup for every record, writes the corresponding table
pointer, and retains every previous table. The table stride is the exact
local-width storage size; the following setup host computes it explicitly.
-/

namespace ThreeSum.LightReportingSuffixCatalog

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix ReportingHostQueryBounds

set_option maxHeartbeats 1800000

variable {lim : Limits}



















































































































































theorem time_bound {W V cut offset n : ℕ} (hfit : offset+V ≤ W) (hcut : cut ≤ V) :
    time W V cut offset n ≤ 21000*(W+1)^4*(downsetCap V cut+1)*(n+1) := by
  have hs := LightReportingSuffixSetup.time_bound hfit hcut
  have hp : 1 ≤ (W+1)^4*(downsetCap V cut+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hm := Nat.mul_le_mul_left n hs
  unfold time
  nlinarith

end ThreeSum.LightReportingSuffixCatalog

end

section


/-! # Suffix catalog construction computes its own physical table stride -/

namespace ThreeSum.LightReportingSuffixCatalogSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix LightReportingSuffixCatalog

variable {lim : Limits}




















































































theorem time_bound_sourceProof {W V cut offset n : ℕ} (hfit : offset+V ≤ W) (hcut : cut ≤ V) :
    time W V cut offset n ≤ 23000*(W+1)^4*(downsetCap V cut+1)*(n+1) := by
  have hc := LightReportingSuffixCatalog.time_bound (n := n) hfit hcut
  have hs := LightDownsetSize.time_bound V
  have hV : V ≤ W := by omega
  have hp : (V+1)^2 ≤ (W+1)^4 :=
    (Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hpos : 1 ≤ (W+1)^4*(downsetCap V cut+1)*(n+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hm : (W+1)^4 ≤ (W+1)^4*(downsetCap V cut+1)*(n+1) :=
    (Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_mul_of_pos_right _ (by omega))
  unfold time
  nlinarith

end ThreeSum.LightReportingSuffixCatalogSetup

end


theorem solution : ∀ {W V cut offset n : Nat},
  @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset V) W →
    @LE.le.{0} Nat instLENat cut V →
      @LE.le.{0} Nat instLENat (ThreeSum.LightReportingSuffixCatalogSetup.time W V cut offset n)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 23000) (instOfNatNat (nat_lit 23000)))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.SubsetAddress.downsetCap V cut)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @ThreeSum.LightReportingSuffixCatalogSetup.time_bound_sourceProof

#print axioms solution

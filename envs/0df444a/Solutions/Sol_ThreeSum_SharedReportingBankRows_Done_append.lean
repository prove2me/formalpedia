-- Prove2me | solution 1 for ThreeSum.SharedReportingBankRows.Done.append
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:38:00.058911+00:00
-- url     : https://prove2.me/submissions/a274cb1f-354e-4119-afe2-01324c1ce9b9

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_of_window


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Exact compact layout for a shared reporting catalog cell

The local pair and prefix counts are retained exactly. Each cell reserves
the two prefix arrays, its pointer row, all suffix boxes, the sorted index,
and the polynomial scratch used by the existing constructor. Layout sums
are later computed by the bank setup loop.
-/

namespace ThreeSum.SharedReportingBankLayout

open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 1400000
set_option maxRecDepth 9000




































theorem ordered (base h J k boxCut : ℕ) :
    base ≤ pairL base h ∧ pairL base h ≤ pairR base h ∧ pairR base h ≤ stageL base h ∧
      stageL base h ≤ stageR base h k ∧ stageR base h k ≤ pointers base h k ∧
      pointers base h k ≤ boxes base h k ∧ boxes base h k ≤ masks base h J k boxCut ∧
      masks base h J k boxCut ≤ work base h J k boxCut ∧
      work base h J k boxCut ≤ finish base h J k boxCut := by
  simp only [finish,work,masks,boxes,pointers,stageR,stageL,pairR,pairL]
  omega

theorem finish_add (base h J k boxCut : ℕ) :
    finish base h J k boxCut=base+cellSize h J k boxCut := by
  unfold cellSize finish work masks boxes pointers stageR stageL pairR pairL
  omega






theorem index_end (base h J k boxCut : ℕ) :
    index base h J k boxCut+count h k ≤ work base h J k boxCut := by
  unfold index work
  omega

























































theorem levelOffset_step (h J : ℕ) (boxCut : ℕ → ℕ) (k : ℕ) :
    levelOffset h J boxCut k ≤ levelOffset h J boxCut (k+1) := by
  rw [levelOffset]
  omega

theorem levelOffset_mono (h J : ℕ) (boxCut : ℕ → ℕ) : Monotone (levelOffset h J boxCut) :=
  monotone_nat_of_le_succ (levelOffset_step h J boxCut)

theorem finish_level (base h J k : ℕ) (boxCut : ℕ → ℕ) :
    finish (base+levelOffset h J boxCut k) h J k (boxCut k)=
      base+levelOffset h J boxCut (k+1) := by
  rw [finish_add,levelOffset]
  omega

end ThreeSum.SharedReportingBankLayout

end

section


/-! # Exact level layout and retention for one shared source pair -/

namespace ThreeSum.SharedReportingBankLevels

open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1400000







































































theorem baseAt_mono (base h J : ℕ) : Monotone (baseAt base h J) := by
  intro i j hij
  exact Nat.add_le_add_left (levelOffset_mono h J (boxCut h J) hij) base

theorem finish_baseAt (base h J k : ℕ) :
    finish (baseAt base h J k) h J k (boxCut h J k)=baseAt base h J (k+1) :=
  finish_level base h J k (boxCut h J)

theorem catalog_low (base h J k : ℕ) :
    base ≤ (catalogAt base h J k).indexBase ∧
    base ≤ (catalogAt base h J k).ptrBase ∧
    base ≤ (catalogAt base h J k).boxBase := by
  have ho := ordered (baseAt base h J k) h J k (boxCut h J k)
  have hb : base ≤ baseAt base h J k := Nat.le_add_right _ _
  dsimp only [catalogAt,catalog,index]
  omega

theorem catalog_end (base h J k : ℕ) :
    (catalogAt base h J k).indexBase+count h k ≤ baseAt base h J (k+1) ∧
    (catalogAt base h J k).ptrBase+count h k ≤ baseAt base h J (k+1) ∧
    (catalogAt base h J k).boxBase+count h k*
      stride ((J-k)*(512*h)) (boxCut h J k) ≤ baseAt base h J (k+1) := by
  have ho := ordered (baseAt base h J k) h J k (boxCut h J k)
  have hi := index_end (baseAt base h J k) h J k (boxCut h J k)
  have hp : pointers (baseAt base h J k) h k+count h k=boxes (baseAt base h J k) h k := rfl
  have hm : boxes (baseAt base h J k) h k+count h k*
      stride ((J-k)*(512*h)) (boxCut h J k)=masks (baseAt base h J k) h J k (boxCut h J k) := rfl
  rw [← finish_baseAt]
  dsimp only [catalogAt,catalog]
  omega























end ThreeSum.SharedReportingBankLevels

end

section


/-! # Exact occurrence/B-band/C-band row order and retained catalog ownership -/

namespace ThreeSum.SharedReportingBankRows

open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData

set_option maxHeartbeats 1800000








theorem digit_injective {n a b c d : ℕ} (hb : b < n) (hd : d < n)
    (he : a*n+b=c*n+d) : a=c ∧ b=d := by
  have hmod := congrArg (fun x => x%n) he
  have hbd : b=d := by simpa [Nat.add_mod,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hd] using hmod
  have hp : a*n=c*n := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega) hp,hbd⟩

theorem rank_injective {nb nc s i j s' i' j' : ℕ}
    (hi : i < nb) (hj : j < nc) (hi' : i' < nb) (hj' : j' < nc)
    (he : rank nb nc s i j=rank nb nc s' i' j') : s=s' ∧ i=i' ∧ j=j' := by
  have hinner := digit_injective hj hj' he
  have houter := digit_injective hi hi' hinner.1
  exact ⟨houter.1,houter.2,hinner.2⟩

theorem rank_lt {S nb nc s i j : ℕ} (hs : s < S) (hi : i < nb) (hj : j < nc) :
    rank nb nc s i j < pairs S nb nc := by
  have hx : s*nb+i < S*nb := calc
    _ < s*nb+nb := Nat.add_lt_add_left hi _
    _ = (s+1)*nb := by ring
    _ ≤ S*nb := Nat.mul_le_mul_right nb (by omega)
  calc
    _ < (s*nb+i)*nc+nc := Nat.add_lt_add_left hj _
    _ = (s*nb+i+1)*nc := by ring
    _ ≤ S*nb*nc := Nat.mul_le_mul_right nc (by omega)































theorem rowBase_next (base h J K q : ℕ) :
    baseAt (rowBase base h J K q) h J K=rowBase base h J K (q+1) := by
  unfold rowBase baseAt
  ring
theorem rowBase_mono (base h J K : ℕ) : Monotone (rowBase base h J K) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem entry_of_later_block {h J k record nextRecord n low bound : ℕ} {μ ν : ℕ → ℤ}
    {D : Catalog} {hk : k ≤ J} {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Entry μ record D hk f g) (heq : KeptBut μ ν bound nextRecord n)
    (hrecord : record+5 ≤ nextRecord) (hnext : nextRecord+n ≤ low)
    (hlow : low ≤ bound) (hindexLow : low ≤ D.indexBase)
    (hptrLow : low ≤ D.ptrBase) (hboxLow : low ≤ D.boxBase)
    (hindex : D.indexBase+count h k ≤ bound) (hptr : D.ptrBase+count h k ≤ bound)
    (hbox : D.boxBase+count h k*stride ((J-k)*(512*h)) D.boxCut ≤ bound) :
    Entry ν record D hk f g := by
  refine ⟨?_,H.tables.of_window (fun a ha hb => heq a ⟨hb,Or.inr (by omega)⟩)
    hindexLow hptrLow hboxLow hindex hptr hbox⟩
  intro i hi
  have hi' : i < 5 := by
    simpa only [Catalog.record,List.length_map,List.length_cons,List.length_nil] using hi
  exact (heq _ ⟨by omega,Or.inl (by omega)⟩).trans (H.header i hi)

theorem levels_of_later_row {μ ν : ℕ → ℤ} {record base h J K nextRecord nextBase : ℕ}
    {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Built μ record base h J K f g)
    (heq : KeptBut μ ν nextBase nextRecord (5*K))
    (hrecords : record+5*K ≤ nextRecord) (hnext : nextRecord+5*K ≤ base)
    (hpayload : baseAt base h J K ≤ nextBase) : Built ν record base h J K f g := by
  intro k hk
  obtain ⟨hkJ,Hk⟩ := H k hk
  have hlow := catalog_low base h J k
  have hend := catalog_end base h J k
  have hbefore := (baseAt_mono base h J (show k+1 ≤ K by omega)).trans hpayload
  refine ⟨hkJ,entry_of_later_block Hk heq (by omega) hnext
    ((Nat.le_add_right _ _).trans hpayload) hlow.1 hlow.2.1 hlow.2.2
    (hend.1.trans hbefore) (hend.2.1.trans hbefore) (hend.2.2.trans hbefore)⟩
















theorem Done.append_sourceProof {μ ν : ℕ → ℤ} {record base h J K NB NC g s i j q : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : Done μ record base h J K NB NC g q fB fC p shift)
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g)
    (hq : q=rank (BandPartition.size NB g) (BandPartition.size NC g) s i j)
    (Hnew : Built ν (rowRecord record K q) (rowBase base h J K q) h J K
      (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val) (representative h J s))
      (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val) (representative h J s)))
    (heq : KeptBut μ ν (rowBase base h J K q) (rowRecord record K q) (5*K))
    (hslab : record+5*K*total h J NB NC g ≤ base) :
    Done ν record base h J K NB NC g (q+1) fB fC p shift := by
  have hqLt : q < total h J NB NC g := by rw [hq]; exact rank_lt hs hi hj
  have hmeta := Nat.mul_le_mul_left (5*K) (show q+1 ≤ total h J NB NC g by omega)
  have hnext : rowRecord record K q+5*K ≤ base := by unfold rowRecord; nlinarith
  intro s' hs' i' hi' j' hj' hr
  rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | hr
  · have Hold := H s' hs' i' hi' j' hj' hr
    have hm := Nat.mul_le_mul_left (5*K) (show
      rank (BandPartition.size NB g) (BandPartition.size NC g) s' i' j'+1 ≤ q by omega)
    apply levels_of_later_row Hold heq
    · unfold rowRecord
      nlinarith
    · exact hnext.trans (Nat.le_add_right _ _)
    · rw [rowBase_next]
      exact rowBase_mono base h J K (by omega)
  · have hh := rank_injective hi' hj' hi hj (hr.trans hq)
    rcases hh with ⟨rfl,rfl,rfl⟩
    simpa only [← hq] using Hnew

end ThreeSum.SharedReportingBankRows

end


theorem solution : ∀ {μ ν : Nat → Int} {record base h J K NB NC g s i j q : Nat} {fB fC : Nat → Int} {p shift : Int},
  ThreeSum.SharedReportingBankRows.Done μ record base h J K NB NC g q fB fC p shift →
    @LT.lt.{0} Nat instLTNat s (ThreeSum.LightBlockSourceCatalog.count h J) →
      @LT.lt.{0} Nat instLTNat i (ThreeSum.BandPartition.size NB g) →
        @LT.lt.{0} Nat instLTNat j (ThreeSum.BandPartition.size NC g) →
          @Eq.{1} Nat q
              (ThreeSum.SharedReportingBankRows.rank (ThreeSum.BandPartition.size NB g)
                (ThreeSum.BandPartition.size NC g) s i j) →
            ThreeSum.SharedReportingBankLevels.Built ν (ThreeSum.SharedReportingBankRows.rowRecord record K q)
                (ThreeSum.SharedReportingBankRows.rowBase base h J K q) h J K
                (@ThreeSum.BlockIndexedQuery.leftSource.{0} (Fin NB) h J p (ThreeSum.SourceBandPartition.source NB g i)
                  (fun (t : Fin NB) => fB (@Fin.val NB t)) (ThreeSum.BlockSourceOccurrenceOrder.representative h J s))
                (@ThreeSum.BlockIndexedQuery.rightSource.{0} (Fin NC) h J p shift
                  (ThreeSum.SourceBandPartition.source NC g j) (fun (t : Fin NC) => fC (@Fin.val NC t))
                  (ThreeSum.BlockSourceOccurrenceOrder.representative h J s)) →
              Light.KeptBut μ ν (ThreeSum.SharedReportingBankRows.rowBase base h J K q)
                  (ThreeSum.SharedReportingBankRows.rowRecord record K q)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) K) →
                @LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) K)
                        (ThreeSum.SharedReportingBankRows.total h J NB NC g)))
                    base →
                  ThreeSum.SharedReportingBankRows.Done ν record base h J K NB NC g
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    fB fC p shift := by
  exact @ThreeSum.SharedReportingBankRows.Done.append_sourceProof

#print axioms solution

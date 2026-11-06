-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeed_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:35:42.942421+00:00
-- url     : https://prove2.me/submissions/1ce53a39-4087-4b96-8023-4caa09def4fa

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedBaseRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Valuation.LocalSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSeedSplittingIdeals
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing

section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2000] sourceSeedBaseValuationRingBaseModule
attribute [local instance 2000] sourceSeedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceSeedBaseValuationRingAlgebra
attribute [local instance 2000] sourceSeedBaseValuationRingSMul
attribute [local instance 2000] sourceSeedBaseValuationRingModule
attribute [local instance] sourceSeedBaseScalarTower
attribute [local instance] sourceSeedIntegralClosureTorsionFree
attribute [local instance] sourceSeedIntegralClosureFinite
attribute [local instance] sourceSeedIntegralClosureIsFractionRing
attribute [local instance] sourceSeedIntegralClosureIsDedekind
private theorem sourceSeed_ramificationIdx_mul_inertiaDeg_eq_one
    (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).ramificationIdx' P.1 *
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).inertiaDeg' P.1 = 1 := by
  let O := SourceSeedBaseValuationRing
  let C := SourceSeedIntegralClosure m
  let K := GaloisBaseField
  let L := SourceField m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let s := IsDedekindDomain.primesOverFinset p C
  let f : Ideal C → ℕ := fun Q => p.ramificationIdx' Q * p.inertiaDeg' Q
  letI : IsDiscreteValuationRing O :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hPmem : P.1 ∈ s :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 C).2 P.2
  have hpositive : ∀ Q ∈ s, 0 < f Q := by
    intro Q hQ
    have hQdata := (IsDedekindDomain.mem_primesOverFinset_iff hp0 C).1 hQ
    letI : Q.IsPrime := hQdata.1
    letI : Q.LiesOver p := hQdata.2
    exact Nat.mul_pos
      (Nat.pos_of_ne_zero
        (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q hp0))
      (Nat.pos_of_ne_zero (Ideal.inertiaDeg_ne_zero p Q))
  have hrest : (s.erase P.1).card ≤ ∑ Q ∈ s.erase P.1, f Q := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun Q hQ =>
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (hpositive Q (Finset.mem_of_mem_erase hQ)))
  have hsum : ∑ Q ∈ s, f Q = Module.finrank K L :=
    Ideal.sum_ramification_inertia C K L hp0
  have hcard : s.card = Module.finrank K L := by
    calc
      s.card = (p.primesOver C).ncard := by
        rw [← IsDedekindDomain.coe_primesOverFinset hp0 C,
          Set.ncard_coe_finset]
      _ = 240 * 16 ^ m := sourceSeed_primesOver_ncard m
      _ = Module.finrank K L := (sourceSeed_fixedBase_finrank m).symm
  have hbound : f P.1 + (s.erase P.1).card ≤ Module.finrank K L := by
    calc
      f P.1 + (s.erase P.1).card ≤
          f P.1 + ∑ Q ∈ s.erase P.1, f Q :=
        Nat.add_le_add_left hrest _
      _ = ∑ Q ∈ s, f Q := Finset.add_sum_erase s f hPmem
      _ = Module.finrank K L := hsum
  have hcardErase : (s.erase P.1).card + 1 = Module.finrank K L := by
    calc
      (s.erase P.1).card + 1 = s.card := Finset.card_erase_add_one hPmem
      _ = Module.finrank K L := hcard
  have hfone : f P.1 = 1 := by
    have hfpos : 0 < f P.1 := hpositive P.1 hPmem
    omega
  exact hfone
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingBaseModule
attribute [local instance 2000] sourceSeedBaseValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceSeedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingAlgebra
attribute [local instance 2000] sourceSeedBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingSMul
attribute [local instance 2000] sourceSeedBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingModule
attribute [local instance 2000] sourceSeedBaseValuationRingModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseScalarTower
attribute [local instance] sourceSeedBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureTorsionFree
attribute [local instance] sourceSeedIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureFinite
attribute [local instance] sourceSeedIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureIsFractionRing
attribute [local instance] sourceSeedIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureIsDedekind
attribute [local instance] sourceSeedIntegralClosureIsDedekind
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).ramificationIdx'
      P.1 = 1 := by
  apply Nat.eq_one_of_dvd_one
  exact ⟨(IsLocalRing.maximalIdeal
      SourceSeedBaseValuationRing).inertiaDeg' P.1,
    (sourceSeed_ramificationIdx_mul_inertiaDeg_eq_one m P).symm⟩
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

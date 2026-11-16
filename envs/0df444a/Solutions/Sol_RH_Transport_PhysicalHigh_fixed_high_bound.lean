-- Prove2me | solution 1 for RH.Transport.PhysicalHigh.fixed_high_bound
-- status  : ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T04:36:12.473165+00:00
-- url     : https://prove2.me/submissions/38a8a498-a706-40bc-bedf-b45cc1483af2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B028
import Definitions.Def_Transport_PhysicalHigh_MomentBound
import Definitions.Def_Transport_DataProbe
import Theorems.Thm_RH_Transport_PhysicalHigh_actual_high_probe_from_raw_moments
import Theorems.Thm_RH_Transport_TunedCandidate_boundary_value
set_option autoImplicit false

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.QuantitativePassage
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators
namespace CompletedDyadic

theorem pow_rpow_comm (s : ℝ) (n : ℕ) : ((2:ℝ)^n)^s=((2:ℝ)^s)^n := by
  rw [←Real.rpow_natCast_mul (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

theorem kernelTerm_nonneg (t s A : ℝ) (ht : 0<t) (n : ℕ) : 0≤kernelTerm t s A n := by
  unfold kernelTerm
  positivity

theorem kernelTerm_le_head (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤((2:ℝ)^s)^n := by
  rw [kernelTerm,←pow_rpow_comm]
  exact div_le_self (Real.rpow_nonneg (by positivity) _)
    (Real.one_le_rpow (by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]) hA)

theorem kernelTerm_le_tail (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤t^(-A)*((2:ℝ)^(s-A))^n := by
  have hn : 0<(2:ℝ)^n := by positivity
  have htA : 0<t^A := Real.rpow_pos_of_pos ht _
  calc
    _ ≤ ((2:ℝ)^n)^s/(t*(2:ℝ)^n)^A := by
      unfold kernelTerm
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (Real.rpow_le_rpow (by positivity) (by linarith) hA)
    _ = t^(-A)*(((2:ℝ)^n)^s/((2:ℝ)^n)^A) := by
      rw [Real.mul_rpow ht.le hn.le,Real.rpow_neg ht.le]
      ring
    _ = _ := by rw [←Real.rpow_sub hn,pow_rpow_comm]

theorem ratio_lt_one (s A : ℝ) (hsA : s<A) : (2:ℝ)^(s-A)<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsA)

theorem kernel_summable (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (hsA : s<A) :
    Summable (kernelTerm t s A) := by
  have hq := summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (s-A)) (ratio_lt_one s A hsA)
  exact (hq.mul_left (t^(-A))).of_nonneg_of_le (kernelTerm_nonneg t s A ht) (kernelTerm_le_tail t s A ht hA)

theorem kernel_sum_cutoff (t s A : ℝ) (ht : 0<t) (hs : 0<s) (hsA : s<A) (N : ℕ) :
    (∑'n : ℕ,kernelTerm t s A n)≤
      ((2:ℝ)^s)^N/((2:ℝ)^s-1)+t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
  have hA : 0≤A := by linarith
  have hp : 1<(2:ℝ)^s := Real.one_lt_rpow (by norm_num) hs
  have hq : (2:ℝ)^(s-A)<1 := ratio_lt_one s A hsA
  have hq0 : 0≤(2:ℝ)^(s-A) := by positivity
  have hsum := kernel_summable t s A ht hA hsA
  have hhead : (∑n∈Finset.range N,kernelTerm t s A n)≤((2:ℝ)^s)^N/((2:ℝ)^s-1) := by
    apply (Finset.sum_le_sum (fun n _ => kernelTerm_le_head t s A ht hA n)).trans
    rw [geom_sum_eq hp.ne']
    exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hp.le)
  have htail : (∑'n : ℕ,kernelTerm t s A (n+N))≤
      t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
    have hgeo := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A)*((2:ℝ)^(s-A))^N)
    have hb := Summable.tsum_le_tsum (fun n => show kernelTerm t s A (n+N)≤
      (t^(-A)*((2:ℝ)^(s-A))^N)*((2:ℝ)^(s-A))^n by
        simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using kernelTerm_le_tail t s A ht hA (n+N))
      ((summable_nat_add_iff N).mpr hsum) hgeo
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    simpa only [div_eq_mul_inv] using hb
  rw [←hsum.sum_add_tsum_nat_add N]
  exact add_le_add hhead htail

theorem kernel_sum_bound (s A : ℝ) (hs : 0<s) (hsA : s<A) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t →
      Summable (kernelTerm t s A) ∧ (∑'n : ℕ,kernelTerm t s A n)≤C*t^(-s) := by
  let r : ℝ := (2:ℝ)^s
  let q : ℝ := (2:ℝ)^(s-A)
  have hr : 1< r := Real.one_lt_rpow (by norm_num) hs
  have hq : q<1 := ratio_lt_one s A hsA
  have hq0 : 0≤q := by dsimp [q]; positivity
  let C := r/(r-1)+1/(1-q)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro t ht
  have hA : 0≤A := by linarith
  have hsum := kernel_summable t s A ht hA hsA
  refine ⟨hsum,?_⟩
  by_cases ht1 : 1≤t
  · have hg := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A))
    have hb := hsum.tsum_le_tsum (fun n => kernelTerm_le_tail t s A ht hA n) hg
    change (∑'n : ℕ,kernelTerm t s A n)≤∑'n : ℕ,t^(-A)*q^n at hb
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    calc
      _ ≤ t^(-A)/(1-q) := by simpa only [div_eq_mul_inv] using hb
      _ ≤ t^(-s)/(1-q) := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (by linarith)
      _ ≤ C*t^(-s) := by
        have hp : 0≤ r/(r-1)*t^(-s) := by positivity
        calc
          _ ≤ r/(r-1)*t^(-s)+t^(-s)/(1-q) := le_add_of_nonneg_left hp
          _ = C*t^(-s) := by dsimp [C]; ring
  · have ht_le : t≤1 := le_of_not_ge ht1
    have hit : 1≤1/t := (one_le_div ht).mpr ht_le
    obtain ⟨N,hN,hN'⟩ := exists_nat_pow_near hit (by norm_num : (1:ℝ)<2)
    have hheadpow : r^(N+1)≤ r*t^(-s) := by
      change ((2:ℝ)^s)^(N+1)≤(2:ℝ)^s*t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ ((2:ℝ)/t)^s := by
          apply Real.rpow_le_rpow (by positivity) _ hs.le
          rw [pow_succ]
          calc
            _ ≤ (1/t)*2 := mul_le_mul_of_nonneg_right hN (by norm_num)
            _ = 2/t := by ring
        _ = _ := by rw [Real.div_rpow (by norm_num) ht.le,Real.rpow_neg ht.le]; ring
    have htailpow : t^(-A)*q^(N+1)≤t^(-s) := by
      change t^(-A)*((2:ℝ)^(s-A))^(N+1)≤t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ t^(-A)*(1/t)^(s-A) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) hN'.le (by linarith)) (by positivity)
        _ = t^(-A)*t^(-(s-A)) := by rw [one_div,Real.inv_rpow ht.le,←Real.rpow_neg ht.le]
        _ = t^(-s) := by rw [←Real.rpow_add ht]; congr 1; ring
    have hb := kernel_sum_cutoff t s A ht hs hsA (N+1)
    change (∑'n : ℕ,kernelTerm t s A n)≤ r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) at hb
    calc
      _ ≤ r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) := hb
      _ ≤ (r*t^(-s))/(r-1)+t^(-s)/(1-q) := add_le_add
        (div_le_div_of_nonneg_right hheadpow (by linarith))
        (div_le_div_of_nonneg_right htailpow (by linarith))
      _ = C*t^(-s) := by dsimp [C]; ring

end CompletedDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.FiniteConductor
namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.mono {χ : MulChar R ℂ} {I J : Ideal R}
    (h : FactorsThroughIdeal χ I) (hJI : J ≤ I) : FactorsThroughIdeal χ J := by
  rw [factorsThroughIdeal_iff] at h ⊢
  exact fun u hu => h u (hJI hu)

end

end SevenEighths.FiniteConductor

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum
namespace OAI

noncomputable section
namespace SevenEighths.HeckeZeroSupremum
open HeckeFamily

theorem zeroRealParts_le_one {x : ℝ} (hx : x ∈ zeroRealParts) : x ≤ 1 := by
  obtain ⟨χ, s, _, _, hz, rfl⟩ := hx
  by_contra h
  exact LFunction_ne_zero_of_one_lt_re χ (lt_of_not_ge h) hz

theorem zeroSet_nonempty : zeroSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem beta_le_one : beta ≤ 1 := by
  apply csSup_le zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

end SevenEighths.HeckeZeroSupremum

end

end OAI
end

section
-- module Solutions.OAIHecke.Vendor.PrimeNumberTheoremAnd.Sobolev
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

namespace CS

variable {f : CS n E} {R x v : ℝ}

theorem bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicTailBudget
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic

theorem constant_absorbed_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, C≤Z^ε := by
  exact (tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop C)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.RowPartition
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma rowNorm_ge_one (u : FreeRow) : 1≤ rowNorm u := by
  unfold rowNorm
  have hn : (Ideal.span {u.val}:Ideal O)≠⊥ := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeCalibration
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma centralCubeIntegral_calibration_zero {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=0 := by
  simp [centralCubeIntegral,continuedRowOnLines,continuedPhysicalRowKernel,hc]

theorem finiteCentralCubeRows_filter_calibration {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e : ℝ) (a H : FreeRow→ℝ) :
    finiteCentralCubeRows S hS hmax η (R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0))
      T hT W Yp W0 W1 X Y Z e a H=
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H := by
  unfold finiteCentralCubeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp [hc,centralCubeIntegral_calibration_zero S hS hmax _ _ η u hc]
  · simp [hc]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeBinPartition
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma sum_cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u≤n ∧ grid u≤ m) (f : FreeRow→ℂ) :
    (∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),∑u∈cubeBinRows R idx grid i k,f u)=∑u∈R,f u := by
  have hm : ∀u∈R,(idx u,grid u)∈(Finset.range (n+1)).product (Finset.range (m+1)) := by
    intro u hu
    simpa only [Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range] using
      And.intro (Nat.lt_succ_of_le (hlabel u hu).1) (Nat.lt_succ_of_le (hlabel u hu).2)
  have hs := Finset.sum_fiberwise_of_maps_to hm f
  simpa only [Finset.product_eq_sprod,Finset.sum_product,Prod.mk.injEq,cubeBinRows] using hs

theorem finiteCentralCubeRows_bin_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B : ℝ) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u≤n ∧ grid u≤ m) :
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*B)=
    ∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),
      finiteCentralCubeRows S hS hmax η (cubeBinRows R idx grid i k) T hT W Yp W0 W1 X Y Z e
        (fun _=>51/100+e*k) (fun _=>(3*i+1:ℕ)*B) := by
  unfold finiteCentralCubeRows
  rw [←sum_cubeBinRows R idx grid n m hlabel]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro u hu
  rcases (mem_cubeBinRows R idx grid i k u).mp hu with ⟨hu,hi,hk⟩
  simp only [hi,hk]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CentralExponent
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeCentralExponent

lemma original_exponent_identity (a d R q : ℝ) :
    sourceExponent a d R q=3/16+relativeExponent (2*a-1) d R q := by
  unfold sourceExponent relativeExponent
  ring

lemma relative_extend (δ d R q ζ : ℝ) (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    relativeExponent δ d R q≤ relativeExponent δ (13/16) R q+2*ζ := by
  have hh := mul_le_mul_of_nonneg_right (show d-13/16≤ζ by linarith) hslo
  have hh' := mul_le_mul_of_nonneg_left hshi hζ
  unfold relativeExponent
  nlinarith

lemma floor_source_margin (q Δ ζ d : ℝ) (hq : q≤1/100)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ) :
    sourceExponent (51/100) d 1 q-(3/16+Δ)≤-7/1200-Δ+2*ζ := by
  have he := relative_extend (1/50) d 1 q ζ hζ hd (by norm_num) (by norm_num)
  rw [original_exponent_identity]
  norm_num only at *
  unfold relativeExponent at he ⊢
  nlinarith

lemma realLoss_bound (N : ℕ) (d e eps heightLoss mesh : ℝ)
    (hd : d≤1) (he : 0≤e) (heps : 0≤eps) :
    realLoss N d e eps heightLoss mesh≤26*e+(N+8)*eps+heightLoss+mesh/6 := by
  have h1 := mul_le_mul_of_nonneg_right hd he
  have h2 := mul_le_mul_of_nonneg_right hd (show 0≤eps*(N+8) by positivity)
  unfold realLoss
  nlinarith

end SevenEighths.ProbeCentralExponent

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CentralDyadicWeight
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

lemma dyad_conductor_margin (Z v margin : ℝ) (hZ : 0<Z) (hmargin : 2≤Z^margin)
    (R : Finset FreeRow) (hR : ∀u∈R,rowNorm u≤2*Z^v) :
    ∀u∈R,rowNorm u≤Z^((v+2*margin)-margin) := by
  intro u hu
  calc
    rowNorm u≤2*Z^v := hR u hu
    _ ≤ Z^margin*Z^v := mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring
end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorDyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

lemma bounded_dyadic_power_sum (p : ℝ) (hp : 0<p) :
    ∃C : ℝ,0<C ∧ ∀H : ℝ,0<H → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤H) → (∑n∈F,((2:ℝ)^n)^p)≤C*H^p := by
  obtain ⟨C,hC,hmain⟩ := CompletedDyadic.kernel_sum_bound p (p+1) hp (by linarith)
  refine ⟨(2:ℝ)^(p+1)*C,by positivity,?_⟩
  intro H hH F hF
  obtain ⟨hs,hb⟩ := hmain H⁻¹ (inv_pos.mpr hH)
  have hpoint (n : ℕ) (hn : n∈F) : ((2:ℝ)^n)^p≤(2:ℝ)^(p+1)*CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := by
    have hd : 0<1+H⁻¹*(2:ℝ)^n := by positivity
    have hu : H⁻¹*(2:ℝ)^n≤1 := by
      rw [mul_comm,←div_eq_mul_inv]
      exact (div_le_one hH).mpr (hF n hn)
    have hh : (1+H⁻¹*(2:ℝ)^n)^(p+1)≤(2:ℝ)^(p+1) :=
      Real.rpow_le_rpow hd.le (by linarith) (by linarith)
    unfold CompletedDyadic.kernelTerm
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hd _)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh
      (Real.rpow_nonneg (show (0:ℝ)≤(2:ℝ)^n by positivity) p)
  calc
    _ ≤ ∑n∈F,(2:ℝ)^(p+1)*CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := Finset.sum_le_sum hpoint
    _ = (2:ℝ)^(p+1)*∑n∈F,CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := (Finset.mul_sum _ _ _).symm
    _ ≤ (2:ℝ)^(p+1)*∑'n,CompletedDyadic.kernelTerm H⁻¹ p (p+1) n :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum F (fun n _=>by unfold CompletedDyadic.kernelTerm;positivity)) (by positivity)
    _ ≤ (2:ℝ)^(p+1)*(C*(H⁻¹)^(-p)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [Real.inv_rpow hH.le,Real.rpow_neg hH.le,inv_inv];ring

lemma retained_dyadic_partition (rows : Finset FreeRow) (H : ℝ)
    (hrows : ∀u∈rows,u.val≠1 ∧ rowNorm u≤H) :
    (smallDyadicIndices H).biUnion (fun n=>rows∩dyadicRows 1 n)=rows := by
  ext u
  constructor
  · intro hu
    obtain ⟨n,hn,hu⟩ := Finset.mem_biUnion.mp hu
    exact (Finset.mem_inter.mp hu).1
  · intro hu
    obtain ⟨n,hn⟩ := exists_dyadicRows 1 (by norm_num) u (hrows u hu).1 (rowNorm_ge_one u)
    refine Finset.mem_biUnion.mpr ⟨n,?_,Finset.mem_inter.mpr ⟨hu,hn⟩⟩
    rw [mem_smallDyadicIndices]
    have hlo := (mem_dyadicRows.mp hn).2.1
    simpa only [one_mul] using hlo.trans (hrows u hu).2

lemma retained_dyadic_sum {A : Type*} [AddCommMonoid A] (rows : Finset FreeRow) (H : ℝ)
    (hrows : ∀u∈rows,u.val≠1 ∧ rowNorm u≤H) (f : FreeRow→A) :
    (∑u∈rows,f u)=∑n∈smallDyadicIndices H,∑u∈rows∩dyadicRows 1 n,f u := by
  conv_lhs => rw [←retained_dyadic_partition rows H hrows]
  apply Finset.sum_biUnion
  intro m hm n hn hmn
  exact (dyadicRows_disjoint 1 (by norm_num) hmn).mono (Finset.inter_subset_right) (Finset.inter_subset_right)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

lemma sourceDyad_scale {Z : ℝ} (hZ : 1<Z) (k : ℕ) :
    Z^(sourceDyadExponent Z k)=(2:ℝ)^k :=
  Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (by positivity)

lemma canonical_dyad_cost (loss : ℝ) (hl : 0<loss) :
    ∃C : ℝ,0<C ∧ ∀(Z v : ℝ),1≤Z → v≤1 →
      ((smallDyadicIndices (Z^v)).card:ℝ)≤C*Z^loss := by
  obtain ⟨C,hC,hbound⟩ := bounded_dyadic_power_sum loss hl
  refine ⟨C,hC,?_⟩
  intro Z v hZ hv
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  calc
    _ = ∑k∈smallDyadicIndices (Z^v),(1:ℝ) := by simp
    _ ≤ ∑k∈smallDyadicIndices (Z^v),((2:ℝ)^k)^loss := by
      apply Finset.sum_le_sum
      intro k hk
      exact Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hl.le
    _ ≤ C*(Z^v)^loss := hbound _ (by positivity) _ (fun k hk=>mem_smallDyadicIndices.mp hk)
    _ ≤ C*Z^loss := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [←Real.rpow_mul hZp.le]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

lemma sourceDyad_geometry_eventually (dmin dmax margin vmax : ℝ)
    (_hdmin : 0<dmin) (hdmin1 : dmin<1/100) (hmargin : 0< margin)
    (hdmax : vmax+2*margin≤dmax) :
    ∀ᶠZ : ℝ in atTop,∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤Z^vmax) →
      ∀k : ℕ,(rows∩dyadicRows 1 k).Nonempty →
        0≤ sourceDyadExponent Z k ∧ sourceDyadExponent Z k≤vmax ∧
        dmin≤ sourceDyadConductor Z margin k ∧ sourceDyadConductor Z margin k≤dmax ∧
        (∀u∈rows∩dyadicRows 1 k,
          Z^(sourceDyadExponent Z k)≤ rowNorm u ∧ rowNorm u≤2*Z^(sourceDyadExponent Z k)) ∧
        (∀u∈rows∩dyadicRows 1 k,rowNorm u≤Z^(sourceDyadConductor Z margin k-margin)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<(1/100:ℝ)-dmin by linarith)).eventually (eventually_ge_atTop (2:ℝ)),
    (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop (2:ℝ))] with Z hZ hsmall hmarginZ
  intro rows hrows k hne
  have hZp : 0<Z := zero_lt_one.trans hZ
  obtain ⟨u,hu⟩ := hne
  have hur := (Finset.mem_inter.mp hu).1
  have hud := mem_dyadicRows.mp (Finset.mem_inter.mp hu).2
  have hlow : (2:ℝ)^k≤ rowNorm u := by simpa only [one_mul] using hud.2.1
  have hhigh : rowNorm u<2*(2:ℝ)^k := by simpa only [one_mul] using hud.2.2
  have hv0 : 0≤ sourceDyadExponent Z k := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ,Real.rpow_zero]
    exact one_le_pow₀ (by norm_num)
  have hvmax : sourceDyadExponent Z k≤vmax := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ]
    exact hlow.trans (hrows u hur).2.2
  have hvmin : dmin≤ sourceDyadExponent Z k := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ]
    have hh : 2*Z^dmin≤Z^(1/100:ℝ) := by
      calc
        _ ≤ Z^((1/100:ℝ)-dmin)*Z^dmin := mul_le_mul_of_nonneg_right hsmall (by positivity)
        _ = _ := by rw [←Real.rpow_add hZp];congr 1;ring
    linarith [(hrows u hur).2.1]
  have hnorm : ∀u∈rows∩dyadicRows 1 k,
      Z^(sourceDyadExponent Z k)≤ rowNorm u ∧ rowNorm u≤2*Z^(sourceDyadExponent Z k) := by
    intro u hu
    rw [sourceDyad_scale hZ]
    have hh := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
    simpa only [one_mul] using And.intro hh.1 hh.2.le
  refine ⟨hv0,hvmax,?_,?_,hnorm,?_⟩
  · unfold sourceDyadConductor;linarith
  · unfold sourceDyadConductor;linarith
  · exact dyad_conductor_margin Z (sourceDyadExponent Z k) margin hZp hmarginZ _ (fun u hu=>(hnorm u hu).2)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Transport.PhysicalHigh.TunedData (LW56e2): numeric lemmas on the tuned data
namespace RH.Transport.PhysicalHigh
open OAI OAI.SevenEighths

lemma reservedLoss_pos : 0 < reservedLoss := by norm_num
lemma reservedLoss_le_one : reservedLoss ≤ 1 := by norm_num
lemma conductorCap_pos : 0 < conductorCap := by
  norm_num [conductorCap, TunedCandidate.h, TunedCandidate.hAt, TunedCandidate.ell,
    Geometry.ell, TunedCandidate.p, TunedCandidate.b, TunedCandidate.zeta]
lemma conductorCap_le_one : conductorCap ≤ 1 := by
  norm_num [conductorCap, TunedCandidate.h, TunedCandidate.hAt, TunedCandidate.ell,
    Geometry.ell, TunedCandidate.p, TunedCandidate.b, TunedCandidate.zeta]
lemma conductorCap_ge_dmin : (1 / 200 : ℝ) ≤ conductorCap := by
  norm_num [conductorCap, TunedCandidate.h, TunedCandidate.hAt, TunedCandidate.ell,
    Geometry.ell, TunedCandidate.p, TunedCandidate.b, TunedCandidate.zeta]
lemma conductorCap_supply : (7 / 37 : ℝ) * conductorCap ≤ TunedCandidate.ell := by
  norm_num [conductorCap, TunedCandidate.h, TunedCandidate.hAt, TunedCandidate.ell,
    Geometry.ell, TunedCandidate.p, TunedCandidate.b, TunedCandidate.zeta]


namespace TunedData
variable {Kmin : ℕ} {allowance : ℝ} (D : TunedData Kmin allowance)

lemma conductor_minimum : conductorCap * D.rmin = D.ellMin := by
  rw [D.rmin_eq]
  field_simp [conductorCap_pos.ne']

lemma slot_conductor_lower (j : Fin D.K) : conductorCap * D.rmin ≤ D.ell j := by
  rw [D.conductor_minimum]
  exact D.slots_lower j

lemma high_budget (heightCost : ℝ) (hh : heightCost ≤ reservedLoss) :
    (159 * D.P.ε + reservedLoss + reservedLoss + 7 * reservedLoss) + 2 * reservedLoss +
      (26 * D.P.e + (D.K + 8) * D.P.eps + reservedLoss + reservedLoss * TunedCandidate.ell) +
      (reservedLoss + heightCost + reservedLoss) + reservedLoss ≤ 3 / 4000000000000 := by
  have hc := D.P.central_budget
  have ht : (18 : ℝ) * reservedLoss ≤ 3 / 4000000000000 := by norm_num
  calc
    _ ≤ (159 * D.P.ε + reservedLoss + reservedLoss + 7 * reservedLoss) + 2 * reservedLoss +
      (26 * D.P.e + (D.K + 8) * D.P.eps + reservedLoss + reservedLoss * TunedCandidate.ell) +
      (reservedLoss + reservedLoss + reservedLoss) + reservedLoss := by gcongr
    _ ≤ 18 * reservedLoss := hc
    _ ≤ 3 / 4000000000000 := ht

lemma principal_budget : D.P.sigma + reservedLoss / 8 ≤ 1 / 4000 := by
  have hs := D.P.sigma_t
  norm_num at hs ⊢
  linarith

lemma geometric_budget : D.P.sigma + 8 * D.P.e + reservedLoss / 8 ≤ 1 / 20 := by
  have hs := D.P.sigma_t
  have he := D.P.e_small
  norm_num at hs ⊢
  linarith

lemma window_budget : D.P.sigma + D.P.e ≤ TunedCandidate.B * D.ellMin := by
  have hB : (1 / 2 : ℝ) ≤ TunedCandidate.B := by rw [TunedCandidate.boundary_value]; norm_num
  have hs := D.P.sigma_slot
  have he := D.P.e_slot
  have hh := mul_le_mul_of_nonneg_right hB D.ellMin_pos.le
  linarith

lemma floor_budget : 26 * D.P.e + (D.K + 8) * D.P.eps + reservedLoss +
    reservedLoss * TunedCandidate.ell + reservedLoss / 8 + D.P.sigma ≤ 1 / 200 := by
  have hc := D.P.central_budget
  have hs := D.P.sigma_t
  have hε := D.P.epsilon_pos
  norm_num at hc hs ⊢
  linarith

lemma central_saving : D.P.sigma + reservedLoss / 8 + reservedLoss / 8 ≤ reservedLoss := by
  have hs := D.P.sigma_t
  norm_num at hs ⊢
  linarith

end TunedData

end RH.Transport.PhysicalHigh
end

open RH RH.Transport RH.Transport.PhysicalHigh
open scoped Classical BigOperators ContDiff
open Filter
open OAI OAI.SevenEighths
open ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison
open HeckeInverseAmplification HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open ProbeMellinBoundary
noncomputable section

theorem solution (hβ : TunedCandidate.B<HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta≤7/8)
    {Kmin : ℕ} {allowance : ℝ} (D : TunedData Kmin allowance)
    {Δ : ℝ} {seed : HighData Δ} (F : SourceData seed)
    (hfirst : FirstTail (4*D.P.e) F.S)
    (counts : CountParameters F.modulus ⊤ reservedLoss) (τ : ℝ)
    (hτ : 0<τ) (hτd : τ<(1/200:ℝ)/2) (hτcost : 4*τ<(1/200:ℝ)*D.P.cost)
    (hτt : τ<reservedLoss) (hτ2 : 2*τ≤reservedLoss) (hτeps : τ*(2+4*D.P.eps)<reservedLoss) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∃Ct : ℝ,0<Ct ∧ ∀ᶠZ : ℝ in atTop,
      ∀C0 : ℝ,0≤C0 → TunedSourceMomentBound F D counts η Z τ (C0*Z^reservedLoss) (Z^(2*τ)) →
      ‖RH.Transport.dataProbe F D η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) (TunedCandidate.signal 0) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*D.P.eps))*Z^(TunedCandidate.signal HeckeZeroSupremum.beta-D.P.sigma) := by
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  have ht := reservedLoss_pos
  have ht1 := reservedLoss_le_one
  have hconductor : TunedCandidate.h+TunedCandidate.zeta+2*reservedLoss≤ conductorCap := le_rfl
  obtain ⟨n,hn,C,hC,hbound⟩ := RH.Transport.PhysicalHigh.actual_high_probe_from_raw_moments F.modulus ⊤ le_top D.K
    D.P.e D.P.eps 1 2 1 reservedLoss (1/200) conductorCap D.rmin τ D.P.ε D.P.κ D.P.cost reservedLoss reservedLoss reservedLoss
    D.P.e_pos D.P.e_small D.P.eps_pos (by norm_num) (by norm_num) (by norm_num)
    ht.le (by norm_num) conductorCap_pos.le conductorCap_ge_dmin D.rmin_pos hτ D.P.epsilon_pos D.P.kappa_pos
    D.P.cost_pos.le ht D.P.phase_budget D.P.epsilon_gap ht (by linarith) hτeps
    F.S F.exclusions hfirst F.maximal D.ell D.slots_injective
    D.slot_conductor_lower D.slots_upper
    (fun _=>F.w) (fun _=>F.support) (fun _=>F.smooth) (fun _=>F.bounded)
    (fun _=>F.compact) (fun _=>F.nonzero) D.slots_sum
    conductorCap_supply conductorCap_le_one D.P.epsilon_small D.P.kappa_small hτd hτcost (by nlinarith [D.P.detector_budget])
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    reservedLoss reservedLoss reservedLoss (2*τ) reservedLoss ht ht ht (by linarith)
    (2*reservedLoss) reservedLoss (by positivity) (D.high_budget (2*τ) hτ2)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (reservedLoss/8) (by positivity) (reservedLoss/8) (by positivity) (by norm_num) hconductor (by linarith) hβ.le hceiling
    D.P.sigma D.P.sigma_pos D.geometric_budget D.principal_budget (by simpa only [D.conductor_minimum] using D.window_budget) D.floor_budget D.central_saving counts
  refine ⟨C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,hb⟩ := hbound η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [hb,sourceDyad_geometry_eventually (1/200) conductorCap reservedLoss (TunedCandidate.h+TunedCandidate.zeta)
    (by norm_num) (by norm_num) ht hconductor,
    HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hb hgeo hnheight hZ
  intro C0 hC0 hmom
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,hestimate⟩ := hb
  apply hestimate C0 hC0
  intro k hk i hi j hj
  dsimp only
  intro hne t htheight
  let rows := supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^(TunedCandidate.h+TunedCandidate.zeta))) grid
  let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
  have hsub : rows'⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsubr : rows'⊆rows := hsub.trans Finset.inter_subset_left
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ Z^(TunedCandidate.h+TunedCandidate.zeta) := by
    intro u hu
    have hh := mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).1
    exact ⟨hh.1,hh.2.1,hh.2.2.le⟩
  have hg := hgeo rows hrows k (hne.mono hsub)
  have hi' : (i:ℝ)≤ n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hheight : (3*i+1:ℕ)*Z^τ≤ Z^(2*τ) := by
    have hZp : 0< Z := zero_lt_one.trans hZ
    calc
      _≤(3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
      _≤ Z^τ*Z^τ := mul_le_mul_of_nonneg_right hnheight (by positivity)
      _=Z^(2*τ) := by rw [←Real.rpow_add hZp];congr 1;ring
  apply hmom rows' (fun v hv=>(hrows v (hsubr hv)).2.1)
    (sourceDyadConductor Z reservedLoss k) hg.2.2.1
    (51/100+D.P.e*j) conductorCap reservedLoss reservedLoss i
    ((17/50:ℂ)+t.1.2*Complex.I)
  · simp
  · simpa using htheight.2.trans hheight


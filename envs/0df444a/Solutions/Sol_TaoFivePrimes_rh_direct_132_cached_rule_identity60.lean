-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_cached_rule_identity60
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:47:20.829986+00:00
-- url     : https://prove2.me/submissions/b69d5842-8b0a-4080-9169-129688117153

import Definitions.Def_TaoFivePrimes_RHDirect132CachedRule
import Definitions.Def_TaoFivePrimes_RHDirect132Rule
import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Theorems.Thm_TaoFivePrimes_rh_direct_132_analytic_gamma_correlation
import Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_cached_lookup
import Theorems.Thm_TaoFivePrimes_rh_direct_132_cached_phase_data
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RH14MomentEnclosureProof
section Height100Module1

set_option autoImplicit false
open Finset
open scoped BigOperators

namespace CertifiedMomentConvolution

lemma sum_triangle {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℕ → ℕ → R) :
    (∑ j ∈ range N, ∑ m ∈ range (j+1), f m (j-m)) =
      ∑ m ∈ range N, ∑ l ∈ range (N-m), f m l := by
  classical
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun x _ => ⟨x.2, x.1-x.2⟩)
  · intro x hx
    simp only [mem_sigma, mem_range] at hx ⊢
    omega
  · intro x hx y hy hxy
    simp only [mem_sigma, mem_range] at hx hy
    have h1 := congrArg Sigma.fst hxy
    have h2 := congrArg (fun z : Sigma (fun _ : ℕ => ℕ) => z.2) hxy
    apply Sigma.ext <;> simp_all
    omega
  · intro y hy
    simp only [mem_sigma, mem_range] at hy
    refine ⟨⟨y.1+y.2, y.1⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]
      omega
    · simp
  · intro x hx
    rfl

/-- A truncated convolution can be integrated by first correlating the base
coefficients with the integration weights. -/
theorem integrated_convolution {R : Type*} [CommSemiring R]
    (N : ℕ) (a h w : ℕ → R) :
    (∑ j ∈ range N, (∑ m ∈ range (j+1), a m * h (j-m)) * w j) =
      ∑ m ∈ range N, a m * (∑ l ∈ range (N-m), h l * w (m+l)) := by
  simp_rw [sum_mul]
  calc
    (∑ j ∈ range N, ∑ m ∈ range (j+1), a m * h (j-m) * w j) =
        ∑ j ∈ range N, ∑ m ∈ range (j+1), a m * h (j-m) * w (m+(j-m)) := by
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intro m hm
      congr 2
      have hmj : m≤ j := by simpa using mem_range.mp hm
      omega
    _ = ∑ m ∈ range N, ∑ l ∈ range (N-m), a m * h l * w (m+l) :=
      sum_triangle N (fun m l => a m * h l * w (m+l))
    _ = _ := by simp_rw [mul_sum, mul_assoc]

/-- The common base correlation is independent of the moment order. -/
noncomputable def correlation {R : Type*} [Semiring R] (N : ℕ) (h w : ℕ → R) (m : ℕ) : R :=
  ∑ l ∈ range (N-m), h l * w (m+l)

end CertifiedMomentConvolution

end Height100Module1

end RH14MomentEnclosureProof

open Complex Finset
open RH14MomentEnclosureProof.CertifiedMomentConvolution

namespace Direct132Correlation

lemma triple_convolution (N : ℕ) (p e b w : ℕ → ℂ) (φ : ℂ) :
    (∑ j ∈ range N, w j *
      ∑ m ∈ range (j+1), p m *
        ∑ l ∈ range (j-m+1), e l*(φ*b (j-m-l))) =
      φ * ∑ m ∈ range N, p m *
        ∑ l ∈ range (N-m), e l *
          ∑ r ∈ range (N-m-l), b r*w (m+l+r) := by
  have h0 :
      (∑ j ∈ range N, w j *
        ∑ m ∈ range (j+1), p m *
          ∑ l ∈ range (j-m+1), e l*(φ*b (j-m-l))) =
      φ * ∑ j ∈ range N,
        (∑ m ∈ range (j+1), p m *
          ∑ l ∈ range (j-m+1), e l*b (j-m-l))*w j := by
    simp only [mul_sum,sum_mul]
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro l hl
    ring
  rw [h0]
  congr 1
  rw [integrated_convolution N p (fun j =>
    ∑ l ∈ range (j+1), e l*b (j-l)) w]
  apply sum_congr rfl
  intro m hm
  congr 1
  have h := integrated_convolution (N-m) e b (fun r => w (m+r))
  simpa only [Nat.add_assoc] using h

end Direct132Correlation

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Complex Finset

namespace Direct132PowerJet

lemma center_eq (i : ℕ) :
    RHDirect132Rule.center i = (3:ℂ)*((2*i+1:ℕ):ℂ)/16 := by
  unfold RHDirect132Rule.center
  push_cast
  ring

lemma power_jet (i k m : ℕ) (hm : m≤k) :
    RHDirect132Rule.powerJet i k m =
      (3:ℂ)^k*((2*i+1:ℕ):ℂ)^(k-m)*(Nat.choose k m:ℂ)/
        ((16:ℂ)^k*(k.factorial:ℂ)) := by
  have hchoose : (Nat.choose k m:ℂ)*(m.factorial:ℂ)*((k-m).factorial:ℂ) =
      (k.factorial:ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hm
  have hm0 : (m.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hkm0 : ((k-m).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k-m)
  have hk0 : (k.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h16 : (16:ℂ)^k ≠ 0 := pow_ne_zero k (by norm_num)
  have h16a : (16:ℂ)^(k-m) ≠ 0 := pow_ne_zero (k-m) (by norm_num)
  have h16b : (16:ℂ)^m ≠ 0 := pow_ne_zero m (by norm_num)
  have hp3 : (3:ℂ)^(k-m)*(3:ℂ)^m=(3:ℂ)^k := by
    rw [←pow_add,Nat.sub_add_cancel hm]
  have hp16 : (16:ℂ)^(k-m)*(16:ℂ)^m=(16:ℂ)^k := by
    rw [←pow_add,Nat.sub_add_cancel hm]
  unfold RHDirect132Rule.powerJet
  rw [if_pos hm,center_eq]
  rw [div_pow,mul_pow,div_pow]
  field_simp
  rw [←hp3,←hp16,←hchoose]
  ring

end Direct132PowerJet

namespace Direct132PanelWorking
open Direct132Correlation Direct132PowerJet

lemma panel_rearranged (i k : ℕ) (hi : i<16) (hk : k<60) :
    RHDirect132Rule.panel i k =
      (3/16:ℂ)*RHDirectPhase132.asComplex (RHDirectPhase132.panels i) *
        ∑ m ∈ range (k+1), RHDirect132Rule.powerJet i k m *
          ((((RHDirect132CachedRule.gamma i m).1:ℤ):ℂ) +
            Complex.I*(((RHDirect132CachedRule.gamma i m).2:ℤ):ℂ))/
          ((CertifiedFixedPoint.scale310:ℂ)*(RHNextMomentInteger.weightDenominator:ℂ)*
            ((8:ℂ)^183*((183:ℕ).factorial:ℂ))) := by
  have houter :
      (∑ m ∈ range 184, RHDirect132Rule.powerJet i k m *
        ∑ l ∈ range (184-m), RHDirect132Rule.phaseJet l *
          ∑ r ∈ range (184-m-l), RHDirect132Rule.baseJet i r *
            RHDirect132Rule.weight (m+l+r)) =
      ∑ m ∈ range (k+1), RHDirect132Rule.powerJet i k m *
        ((((RHDirect132CachedRule.gamma i m).1:ℤ):ℂ) +
          Complex.I*(((RHDirect132CachedRule.gamma i m).2:ℤ):ℂ))/
        ((CertifiedFixedPoint.scale310:ℂ)*(RHNextMomentInteger.weightDenominator:ℂ)*
          ((8:ℂ)^183*((183:ℕ).factorial:ℂ))) := by
    rw [←Finset.sum_subset (Finset.range_mono (by omega : k+1≤184))]
    · apply sum_congr rfl
      intro m hm
      have hmk : m≤k := by have := mem_range.mp hm; omega
      have hm60 : m<60 := by omega
      have hm184 : m<184 := by omega
      rw [TaoFivePrimes.rh_direct_132_analytic_gamma_correlation i m hi hm184]
      rw [TaoFivePrimes.rh_direct_132_gamma_cached_lookup i m hi hm60]
      simp only [Prod.fst,Prod.snd,div_eq_mul_inv]
      ring
    · intro m hm184 hmk
      have hnot : ¬m≤k := by simp only [mem_range] at hmk; omega
      simp [RHDirect132Rule.powerJet,hnot]
  unfold RHDirect132Rule.panel
  rw [triple_convolution 184 (RHDirect132Rule.powerJet i k)
    RHDirect132Rule.phaseJet (RHDirect132Rule.baseJet i) RHDirect132Rule.weight
    (RHDirectPhase132.asComplex (RHDirectPhase132.panels i)),houter]
  ring

lemma panel_value (i k : ℕ) (hi : i<16) (hk : k<60) :
    RHDirect132Rule.panel i k =
      (3:ℂ)^(k+1)*
        ((((RHDirect132CachedRule.phaseData.getD i (0,0)).1:ℤ):ℂ) +
          Complex.I*(((RHDirect132CachedRule.phaseData.getD i (0,0)).2:ℤ):ℂ))*
        ((RHDirect132CachedRule.panelRe i k:ℂ)+
          Complex.I*(RHDirect132CachedRule.panelIm i k:ℂ))/
      (RHDirect132CachedRule.denominator k:ℂ) := by
  have hgamma :
      (∑ m ∈ range (k+1), (RHDirect132CachedRule.weight i k m:ℂ)*
        ((((RHDirect132CachedRule.gamma i m).1:ℤ):ℂ) +
          Complex.I*(((RHDirect132CachedRule.gamma i m).2:ℤ):ℂ))) =
      ((RHDirect132CachedRule.panelRe i k:ℂ)+
        Complex.I*(RHDirect132CachedRule.panelIm i k:ℂ)) := by
    unfold RHDirect132CachedRule.panelRe RHDirect132CachedRule.panelIm
    push_cast
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    ring
  have hsum :
      (∑ m ∈ range (k+1), RHDirect132Rule.powerJet i k m *
        ((((RHDirect132CachedRule.gamma i m).1:ℤ):ℂ) +
          Complex.I*(((RHDirect132CachedRule.gamma i m).2:ℤ):ℂ))/
        ((CertifiedFixedPoint.scale310:ℂ)*(RHNextMomentInteger.weightDenominator:ℂ)*
          ((8:ℂ)^183*((183:ℕ).factorial:ℂ)))) =
      (3:ℂ)^k/((16:ℂ)^k*(k.factorial:ℂ)*
        ((CertifiedFixedPoint.scale310:ℂ)*(RHNextMomentInteger.weightDenominator:ℂ)*
          ((8:ℂ)^183*((183:ℕ).factorial:ℂ)))) *
        ((RHDirect132CachedRule.panelRe i k:ℂ)+
          Complex.I*(RHDirect132CachedRule.panelIm i k:ℂ)) := by
    rw [←hgamma,Finset.mul_sum]
    apply sum_congr rfl
    intro m hm
    have hmk : m≤k := by have := mem_range.mp hm; omega
    rw [power_jet i k m hmk]
    unfold RHDirect132CachedRule.weight
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [panel_rearranged i k hi hk,hsum]
  unfold RHDirectPhase132.asComplex
  rw [←TaoFivePrimes.rh_direct_132_cached_phase_data ⟨i,hi⟩]
  unfold RHDirect132CachedRule.denominator
  push_cast
  rw [pow_succ]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma rule_cached (k : ℕ) (hk : k<60) :
    RHDirect132Rule.rule k = RHDirect132CachedRule.value k := by
  have hpanels :
      (∑ i ∈ range 16, RHDirect132Rule.panel i k) =
      ∑ i ∈ range 16,
        (3:ℂ)^(k+1)*
          ((((RHDirect132CachedRule.phaseData.getD i (0,0)).1:ℤ):ℂ) +
            Complex.I*(((RHDirect132CachedRule.phaseData.getD i (0,0)).2:ℤ):ℂ))*
          ((RHDirect132CachedRule.panelRe i k:ℂ)+
            Complex.I*(RHDirect132CachedRule.panelIm i k:ℂ))/
        (RHDirect132CachedRule.denominator k:ℂ) := by
    apply sum_congr rfl
    intro i hi
    exact panel_value i k (mem_range.mp hi) hk
  have hnum :
      (∑ i ∈ range 16,
        ((((RHDirect132CachedRule.phaseData.getD i (0,0)).1:ℤ):ℂ) +
          Complex.I*(((RHDirect132CachedRule.phaseData.getD i (0,0)).2:ℤ):ℂ))*
        ((RHDirect132CachedRule.panelRe i k:ℂ)+
          Complex.I*(RHDirect132CachedRule.panelIm i k:ℂ))) =
      ((RHDirect132CachedRule.numeratorRe k:ℂ)+
        Complex.I*(RHDirect132CachedRule.numeratorIm k:ℂ)) := by
    unfold RHDirect132CachedRule.numeratorRe RHDirect132CachedRule.numeratorIm
    push_cast
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    ring_nf
    simp only [Complex.I_sq]
    ring
  unfold RHDirect132Rule.rule
  rw [hpanels]
  unfold RHDirect132CachedRule.value
  rw [←hnum,Finset.mul_sum,Finset.sum_div]
  apply sum_congr rfl
  intro i hi
  ring

end Direct132PanelWorking

theorem solution (k : ℕ) (hk : k<60) :
    RHDirect132Rule.rule k = RHDirect132CachedRule.value k :=
  Direct132PanelWorking.rule_cached k hk

-- Prove2me | solution 1 for SmoothJordanDomain.closure_support_and_carrier_strict_of_support_at_mem_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:32:36.046207+00:00
-- url     : https://prove2.me/submissions/3c70a11e-b26e-4622-8d8e-dbb2136f3ad1

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
section
open Complex Set
open scoped Real
private theorem realCLM_apply_eq_re_im
    (f : ℂ →L[ℝ] ℝ) (z : ℂ) :
    f z = z.re * f 1 + z.im * f I := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [map_add]
  rw [show (z.re : ℂ) = z.re • (1 : ℂ) by
      rw [Complex.real_smul, mul_one],
    show z.im * I = z.im • I by
      rw [Complex.real_smul],
    map_smul, map_smul]
  simp only [smul_eq_mul]
end

set_option autoImplicit false
open Complex Set
open scoped Real
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (t : ℝ)
    (hcside :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    (∀ z ∈ closure Omega.carrier,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (z - Omega.boundaryParam t)).re ≤ 0) ∧
    ∀ z ∈ Omega.carrier,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (z - Omega.boundaryParam t)).re < 0 := by
  let gamma := Omega.boundaryParam
  let D := deriv gamma t
  have hgammaFrontier : gamma t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hgammaNot : gamma t ∉ Omega.carrier := by
    intro hmem
    have hempty : gamma t ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hmem, hgammaFrontier⟩
    exact hempty
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point
    Omega.strictConvex_carrier.convex Omega.isOpen_carrier hgammaNot
  have hfclosed : IsClosed {z : ℂ | f z ≤ f (gamma t)} :=
    isClosed_le f.continuous continuous_const
  have hfcarrier : Omega.carrier ⊆ {z : ℂ | f z ≤ f (gamma t)} := by
    intro z hz
    exact (hf z hz).le
  have hfclosure : closure Omega.carrier ⊆
      {z : ℂ | f z ≤ f (gamma t)} :=
    closure_minimal hfcarrier hfclosed
  have hfall : ∀ s, f (gamma s) ≤ f (gamma t) := by
    intro s
    exact hfclosure (frontier_subset_closure (by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self s))
  have hlocal : IsLocalMax (f ∘ gamma) t :=
    Filter.Eventually.of_forall hfall
  have hgammaDeriv : HasDerivAt gamma D t :=
    (Omega.boundaryParam_contDiff.differentiable (by norm_num) t).hasDerivAt
  have hcompDeriv := f.hasFDerivAt.comp_hasDerivAt t hgammaDeriv
  have hfD : f D = 0 := by
    rw [← hcompDeriv.deriv]
    exact hlocal.deriv_eq_zero
  let alpha := f 1
  let beta := f I
  let nsq := Complex.normSq D
  let lambda := (D.im * alpha - D.re * beta) / nsq
  have hDcoord : D.re * alpha + D.im * beta = 0 := by
    simpa only [alpha, beta] using
      (realCLM_apply_eq_re_im f D).symm.trans hfD
  have hnsq : nsq ≠ 0 := by
    dsimp only [nsq]
    intro hzero
    exact Omega.boundaryParam_regular t
      (Complex.normSq_eq_zero.mp hzero)
  have halpha : alpha = lambda * D.im := by
    dsimp only [lambda, nsq]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hnsq).2
    dsimp only [nsq]
    rw [Complex.normSq_apply, ← sub_eq_zero]
    calc
      alpha * (D.re * D.re + D.im * D.im) -
          (D.im * alpha - D.re * beta) * D.im =
        D.re * (D.re * alpha + D.im * beta) := by ring
      _ = 0 := by rw [hDcoord, mul_zero]
  have hbeta : beta = lambda * (-D.re) := by
    dsimp only [lambda, nsq]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hnsq).2
    dsimp only [nsq]
    rw [Complex.normSq_apply, ← sub_eq_zero]
    calc
      beta * (D.re * D.re + D.im * D.im) -
          (D.im * alpha - D.re * beta) * (-D.re) =
        D.im * (D.re * alpha + D.im * beta) := by ring
      _ = 0 := by rw [hDcoord, mul_zero]
  have hf_normal : ∀ z : ℂ,
      f z = lambda *
        ((starRingEnd ℂ) (-I * D) * z).re := by
    intro z
    rw [realCLM_apply_eq_re_im f z]
    change z.re * alpha + z.im * beta = _
    rw [halpha, hbeta]
    simp only [map_mul, map_neg, Complex.conj_I, Complex.mul_re,
      Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.conj_re, Complex.conj_im]
    ring
  have hfcneg : f (c - gamma t) < 0 := by
    have hlt := hf c hc
    rw [map_sub]
    linarith
  have hNcneg :
      ((starRingEnd ℂ) (-I * D) * (c - gamma t)).re < 0 := by
    apply lt_of_le_of_ne hcside
    intro hzero
    rw [hf_normal, hzero, mul_zero] at hfcneg
    exact lt_irrefl 0 hfcneg
  have hlambda : 0 < lambda := by
    rw [hf_normal] at hfcneg
    rcases mul_neg_iff.mp hfcneg with h | h
    · exact h.1
    · exact (not_lt_of_ge hNcneg.le h.2).elim
  constructor
  · intro z hz
    have hfz : f (z - gamma t) ≤ 0 := by
      rw [map_sub]
      have hle := hfclosure hz
      exact sub_nonpos.mpr hle
    rw [hf_normal] at hfz
    nlinarith only [hfz, hlambda]
  · intro z hz
    have hfz : f (z - gamma t) < 0 := by
      rw [map_sub]
      exact sub_neg.mpr (hf z hz)
    rw [hf_normal] at hfz
    nlinarith only [hfz, hlambda]
end SmoothJordanDomain

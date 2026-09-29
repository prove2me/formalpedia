-- Prove2me | solution 1 for RegularSingular.exists_twoLevel_coeff_of_transport_of_slice_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/02b08ea3-243e-54ad-8100-f36ec29af480

import Theorems.Thm_RegularSingular_exists_transferMatrix_expLogExpansion_rescale_expTwist
import Theorems.Thm_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RegularSingular_exists_twoLevel_coeff_of_transport_of_slice_expansion

set_option autoImplicit false
set_option maxHeartbeats 6400000

open Finset Filter Topology

section Canonical

private theorem continuous_coeff_of_local_expansion {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    {n J : ℕ} (e : Fin n → ℂ) (θ : ℝ)
    (F : P → ℝ → ℂ) (hF : ∀ y ∈ Set.Ioc (0 : ℝ) 1, Continuous fun p => F p y)
    (c : P → Fin n → Fin J → ℂ)
    (hBloc : ∀ p₀ : P, ∃ B₀ : ℝ, ∀ᶠ p in 𝓝 p₀, ∀ i j, ‖c p i j‖ ≤ B₀)
    (hexp : ∀ p₀ : P, ∃ C₀ : ℝ, ∀ᶠ p in 𝓝 p₀, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F p y - ∑ i : Fin n, ∑ j : Fin J, c p i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
        C₀ * y ^ θ)
    (huniq : ∀ (d : Fin n → Fin J → ℂ) (C' : ℝ),
      (∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖∑ i : Fin n, ∑ j : Fin J, d i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C' * y ^ θ) →
      d = 0) :
    Continuous c := by
  classical
  rw [continuous_iff_seqContinuous]
  intro x p₀ hx
  obtain ⟨C₀, hC₀⟩ := hexp p₀
  obtain ⟨B₀, hB₀⟩ := hBloc p₀
  have hCseq : ∀ᶠ k in atTop, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F (x k) y - ∑ i : Fin n, ∑ j : Fin J, c (x k) i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
        C₀ * y ^ θ := hx.eventually hC₀
  have hBseq : ∀ᶠ k in atTop, ∀ i j, ‖c (x k) i j‖ ≤ B₀ := hx.eventually hB₀
  refine tendsto_of_subseq_tendsto fun φ hφ => ?_
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hBseq
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hφ.eventually (eventually_ge_atTop N₀))

  set v : ℕ → (Fin n → Fin J → ℂ) := fun k => c (x (φ (k + N))) with hv
  have hbdd : ∀ k, v k ∈ Metric.closedBall (0 : Fin n → Fin J → ℂ) (max B₀ 0) := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right]
    have hk : N₀ ≤ φ (k + N) := hN (k + N) (Nat.le_add_left N k)
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun j => ?_
    exact (hN₀ _ hk i j).trans (le_max_left _ _)
  obtain ⟨a, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbdd

  have hidx : Tendsto (fun k => φ (ψ k + N)) atTop atTop :=
    hφ.comp ((tendsto_add_atTop_nat N).comp hψ.tendsto_atTop)
  have hxs : Tendsto (fun k => x (φ (ψ k + N))) atTop (𝓝 p₀) := hx.comp hidx

  have hlim_exp : ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F p₀ y - ∑ i : Fin n, ∑ j : Fin J, a i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
        C₀ * y ^ θ := by
    intro y hy
    have hFlim : Tendsto (fun k => F (x (φ (ψ k + N))) y) atTop (𝓝 (F p₀ y)) :=
      ((hF y hy).tendsto p₀).comp hxs
    have hclim : ∀ i j, Tendsto (fun k => (v ∘ ψ) k i j) atTop (𝓝 (a i j)) :=
      fun i j => tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim i) j
    have hsumlim : Tendsto (fun k => ∑ i : Fin n, ∑ j : Fin J,
        (v ∘ ψ) k i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))) atTop
        (𝓝 (∑ i : Fin n, ∑ j : Fin J, a i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)))) := by
      refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
      exact (hclim i j).mul tendsto_const_nhds
    have hdiff : Tendsto (fun k => ‖F (x (φ (ψ k + N))) y - ∑ i : Fin n, ∑ j : Fin J,
        (v ∘ ψ) k i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖) atTop
        (𝓝 ‖F p₀ y - ∑ i : Fin n, ∑ j : Fin J, a i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖) :=
      (hFlim.sub hsumlim).norm
    refine le_of_tendsto hdiff ?_
    have hCev := hidx.eventually hCseq
    filter_upwards [hCev] with k hk
    exact hk y hy

  have ha : a = c p₀ := by
    have h0 := huniq (a - c p₀) (C₀ + C₀) (fun y hy => ?_)
    · exact sub_eq_zero.1 h0
    have h1 := hlim_exp y hy
    have h2 := hC₀.self_of_nhds y hy
    have hsplit : ∑ i : Fin n, ∑ j : Fin J,
        (a - c p₀) i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) =
        (F p₀ y - ∑ i : Fin n, ∑ j : Fin J, c p₀ i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))) -
        (F p₀ y - ∑ i : Fin n, ∑ j : Fin J, a i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))) := by
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hsplit, add_mul]
    exact (norm_sub_le _ _).trans (add_le_add h2 h1)
  refine ⟨fun k => ψ k + N, ?_⟩
  rw [← ha]
  exact hlim

private theorem exists_canonical_coeff {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    {n J : ℕ} (e : Fin n → ℂ) (θ : ℝ)
    (F : P → ℝ → ℂ) (hF : ∀ y ∈ Set.Ioc (0 : ℝ) 1, Continuous fun p => F p y)
    (hloc : ∀ p₀ : P, ∃ C B : ℝ, ∀ᶠ p in 𝓝 p₀, ∃ v : Fin n → Fin J → ℂ, (∀ i j, ‖v i j‖ ≤ B) ∧
      ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖F p y - ∑ i : Fin n, ∑ j : Fin J, v i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
          C * y ^ θ)
    (huniq : ∀ (d : Fin n → Fin J → ℂ) (C' : ℝ),
      (∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖∑ i : Fin n, ∑ j : Fin J, d i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C' * y ^ θ) →
      d = 0) :
    ∃ c : P → Fin n → Fin J → ℂ, Continuous c ∧
      (∀ p₀ : P, ∃ C : ℝ, ∀ᶠ p in 𝓝 p₀, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖F p y - ∑ i : Fin n, ∑ j : Fin J, c p i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
          C * y ^ θ) ∧
      (∀ K : Set P, IsCompact K → ∃ C : ℝ, ∀ p ∈ K, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖F p y - ∑ i : Fin n, ∑ j : Fin J, c p i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
          C * y ^ θ) := by
  classical

  have hex : ∀ p : P, ∃ v : Fin n → Fin J → ℂ, ∃ C : ℝ, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F p y - ∑ i : Fin n, ∑ j : Fin J, v i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
        C * y ^ θ := by
    intro p
    obtain ⟨C, B, hCB⟩ := hloc p
    obtain ⟨v, -, hv⟩ := hCB.self_of_nhds
    exact ⟨v, C, hv⟩
  choose c Cc hc using hex

  have hloc' : ∀ p₀ : P, ∃ C B : ℝ, ∀ᶠ p in 𝓝 p₀, (∀ i j, ‖c p i j‖ ≤ B) ∧
      ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖F p y - ∑ i : Fin n, ∑ j : Fin J, c p i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
          C * y ^ θ := by
    intro p₀
    obtain ⟨C, B, hCB⟩ := hloc p₀
    refine ⟨C, B, ?_⟩
    filter_upwards [hCB] with p hp
    obtain ⟨v, hvB, hv⟩ := hp
    have hvc : v = c p := by
      have h0 := huniq (v - c p) (Cc p + C) (fun y hy => ?_)
      · exact sub_eq_zero.1 h0
      have hsplit : ∑ i : Fin n, ∑ j : Fin J,
          (v - c p) i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) =
          (F p y - ∑ i : Fin n, ∑ j : Fin J, c p i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))) -
          (F p y - ∑ i : Fin n, ∑ j : Fin J, v i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))) := by
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
        ring
      rw [hsplit, add_mul]
      exact (norm_sub_le _ _).trans (add_le_add (hc p y hy) (hv y hy))
    rw [← hvc]
    exact ⟨hvB, hv⟩
  have hexp : ∀ p₀ : P, ∃ C : ℝ, ∀ᶠ p in 𝓝 p₀, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F p y - ∑ i : Fin n, ∑ j : Fin J, c p i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
        C * y ^ θ := by
    intro p₀
    obtain ⟨C, B, h⟩ := hloc' p₀
    exact ⟨C, h.mono fun p hp => hp.2⟩
  refine ⟨c, ?_, hexp, ?_⟩
  · refine continuous_coeff_of_local_expansion e θ F hF c ?_ hexp huniq
    intro p₀
    obtain ⟨C, B, h⟩ := hloc' p₀
    exact ⟨B, h.mono fun p hp => hp.1⟩
  · intro K hK
    choose Cl hCl using hexp
    obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun p _ => {p' | ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F p' y - ∑ i : Fin n, ∑ j : Fin J, c p' i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
        Cl p * y ^ θ}) (fun p _ => hCl p)
    refine ⟨∑ x ∈ t, |Cl x|, fun p hp y hy => ?_⟩
    obtain ⟨x, hxt, hpx⟩ := Set.mem_iUnion₂.1 (ht hp)
    have h1 := hpx y hy
    have h2 : Cl x ≤ ∑ x ∈ t, |Cl x| :=
      (le_abs_self _).trans
        (Finset.single_le_sum (f := fun x : ↥K => |Cl x|) (fun x _ => abs_nonneg (Cl x)) hxt)
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hy.1.le θ))

end Canonical

section Helpers

private theorem huniq_family {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ)
    (hre : ∀ i, (e i).re ≤ ρ) (hδ : 0 < δ) (dd : Fin n → Fin J → ℂ) (C' : ℝ)
    (hdd : ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖∑ i : Fin n, ∑ j : Fin J, dd i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C' * y ^ (ρ + δ)) :
    dd = 0 := by
  have hS4 := LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
    (ι := Fin n × Fin J) (fun ij => e ij.1) (fun ij => (ij.2 : ℕ)) (fun ij => dd ij.1 ij.2)
    (by
      intro ij ij' h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (he h.1) (Fin.ext h.2))
    (ρ + δ)
    (fun y => ∑ i : Fin n, ∑ j : Fin J, dd i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)))
    (fun _ => 0)
    (by
      intro y _ _
      simp [Fintype.sum_prod_type])
    ⟨0, fun y _ _ => by simp⟩
    ⟨C', fun y hy0 hy1 => hdd y ⟨hy0, hy1⟩⟩
  funext i j
  exact hS4 (i, j) (by simp only; linarith [hre i])

private theorem coeff_eq_of_two_expansions {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ)
    (hre : ∀ i, (e i).re ≤ ρ) (hδ : 0 < δ) (F : ℝ → ℂ) (a b : Fin n → Fin J → ℂ)
    (ha : ∃ Ca : ℝ, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F y - ∑ i : Fin n, ∑ j : Fin J, a i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ Ca * y ^ (ρ + δ))
    (hb : ∃ Cb : ℝ, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F y - ∑ i : Fin n, ∑ j : Fin J, b i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ Cb * y ^ (ρ + δ)) :
    a = b := by
  obtain ⟨Ca, ha⟩ := ha
  obtain ⟨Cb, hb⟩ := hb
  have h0 := huniq_family e he ρ δ hre hδ (a - b) (Cb + Ca) (fun y hy => ?_)
  · exact sub_eq_zero.1 h0
  have hsplit : ∑ i : Fin n, ∑ j : Fin J,
      (a - b) i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) =
      (F y - ∑ i : Fin n, ∑ j : Fin J, b i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))) -
      (F y - ∑ i : Fin n, ∑ j : Fin J, a i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))) := by
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsplit, add_mul]
  exact (norm_sub_le _ _).trans (add_le_add (hb y hy) (ha y hy))

private theorem rpow_le_max_of_mem_Icc (r a b z : ℝ) (ha : 0 < a) (hz : z ∈ Set.Icc a b) :
    z ^ r ≤ max (a ^ r) (b ^ r) := by
  have hzpos : 0 < z := ha.trans_le hz.1
  rcases le_or_gt 0 r with h | h
  · exact (Real.rpow_le_rpow hzpos.le hz.2 h).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos ha hz.1 h.le).trans (le_max_left _ _)

private theorem exists_depth {n : ℕ} (e : Fin n → ℂ) (ρ δ aB : ℝ) :
    ∃ Kd : ℕ, aB / (Kd + 1) ≤ 1 / 2 ∧ ∀ i, ρ + δ + 1 ≤ (e i).re + Kd := by
  classical
  refine ⟨⌈2 * aB⌉₊ + ⌈ρ + δ + 1 + ∑ i : Fin n, |(e i).re|⌉₊, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have h1 : 2 * aB ≤ (⌈2 * aB⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ⌈ρ + δ + 1 + ∑ i : Fin n, |(e i).re|⌉₊]
  · intro i
    have h1 : ρ + δ + 1 + ∑ i : Fin n, |(e i).re| ≤ (⌈ρ + δ + 1 + ∑ i : Fin n, |(e i).re|⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : |(e i).re| ≤ ∑ i : Fin n, |(e i).re| :=
      Finset.single_le_sum (f := fun i => |(e i).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h4 := neg_abs_le (e i).re
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ⌈2 * aB⌉₊]

private theorem norm_twoPiI_mul_div_le (n₁ nB lam lam₀ : ℝ) (hn : |n₁| ≤ nB) (hnB : 0 ≤ nB) (hlam₀ : 0 < lam₀)
    (hlam : lam₀ ≤ lam) :
    ‖(2 * Real.pi * Complex.I * (n₁ : ℂ)) / ((lam : ℝ) : ℂ)‖ ≤ 2 * Real.pi * nB / lam₀ ∧
      ((2 * Real.pi * Complex.I * (n₁ : ℂ)) / ((lam : ℝ) : ℂ)).re = 0 := by
  have hlam_pos : 0 < lam := hlam₀.trans_le hlam
  have hanorm : ‖2 * Real.pi * Complex.I * (n₁ : ℂ)‖ = 2 * Real.pi * |n₁| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  constructor
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam_pos, hanorm]
    have h1 : 2 * Real.pi * |n₁| ≤ 2 * Real.pi * nB := mul_le_mul_of_nonneg_left hn (by positivity)
    calc 2 * Real.pi * |n₁| / lam ≤ 2 * Real.pi * nB / lam := div_le_div_of_nonneg_right h1 hlam_pos.le
      _ ≤ 2 * Real.pi * nB / lam₀ := div_le_div_of_nonneg_left (by positivity) hlam₀ hlam
  · rw [Complex.div_ofReal_re]
    simp [Complex.mul_re, Complex.mul_im]

private theorem norm_sum_mul_sub_le {ι : Type*} [Fintype ι] (L : ι → ℂ) (Lb : ℝ) (hL : ∀ s, ‖L s‖ ≤ Lb)
    (f g : ι → ℂ) (Cx : ℝ) (h : ∀ s, ‖f s - g s‖ ≤ Cx) :
    ‖∑ s, L s * f s - ∑ s, L s * g s‖ ≤ Fintype.card ι * Lb * Cx := by
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ s, ‖L s * f s - L s * g s‖ ≤ ∑ _s : ι, Lb * Cx := Finset.sum_le_sum fun s _ => by
        rw [← mul_sub, norm_mul]
        exact mul_le_mul (hL s) (h s) (norm_nonneg _) ((norm_nonneg _).trans (hL s))
    _ = Fintype.card ι * Lb * Cx := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Helpers

section Passages

variable {P : Type*} [TopologicalSpace P]

private theorem exists_bound_W (W : ℝ → ℝ → P → ℂ)
    (hWc : ContinuousOn (fun w : ℝ × ℝ × P => W w.1 w.2.1 w.2.2) (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ))
    (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (K₀ : Set P) (hK₀ : IsCompact K₀) :
    ∃ W₀ : ℝ, 0 ≤ W₀ ∧ ∀ s ∈ Set.Icc a₁ b₁, ∀ z ∈ Set.Icc a₂ b₂, ∀ k ∈ K₀, ‖W s z k‖ ≤ W₀ := by
  have hcomp : IsCompact (Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂ ×ˢ K₀) := isCompact_Icc.prod (isCompact_Icc.prod hK₀)
  have hsub : Set.Icc a₁ b₁ ×ˢ Set.Icc a₂ b₂ ×ˢ K₀ ⊆ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set P) := by
    rintro ⟨s, z, k⟩ ⟨hs, hz, -⟩
    exact ⟨ha₁.trans_le hs.1, ha₂.trans_le hz.1, Set.mem_univ _⟩
  obtain ⟨W₀, hW₀⟩ := hcomp.exists_bound_of_continuousOn (hWc.mono hsub)
  refine ⟨max W₀ 0, le_max_right _ _, fun s hs z hz k hk => ?_⟩
  exact (hW₀ (s, z, k) ⟨hs, hz, hk⟩).trans (le_max_left _ _)

private theorem level1_passage
    {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    (S : Set P) (W : ℝ → ℝ → P → ℂ)
    (hWc : ContinuousOn (fun w : ℝ × ℝ × P => W w.1 w.2.1 w.2.2) (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ))
    (htrans : ∀ K : Set P, IsCompact K → ∃ (lam₀ nB Ω : ℝ) (K₀ : Set P), 0 < lam₀ ∧ lam₀ ≤ 1 ∧ 0 ≤ nB ∧
      0 ≤ Ω ∧ IsCompact K₀ ∧ K₀ ⊆ S ∧ ∀ g ∈ K, ∃ (lam τ n₁ n₂ : ℝ) (κ₁ : ℂ) (k' : P), k' ∈ K₀ ∧
        lam₀ ≤ lam ∧ lam ≤ lam₀⁻¹ ∧ lam₀ ≤ τ ∧ τ ≤ lam₀⁻¹ ∧ |n₁| ≤ nB ∧ |n₂| ≤ nB ∧ ‖κ₁‖ ≤ Ω ∧
        ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
          W y₁ y₂ g = κ₁ * Complex.exp (2 * Real.pi * Complex.I * ((y₁ * n₁ + y₂ * n₂ : ℝ) : ℂ)) *
            W (lam * y₁) (τ * y₂) k')
    (hslice : ∀ K₀ : Set P, IsCompact K₀ → K₀ ⊆ S → ∀ Z : ℝ, 2 ≤ Z →
      ∃ (m C : ℝ) (cS : Fin n → Fin J → ℝ → P → ℂ) (c₂ : Fin n → Fin J → Fin n → Fin J → P → ℂ),
        (∀ k ∈ K₀, ∀ i j i' j', ‖c₂ i j i' j' k‖ ≤ C) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ i j, ‖cS i j z k‖ ≤ C * z ^ (-m)) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
          ‖W y z k - ∑ i : Fin n, ∑ j : Fin J,
              cS i j z k * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * z ^ (-m) * y ^ (ρ + δ)) ∧
        (∀ k ∈ K₀, ∀ i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1,
          ‖cS i j z k - ∑ i' : Fin n, ∑ j' : Fin J,
              c₂ i j i' j' k * ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * z ^ (ρ + δ)))
    (K : Set P) (hK : IsCompact K) (b : ℝ) (hb : 1 ≤ b) :
    ∃ C B : ℝ, ∀ g ∈ K, ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∃ v : Fin n → Fin J → ℂ, (∀ i j, ‖v i j‖ ≤ B) ∧
      ∀ y₁ ∈ Set.Ioc (0 : ℝ) 1,
        ‖W y₁ y₂ g - ∑ i : Fin n, ∑ j : Fin J, v i j * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
          C * y₁ ^ (ρ + δ) := by
  classical
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb
  obtain ⟨lam₀, nB, Ω, K₀, hlam₀, hlam₀1, hnB, hΩ, hK₀, hK₀S, hT⟩ := htrans K hK
  set Z : ℝ := max 2 (lam₀⁻¹ * b) with hZ
  obtain ⟨m, C, cS, c₂, -, hcSb, hexp1, -⟩ := hslice K₀ hK₀ hK₀S Z (le_max_left _ _)
  set Cp : ℝ := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hCCp : C ≤ Cp := le_max_left _ _
  set zlo : ℝ := lam₀ * b⁻¹ with hzlo
  set zhi : ℝ := lam₀⁻¹ * b with hzhi
  have hzlo0 : 0 < zlo := by positivity
  set zmB : ℝ := max (zlo ^ (-m)) (zhi ^ (-m)) with hzmB
  have hzmB0 : 0 ≤ zmB := le_max_of_le_left (Real.rpow_nonneg hzlo0.le _)
  obtain ⟨W₀, hW₀0, hW₀⟩ := exists_bound_W W hWc lam₀ lam₀⁻¹ zlo zhi hlam₀ hzlo0 K₀ hK₀
  set aB : ℝ := 2 * Real.pi * nB / lam₀ with haB
  have haB0 : 0 ≤ aB := by positivity
  obtain ⟨Kd, hKd1, hKd2⟩ := exists_depth e ρ δ aB
  set Bc' : ℝ := Cp * zmB with hBc'
  have hBc'0 : 0 ≤ Bc' := mul_nonneg hCp0 hzmB0

  refine ⟨max (Ω * (Real.exp aB * Bc' +
        (aB ^ Kd / (Kd.factorial : ℝ) * 2 * Bc') * ∑ _i : Fin n, ∑ j : Fin J, ((j : ℝ) + 1) ^ (j : ℕ) +
        (Bc' * Real.exp aB) * ∑ _i : Fin n, ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ)) *
        max (lam₀ ^ (ρ + δ)) (lam₀ ^ (-(ρ + δ))))
      ((Ω * W₀ + Ω * ((n : ℝ) * Bc' * Real.exp aB *
          (∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re))) *
          ((J : ℝ) * (1 + |Real.log lam₀|) ^ J * 2 ^ J)) *
        ∑ i₁ : Fin n, ∑ j : Fin J, max (lam₀ ^ (e i₁).re) 1 * |Real.log lam₀| ^ (j : ℕ)) /
        min (lam₀ ^ (ρ + δ)) 1),
    Ω * ((n : ℝ) * Bc' * Real.exp aB *
      (∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re))) *
      ((J : ℝ) * (1 + |Real.log lam₀|) ^ J * 2 ^ J)), fun g hg y₂ hy₂l hy₂u => ?_⟩
  obtain ⟨lam, τ, n₁, n₂, κ₁, k', hk', hl1, hl2, ht1, ht2, hn1, hn2, hκ, hid⟩ := hT g hg
  have hy₂pos : 0 < y₂ := (inv_pos.2 hb0).trans_le hy₂l
  have hlam_pos : 0 < lam := hlam₀.trans_le hl1
  have hτ_pos : 0 < τ := hlam₀.trans_le ht1

  set z : ℝ := τ * y₂ with hz
  have hzI : z ∈ Set.Icc zlo zhi := by
    constructor
    · calc zlo = lam₀ * b⁻¹ := rfl
        _ ≤ τ * y₂ := mul_le_mul ht1 hy₂l (inv_pos.2 hb0).le hτ_pos.le
    · calc τ * y₂ ≤ lam₀⁻¹ * b := mul_le_mul ht2 hy₂u hy₂pos.le (inv_pos.2 hlam₀).le
        _ = zhi := rfl
  have hzZ : z ∈ Set.Ioc (0 : ℝ) Z := ⟨mul_pos hτ_pos hy₂pos, hzI.2.trans (le_max_right _ _)⟩
  have hzm : z ^ (-m) ≤ zmB := rpow_le_max_of_mem_Icc (-m) zlo zhi z hzlo0 hzI
  have hCzm : C * z ^ (-m) ≤ Bc' := by
    calc C * z ^ (-m) ≤ Cp * z ^ (-m) := mul_le_mul_of_nonneg_right hCCp (Real.rpow_nonneg hzZ.1.le _)
      _ ≤ Cp * zmB := mul_le_mul_of_nonneg_left hzm hCp0

  obtain ⟨ha', ha're⟩ := norm_twoPiI_mul_div_le n₁ nB lam lam₀ hn1 hnB hlam₀ hl1
  set a' : ℂ := (2 * Real.pi * Complex.I * (n₁ : ℂ)) / ((lam : ℝ) : ℂ) with ha'def
  set κ₀ : ℂ := κ₁ * Complex.exp (2 * Real.pi * Complex.I * ((y₂ * n₂ : ℝ) : ℂ)) with hκ₀
  have hκ₀norm : ‖κ₀‖ ≤ Ω := by
    rw [hκ₀, norm_mul]
    have h2 : ‖Complex.exp (2 * Real.pi * Complex.I * ((y₂ * n₂ : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [h2, mul_one]
    exact hκ
  obtain ⟨L, -, hT1⟩ := RegularSingular.exists_transferMatrix_expLogExpansion_rescale_expTwist e he ρ δ hδ hre
    hcl hgap lam₀ hlam₀ hlam₀1 aB Kd hKd1 hKd2 Ω hΩ κ₀ a' hκ₀norm ha' ha're lam hlam_pos hl1 hl2
  obtain ⟨hvB, hv⟩ := hT1 Bc' Bc' W₀ hBc'0 hBc'0 hW₀0 (fun s => W s z k') (fun y₁ => W y₁ y₂ g)
    (fun i j => cS i j z k')
    (fun i j => (hcSb k' hk' z hzZ i j).trans hCzm)
    (fun y hy => (hexp1 k' hk' z hzZ y hy).trans
      (mul_le_mul_of_nonneg_right hCzm (Real.rpow_nonneg hy.1.le _)))
    (fun s hs1 hs2 => hW₀ s ⟨hs1, hs2⟩ z hzI k' hk')
    (by
      intro y₁ hy₁
      show W y₁ y₂ g = κ₀ * (Complex.exp (a' * ((lam * y₁ : ℝ) : ℂ)) * W (lam * y₁) z k')
      rw [hid y₁ y₂ hy₁ hy₂pos]
      have hexp : Complex.exp (2 * Real.pi * Complex.I * ((y₁ * n₁ + y₂ * n₂ : ℝ) : ℂ)) =
          Complex.exp (2 * Real.pi * Complex.I * ((y₂ * n₂ : ℝ) : ℂ)) *
            Complex.exp (a' * ((lam * y₁ : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        rw [ha'def]
        push_cast
        field_simp [hlam_pos.ne']
        ring
      rw [hexp, hz]
      ring)
  exact ⟨_, hvB, hv⟩

private theorem level2_passage
    {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    (S : Set P) (W : ℝ → ℝ → P → ℂ)
    (hWc : ContinuousOn (fun w : ℝ × ℝ × P => W w.1 w.2.1 w.2.2) (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ))
    (htrans : ∀ K : Set P, IsCompact K → ∃ (lam₀ nB Ω : ℝ) (K₀ : Set P), 0 < lam₀ ∧ lam₀ ≤ 1 ∧ 0 ≤ nB ∧
      0 ≤ Ω ∧ IsCompact K₀ ∧ K₀ ⊆ S ∧ ∀ g ∈ K, ∃ (lam τ n₁ n₂ : ℝ) (κ₁ : ℂ) (k' : P), k' ∈ K₀ ∧
        lam₀ ≤ lam ∧ lam ≤ lam₀⁻¹ ∧ lam₀ ≤ τ ∧ τ ≤ lam₀⁻¹ ∧ |n₁| ≤ nB ∧ |n₂| ≤ nB ∧ ‖κ₁‖ ≤ Ω ∧
        ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
          W y₁ y₂ g = κ₁ * Complex.exp (2 * Real.pi * Complex.I * ((y₁ * n₁ + y₂ * n₂ : ℝ) : ℂ)) *
            W (lam * y₁) (τ * y₂) k')
    (hslice : ∀ K₀ : Set P, IsCompact K₀ → K₀ ⊆ S → ∀ Z : ℝ, 2 ≤ Z →
      ∃ (m C : ℝ) (cS : Fin n → Fin J → ℝ → P → ℂ) (c₂ : Fin n → Fin J → Fin n → Fin J → P → ℂ),
        (∀ k ∈ K₀, ∀ i j i' j', ‖c₂ i j i' j' k‖ ≤ C) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ i j, ‖cS i j z k‖ ≤ C * z ^ (-m)) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
          ‖W y z k - ∑ i : Fin n, ∑ j : Fin J,
              cS i j z k * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * z ^ (-m) * y ^ (ρ + δ)) ∧
        (∀ k ∈ K₀, ∀ i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1,
          ‖cS i j z k - ∑ i' : Fin n, ∑ j' : Fin J,
              c₂ i j i' j' k * ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * z ^ (ρ + δ)))
    (c : Fin n → Fin J → ℝ → P → ℂ)
    (hcexp : ∀ y₂ : ℝ, 0 < y₂ → ∀ g : P, ∃ C' : ℝ, ∀ y₁ ∈ Set.Ioc (0 : ℝ) 1,
      ‖W y₁ y₂ g - ∑ i : Fin n, ∑ j : Fin J,
          c i j y₂ g * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C' * y₁ ^ (ρ + δ))
    (K : Set P) (hK : IsCompact K) :
    ∃ C B : ℝ, ∀ g ∈ K, ∀ (i : Fin n) (j : Fin J), ∃ v : Fin n → Fin J → ℂ, (∀ i' j', ‖v i' j'‖ ≤ B) ∧
      ∀ y₂ ∈ Set.Ioc (0 : ℝ) 1,
        ‖c i j y₂ g - ∑ i' : Fin n, ∑ j' : Fin J,
            v i' j' * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * y₂ ^ (ρ + δ) := by
  classical
  obtain ⟨lam₀, nB, Ω, K₀, hlam₀, hlam₀1, hnB, hΩ, hK₀, hK₀S, hT⟩ := htrans K hK
  set Z : ℝ := max 2 (lam₀⁻¹ * lam₀⁻¹) with hZ
  obtain ⟨m, C, cS, c₂, hc₂b, hcSb, hexp1, hexp2⟩ := hslice K₀ hK₀ hK₀S Z (le_max_left _ _)
  set Cp : ℝ := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hCCp : C ≤ Cp := le_max_left _ _
  have hlam₀inv1 : 1 ≤ lam₀⁻¹ := one_le_inv₀ hlam₀ |>.2 hlam₀1

  set wlo : ℝ := lam₀ * lam₀ with hwlo
  set whi : ℝ := lam₀⁻¹ * lam₀⁻¹ with hwhi
  have hwlo0 : 0 < wlo := by positivity
  set zW : ℝ := max (wlo ^ (-m)) (whi ^ (-m)) with hzW
  have hzW0 : 0 ≤ zW := le_max_of_le_left (Real.rpow_nonneg hwlo0.le _)
  have hprodI : ∀ t s : ℝ, lam₀ ≤ t → t ≤ lam₀⁻¹ → lam₀ ≤ s → s ≤ lam₀⁻¹ → t * s ∈ Set.Icc wlo whi := by
    intro t s ht1 ht2 hs1 hs2
    exact ⟨mul_le_mul ht1 hs1 hlam₀.le (hlam₀.le.trans ht1),
      mul_le_mul ht2 hs2 (hlam₀.le.trans hs1) (inv_pos.2 hlam₀).le⟩
  have hbandI : ∀ t : ℝ, lam₀ ≤ t → t ≤ lam₀⁻¹ → t ∈ Set.Icc wlo whi := by
    intro t ht1 ht2
    have h := hprodI t 1 ht1 ht2 hlam₀1 hlam₀inv1
    rwa [mul_one] at h
  have hwZ : ∀ z ∈ Set.Icc wlo whi, z ∈ Set.Ioc (0 : ℝ) Z := fun z hz =>
    ⟨hwlo0.trans_le hz.1, hz.2.trans (le_max_right _ _)⟩
  have hcSW : ∀ k' ∈ K₀, ∀ z ∈ Set.Icc wlo whi, ∀ i j, ‖cS i j z k'‖ ≤ Cp * zW := by
    intro k' hk' z hz i j
    refine (hcSb k' hk' z (hwZ z hz) i j).trans ?_
    exact mul_le_mul hCCp (rpow_le_max_of_mem_Icc (-m) wlo whi z hwlo0 hz) (Real.rpow_nonneg (hwZ z hz).1.le _)
      hCp0

  set aB : ℝ := 2 * Real.pi * nB / lam₀ with haB
  have haB0 : 0 ≤ aB := by positivity
  obtain ⟨Kd, hKd1, hKd2⟩ := exists_depth e ρ δ aB

  set LAM : ℝ := ∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re)) with hLAM
  set JBn : ℝ := (1 + |Real.log lam₀|) ^ J * 2 ^ J with hJBn
  set Lb : ℝ := Ω * (Real.exp aB * LAM * JBn) with hLb
  set B₂ : ℝ := 1 * ((n : ℝ) * Cp * Real.exp aB * LAM * ((J : ℝ) * (1 + |Real.log lam₀|) ^ J * 2 ^ J)) with hB₂
  set C₂ : ℝ := max (1 * (Real.exp aB * Cp +
        (aB ^ Kd / (Kd.factorial : ℝ) * 2 * Cp) * ∑ _i : Fin n, ∑ j : Fin J, ((j : ℝ) + 1) ^ (j : ℕ) +
        (Cp * Real.exp aB) * ∑ _i : Fin n, ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ)) *
        max (lam₀ ^ (ρ + δ)) (lam₀ ^ (-(ρ + δ))))
      ((1 * (Cp * zW) + 1 * ((n : ℝ) * Cp * Real.exp aB * LAM * ((J : ℝ) * (1 + |Real.log lam₀|) ^ J * 2 ^ J)) *
        ∑ i₁ : Fin n, ∑ j : Fin J, max (lam₀ ^ (e i₁).re) 1 * |Real.log lam₀| ^ (j : ℕ)) /
        min (lam₀ ^ (ρ + δ)) 1) with hC₂
  set NJ : ℝ := (Fintype.card (Fin n × Fin J) : ℝ) with hNJ
  set B₃ : ℝ := NJ * Lb * B₂ with hB₃
  set C₃ : ℝ := NJ * Lb * C₂ with hC₃
  set W₃ : ℝ := NJ * Lb * (Cp * zW) with hW₃
  have hLAM0 : 0 ≤ LAM := Finset.sum_nonneg fun _ _ =>
    add_nonneg (Real.rpow_nonneg hlam₀.le _) (Real.rpow_nonneg hlam₀.le _)
  have hLb0 : 0 ≤ Lb := by positivity
  have hB₂0 : 0 ≤ B₂ := by positivity
  have hC₂0 : 0 ≤ C₂ := by
    rw [hC₂]
    refine le_max_of_le_right (div_nonneg ?_ (lt_min (Real.rpow_pos_of_pos hlam₀ _) one_pos).le)
    refine add_nonneg (by positivity) (mul_nonneg (by positivity) ?_)
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (le_max_of_le_right zero_le_one) (pow_nonneg (abs_nonneg _) _)
  have hB₃0 : 0 ≤ B₃ := by positivity
  have hC₃0 : 0 ≤ C₃ := by positivity
  have hW₃0 : 0 ≤ W₃ := by positivity
  refine ⟨max ((1 : ℝ) * (Real.exp aB * C₃ +
        (aB ^ Kd / (Kd.factorial : ℝ) * 2 * B₃) * ∑ _i : Fin n, ∑ j : Fin J, ((j : ℝ) + 1) ^ (j : ℕ) +
        (B₃ * Real.exp aB) * ∑ _i : Fin n, ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ)) *
        max ((1 : ℝ) ^ (ρ + δ)) ((1 : ℝ) ^ (-(ρ + δ))))
      (((1 : ℝ) * W₃ + (1 : ℝ) * ((n : ℝ) * B₃ * Real.exp aB *
          (∑ i₁ : Fin n, ((1 : ℝ) ^ (e i₁).re + (1 : ℝ) ^ (-(e i₁).re))) *
          ((J : ℝ) * (1 + |Real.log 1|) ^ J * 2 ^ J)) *
        ∑ i₁ : Fin n, ∑ j : Fin J, max ((1 : ℝ) ^ (e i₁).re) 1 * |Real.log 1| ^ (j : ℕ)) /
        min ((1 : ℝ) ^ (ρ + δ)) 1),
    (1 : ℝ) * ((n : ℝ) * B₃ * Real.exp aB *
      (∑ i₁ : Fin n, ((1 : ℝ) ^ (e i₁).re + (1 : ℝ) ^ (-(e i₁).re))) *
      ((J : ℝ) * (1 + |Real.log 1|) ^ J * 2 ^ J)), fun g hg i j => ?_⟩
  obtain ⟨lam, τ, n₁, n₂, κ₁, k', hk', hl1, hl2, ht1, ht2, hn1, hn2, hκ, hid⟩ := hT g hg
  have hlam_pos : 0 < lam := hlam₀.trans_le hl1
  have hτ_pos : 0 < τ := hlam₀.trans_le ht1

  obtain ⟨ha', ha're⟩ := norm_twoPiI_mul_div_le n₁ nB lam lam₀ hn1 hnB hlam₀ hl1
  set a' : ℂ := (2 * Real.pi * Complex.I * (n₁ : ℂ)) / ((lam : ℝ) : ℂ) with ha'def
  obtain ⟨L, hLbd, hT1⟩ := RegularSingular.exists_transferMatrix_expLogExpansion_rescale_expTwist e he ρ δ hδ hre
    hcl hgap lam₀ hlam₀ hlam₀1 aB Kd hKd1 hKd2 Ω hΩ κ₁ a' hκ ha' ha're lam hlam_pos hl1 hl2
  have hLb' : ∀ i k i₀ m', ‖L i k i₀ m'‖ ≤ Lb := fun i k i₀ m' => (hLbd i k i₀ m').trans (by rw [hLb])

  have hident : ∀ y₂ ∈ Set.Ioc (0 : ℝ) 1, ∀ i k,
      c i k y₂ g = Complex.exp (2 * Real.pi * Complex.I * ((y₂ * n₂ : ℝ) : ℂ)) *
        ∑ i₀ : Fin n, ∑ m' : Fin J, L i k i₀ m' * cS i₀ m' (τ * y₂) k' := by
    intro y₂ hy₂ i k
    have hy₂pos : 0 < y₂ := hy₂.1
    set z : ℝ := τ * y₂ with hz
    have hz0 : 0 < z := mul_pos hτ_pos hy₂pos
    have hzZ : z ∈ Set.Ioc (0 : ℝ) Z := by
      refine ⟨hz0, le_trans ?_ (le_max_right _ _)⟩
      calc τ * y₂ ≤ lam₀⁻¹ * 1 := mul_le_mul ht2 hy₂.2 hy₂pos.le (inv_pos.2 hlam₀).le
        _ ≤ lam₀⁻¹ * lam₀⁻¹ := mul_le_mul_of_nonneg_left hlam₀inv1 (inv_pos.2 hlam₀).le
    have hzm : 0 ≤ z ^ (-m) := Real.rpow_nonneg hz0.le _
    obtain ⟨W₀, hW₀0, hW₀⟩ := exists_bound_W W hWc lam₀ lam₀⁻¹ z z hlam₀ hz0 K₀ hK₀
    obtain ⟨-, hv⟩ := hT1 (Cp * z ^ (-m)) (Cp * z ^ (-m)) W₀ (mul_nonneg hCp0 hzm) (mul_nonneg hCp0 hzm) hW₀0
      (fun s => W s z k') (fun y₁ => κ₁ * (Complex.exp (a' * ((lam * y₁ : ℝ) : ℂ)) * W (lam * y₁) z k'))
      (fun i' j' => cS i' j' z k')
      (fun i' j' => (hcSb k' hk' z hzZ i' j').trans (mul_le_mul_of_nonneg_right hCCp hzm))
      (fun y hy => (hexp1 k' hk' z hzZ y hy).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCCp hzm) (Real.rpow_nonneg hy.1.le _)))
      (fun s hs1 hs2 => hW₀ s ⟨hs1, hs2⟩ z ⟨le_rfl, le_rfl⟩ k' hk')
      (fun y₁ _ => rfl)

    set ph : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((y₂ * n₂ : ℝ) : ℂ)) with hph
    have hph1 : ‖ph‖ = 1 := by rw [hph, Complex.norm_exp]; simp
    have hWph : ∀ y₁ : ℝ, 0 < y₁ →
        W y₁ y₂ g = ph * (κ₁ * (Complex.exp (a' * ((lam * y₁ : ℝ) : ℂ)) * W (lam * y₁) z k')) := by
      intro y₁ hy₁
      rw [hid y₁ y₂ hy₁ hy₂pos]
      have hexp : Complex.exp (2 * Real.pi * Complex.I * ((y₁ * n₁ + y₂ * n₂ : ℝ) : ℂ)) =
          ph * Complex.exp (a' * ((lam * y₁ : ℝ) : ℂ)) := by
        rw [hph, ← Complex.exp_add]
        congr 1
        rw [ha'def]
        push_cast
        field_simp [hlam_pos.ne']
        ring
      rw [hexp, hz]
      ring
    have hfac : ∀ y₁ : ℝ, ∑ i' : Fin n, ∑ j' : Fin J,
        (ph * ∑ i₀ : Fin n, ∑ m' : Fin J, L i' j' i₀ m' * cS i₀ m' z k') *
          ((y₁ : ℂ) ^ e i' * ((Real.log y₁ : ℝ) : ℂ) ^ (j' : ℕ)) =
        ph * ∑ i' : Fin n, ∑ j' : Fin J, (∑ i₀ : Fin n, ∑ m' : Fin J, L i' j' i₀ m' * cS i₀ m' z k') *
          ((y₁ : ℂ) ^ e i' * ((Real.log y₁ : ℝ) : ℂ) ^ (j' : ℕ)) := by
      intro y₁
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      ring
    have heq := coeff_eq_of_two_expansions e he ρ δ hre hδ (fun y₁ => W y₁ y₂ g) (fun i' j' => c i' j' y₂ g)
      (fun i' j' => ph * ∑ i₀ : Fin n, ∑ m' : Fin J, L i' j' i₀ m' * cS i₀ m' z k') (hcexp y₂ hy₂pos g)
      ⟨_, fun y₁ hy₁ => by
        show ‖W y₁ y₂ g - ∑ i' : Fin n, ∑ j' : Fin J,
          (ph * ∑ i₀ : Fin n, ∑ m' : Fin J, L i' j' i₀ m' * cS i₀ m' z k') *
            ((y₁ : ℂ) ^ e i' * ((Real.log y₁ : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ _
        rw [hWph y₁ hy₁.1, hfac, ← mul_sub, norm_mul, hph1, one_mul]
        exact hv y₁ hy₁⟩
    exact congrFun (congrFun heq i) k

  obtain ⟨L₂, -, hT2⟩ := RegularSingular.exists_transferMatrix_expLogExpansion_rescale_expTwist e he ρ δ hδ hre
    hcl hgap lam₀ hlam₀ hlam₀1 aB Kd hKd1 hKd2 1 zero_le_one 1 0 (by simp) (by simpa using haB0)
    (Complex.zero_re) τ hτ_pos ht1 ht2
  have hres : ∀ s : Fin n × Fin J,
      (∀ i' j', ‖∑ i₀ : Fin n, ∑ m' : Fin J, L₂ i' j' i₀ m' * c₂ s.1 s.2 i₀ m' k'‖ ≤ B₂) ∧
      ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖cS s.1 s.2 (τ * y) k' - ∑ i' : Fin n, ∑ j' : Fin J,
          (∑ i₀ : Fin n, ∑ m' : Fin J, L₂ i' j' i₀ m' * c₂ s.1 s.2 i₀ m' k') *
            ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C₂ * y ^ (ρ + δ) := by
    intro s
    exact hT2 Cp Cp (Cp * zW) hCp0 hCp0 (mul_nonneg hCp0 hzW0) (fun z => cS s.1 s.2 z k')
      (fun y => cS s.1 s.2 (τ * y) k') (fun i₀ m' => c₂ s.1 s.2 i₀ m' k')
      (fun i₀ m' => (hc₂b k' hk' s.1 s.2 i₀ m').trans hCCp)
      (fun z hz => (hexp2 k' hk' s.1 s.2 z hz).trans
        (mul_le_mul_of_nonneg_right hCCp (Real.rpow_nonneg hz.1.le _)))
      (fun z hz1 hz2 => hcSW k' hk' z (hbandI z hz1 hz2) s.1 s.2)
      (fun y hy => by simp)

  set v₂ : Fin n × Fin J → Fin n → Fin J → ℂ := fun s i' j' =>
    ∑ i₀ : Fin n, ∑ m' : Fin J, L₂ i' j' i₀ m' * c₂ s.1 s.2 i₀ m' k' with hv₂
  set G : ℝ → ℂ := fun y => ∑ s : Fin n × Fin J, L i j s.1 s.2 * cS s.1 s.2 (τ * y) k' with hG
  set v₃ : Fin n → Fin J → ℂ := fun i' j' => ∑ s : Fin n × Fin J, L i j s.1 s.2 * v₂ s i' j' with hv₃
  have hv₃B : ∀ i' j', ‖v₃ i' j'‖ ≤ B₃ := by
    intro i' j'
    rw [hv₃]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ s : Fin n × Fin J, ‖L i j s.1 s.2 * v₂ s i' j'‖ ≤ ∑ _s : Fin n × Fin J, Lb * B₂ :=
          Finset.sum_le_sum fun s _ => by
            rw [norm_mul]
            exact mul_le_mul (hLb' i j s.1 s.2) ((hres s).1 i' j') (norm_nonneg _) hLb0
      _ = B₃ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hB₃, hNJ]; ring
  have hG₃ : ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖G y - ∑ i' : Fin n, ∑ j' : Fin J, v₃ i' j' * ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤
        C₃ * y ^ (ρ + δ) := by
    intro y hy
    have hsum : ∑ i' : Fin n, ∑ j' : Fin J, v₃ i' j' * ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j' : ℕ)) =
        ∑ s : Fin n × Fin J, L i j s.1 s.2 * ∑ i' : Fin n, ∑ j' : Fin J,
          v₂ s i' j' * ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j' : ℕ)) := by
      calc ∑ i' : Fin n, ∑ j' : Fin J, v₃ i' j' * ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j' : ℕ))
          = ∑ i' : Fin n, ∑ j' : Fin J, ∑ s : Fin n × Fin J,
              L i j s.1 s.2 * v₂ s i' j' * ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j' : ℕ)) := by
            simp only [hv₃, Finset.sum_mul]
        _ = ∑ i' : Fin n, ∑ s : Fin n × Fin J, ∑ j' : Fin J,
              L i j s.1 s.2 * v₂ s i' j' * ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j' : ℕ)) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ s : Fin n × Fin J, ∑ i' : Fin n, ∑ j' : Fin J,
              L i j s.1 s.2 * v₂ s i' j' * ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j' : ℕ)) :=
            Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j' _ => ?_
            ring
    rw [hsum, hG]
    have h := norm_sum_mul_sub_le (fun s : Fin n × Fin J => L i j s.1 s.2) Lb (fun s => hLb' i j s.1 s.2)
      (fun s => cS s.1 s.2 (τ * y) k')
      (fun s => ∑ i' : Fin n, ∑ j' : Fin J, v₂ s i' j' * ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j' : ℕ)))
      (C₂ * y ^ (ρ + δ)) (fun s => (hres s).2 y hy)
    refine h.trans (le_of_eq ?_)
    rw [hC₃, hNJ]; ring
  have hGW₃ : ∀ s : ℝ, 1 ≤ s → s ≤ 1⁻¹ → ‖G s‖ ≤ W₃ := by
    intro s hs1 hs2
    have hs : s = 1 := le_antisymm (by simpa using hs2) hs1
    rw [hs, hG]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ s : Fin n × Fin J, ‖L i j s.1 s.2 * cS s.1 s.2 (τ * 1) k'‖ ≤ ∑ _s : Fin n × Fin J, Lb * (Cp * zW) :=
          Finset.sum_le_sum fun s _ => by
            rw [norm_mul, mul_one]
            exact mul_le_mul (hLb' i j s.1 s.2) (hcSW k' hk' τ (hbandI τ ht1 ht2) s.1 s.2) (norm_nonneg _) hLb0
      _ = W₃ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hW₃, hNJ]; ring

  obtain ⟨ha₂, ha₂re⟩ := norm_twoPiI_mul_div_le n₂ nB 1 lam₀ hn2 hnB hlam₀ hlam₀1
  set a₂ : ℂ := (2 * Real.pi * Complex.I * (n₂ : ℂ)) / (((1 : ℝ) : ℝ) : ℂ) with ha₂def
  obtain ⟨L₄, -, hT4⟩ := RegularSingular.exists_transferMatrix_expLogExpansion_rescale_expTwist e he ρ δ hδ hre
    hcl hgap 1 one_pos le_rfl aB Kd hKd1 hKd2 1 zero_le_one 1 a₂ (by simp) ha₂ ha₂re 1 one_pos le_rfl
    (by simp)
  obtain ⟨hv₄B, hv₄⟩ := hT4 B₃ C₃ W₃ hB₃0 hC₃0 hW₃0 G
    (fun y => 1 * (Complex.exp (a₂ * ((1 * y : ℝ) : ℂ)) * G (1 * y))) v₃ hv₃B hG₃ hGW₃ (fun y _ => rfl)
  refine ⟨fun i' j' => ∑ i₀ : Fin n, ∑ m' : Fin J, L₄ i' j' i₀ m' * v₃ i₀ m', hv₄B, fun y₂ hy₂ => ?_⟩
  have hcF : c i j y₂ g = 1 * (Complex.exp (a₂ * ((1 * y₂ : ℝ) : ℂ)) * G (1 * y₂)) := by
    rw [hident y₂ hy₂ i j, hG]
    simp only [one_mul, Fintype.sum_prod_type]
    congr 1
    rw [ha₂def]
    congr 1
    push_cast
    ring
  rw [hcF]
  exact hv₄ y₂ hy₂

end Passages

theorem solution
    {P : Type*} [TopologicalSpace P] [LocallyCompactSpace P] [FirstCountableTopology P]
    {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    (S : Set P) (W : ℝ → ℝ → P → ℂ)
    (hWc : ContinuousOn (fun w : ℝ × ℝ × P => W w.1 w.2.1 w.2.2) (Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.univ))
    (htrans : ∀ K : Set P, IsCompact K → ∃ (lam₀ nB Ω : ℝ) (K₀ : Set P), 0 < lam₀ ∧ lam₀ ≤ 1 ∧ 0 ≤ nB ∧
      0 ≤ Ω ∧ IsCompact K₀ ∧ K₀ ⊆ S ∧ ∀ g ∈ K, ∃ (lam τ n₁ n₂ : ℝ) (κ₁ : ℂ) (k' : P), k' ∈ K₀ ∧
        lam₀ ≤ lam ∧ lam ≤ lam₀⁻¹ ∧ lam₀ ≤ τ ∧ τ ≤ lam₀⁻¹ ∧ |n₁| ≤ nB ∧ |n₂| ≤ nB ∧ ‖κ₁‖ ≤ Ω ∧
        ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
          W y₁ y₂ g = κ₁ * Complex.exp (2 * Real.pi * Complex.I * ((y₁ * n₁ + y₂ * n₂ : ℝ) : ℂ)) *
            W (lam * y₁) (τ * y₂) k')
    (hslice : ∀ K₀ : Set P, IsCompact K₀ → K₀ ⊆ S → ∀ Z : ℝ, 2 ≤ Z →
      ∃ (m C : ℝ) (cS : Fin n → Fin J → ℝ → P → ℂ) (c₂ : Fin n → Fin J → Fin n → Fin J → P → ℂ),
        (∀ k ∈ K₀, ∀ i j i' j', ‖c₂ i j i' j' k‖ ≤ C) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ i j, ‖cS i j z k‖ ≤ C * z ^ (-m)) ∧
        (∀ k ∈ K₀, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
          ‖W y z k - ∑ i : Fin n, ∑ j : Fin J,
              cS i j z k * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * z ^ (-m) * y ^ (ρ + δ)) ∧
        (∀ k ∈ K₀, ∀ i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1,
          ‖cS i j z k - ∑ i' : Fin n, ∑ j' : Fin J,
              c₂ i j i' j' k * ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * z ^ (ρ + δ))) :
    ∃ c : Fin n → Fin J → ℝ → P → ℂ,
      (∀ i j, ContinuousOn (fun p : ℝ × P => c i j p.1 p.2) {p | 0 < p.1}) ∧
      (∀ K : Set P, IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K, ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b →
        ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖W y₁ y₂ k - ∑ i : Fin n, ∑ j : Fin J,
            c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * y₁ ^ (ρ + δ)) ∧
      ∃ c' : Fin n → Fin J → Fin n → Fin J → P → ℂ,
        (∀ i j i' j', Continuous (c' i j i' j')) ∧
        ∀ K : Set P, IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J), ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖c i j y₂ k - ∑ i' : Fin n, ∑ j' : Fin J,
              c' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * y₂ ^ (ρ + δ) := by
  classical

  set Pset : Set (ℝ × P) := {p : ℝ × P | 0 < p.1} with hPset
  haveI : FirstCountableTopology Pset := inferInstanceAs (FirstCountableTopology ↥{p : ℝ × P | 0 < p.1})
  set F : Pset → ℝ → ℂ := fun p y₁ => W y₁ p.1.1 p.1.2 with hF
  have hFc : ∀ y₁ ∈ Set.Ioc (0 : ℝ) 1, Continuous fun p : Pset => F p y₁ := by
    intro y₁ hy₁
    have hmap : Continuous fun p : Pset => ((y₁, p.1.1, p.1.2) : ℝ × ℝ × P) :=
      continuous_const.prodMk (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd)
    exact hWc.comp_continuous hmap (fun p => ⟨hy₁.1, p.2, Set.mem_univ _⟩)

  have hloc : ∀ p₀ : Pset, ∃ C B : ℝ, ∀ᶠ p in nhds p₀, ∃ v : Fin n → Fin J → ℂ, (∀ i j, ‖v i j‖ ≤ B) ∧
      ∀ y₁ ∈ Set.Ioc (0 : ℝ) 1,
        ‖F p y₁ - ∑ i : Fin n, ∑ j : Fin J, v i j * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
          C * y₁ ^ (ρ + δ) := by
    intro p₀
    obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds p₀.1.2
    have hy₀ : 0 < p₀.1.1 := p₀.2
    set b : ℝ := max (2 * p₀.1.1) (2 / p₀.1.1) + 1 with hb
    have hb1 : 1 ≤ b := by
      have : 0 ≤ max (2 * p₀.1.1) (2 / p₀.1.1) := le_max_of_le_left (by positivity)
      linarith
    obtain ⟨C, B, hCB⟩ := level1_passage e he ρ δ hδ hre hcl hgap S W hWc htrans hslice K hKc b hb1
    refine ⟨C, B, ?_⟩
    have hnhds : ∀ᶠ p : Pset in nhds p₀, p.1.1 ∈ Set.Ioo (p₀.1.1 / 2) (2 * p₀.1.1) ∧ p.1.2 ∈ K := by
      have h1' : ∀ᶠ q : ℝ × P in nhds p₀.1, q.1 ∈ Set.Ioo (p₀.1.1 / 2) (2 * p₀.1.1) ∧ q.2 ∈ K := by
        refine Filter.Eventually.and ?_ ?_
        · exact (continuous_fst.tendsto p₀.1).eventually (Ioo_mem_nhds (by linarith) (by linarith))
        · exact (continuous_snd.tendsto p₀.1).eventually hKn
      exact (continuous_subtype_val.tendsto p₀).eventually h1'
    filter_upwards [hnhds] with p hp
    obtain ⟨hpy, hpK⟩ := hp
    have hl : b⁻¹ ≤ p.1.1 := by
      have h2 : 2 / p₀.1.1 ≤ b := by
        have := le_max_right (2 * p₀.1.1) (2 / p₀.1.1)
        linarith
      have h3 : b⁻¹ ≤ (2 / p₀.1.1)⁻¹ := (inv_le_inv₀ (by linarith) (by positivity)).2 h2
      rw [inv_div] at h3
      linarith [hpy.1]
    have hu' : p.1.1 ≤ b := by
      have := le_max_left (2 * p₀.1.1) (2 / p₀.1.1)
      linarith [hpy.2]
    obtain ⟨v, hvB, hv⟩ := hCB p.1.2 hpK p.1.1 hl hu'
    exact ⟨v, hvB, fun y₁ hy₁ => hv y₁ hy₁⟩
  have huniq : ∀ (dd : Fin n → Fin J → ℂ) (C' : ℝ),
      (∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖∑ i : Fin n, ∑ j : Fin J, dd i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C' * y ^ (ρ + δ)) →
      dd = 0 := fun dd C' hdd => huniq_family e he ρ δ hre hδ dd C' hdd
  obtain ⟨cP, hcP_cont, hcP_loc, hcP_cpt⟩ := exists_canonical_coeff (P := Pset) e (ρ + δ) F hFc hloc huniq

  set c : Fin n → Fin J → ℝ → P → ℂ := fun i j y₂ g => if h : 0 < y₂ then cP ⟨(y₂, g), h⟩ i j else 0 with hc
  have hc_pos : ∀ i j (y₂ : ℝ) (g : P) (h : 0 < y₂), c i j y₂ g = cP ⟨(y₂, g), h⟩ i j := by
    intro i j y₂ g h
    simp only [hc, dif_pos h]
  have hccont : ∀ i j, ContinuousOn (fun p : ℝ × P => c i j p.1 p.2) {p | 0 < p.1} := by
    intro i j
    rw [continuousOn_iff_continuous_restrict]
    have hres : Set.domRestrict {p : ℝ × P | 0 < p.1} (fun p : ℝ × P => c i j p.1 p.2) =
        fun p => cP ⟨p.1, p.2⟩ i j := by
      funext p
      rw [Set.domRestrict_apply, hc_pos i j _ _ (show (0 : ℝ) < (p : ℝ × P).1 from p.2)]
    rw [hres]
    exact (continuous_apply j).comp ((continuous_apply i).comp (hcP_cont.comp (continuous_subtype_val.subtype_mk _)))
  have hcexp : ∀ y₂ : ℝ, 0 < y₂ → ∀ g : P, ∃ C' : ℝ, ∀ y₁ ∈ Set.Ioc (0 : ℝ) 1,
      ‖W y₁ y₂ g - ∑ i : Fin n, ∑ j : Fin J,
          c i j y₂ g * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C' * y₁ ^ (ρ + δ) := by
    intro y₂ hy₂ g
    obtain ⟨C', hC'⟩ := hcP_loc ⟨(y₂, g), hy₂⟩
    refine ⟨C', fun y₁ hy₁ => ?_⟩
    have h := hC'.self_of_nhds y₁ hy₁
    simp only [hF] at h
    simp only [hc_pos _ _ _ _ hy₂]
    exact h

  have h2 : ∀ (i : Fin n) (j : Fin J), ∃ c'ij : P → Fin n → Fin J → ℂ, Continuous c'ij ∧
      ∀ K : Set P, IsCompact K → ∃ C : ℝ, ∀ g ∈ K, ∀ y₂ ∈ Set.Ioc (0 : ℝ) 1,
        ‖c i j y₂ g - ∑ i' : Fin n, ∑ j' : Fin J,
            c'ij g i' j' * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * y₂ ^ (ρ + δ) := by
    intro i j
    have hF₂c : ∀ y₂ ∈ Set.Ioc (0 : ℝ) 1, Continuous fun g : P => c i j y₂ g := by
      intro y₂ hy₂
      have hres : (fun g : P => c i j y₂ g) = fun g => cP ⟨(y₂, g), hy₂.1⟩ i j := by
        funext g
        exact hc_pos i j y₂ g hy₂.1
      rw [hres]
      have hmap : Continuous fun g : P => (⟨(y₂, g), hy₂.1⟩ : Pset) :=
        Continuous.subtype_mk (continuous_const.prodMk continuous_id) _
      exact (continuous_apply j).comp ((continuous_apply i).comp (hcP_cont.comp hmap))
    have hloc₂ : ∀ g₀ : P, ∃ C B : ℝ, ∀ᶠ g in nhds g₀, ∃ v : Fin n → Fin J → ℂ, (∀ i' j', ‖v i' j'‖ ≤ B) ∧
        ∀ y₂ ∈ Set.Ioc (0 : ℝ) 1,
          ‖c i j y₂ g - ∑ i' : Fin n, ∑ j' : Fin J,
              v i' j' * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * y₂ ^ (ρ + δ) := by
      intro g₀
      obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds g₀
      obtain ⟨C, B, hCB⟩ := level2_passage e he ρ δ hδ hre hcl hgap S W hWc htrans hslice c hcexp K hKc
      refine ⟨C, B, ?_⟩
      filter_upwards [hKn] with g hg
      exact hCB g hg i j
    obtain ⟨c'ij, hc'c, -, hc'K⟩ := exists_canonical_coeff (P := P) e (ρ + δ) (fun g y₂ => c i j y₂ g) hF₂c hloc₂
      huniq
    exact ⟨c'ij, hc'c, fun K hK => hc'K K hK⟩
  choose c' hc'c hc'K using h2
  refine ⟨c, hccont, ?_, fun i j i' j' g => c' i j g i' j', ?_, ?_⟩
  ·
    intro K hK b hb
    have hbinv : 0 < b⁻¹ := inv_pos.2 (by linarith)
    have hS : IsCompact {p : Pset | p.1.1 ∈ Set.Icc b⁻¹ b ∧ p.1.2 ∈ K} := by
      rw [Subtype.isCompact_iff]
      convert (isCompact_Icc (a := b⁻¹) (b := b)).prod hK using 1
      ext q
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_prod, Subtype.exists, Prod.exists]
      constructor
      · rintro ⟨y, g, hy, ⟨hI, hg⟩, rfl⟩
        exact ⟨hI, hg⟩
      · rintro ⟨hI, hg⟩
        exact ⟨q.1, q.2, hbinv.trans_le hI.1, ⟨hI, hg⟩, rfl⟩
    obtain ⟨C, hC⟩ := hcP_cpt _ hS
    refine ⟨C, fun k hk y₂ hy₂l hy₂u y₁ hy₁0 hy₁1 => ?_⟩
    have hy₂pos : 0 < y₂ := hbinv.trans_le hy₂l
    have := hC ⟨(y₂, k), hy₂pos⟩ ⟨⟨hy₂l, hy₂u⟩, hk⟩ y₁ ⟨hy₁0, hy₁1⟩
    simp only [hF] at this
    simp only [hc_pos _ _ _ _ hy₂pos]
    exact this
  · intro i j i' j'
    exact (continuous_apply j').comp ((continuous_apply i').comp (hc'c i j))
  · intro K hK
    have hCij : ∀ (i : Fin n) (j : Fin J), ∃ C : ℝ, ∀ g ∈ K, ∀ y₂ ∈ Set.Ioc (0 : ℝ) 1,
        ‖c i j y₂ g - ∑ i' : Fin n, ∑ j' : Fin J,
            c' i j g i' j' * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ))‖ ≤ C * y₂ ^ (ρ + δ) :=
      fun i j => hc'K i j K hK
    choose Cij hCij using hCij
    refine ⟨∑ i : Fin n, ∑ j : Fin J, |Cij i j|, fun k hk i j y₂ hy₂0 hy₂1 => ?_⟩
    have h1 := hCij i j k hk y₂ ⟨hy₂0, hy₂1⟩
    have h2 : Cij i j ≤ ∑ i : Fin n, ∑ j : Fin J, |Cij i j| := by
      calc Cij i j ≤ |Cij i j| := le_abs_self _
        _ ≤ ∑ j : Fin J, |Cij i j| :=
            Finset.single_le_sum (f := fun j => |Cij i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
        _ ≤ ∑ i : Fin n, ∑ j : Fin J, |Cij i j| :=
            Finset.single_le_sum (f := fun i => ∑ j : Fin J, |Cij i j|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hy₂0.le _))

end S_RegularSingular_exists_twoLevel_coeff_of_transport_of_slice_expansion
end P2MW
export P2MW.S_RegularSingular_exists_twoLevel_coeff_of_transport_of_slice_expansion (solution)

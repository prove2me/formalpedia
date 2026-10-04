-- Prove2me | solution 1 for SennottDP.Tauberian.tauberian_theorem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:03:41.883251+00:00
-- url     : https://prove2.me/submissions/b88c5281-dbe7-4084-95ca-77b0ce8ab44f

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries
import Definitions.Def_SennottDP_Tauberian_KaramataR
import Theorems.Thm_SennottDP_Tauberian_abelian_inequalities
import Theorems.Thm_SennottDP_Tauberian_abel_limit_r
import Theorems.Thm_SennottDP_Tauberian_integral_r

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- `a_N = exp(-1/(N+1))`. -/
noncomputable def ttA (N : ℕ) : ℝ≥0 :=
  ⟨Real.exp (-(1 / ((N : ℝ) + 1))), (Real.exp_pos _).le⟩

theorem ttA_coe (N : ℕ) : ((ttA N : ℝ≥0) : ℝ) = Real.exp (-(1 / ((N : ℝ) + 1))) := rfl

theorem ttA_lt_one (N : ℕ) : ttA N < 1 := by
  rw [← NNReal.coe_lt_coe, ttA_coe, NNReal.coe_one]
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (by positivity))

theorem ttA_tendsto : Tendsto ttA atTop (𝓝[<] (1 : ℝ≥0)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall ttA_lt_one⟩
  rw [← NNReal.tendsto_coe]
  simp only [ttA_coe, NNReal.coe_one]
  have h0 : Tendsto (fun N : ℕ => -(1 / ((N : ℝ) + 1))) atTop (𝓝 (-0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.neg
  rw [neg_zero] at h0
  have := (Real.continuous_exp.tendsto 0).comp h0
  rw [Real.exp_zero] at this
  exact this

/-- The truncated sum: `∑ α^n u_n r(α^n) = w_{N+2}` at `α = a_N`. -/
theorem tt_sum (u : ℕ → ℝ≥0∞) (N : ℕ) :
    ∑' n : ℕ, ((ttA N : ℝ≥0) : ℝ≥0∞) ^ n * u n * ENNReal.ofReal (r (((ttA N : ℝ≥0) : ℝ) ^ n))
      = w u (N + 2) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hpow : ∀ n : ℕ, (((ttA N : ℝ≥0) : ℝ)) ^ n = Real.exp (-((n : ℝ) / ((N : ℝ) + 1))) := by
    intro n
    rw [ttA_coe, ← Real.exp_nat_mul]
    congr 1
    field_simp
  have hterm : ∀ n : ℕ, ((ttA N : ℝ≥0) : ℝ≥0∞) ^ n * u n *
      ENNReal.ofReal (r (((ttA N : ℝ≥0) : ℝ) ^ n)) = if n < N + 2 then u n else 0 := by
    intro n
    have hcoe : ((ttA N : ℝ≥0) : ℝ≥0∞) ^ n = ENNReal.ofReal ((((ttA N : ℝ≥0) : ℝ)) ^ n) := by
      rw [ENNReal.ofReal_pow NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
    rw [hcoe]
    unfold r
    rw [hpow]
    by_cases hn : n < N + 2
    · rw [if_pos hn, if_pos]
      · rw [mul_comm (ENNReal.ofReal _) (u n), mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          mul_inv_cancel₀ (Real.exp_pos _).ne', ENNReal.ofReal_one, mul_one]
      · rw [Real.exp_le_exp, neg_le_neg_iff, div_le_one hN]
        have : (n : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast (show n ≤ N + 1 by omega)
        exact this
    · rw [if_neg hn, if_neg, ENNReal.ofReal_zero, mul_zero]
      rw [Real.exp_le_exp, neg_le_neg_iff, div_le_one hN, not_le]
      exact_mod_cast (show N + 1 < n by omega)
  rw [tsum_congr hterm, tsum_eq_sum (s := Finset.range (N + 2))]
  · unfold w
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_pos (Finset.mem_range.mp hn)]
  · intro n hn
    rw [if_neg (fun h => hn (Finset.mem_range.mpr h))]

/-- `(N+2)(1 - a_N) → 1`. -/
theorem tt_ratio :
    Tendsto (fun N : ℕ => (1 - ((ttA N : ℝ≥0) : ℝ≥0∞)) * ((N : ℝ≥0∞) + 2)) atTop (𝓝 1) := by
  have heq : ∀ N : ℕ, (1 - ((ttA N : ℝ≥0) : ℝ≥0∞)) * ((N : ℝ≥0∞) + 2) =
      ENNReal.ofReal ((1 - Real.exp (-(1 / ((N : ℝ) + 1)))) * ((N : ℝ) + 2)) := by
    intro N
    have hsub : ENNReal.ofReal (1 - ((ttA N : ℝ≥0) : ℝ)) = 1 - ((ttA N : ℝ≥0) : ℝ≥0∞) := by
      rw [← NNReal.coe_one, ← NNReal.coe_sub (ttA_lt_one N).le, ENNReal.ofReal_coe_nnreal,
        ENNReal.coe_sub, ENNReal.coe_one]
    rw [ENNReal.ofReal_mul (by
      have := ttA_lt_one N
      have : ((ttA N : ℝ≥0) : ℝ) < 1 := by exact_mod_cast this
      rw [← ttA_coe]; linarith), ← ttA_coe, hsub]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) (by norm_num)]
    simp
  simp_rw [heq]
  rw [← ENNReal.ofReal_one]
  refine ENNReal.tendsto_ofReal ?_
  have hup : Tendsto (fun N : ℕ => 1 + 1 / ((N : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun N => ?_) (fun N => ?_)
  · -- lower bound: exp(-h) ≤ 1/(1+h)
    set h := 1 / ((N : ℝ) + 1) with hh
    have hpos : 0 < h := by positivity
    have h1 : Real.exp (-h) * (1 + h) ≤ 1 := by
      have := Real.add_one_le_exp h
      have he : Real.exp (-h) * Real.exp h = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-h)]
    have hN2 : (N : ℝ) + 2 = (1 + h) * ((N : ℝ) + 1) := by
      rw [hh]; field_simp; ring
    have hhN : h * ((N : ℝ) + 1) = 1 := by rw [hh]; field_simp
    show 1 ≤ (1 - Real.exp (-h)) * ((N : ℝ) + 2)
    rw [hN2]
    nlinarith [Real.exp_pos (-h), show (0 : ℝ) < (N : ℝ) + 1 by positivity]
  · set h := 1 / ((N : ℝ) + 1) with hh
    have h1 : 1 - h ≤ Real.exp (-h) := by linarith [Real.add_one_le_exp (-h)]
    have hN2 : (N : ℝ) + 2 = (1 + h) * ((N : ℝ) + 1) := by
      rw [hh]; field_simp; ring
    have hhN : h * ((N : ℝ) + 1) = 1 := by rw [hh]; field_simp
    show (1 - Real.exp (-h)) * ((N : ℝ) + 2) ≤ 1 + h
    rw [hN2]
    have hp : (0 : ℝ) ≤ (1 + h) * ((N : ℝ) + 1) := by positivity
    nlinarith [show (0 : ℝ) < h by positivity]

/-- The Tauberian direction: Abel convergence to a finite limit implies Cesàro convergence. -/
theorem tt_cesaro (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    Tendsto (cesaroMean u) atTop (𝓝 L) := by
  have hr := (abel_limit_r u hu0 L hL hlim).comp ttA_tendsto
  have hI : ∫ x in (0 : ℝ)..1, r x = 1 := integral_r.1.trans integral_r.2
  rw [hI, ENNReal.ofReal_one, mul_one] at hr
  have hG : Tendsto (fun N : ℕ => (1 - ((ttA N : ℝ≥0) : ℝ≥0∞)) * w u (N + 2)) atTop (𝓝 L) := by
    refine hr.congr fun N => ?_
    simp only [Function.comp]
    rw [tt_sum]
  have hd : Tendsto (fun N : ℕ => ((1 - ((ttA N : ℝ≥0) : ℝ≥0∞)) * ((N : ℝ≥0∞) + 2))⁻¹) atTop
      (𝓝 1) := by
    have := tendsto_inv_iff.mpr tt_ratio
    rwa [inv_one] at this
  have hprod := ENNReal.Tendsto.mul hG (Or.inr ENNReal.one_ne_top) hd (Or.inr hL)
  rw [mul_one] at hprod
  rw [← tendsto_add_atTop_iff_nat 2]
  refine hprod.congr fun N => ?_
  have hα : ((ttA N : ℝ≥0) : ℝ≥0∞) < 1 := by exact_mod_cast ttA_lt_one N
  have h0 : (1 - ((ttA N : ℝ≥0) : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hα).ne'
  have ht : (1 - ((ttA N : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  unfold cesaroMean
  rw [ENNReal.mul_inv (Or.inl h0) (Or.inl ht), div_eq_mul_inv]
  have hc : ((N + 2 : ℕ) : ℝ≥0∞) = (N : ℝ≥0∞) + 2 := by push_cast; ring
  rw [hc]
  calc (1 - ((ttA N : ℝ≥0) : ℝ≥0∞)) * w u (N + 2) *
        ((1 - ((ttA N : ℝ≥0) : ℝ≥0∞))⁻¹ * ((N : ℝ≥0∞) + 2)⁻¹)
      = ((1 - ((ttA N : ℝ≥0) : ℝ≥0∞)) * (1 - ((ttA N : ℝ≥0) : ℝ≥0∞))⁻¹) *
          (w u (N + 2) * ((N : ℝ≥0∞) + 2)⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel h0 ht, one_mul]

end SennottDP.Tauberian

open SennottDP.Tauberian in
theorem solution (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) :
    (liminf (cesaroMean u) atTop ≤ liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (cesaroMean u) atTop) ∧
    List.TFAE
      [liminf (cesaroMean u) atTop = liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
          liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) = limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
          limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) = limsup (cesaroMean u) atTop ∧
          limsup (cesaroMean u) atTop ≠ ⊤,
        ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ Tendsto (cesaroMean u) atTop (𝓝 L),
        ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)] := by
  have : (𝓝[<] (1 : ℝ≥0)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, zero_lt_one⟩
  have hab := abelian_inequalities u hu0
  obtain ⟨h1, h2, h3⟩ := id hab
  refine ⟨hab, ?_⟩
  tfae_have 1 → 2 := by
    rintro ⟨e1, e2, e3, hne⟩
    refine ⟨limsup (cesaroMean u) atTop, hne, ?_⟩
    exact tendsto_of_liminf_eq_limsup (e1.trans (e2.trans e3)) rfl
  tfae_have 2 → 3 := by
    rintro ⟨L, hL, ht⟩
    refine ⟨L, hL, ?_⟩
    have hli := ht.liminf_eq
    have hls := ht.limsup_eq
    have a1 : liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) = L :=
      le_antisymm (h2.trans (h3.trans hls.le)) (hli ▸ h1)
    have a2 : limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) = L :=
      le_antisymm (hls ▸ h3) (hli ▸ (h1.trans h2))
    exact tendsto_of_liminf_eq_limsup a1 a2
  tfae_have 3 → 1 := by
    rintro ⟨L, hL, ht⟩
    have hc := tt_cesaro u hu0 L hL ht
    rw [hc.liminf_eq, hc.limsup_eq, ht.liminf_eq, ht.limsup_eq]
    exact ⟨rfl, rfl, rfl, hL⟩
  tfae_finish



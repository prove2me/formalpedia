-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.corollary_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T10:30:12.361201+00:00
-- url     : https://prove2.me/submissions/ffbf0b0a-ef49-4acf-bdb9-867f725daca5

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model
import Theorems.Thm_RandomLeadGBS_Diffusion_lemma_5

open Filter Topology MeasureTheory ProbabilityTheory Real Set
open scoped NNReal
open RandomLeadGBS.Diffusion

namespace GBSCor6

lemma half_mean (v : ℝ≥0) (hv : v ≠ 0) :
    ∫ x, max (-x) 0 ∂(gaussianReal 0 v) = √((v : ℝ) / (2 * π)) := by
  have hvpos : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have h1 : ∫ x, gaussianPDFReal 0 v x * max (-x) 0 = ∫ x, gaussianPDFReal 0 v x * max x 0 := by
    rw [← integral_neg_eq_self (fun x => gaussianPDFReal 0 v x * max (-x) 0)]
    congr 1; funext x
    simp only [neg_neg, gaussianPDFReal, sub_zero, even_two, Even.neg_pow]
  rw [h1]
  have h2 : ∫ x, gaussianPDFReal 0 v x * max x 0 =
      ∫ x in Ioi (0 : ℝ), (√(2 * π * v))⁻¹ * (x ^ (1 : ℝ) * rexp (-(1 / (2 * v)) * x ^ (2 : ℝ))) := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1; funext x
    by_cases hx : 0 < x
    · rw [indicator_of_mem (mem_Ioi.mpr hx)]
      simp only [gaussianPDFReal, sub_zero, rpow_one, max_eq_left hx.le]
      rw [show x ^ (2 : ℝ) = x ^ 2 by norm_cast]
      have e : -x ^ 2 / (2 * (v : ℝ)) = -(1 / (2 * v)) * x ^ 2 := by ring
      rw [e]; ring
    · rw [indicator_of_notMem (by simpa using hx)]
      simp [max_eq_right (not_lt.mp hx)]
  rw [h2, integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by positivity)]
  have e1 : (-((1 : ℝ) + 1) / 2) = -1 := by norm_num
  have e2 : (((1 : ℝ) + 1) / 2) = 1 := by norm_num
  rw [e1, e2, Real.Gamma_one, Real.rpow_neg_one]
  have hπ : 0 < π := Real.pi_pos
  have hs : 0 < √(2 * π * v) := Real.sqrt_pos.mpr (by positivity)
  rw [show ((v : ℝ) / (2 * π)) = ((√(2 * π * v))⁻¹ * v) ^ 2 by
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]; field_simp]
  rw [Real.sqrt_sq (by positivity)]
  field_simp


/-- The truncated negative part `x ↦ min (x⁻) c` as a bounded continuous function. -/
noncomputable def phi (c : ℝ) (hc : 0 ≤ c) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (max (-x) 0) c, (continuous_neg.max continuous_const).min continuous_const⟩ c
    (by
      intro x y
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have hx0 : 0 ≤ min (max (-x) 0) c := le_min (le_max_right _ _) hc
      have hy0 : 0 ≤ min (max (-y) 0) c := le_min (le_max_right _ _) hc
      have hxc : min (max (-x) 0) c ≤ c := min_le_right _ _
      have hyc : min (max (-y) 0) c ≤ c := min_le_right _ _
      rw [abs_le]; constructor <;> linarith)

lemma phi_apply (c : ℝ) (hc : 0 ≤ c) (x : ℝ) : phi c hc x = min (max (-x) 0) c := rfl

/-- `(-c - x)⁺ = x⁻ - min (x⁻) c` for `c ≥ 0`. -/
lemma split (c : ℝ) (hc : 0 ≤ c) (x : ℝ) :
    max (-c - x) 0 = max (-x) 0 - min (max (-x) 0) c := by
  rcases le_total (-x) 0 with h | h
  · rw [max_eq_right (by linarith), max_eq_right h, min_eq_left hc]; ring
  · rw [max_eq_left h]
    rcases le_total (-x) c with h' | h'
    · rw [min_eq_left h', max_eq_right (by linarith)]; ring
    · rw [min_eq_right h', max_eq_left (by linarith)]; ring

end GBSCor6

open GBSCor6

theorem solution (P : Params) (hP : P.Standing) (hx : ∀ r, P.xs r = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ r₀ : ℝ, ∀ r ≥ r₀, ∀ p : ℤ → ℝ, IsArtStationary P r p →
      Summable (fun j : ℤ => p j * max (-c - (j : ℝ) / Real.sqrt r) 0) ∧
      ∑' j : ℤ, p j * max (-c - (j : ℝ) / Real.sqrt r) 0 ≤ ε := by
  intro ε hε
  obtain ⟨hex, hlim⟩ := lemma_5 P hP hx
  obtain ⟨hβ, hγ, -⟩ := hP
  have hγr : (1 : ℝ) ≤ P.γ := by exact_mod_cast hγ
  have hβγ : 0 < P.β * P.γ := by positivity
  set v : ℝ≥0 := (1 / (P.β * P.γ)).toNNReal with hvdef
  have hvval : (v : ℝ) = 1 / (P.β * P.γ) := Real.coe_toNNReal _ (by positivity)
  have hv : v ≠ 0 := by
    intro h0
    have : (v : ℝ) = 0 := by rw [h0]; rfl
    rw [hvval] at this
    have : 0 < 1 / (P.β * P.γ) := by positivity
    linarith
  set N := gaussianReal 0 v with hN
  set K : ℝ := (2 * π * P.β * P.γ) ^ (-(1 / 2 : ℝ)) with hKdef
  have hπ : 0 < π := Real.pi_pos
  have hK : ∫ x, max (-x) 0 ∂N = K := by
    rw [hN, half_mean v hv, hvval, hKdef]
    rw [show 1 / (P.β * P.γ) / (2 * π) = (2 * π * P.β * P.γ)⁻¹ by field_simp]
    rw [Real.sqrt_inv, Real.rpow_neg (by positivity), Real.sqrt_eq_rpow]
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hid : Integrable (fun x : ℝ => x) N :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by simp))
  have hNint : Integrable (fun x : ℝ => max (-x) 0) N := hid.neg_part
  -- monotone convergence of the truncations
  have hmc : Tendsto (fun n : ℕ => ∫ x, min (max (-x) 0) (n : ℝ) ∂N) atTop (𝓝 K) := by
    rw [← hK]
    apply integral_tendsto_of_tendsto_of_monotone
    · intro n
      refine Integrable.of_bound
        ((continuous_neg.max continuous_const).min continuous_const).aestronglyMeasurable
        (n : ℝ) (Eventually.of_forall fun x => ?_)
      have h0 : 0 ≤ min (max (-x) 0) (n : ℝ) := le_min (le_max_right _ _) (Nat.cast_nonneg n)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact min_le_right _ _
    · exact hNint
    · exact Eventually.of_forall fun x m n hmn => min_le_min le_rfl (by exact_mod_cast hmn)
    · refine Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_
      obtain ⟨N0, hN0⟩ := exists_nat_ge (max (-x) 0)
      filter_upwards [eventually_ge_atTop N0] with n hn
      have : max (-x) 0 ≤ (n : ℝ) := le_trans hN0 (by exact_mod_cast hn)
      rw [min_eq_left this]
  obtain ⟨n, hn1, hnK⟩ : ∃ n : ℕ, 1 ≤ n ∧ K - ε / 2 < ∫ x, min (max (-x) 0) (n : ℝ) ∂N := by
    have h1 := hmc.eventually (lt_mem_nhds (by linarith : K - ε / 2 < K))
    obtain ⟨n, hn⟩ := (h1.and (eventually_ge_atTop 1)).exists
    exact ⟨n, hn.2, hn.1⟩
  set c : ℝ := (n : ℝ) with hcdef
  have hc1 : (1 : ℝ) ≤ c := by rw [hcdef]; exact_mod_cast hn1
  have hc0 : (0 : ℝ) ≤ c := by linarith
  refine ⟨c, by linarith, ?_⟩
  by_contra hbad
  push Not at hbad
  classical
  let Bad : ℝ → (ℤ → ℝ) → Prop := fun r p => IsArtStationary P r p ∧
    (Summable (fun j : ℤ => p j * max (-c - (j : ℝ) / Real.sqrt r) 0) →
      ε < ∑' j : ℤ, p j * max (-c - (j : ℝ) / Real.sqrt r) 0)
  let pf : ℝ → ℤ → ℝ := fun r =>
    if h : ∃ p, Bad r p then h.choose else if h' : 0 < r then (hex r h').choose else fun _ => 0
  have hpf_stat : ∀ r, 0 < r → IsArtStationary P r (pf r) := by
    intro r hr
    simp only [pf]
    split_ifs with h
    · exact h.choose_spec.1
    · exact (hex r hr).choose_spec
  have hpf_bad : ∀ r, (∃ p, Bad r p) → Bad r (pf r) := by
    intro r h
    simp only [pf, dif_pos h]
    exact h.choose_spec
  have hpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  obtain ⟨hw, -, hneg⟩ := hlim pf (by filter_upwards [hpos] with r hr using hpf_stat r hr)
  have hφ := hw (phi c hc0)
  simp only [phi_apply] at hφ
  have hev : ∀ᶠ r in atTop,
      Summable (fun j : ℤ => pf r j * max (-c - (j : ℝ) / Real.sqrt r) 0) ∧
      ∑' j : ℤ, pf r j * max (-c - (j : ℝ) / Real.sqrt r) 0 < ε := by
    have h1 : ∀ᶠ r in atTop, 0 < ∑' j : ℤ, pf r j * max (-((j : ℝ) / Real.sqrt r)) 0 :=
      hneg.eventually (lt_mem_nhds hKpos)
    have h2 : ∀ᶠ r in atTop, (∑' j : ℤ, pf r j * max (-((j : ℝ) / Real.sqrt r)) 0) -
        (∑' j : ℤ, pf r j * min (max (-((j : ℝ) / Real.sqrt r)) 0) c) < ε := by
      have := hneg.sub hφ
      exact this.eventually (gt_mem_nhds (by linarith))
    filter_upwards [h1, h2, hpos] with r h1 h2 hr
    have hnn : ∀ j, 0 ≤ pf r j := (hpf_stat r hr).1
    have hs1 : Summable (fun j : ℤ => pf r j * max (-((j : ℝ) / Real.sqrt r)) 0) := by
      by_contra hns
      rw [tsum_eq_zero_of_not_summable hns] at h1
      exact lt_irrefl _ h1
    have hs2 : Summable (fun j : ℤ => pf r j * min (max (-((j : ℝ) / Real.sqrt r)) 0) c) := by
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hnn j) (le_min (le_max_right _ _) hc0))
        (fun j => ?_) ((hpf_stat r hr).2.1.mul_right c)
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) (hnn j)
    have heq : (fun j : ℤ => pf r j * max (-c - (j : ℝ) / Real.sqrt r) 0) =
        fun j => pf r j * max (-((j : ℝ) / Real.sqrt r)) 0 -
          pf r j * min (max (-((j : ℝ) / Real.sqrt r)) 0) c := by
      funext j
      rw [show -c - (j : ℝ) / Real.sqrt r = -c - ((j : ℝ) / Real.sqrt r) by ring,
        split c hc0, mul_sub]
    rw [heq]
    exact ⟨hs1.sub hs2, by rw [Summable.tsum_sub hs1 hs2]; exact h2⟩
  have hfreq : ∃ᶠ r in atTop, ∃ p, Bad r p := by
    rw [frequently_atTop]
    intro r₀
    obtain ⟨r, hr, p, hp, hp2⟩ := hbad r₀
    exact ⟨r, hr, p, hp, hp2⟩
  obtain ⟨r, ⟨hS, hlt⟩, hb⟩ := (hev.and_frequently hfreq).exists
  have := (hpf_bad r hb).2 hS
  linarith

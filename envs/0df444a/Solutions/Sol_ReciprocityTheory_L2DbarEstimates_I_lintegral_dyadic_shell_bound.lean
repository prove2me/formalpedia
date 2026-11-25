-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.lintegral_dyadic_shell_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:32.484016+00:00
-- url     : https://prove2.me/submissions/6ef9b3a3-569a-4055-a662-30986ca3760d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {α : Type*} [MeasurableSpace α] (μ : Measure α) (e : α → ℝ) (he : Measurable e)
    (he0 : ∀ x, 0 ≤ e x) (U : Set α) (hU : MeasurableSet U) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (n : ℕ) (hn : 1 ≤ n) (ε B : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hB : 0 ≤ B)
    (hZ : μ (U ∩ {x | e x ≤ 0}) = 0)
    (hsh : ∀ t : ℝ, 0 < t → t ≤ ε →
      ∫⁻ x in U ∩ {x | t ^ 2 / 2 ≤ e x ∧ e x ≤ t ^ 2},
        ENNReal.ofReal (f x * e x ^ (-(n : ℝ))) ∂μ ≤ ENNReal.ofReal B) :
    ∫⁻ x in U ∩ {x | e x < ε ^ 2}, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal (2 * B * ε ^ 2) := by
  set t : ℕ → ℝ := fun k => Real.sqrt (ε ^ 2 / 2 ^ k) with ht
  have ht2 : ∀ k, t k ^ 2 = ε ^ 2 / 2 ^ k := fun k => Real.sq_sqrt (by positivity)
  have htpos : ∀ k, 0 < t k := fun k => Real.sqrt_pos.2 (by positivity)
  have htle : ∀ k, t k ≤ ε := fun k => by
    calc t k ≤ Real.sqrt (ε ^ 2) :=
          Real.sqrt_le_sqrt (div_le_self (sq_nonneg _) (one_le_pow₀ one_le_two))
      _ = ε := Real.sqrt_sq hε.le
  set A : ℕ → Set α := fun k => U ∩ {x | t k ^ 2 / 2 ≤ e x ∧ e x ≤ t k ^ 2} with hAdef
  have hA : ∀ k, MeasurableSet (A k) := fun k =>
    hU.inter ((measurableSet_le measurable_const he).inter (measurableSet_le he measurable_const))
  have hcover : U ∩ {x | e x < ε ^ 2} ⊆ (U ∩ {x | e x ≤ 0}) ∪ ⋃ k, A k := by
    rintro x ⟨hxU, hx⟩
    simp only [Set.mem_setOf_eq] at hx
    by_cases h0 : e x ≤ 0
    · exact Or.inl ⟨hxU, h0⟩
    · push_neg at h0
      obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := ε ^ 2 / e x) (y := (2 : ℝ))
        ((one_le_div h0).2 hx.le) (by norm_num)
      refine Or.inr (Set.mem_iUnion.2 ⟨k, hxU, ?_⟩)
      have h1 := (le_div_iff₀ h0).1 hk1
      have h2 := (div_lt_iff₀ h0).1 hk2
      have hp : (0 : ℝ) < 2 ^ k := by positivity
      rw [ht2 k]
      constructor
      · rw [div_div, div_le_iff₀ (by positivity)]
        have h3 : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        rw [h3] at h2
        linarith
      · rw [le_div_iff₀ hp]; nlinarith
  have hk : ∀ k, ∫⁻ x in A k, ENNReal.ofReal (f x) ∂μ ≤
      ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B := by
    intro k
    calc ∫⁻ x in A k, ENNReal.ofReal (f x) ∂μ
        ≤ ∫⁻ x in A k, ENNReal.ofReal (ε ^ 2 / 2 ^ k) *
            ENNReal.ofReal (f x * e x ^ (-(n : ℝ))) ∂μ := by
          refine setLIntegral_mono' (hA k) (fun x hx => ?_)
          obtain ⟨_, hx1, hx2⟩ := hx
          have hex : 0 < e x := lt_of_lt_of_le (by have := htpos k; positivity) hx1
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [Real.rpow_neg (he0 x), Real.rpow_natCast]
          have hpn : 0 < e x ^ n := pow_pos hex n
          have hle1 : e x ≤ 1 := by
            have : t k ^ 2 ≤ 1 := by
              rw [ht2 k]
              calc ε ^ 2 / 2 ^ k ≤ ε ^ 2 := div_le_self (sq_nonneg _) (one_le_pow₀ one_le_two)
                _ ≤ 1 := by nlinarith
            linarith
          have hen : e x ^ n ≤ ε ^ 2 / 2 ^ k := by
            calc e x ^ n ≤ e x := pow_le_of_le_one (he0 x) hle1 (by omega)
              _ ≤ t k ^ 2 := hx2
              _ = ε ^ 2 / 2 ^ k := ht2 k
          rw [show ε ^ 2 / 2 ^ k * (f x * (e x ^ n)⁻¹) = f x * ((ε ^ 2 / 2 ^ k) / e x ^ n) by
            field_simp]
          exact le_mul_of_one_le_right (hf x) ((one_le_div hpn).2 hen)
      _ = ENNReal.ofReal (ε ^ 2 / 2 ^ k) *
            ∫⁻ x in A k, ENNReal.ofReal (f x * e x ^ (-(n : ℝ))) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B :=
          by gcongr; exact hsh (t k) (htpos k) (htle k)
  have hgeo : ∀ k : ℕ, ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B =
      ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal B * 2⁻¹ ^ k := by
    intro k
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2) k,
      ENNReal.ofReal_ofNat, div_eq_mul_inv, ENNReal.inv_pow]
    ring
  calc ∫⁻ x in U ∩ {x | e x < ε ^ 2}, ENNReal.ofReal (f x) ∂μ
      ≤ ∫⁻ x in (U ∩ {x | e x ≤ 0}) ∪ ⋃ k, A k, ENNReal.ofReal (f x) ∂μ :=
        lintegral_mono_set hcover
    _ ≤ ∫⁻ x in U ∩ {x | e x ≤ 0}, ENNReal.ofReal (f x) ∂μ +
          ∫⁻ x in ⋃ k, A k, ENNReal.ofReal (f x) ∂μ := lintegral_union_le _ _ _
    _ ≤ 0 + ∑' k, ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B :=
        add_le_add (le_of_eq (setLIntegral_measure_zero _ _ hZ))
          ((lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum hk))
    _ = ENNReal.ofReal (2 * B * ε ^ 2) := by
        simp_rw [hgeo]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          zero_add, show 2 * B * ε ^ 2 = ε ^ 2 * B * 2 by ring,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (sq_nonneg _),
          ENNReal.ofReal_ofNat]
end ReciprocityTheory.L2DbarEstimates.I

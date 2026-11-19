-- Prove2me | solution 1 for SennottDP.SEN.prop_7_7_2_h_acoi
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:57:56.427212+00:00
-- url     : https://prove2.me/submissions/dea721c5-a235-4af3-818d-e1782d59082a

import Mathlib
import Definitions.Def_SennottDP_SEN_Assumptions
import Theorems.Thm_SennottDP_SEN_prop_B_6_bounded_subsequence

open scoped ENNReal NNReal BigOperators
open Filter Topology

namespace SennottProp772

open SennottDP.SEN

/-! ### Section 1: Abel summation and Tauberian lemmas -/

lemma ennr_sum_add_tsum_nat_add (k : ℕ) (f : ℕ → ℝ≥0∞) :
    (∑ i ∈ Finset.range k, f i) + ∑' i : ℕ, f (i + k) = ∑' i : ℕ, f i := by
  rw [ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_eq_iSup_nat, ENNReal.add_iSup]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    have hsum : (∑ i ∈ Finset.range k, f i) + ∑ i ∈ Finset.range n, f (i + k) =
        ∑ i ∈ Finset.range (k + n), f i := by
      rw [Finset.sum_range_add]
      congr 1; apply Finset.sum_congr rfl; intro i _; rw [Nat.add_comm]
    rw [hsum]
    exact le_iSup (fun m => ∑ i ∈ Finset.range m, f i) (k + n)
  · refine iSup_le fun m => ?_
    refine le_trans (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_add_right m k))) ?_
    have hsum : ∑ i ∈ Finset.range (m + k), f i =
        (∑ i ∈ Finset.range k, f i) + ∑ i ∈ Finset.range m, f (i + k) := by
      rw [Nat.add_comm m k, Finset.sum_range_add]
      congr 1; apply Finset.sum_congr rfl; intro i _; rw [Nat.add_comm]
    rw [hsum]
    exact le_iSup (fun n => (∑ i ∈ Finset.range k, f i) + ∑ i ∈ Finset.range n, f (i + k)) m

lemma tsum_geom_ofReal_mul (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∑' k : ℕ, ENNReal.ofReal α ^ k = (ENNReal.ofReal (1 - α))⁻¹ := by
  have hlt : ENNReal.ofReal α < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hα1
  rw [ENNReal.tsum_geometric, ENNReal.ofReal_sub 1 hα0, ENNReal.ofReal_one]

lemma abel_summation (c : ℕ → ℝ≥0∞) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ENNReal.ofReal (1 - α) * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t =
      ENNReal.ofReal (1 - α) ^ 2 *
        ∑' m : ℕ, ENNReal.ofReal α ^ m * (∑ t ∈ Finset.range (m + 1), c t) := by
  have h1α_pos : 0 < 1 - α := sub_pos.mpr hα1
  have h1α_ne0 : ENNReal.ofReal (1 - α) ≠ 0 := (ENNReal.ofReal_pos.mpr h1α_pos).ne'
  have h1α_ne_top : ENNReal.ofReal (1 - α) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsum :
      ∑' m : ℕ, ENNReal.ofReal α ^ m * (∑ t ∈ Finset.range (m + 1), c t) =
        (ENNReal.ofReal (1 - α))⁻¹ * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t := by
    calc ∑' m : ℕ, ENNReal.ofReal α ^ m * (∑ t ∈ Finset.range (m + 1), c t)
        = ∑' m : ℕ, ∑' t : ℕ, if t ≤ m then ENNReal.ofReal α ^ m * c t else 0 := by
            congr 1; ext m
            rw [Finset.mul_sum]
            rw [← ennr_sum_add_tsum_nat_add (m + 1)]
            have htail : (∑' k : ℕ, if k + (m + 1) ≤ m then ENNReal.ofReal α ^ m * c (k + (m + 1)) else 0) = 0 := by
              apply ENNReal.tsum_eq_zero.mpr
              intro k
              have hnot : ¬ k + (m + 1) ≤ m := by omega
              simp [hnot]
            rw [htail, add_zero]
            apply Finset.sum_congr rfl
            intro t ht
            have hle : t ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
            simp [hle]
      _ = ∑' t : ℕ, ∑' m : ℕ, if t ≤ m then ENNReal.ofReal α ^ m * c t else 0 := ENNReal.tsum_comm
      _ = ∑' t : ℕ, (∑' k : ℕ, ENNReal.ofReal α ^ (t + k)) * c t := by
            congr 1; ext t
            rw [← ENNReal.tsum_mul_right]
            rw [← ennr_sum_add_tsum_nat_add t]
            have hhead : (∑ m ∈ Finset.range t, if t ≤ m then ENNReal.ofReal α ^ m * c t else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro m hm
              have hnot : ¬ t ≤ m := not_le.mpr (Finset.mem_range.mp hm)
              simp [hnot]
            rw [hhead, zero_add]
            congr 1; ext k
            have hle : t ≤ k + t := Nat.le_add_left t k
            rw [if_pos hle, Nat.add_comm]
      _ = ∑' t : ℕ, (ENNReal.ofReal α ^ t * (ENNReal.ofReal (1 - α))⁻¹) * c t := by
            congr 1; ext t
            congr 1
            simp_rw [pow_add, ENNReal.tsum_mul_left, tsum_geom_ofReal_mul α hα0 hα1]
      _ = (ENNReal.ofReal (1 - α))⁻¹ * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t := by
            rw [← ENNReal.tsum_mul_left]
            congr 1; ext t; ring
  rw [hsum, sq]
  calc ENNReal.ofReal (1 - α) * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t
      = ENNReal.ofReal (1 - α) * 1 * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t := by rw [mul_one]
    _ = ENNReal.ofReal (1 - α) * (ENNReal.ofReal (1 - α) * (ENNReal.ofReal (1 - α))⁻¹) *
          ∑' t : ℕ, ENNReal.ofReal α ^ t * c t := by
          rw [ENNReal.mul_inv_cancel h1α_ne0 h1α_ne_top]
    _ = ENNReal.ofReal (1 - α) * ENNReal.ofReal (1 - α) *
          ((ENNReal.ofReal (1 - α))⁻¹ * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t) := by ring

lemma tsum_geom_mul_succ (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ENNReal.ofReal (1 - α) ^ 2 *
      ∑' m : ℕ, ENNReal.ofReal α ^ m * ((m + 1 : ℕ) : ℝ≥0∞) = 1 := by
  have h := abel_summation (fun _ => (1 : ℝ≥0∞)) α hα0 hα1
  simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  rw [tsum_geom_ofReal_mul α hα0 hα1] at h
  have h1α_pos : 0 < 1 - α := sub_pos.mpr hα1
  have h1α_ne0 : ENNReal.ofReal (1 - α) ≠ 0 := (ENNReal.ofReal_pos.mpr h1α_pos).ne'
  have h1α_ne_top : ENNReal.ofReal (1 - α) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.mul_inv_cancel h1α_ne0 h1α_ne_top] at h
  exact h.symm

lemma tauberian_limsup_le (c : ℕ → ℝ≥0∞) :
    limsup (fun α : ℝ => ENNReal.ofReal (1 - α) * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t) (𝓝[<] 1) ≤
      limsup (fun n : ℕ => (∑ t ∈ Finset.range n, c t) / (n : ℝ≥0∞)) atTop := by
  set L := limsup (fun n : ℕ => (∑ t ∈ Finset.range n, c t) / (n : ℝ≥0∞)) atTop
  by_cases hL : L = ⊤
  · rw [hL]; exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hlt : L < L + ε := ENNReal.lt_add_right hL (ENNReal.coe_pos.mpr hε).ne'
  have hev : ∀ᶠ n : ℕ in atTop, (∑ t ∈ Finset.range n, c t) / (n : ℝ≥0∞) < L + ε :=
    eventually_lt_of_limsup_lt hlt
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hv_le : ∀ m ≥ N, ∑ t ∈ Finset.range (m + 1), c t ≤ (L + ε) * ((m + 1 : ℕ) : ℝ≥0∞) := by
    intro m hm
    have h1 := (hN (m + 1) (Nat.le_succ_of_le hm)).le
    have hpos : ((m + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
    have hnt : ((m + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    exact (ENNReal.div_le_iff_le_mul (Or.inl hpos) (Or.inl hnt)).mp h1
  have hfin_N : ∑ t ∈ Finset.range (N + 1), c t ≠ ⊤ := by
    have h1 := hN (N + 1) (Nat.le_succ N)
    intro htop
    rw [htop] at h1
    have htop2 : (⊤ : ℝ≥0∞) / ((N + 1 : ℕ) : ℝ≥0∞) = ⊤ :=
      ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top _)
    rw [htop2] at h1
    exact not_top_lt h1
  set C : ℝ≥0∞ := ∑ m ∈ Finset.range N, ∑ t ∈ Finset.range (m + 1), c t
  have hC_ne_top : C ≠ ⊤ := by
    apply ne_of_lt
    apply ENNReal.sum_lt_top.mpr
    intro m hm
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hfin_N)
    apply Finset.sum_le_sum_of_subset
    exact Finset.range_mono (Nat.succ_le_succ (Finset.mem_range.mp hm).le)
  have hbound : ∀ᶠ α : ℝ in 𝓝[<] 1,
      ENNReal.ofReal (1 - α) * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t ≤
        ENNReal.ofReal (1 - α) ^ 2 * C + (L + ε) := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with α hα
    rw [abel_summation c α hα.1.le hα.2]
    have hsplit : ∑' m : ℕ, ENNReal.ofReal α ^ m * (∑ t ∈ Finset.range (m + 1), c t) ≤
        C + (L + ε) * ∑' m : ℕ, ENNReal.ofReal α ^ m * ((m + 1 : ℕ) : ℝ≥0∞) := by
      rw [← ennr_sum_add_tsum_nat_add N]
      apply add_le_add
      · apply Finset.sum_le_sum
        intro m _
        have hαle : ENNReal.ofReal α ^ m ≤ 1 := pow_le_one₀ (by positivity) (ENNReal.ofReal_le_one.mpr hα.2.le)
        calc ENNReal.ofReal α ^ m * ∑ t ∈ Finset.range (m + 1), c t
            ≤ 1 * ∑ t ∈ Finset.range (m + 1), c t := by gcongr
          _ = ∑ t ∈ Finset.range (m + 1), c t := one_mul _
      · rw [← ENNReal.tsum_mul_left]
        calc ∑' k : ℕ, ENNReal.ofReal α ^ (k + N) * ∑ t ∈ Finset.range (k + N + 1), c t
            ≤ ∑' k : ℕ, (L + ε) * (ENNReal.ofReal α ^ (k + N) * ((k + N + 1 : ℕ) : ℝ≥0∞)) := by
              apply ENNReal.tsum_le_tsum
              intro k
              have := hv_le (k + N) (Nat.le_add_left N k)
              calc ENNReal.ofReal α ^ (k + N) * ∑ t ∈ Finset.range (k + N + 1), c t
                  ≤ ENNReal.ofReal α ^ (k + N) * ((L + ε) * ((k + N + 1 : ℕ) : ℝ≥0∞)) := by gcongr
                _ = (L + ε) * (ENNReal.ofReal α ^ (k + N) * ((k + N + 1 : ℕ) : ℝ≥0∞)) := by ring
          _ ≤ ∑' m : ℕ, (L + ε) * (ENNReal.ofReal α ^ m * ((m + 1 : ℕ) : ℝ≥0∞)) := by
              conv_rhs => rw [← ennr_sum_add_tsum_nat_add N]
              exact le_add_self
    calc ENNReal.ofReal (1 - α) ^ 2 * ∑' m : ℕ, ENNReal.ofReal α ^ m * ∑ t ∈ Finset.range (m + 1), c t
        ≤ ENNReal.ofReal (1 - α) ^ 2 * (C + (L + ε) * ∑' m : ℕ, ENNReal.ofReal α ^ m * ((m + 1 : ℕ) : ℝ≥0∞)) := by
          gcongr
      _ = ENNReal.ofReal (1 - α) ^ 2 * C +
            (L + ε) * (ENNReal.ofReal (1 - α) ^ 2 * ∑' m : ℕ, ENNReal.ofReal α ^ m * ((m + 1 : ℕ) : ℝ≥0∞)) := by
          rw [mul_add]; congr 1; ring
      _ = ENNReal.ofReal (1 - α) ^ 2 * C + (L + ε) := by
          rw [tsum_geom_mul_succ α hα.1.le hα.2, mul_one]
  calc limsup (fun α : ℝ => ENNReal.ofReal (1 - α) * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t) (𝓝[<] 1)
      ≤ limsup (fun α : ℝ => ENNReal.ofReal (1 - α) ^ 2 * C + (L + ε)) (𝓝[<] 1) :=
        limsup_le_limsup hbound
    _ = L + ε := by
        apply Tendsto.limsup_eq
        have h0 : Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) ^ 2 * C + (L + ε)) (𝓝[<] 1)
            (𝓝 (0 ^ 2 * C + (L + ε))) := by
          refine Tendsto.add ?_ tendsto_const_nhds
          refine ENNReal.Tendsto.mul_const ?_ (Or.inr hC_ne_top)
          refine (ENNReal.continuous_pow 2).continuousAt.tendsto.comp ?_
          have hsub : Tendsto (fun α : ℝ => 1 - α) (𝓝[<] 1) (𝓝 (1 - 1)) :=
            (continuous_const.sub continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
          rw [sub_self] at hsub
          have hcomp : Tendsto (ENNReal.ofReal ∘ fun α : ℝ => 1 - α) (𝓝[<] 1) (𝓝 (ENNReal.ofReal 0)) :=
            ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsub
          simpa [Function.comp_def] using hcomp
        simpa using h0

lemma one_sub_inv_pow_ge_exp_neg_two {n : ℕ} (hn : 2 ≤ n) :
    Real.exp (-2) ≤ (1 - (n : ℝ)⁻¹) ^ n := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := Nat.ofNat_le_cast.mpr hn
    linarith
  have hbase_pos : 0 < 1 - (n : ℝ)⁻¹ := by
    rw [sub_pos, inv_lt_one_iff₀]
    right; exact_mod_cast (by omega : 1 < n)
  have hinv : (1 - (n : ℝ)⁻¹)⁻¹ = 1 + ((n : ℝ) - 1)⁻¹ := by
    field_simp
    ring
  have hexp1 : (1 - (n : ℝ)⁻¹)⁻¹ ≤ Real.exp (((n : ℝ) - 1)⁻¹) := by
    rw [hinv, add_comm]
    exact Real.add_one_le_exp _
  have hpow : ((1 - (n : ℝ)⁻¹) ^ n)⁻¹ ≤ Real.exp 2 := by
    rw [← inv_pow]
    calc ((1 - (n : ℝ)⁻¹)⁻¹) ^ n
        ≤ (Real.exp (((n : ℝ) - 1)⁻¹)) ^ n := pow_le_pow_left₀ (inv_nonneg.mpr hbase_pos.le) hexp1 n
      _ = Real.exp ((n : ℝ) * ((n : ℝ) - 1)⁻¹) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp 2 := by
          apply Real.exp_le_exp.mpr
          rw [mul_inv_le_iff₀ hn1_pos]
          have : (2 : ℝ) ≤ n := Nat.ofNat_le_cast.mpr hn
          linarith
  rw [Real.exp_neg]
  exact inv_le_of_inv_le₀ (pow_pos hbase_pos n) hpow

lemma tauberian_tendsto_of_limsup_le_of_le_liminf (c : ℕ → ℝ≥0∞) (J : ℝ≥0)
    (hsup : limsup (fun n : ℕ => (∑ t ∈ Finset.range n, c t) / (n : ℝ≥0∞)) atTop ≤ (J : ℝ≥0∞))
    (hinf : (J : ℝ≥0∞) ≤ liminf (fun α : ℝ => ENNReal.ofReal (1 - α) * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t) (𝓝[<] 1)) :
    Tendsto (fun n : ℕ => (∑ t ∈ Finset.range n, c t) / (n : ℝ≥0∞)) atTop (𝓝 (J : ℝ≥0∞)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ hsup
  by_contra hlt
  push Not at hlt
  set L := liminf (fun n : ℕ => (∑ t ∈ Finset.range n, c t) / (n : ℝ≥0∞)) atTop
  have hL_ne_top : L ≠ ⊤ := (lt_of_lt_of_le hlt le_top).ne
  have hL_lt_J : L.toReal < (J : ℝ) := by
    have h := ENNReal.toReal_strict_mono (ENNReal.coe_ne_top (r := J)) hlt
    simpa using h
  let δ : ℝ := ((J : ℝ) - L.toReal) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  have hJ_sub_δ_pos : 0 < (J : ℝ) - δ := by
    have hL0 : 0 ≤ L.toReal := ENNReal.toReal_nonneg
    dsimp [δ]; linarith
  have hL_lt_sub : L < ENNReal.ofReal ((J : ℝ) - δ) := by
    rw [← ENNReal.ofReal_toReal hL_ne_top]
    exact (ENNReal.ofReal_lt_ofReal_iff hJ_sub_δ_pos).mpr (by dsimp [δ]; linarith)
  let r : ℝ := ((J : ℝ) - δ) / ((J : ℝ) - δ / 2)
  have hr_pos : 0 < r := div_pos hJ_sub_δ_pos (by linarith)
  have hr_lt_one : r < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  let c_const : ℝ := r * (1 - r) * Real.exp (-2) / 2
  have hc_pos : 0 < c_const := by
    have : 0 < Real.exp (-2) := Real.exp_pos _
    have : 0 < 1 - r := sub_pos.mpr hr_lt_one
    positivity
  have hc_le_one : c_const ≤ 1 := by
    have h1 : r * (1 - r) ≤ 1 := by nlinarith
    have h2 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    dsimp [c_const]
    nlinarith [Real.exp_pos (-2)]
  let ε : ℝ := (δ / 2) * c_const / 4
  have hε_pos : 0 < ε := by positivity
  have hε_le_δ : ε ≤ δ / 2 := by
    dsimp [ε]; nlinarith
  -- Upper bound for large m from hsup
  have hsup_lt : limsup (fun n : ℕ => (∑ t ∈ Finset.range n, c t) / (n : ℝ≥0∞)) atTop <
      ENNReal.ofReal ((J : ℝ) + ε) := by
    refine lt_of_le_of_lt hsup ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [J.coe_nonneg])).mpr (by linarith)
  have hev_sup : ∀ᶠ n : ℕ in atTop, (∑ t ∈ Finset.range n, c t) / (n : ℝ≥0∞) < ENNReal.ofReal ((J : ℝ) + ε) :=
    eventually_lt_of_limsup_lt hsup_lt
  rw [Filter.eventually_atTop] at hev_sup
  obtain ⟨N, hN⟩ := hev_sup
  have hv_le : ∀ m ≥ N, ∑ t ∈ Finset.range (m + 1), c t ≤
      ENNReal.ofReal ((J : ℝ) + ε) * ((m + 1 : ℕ) : ℝ≥0∞) := by
    intro m hm
    have h1 := (hN (m + 1) (Nat.le_succ_of_le hm)).le
    exact (ENNReal.div_le_iff_le_mul (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _))).mp h1
  have hfin_N : ∑ t ∈ Finset.range (N + 1), c t ≠ ⊤ := by
    have h1 := hN (N + 1) (Nat.le_succ N)
    intro htop; rw [htop, ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top _)] at h1
    exact not_top_lt h1
  set C : ℝ≥0∞ := ∑ m ∈ Finset.range N, ∑ t ∈ Finset.range (m + 1), c t
  have hC_ne_top : C ≠ ⊤ := by
    apply ne_of_lt; apply ENNReal.sum_lt_top.mpr; intro m hm
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hfin_N)
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ (Finset.mem_range.mp hm).le))
  -- Lower bound from hinf: eventually for α ∈ (1 - η, 1), (1 - α) V_α > J - ε
  have hJ_gt : ENNReal.ofReal ((J : ℝ) - ε) <
      liminf (fun α : ℝ => ENNReal.ofReal (1 - α) * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t) (𝓝[<] 1) := by
    refine lt_of_lt_of_le ?_ hinf
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [J.coe_nonneg])).mpr (by linarith)
  have hev_inf : ∀ᶠ α : ℝ in 𝓝[<] 1,
      ENNReal.ofReal ((J : ℝ) - ε) < ENNReal.ofReal (1 - α) * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t :=
    eventually_lt_of_lt_liminf hJ_gt
  rw [Filter.Eventually, mem_nhdsLT_iff_exists_Ioo_subset] at hev_inf
  obtain ⟨l, hl_lt, hl_sub⟩ := hev_inf
  let η : ℝ := 1 - l
  have hη_pos : 0 < η := sub_pos.mpr hl_lt
  -- Pick a large n with v n / n < J - δ
  have hfreq : ∃ᶠ n : ℕ in atTop,
      (∑ t ∈ Finset.range n, c t) / (n : ℝ≥0∞) < ENNReal.ofReal ((J : ℝ) - δ) :=
    frequently_lt_of_liminf_lt (h := hL_lt_sub)
  rw [Filter.frequently_atTop] at hfreq
  -- Choose threshold M large enough for all bounds
  set M : ℕ := max (max (max 4 (Nat.ceil (η⁻¹) + 1)) (Nat.ceil ((N : ℝ) / r) + 1))
    (max (Nat.ceil (4 / (1 - r)) + 1) (Nat.ceil (Real.sqrt (C.toReal / ε)) + 1))
  obtain ⟨n, hnM, hn_lt⟩ := hfreq M
  have hn4 : 4 ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hnM
  have hn_pos : (0 : ℝ) < n := by positivity
  have hn_η : (n : ℝ)⁻¹ < η := by
    have h1 : Nat.ceil (η⁻¹) + 1 ≤ n :=
      le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hnM
    have h2 : η⁻¹ < n := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast (by omega : Nat.ceil (η⁻¹) < n))
    exact inv_lt_of_inv_lt₀ hη_pos h2
  have hα_mem : 1 - (n : ℝ)⁻¹ ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · have : (n : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < n))
      linarith
    · linarith [inv_pos.mpr hn_pos]
  let α : ℝ := 1 - (n : ℝ)⁻¹
  have h1α : 1 - α = (n : ℝ)⁻¹ := by simp [α]
  have hα_inf : ENNReal.ofReal ((J : ℝ) - ε) <
      ENNReal.ofReal (1 - α) * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t := by
    apply hl_sub
    exact ⟨by dsimp [α, η] at hn_η ⊢; linarith, hα_mem.2⟩
  have hvn_le : ∑ t ∈ Finset.range n, c t ≤ ENNReal.ofReal ((J : ℝ) - δ) * (n : ℝ≥0∞) :=
    (ENNReal.div_le_iff_le_mul (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _))).mp hn_lt.le
  -- Define S_bad = [⌈r * n⌉₊, n)
  set K : ℕ := Nat.ceil (r * n)
  have hK_ge_N : N ≤ K := by
    have h1 : Nat.ceil ((N : ℝ) / r) + 1 ≤ n :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnM
    have h2 : (N : ℝ) / r ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : Nat.ceil ((N : ℝ) / r) ≤ n))
    have h3 : (N : ℝ) ≤ r * n := by linarith [(div_le_iff₀ hr_pos).mp h2]
    exact Nat.cast_le.mp (le_trans h3 (Nat.le_ceil (r * n)))
  have h1r_n : 4 ≤ (1 - r) * n := by
    have h1 : Nat.ceil (4 / (1 - r)) + 1 ≤ n :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnM
    have h2 : 4 / (1 - r) ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : Nat.ceil (4 / (1 - r)) ≤ n))
    linarith [(div_le_iff₀ (sub_pos.mpr hr_lt_one)).mp h2]
  set S_bad : Finset ℕ := Finset.Ico K n
  have hbad_bound : ∀ m ∈ S_bad,
      ∑ t ∈ Finset.range (m + 1), c t + ENNReal.ofReal (δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal ((J : ℝ) + ε) * ((m + 1 : ℕ) : ℝ≥0∞) := by
    intro m hm
    have hmK : K ≤ m := (Finset.mem_Ico.mp hm).1
    have hmn : m < n := (Finset.mem_Ico.mp hm).2
    have hvm_le_vn : ∑ t ∈ Finset.range (m + 1), c t ≤ ∑ t ∈ Finset.range n, c t :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hmn))
    have hm1_ge_rn : r * n ≤ (m + 1 : ℕ) := by
      have : r * n ≤ K := Nat.le_ceil _
      have : (K : ℝ) ≤ m := Nat.cast_le.mpr hmK
      push_cast; linarith
    have hn_le_m1 : (n : ℝ) ≤ ((m + 1 : ℕ) : ℝ) / r := (le_div_iff₀ hr_pos).mpr (by linarith)
    have hvm_le : ∑ t ∈ Finset.range (m + 1), c t ≤
        ENNReal.ofReal ((J : ℝ) - δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞) := by
      calc ∑ t ∈ Finset.range (m + 1), c t
          ≤ ENNReal.ofReal ((J : ℝ) - δ) * (n : ℝ≥0∞) := le_trans hvm_le_vn hvn_le
        _ = ENNReal.ofReal (((J : ℝ) - δ) * n) := by
            rw [ENNReal.ofReal_mul hJ_sub_δ_pos.le, ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal (((J : ℝ) - δ / 2) * ((m + 1 : ℕ) : ℝ)) := by
            apply ENNReal.ofReal_le_ofReal
            have hr_eq : (J : ℝ) - δ = r * ((J : ℝ) - δ / 2) := by
              have hne : (J : ℝ) - δ / 2 ≠ 0 := by linarith
              simp only [r]; rw [div_mul_cancel₀ _ hne]
            rw [hr_eq, mul_assoc]
            have h1 : ((J : ℝ) - δ / 2) * (r * n) ≤ ((J : ℝ) - δ / 2) * ((m + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hm1_ge_rn (by linarith)
            linarith
        _ = ENNReal.ofReal ((J : ℝ) - δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞) := by
            rw [ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_natCast]
    calc ∑ t ∈ Finset.range (m + 1), c t + ENNReal.ofReal (δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞)
        ≤ ENNReal.ofReal ((J : ℝ) - δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞) +
            ENNReal.ofReal (δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞) := by gcongr
      _ = (ENNReal.ofReal ((J : ℝ) - δ / 2) + ENNReal.ofReal (δ / 2)) * ((m + 1 : ℕ) : ℝ≥0∞) := by ring
      _ = ENNReal.ofReal (J : ℝ) * ((m + 1 : ℕ) : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 2; ring
      _ ≤ ENNReal.ofReal ((J : ℝ) + ε) * ((m + 1 : ℕ) : ℝ≥0∞) := by
          gcongr; linarith
  -- Sum over all m with Abel summation
  have hmain_sum :
      ENNReal.ofReal (1 - α) * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t +
        ENNReal.ofReal (1 - α) ^ 2 *
          ∑ m ∈ S_bad, ENNReal.ofReal α ^ m * (ENNReal.ofReal (δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞)) ≤
        ENNReal.ofReal (1 - α) ^ 2 * C + ENNReal.ofReal ((J : ℝ) + ε) := by
    rw [abel_summation c α hα_mem.1.le hα_mem.2, ← mul_add]
    have hinner :
        (∑' m : ℕ, ENNReal.ofReal α ^ m * ∑ t ∈ Finset.range (m + 1), c t) +
          ∑ m ∈ S_bad, ENNReal.ofReal α ^ m * (ENNReal.ofReal (δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞)) ≤
          C + ENNReal.ofReal ((J : ℝ) + ε) * ∑' m : ℕ, ENNReal.ofReal α ^ m * ((m + 1 : ℕ) : ℝ≥0∞) := by
      rw [← ennr_sum_add_tsum_nat_add N]
      have hbad_tsum :
          ∑ m ∈ S_bad, ENNReal.ofReal α ^ m * (ENNReal.ofReal (δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞)) =
            ∑' k : ℕ, if k + N ∈ S_bad then
              ENNReal.ofReal α ^ (k + N) * (ENNReal.ofReal (δ / 2) * ((k + N + 1 : ℕ) : ℝ≥0∞)) else 0 := by
        rw [← ennr_sum_add_tsum_nat_add n]
        have htail : (∑' k : ℕ, if k + n + N ∈ S_bad then
            ENNReal.ofReal α ^ (k + n + N) * (ENNReal.ofReal (δ / 2) * ((k + n + N + 1 : ℕ) : ℝ≥0∞)) else 0) = 0 := by
          apply ENNReal.tsum_eq_zero.mpr; intro k
          have hnot : k + n + N ∉ S_bad := by simp [S_bad]; omega
          simp [hnot]
        rw [htail, add_zero]
        symm
        calc ∑ k ∈ Finset.range n, (if k + N ∈ S_bad then
                ENNReal.ofReal α ^ (k + N) * (ENNReal.ofReal (δ / 2) * ((k + N + 1 : ℕ) : ℝ≥0∞)) else 0)
            = ∑ k ∈ (Finset.range n).filter (fun k => k + N ∈ S_bad),
                ENNReal.ofReal α ^ (k + N) * (ENNReal.ofReal (δ / 2) * ((k + N + 1 : ℕ) : ℝ≥0∞)) := by
                rw [Finset.sum_filter]
          _ = ∑ m ∈ S_bad, ENNReal.ofReal α ^ m * (ENNReal.ofReal (δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞)) := by
                refine Finset.sum_nbij (fun k => k + N) ?_ ?_ ?_ ?_
                · intro k hk; exact (Finset.mem_filter.mp hk).2
                · intro k1 _ k2 _ h; exact Nat.add_right_cancel h
                · intro m hm
                  refine ⟨m - N, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩, ?_⟩
                  · have := (Finset.mem_Ico.mp hm).2; omega
                  · have := (Finset.mem_Ico.mp hm).1
                    rw [Nat.sub_add_cancel (le_trans hK_ge_N this)]; exact hm
                  · have := (Finset.mem_Ico.mp hm).1
                    exact Nat.sub_add_cancel (le_trans hK_ge_N this)
                · intro k _; rfl
      rw [add_assoc, hbad_tsum, ← ENNReal.tsum_add]
      apply add_le_add
      · apply Finset.sum_le_sum; intro m _
        have hαle : ENNReal.ofReal α ^ m ≤ 1 := pow_le_one₀ (by positivity) (ENNReal.ofReal_le_one.mpr hα_mem.2.le)
        calc ENNReal.ofReal α ^ m * ∑ t ∈ Finset.range (m + 1), c t
            ≤ 1 * ∑ t ∈ Finset.range (m + 1), c t := by gcongr
          _ = ∑ t ∈ Finset.range (m + 1), c t := one_mul _
      · rw [← ENNReal.tsum_mul_left]
        calc ∑' k : ℕ, (ENNReal.ofReal α ^ (k + N) * ∑ t ∈ Finset.range (k + N + 1), c t +
                if k + N ∈ S_bad then
                  ENNReal.ofReal α ^ (k + N) * (ENNReal.ofReal (δ / 2) * ((k + N + 1 : ℕ) : ℝ≥0∞)) else 0)
            ≤ ∑' k : ℕ, ENNReal.ofReal ((J : ℝ) + ε) * (ENNReal.ofReal α ^ (k + N) * ((k + N + 1 : ℕ) : ℝ≥0∞)) := by
              apply ENNReal.tsum_le_tsum; intro k
              by_cases hk : k + N ∈ S_bad
              · rw [if_pos hk, ← mul_add]
                calc ENNReal.ofReal α ^ (k + N) *
                      (∑ t ∈ Finset.range (k + N + 1), c t + ENNReal.ofReal (δ / 2) * ((k + N + 1 : ℕ) : ℝ≥0∞))
                    ≤ ENNReal.ofReal α ^ (k + N) *
                        (ENNReal.ofReal ((J : ℝ) + ε) * ((k + N + 1 : ℕ) : ℝ≥0∞)) := by
                      gcongr; exact hbad_bound (k + N) hk
                  _ = ENNReal.ofReal ((J : ℝ) + ε) * (ENNReal.ofReal α ^ (k + N) * ((k + N + 1 : ℕ) : ℝ≥0∞)) := by
                      ring
              · rw [if_neg hk, add_zero]
                calc ENNReal.ofReal α ^ (k + N) * ∑ t ∈ Finset.range (k + N + 1), c t
                    ≤ ENNReal.ofReal α ^ (k + N) *
                        (ENNReal.ofReal ((J : ℝ) + ε) * ((k + N + 1 : ℕ) : ℝ≥0∞)) := by
                      gcongr; exact hv_le (k + N) (Nat.le_add_left N k)
                  _ = ENNReal.ofReal ((J : ℝ) + ε) * (ENNReal.ofReal α ^ (k + N) * ((k + N + 1 : ℕ) : ℝ≥0∞)) := by
                      ring
          _ ≤ ∑' m : ℕ, ENNReal.ofReal ((J : ℝ) + ε) * (ENNReal.ofReal α ^ m * ((m + 1 : ℕ) : ℝ≥0∞)) := by
              conv_rhs => rw [← ennr_sum_add_tsum_nat_add N]
              exact le_add_self
    calc ENNReal.ofReal (1 - α) ^ 2 *
          ((∑' m : ℕ, ENNReal.ofReal α ^ m * ∑ t ∈ Finset.range (m + 1), c t) +
            ∑ m ∈ S_bad, ENNReal.ofReal α ^ m * (ENNReal.ofReal (δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞)))
        ≤ ENNReal.ofReal (1 - α) ^ 2 *
            (C + ENNReal.ofReal ((J : ℝ) + ε) * ∑' m : ℕ, ENNReal.ofReal α ^ m * ((m + 1 : ℕ) : ℝ≥0∞)) := by
          gcongr
      _ = ENNReal.ofReal (1 - α) ^ 2 * C +
            ENNReal.ofReal ((J : ℝ) + ε) *
              (ENNReal.ofReal (1 - α) ^ 2 * ∑' m : ℕ, ENNReal.ofReal α ^ m * ((m + 1 : ℕ) : ℝ≥0∞)) := by
          rw [mul_add]; congr 1; ring
      _ = ENNReal.ofReal (1 - α) ^ 2 * C + ENNReal.ofReal ((J : ℝ) + ε) := by
          rw [tsum_geom_mul_succ α hα_mem.1.le hα_mem.2, mul_one]
  -- Lower bound the S_bad sum
  have hbad_lower : ENNReal.ofReal ((δ / 2) * c_const) ≤
      ENNReal.ofReal (1 - α) ^ 2 *
        ∑ m ∈ S_bad, ENNReal.ofReal α ^ m * (ENNReal.ofReal (δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞)) := by
    have hcard : (1 - r) * n / 2 ≤ (S_bad.card : ℝ) := by
      rw [Nat.card_Ico]
      have hK_lt : (K : ℝ) < r * n + 1 := Nat.ceil_lt_add_one (by positivity)
      have hKn : K ≤ n := by
        have : (K : ℝ) < n := by linarith
        exact_mod_cast this.le
      rw [Nat.cast_sub hKn]
      linarith
    have hterm : ∀ m ∈ S_bad,
        ENNReal.ofReal (Real.exp (-2) * (δ / 2) * (r * n)) ≤
          ENNReal.ofReal α ^ m * (ENNReal.ofReal (δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞)) := by
      intro m hm
      have hmK : K ≤ m := (Finset.mem_Ico.mp hm).1
      have hmn : m < n := (Finset.mem_Ico.mp hm).2
      have hαm : Real.exp (-2) ≤ α ^ m := by
        calc Real.exp (-2) ≤ α ^ n := one_sub_inv_pow_ge_exp_neg_two (by omega)
          _ ≤ α ^ m := pow_le_pow_of_le_one hα_mem.1.le hα_mem.2.le hmn.le
      have hm1 : r * n ≤ ((m + 1 : ℕ) : ℝ) := by
        have : r * n ≤ K := Nat.le_ceil _
        have : (K : ℝ) ≤ m := Nat.cast_le.mpr hmK
        push_cast; linarith
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Real.exp_pos _).le]
      rw [mul_assoc, ← ENNReal.ofReal_pow hα_mem.1.le, ← ENNReal.ofReal_natCast]
      gcongr
    calc ENNReal.ofReal ((δ / 2) * c_const)
        = ENNReal.ofReal ((n : ℝ)⁻¹ ^ 2 * (((1 - r) * n / 2) * (Real.exp (-2) * (δ / 2) * (r * n)))) := by
          congr 1; simp only [c_const]; field_simp
      _ ≤ ENNReal.ofReal ((n : ℝ)⁻¹ ^ 2 * ((S_bad.card : ℝ) * (Real.exp (-2) * (δ / 2) * (r * n)))) := by
          apply ENNReal.ofReal_le_ofReal
          gcongr
      _ = ENNReal.ofReal (1 - α) ^ 2 *
            (S_bad.card * ENNReal.ofReal (Real.exp (-2) * (δ / 2) * (r * n))) := by
          rw [h1α, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ENNReal.ofReal_pow (inv_nonneg.mpr hn_pos.le), ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal (1 - α) ^ 2 *
            ∑ _m ∈ S_bad, ENNReal.ofReal (Real.exp (-2) * (δ / 2) * (r * n)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (1 - α) ^ 2 *
            ∑ m ∈ S_bad, ENNReal.ofReal α ^ m * (ENNReal.ofReal (δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞)) := by
          gcongr with m hm
          exact hterm m hm
  -- Upper bound (1 - α)^2 * C ≤ ε
  have hC_bound : ENNReal.ofReal (1 - α) ^ 2 * C ≤ ENNReal.ofReal ε := by
    rw [h1α, ← ENNReal.ofReal_toReal hC_ne_top, ← ENNReal.ofReal_pow (inv_nonneg.mpr hn_pos.le),
        ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : Nat.ceil (Real.sqrt (C.toReal / ε)) + 1 ≤ n :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnM
    have h2 : Real.sqrt (C.toReal / ε) ≤ n :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : Nat.ceil (Real.sqrt (C.toReal / ε)) ≤ n))
    have h3 : C.toReal / ε ≤ (n : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
      rwa [Real.sq_sqrt (div_nonneg ENNReal.toReal_nonneg hε_pos.le)] at this
    have h4 : C.toReal ≤ ε * (n : ℝ) ^ 2 := by linarith [(div_le_iff₀ hε_pos).mp h3]
    rw [inv_pow]
    exact (inv_mul_le_iff₀ (sq_pos_of_pos hn_pos)).mpr (by linarith)
  -- Combine for contradiction: J - ε + (δ/2)*c_const < J + 2ε, i.e. 4ε < 3ε
  have hcontra : ENNReal.ofReal ((J : ℝ) - ε) + ENNReal.ofReal ((δ / 2) * c_const) <
      ENNReal.ofReal ε + ENNReal.ofReal ((J : ℝ) + ε) := by
    calc ENNReal.ofReal ((J : ℝ) - ε) + ENNReal.ofReal ((δ / 2) * c_const)
        < ENNReal.ofReal (1 - α) * ∑' t : ℕ, ENNReal.ofReal α ^ t * c t +
            ENNReal.ofReal (1 - α) ^ 2 *
              ∑ m ∈ S_bad, ENNReal.ofReal α ^ m * (ENNReal.ofReal (δ / 2) * ((m + 1 : ℕ) : ℝ≥0∞)) :=
          ENNReal.add_lt_add_of_lt_of_le ENNReal.ofReal_ne_top hα_inf hbad_lower
      _ ≤ ENNReal.ofReal (1 - α) ^ 2 * C + ENNReal.ofReal ((J : ℝ) + ε) := hmain_sum
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ((J : ℝ) + ε) := by gcongr
  rw [← ENNReal.ofReal_add (by linarith) (by positivity),
      ← ENNReal.ofReal_add hε_pos.le (by linarith [J.coe_nonneg])] at hcontra
  have hreal := (ENNReal.ofReal_lt_ofReal_iff (by linarith [J.coe_nonneg])).mp hcontra
  have hpos_dc : 0 < δ / 2 * c_const := by positivity
  simp only [ε] at hreal
  linarith

/-! ### Section 2: Bellman inequality `inf' doeQ ≤ discValue` and stationary Markov identities -/

section MDC
open Classical
variable {S : Type} [Countable S] {Act : Type}

/-- The policy obtained by conditioning `θ` on initial state `i` and initial action `a0`. -/
def shiftPolicy (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M)
    (i : S) (a0 : Act) : SennottDP.Discounted.Policy M where
  dist t s as a := θ.dist (t + 1) (Fin.cons i s) (Fin.cons a0 as) a
  dist_supp t s as a ha := by
    apply θ.dist_supp
    simpa [Fin.cons_last] using ha
  dist_sum t s as := by
    simpa [Fin.cons_last] using θ.dist_sum (t + 1) (Fin.cons i s) (Fin.cons a0 as)

lemma fin_tail_init {α : Type*} {n : ℕ} (f : Fin (n + 2) → α) :
    Fin.tail (Fin.init f) = Fin.init (Fin.tail f) := by
  ext k; rfl

open Classical in
lemma histProb_succ_peel (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M)
    (i : S) : ∀ (t : ℕ) (s : Fin (t + 2) → S) (as : Fin (t + 1) → Act),
    SennottDP.Discounted.histProb M θ i (t + 1) s as =
      (if s 0 = i then 1 else 0) *
        θ.dist 0 (fun _ => i) Fin.elim0 (as 0) *
        M.P i (as 0) (s 1) *
        SennottDP.Discounted.histProb M (shiftPolicy M θ i (as 0)) (s 1) t (Fin.tail s) (Fin.tail as)
  | 0, s, as => by
      simp only [SennottDP.Discounted.histProb]
      by_cases h0 : s 0 = i
      · have hinit_s : Fin.init s = fun _ => i := by
          ext k; fin_cases k; simpa [Fin.init] using h0
        have hinit_as : Fin.init as = Fin.elim0 := Subsingleton.elim _ _
        have htail_s : Fin.tail s 0 = s 1 := rfl
        simp [h0, hinit_s, hinit_as, htail_s]
      · have hinit0 : Fin.init s 0 = s 0 := rfl
        simp [h0, hinit0]
  | t + 1, s, as => by
      conv_lhs => unfold SennottDP.Discounted.histProb
      conv_rhs => unfold SennottDP.Discounted.histProb
      rw [histProb_succ_peel M θ i t (Fin.init s) (Fin.init as)]
      by_cases h0 : s 0 = i
      · have hinit0 : Fin.init s 0 = i := h0
        have hinit_as0 : Fin.init as 0 = as 0 := rfl
        have hinit1 : Fin.init s 1 = s 1 := rfl
        have hcons_s : Fin.cons i (Fin.init (Fin.tail s)) = Fin.init s := by
          rw [← fin_tail_init, ← h0]; exact Fin.cons_self_tail (Fin.init s)
        have hcons_as : Fin.cons (as 0) (Fin.init (Fin.tail as)) = Fin.init as := by
          rw [← fin_tail_init, ← hinit_as0]; exact Fin.cons_self_tail (Fin.init as)
        have hshift_dist :
            (shiftPolicy M θ i (as 0)).dist t (Fin.init (Fin.tail s)) (Fin.init (Fin.tail as))
              (Fin.tail as (Fin.last t)) =
            θ.dist (t + 1) (Fin.init s) (Fin.init as) (as (Fin.last (t + 1))) := by
          simp only [shiftPolicy, hcons_s, hcons_as]
          rfl
        have hP_eq :
            M.P (Fin.tail s (Fin.castSucc (Fin.last t))) (Fin.tail as (Fin.last t))
              (Fin.tail s (Fin.last (t + 1))) =
            M.P (s (Fin.castSucc (Fin.last (t + 1)))) (as (Fin.last (t + 1)))
              (s (Fin.last (t + 2))) := rfl
        rw [hinit0, hinit_as0, hinit1, fin_tail_init, fin_tail_init, hshift_dist, hP_eq]
        simp only [h0, ↓reduceIte, one_mul]
        ring
      · have hinit0 : Fin.init s 0 = s 0 := rfl
        simp [h0, hinit0]

lemma expCost_zero_eq (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M) (i : S) :
    SennottDP.Discounted.expCost M θ i 0 =
      ∑ a ∈ M.A i, θ.dist 0 (fun _ => i) Fin.elim0 a * (M.C i a : ℝ≥0∞) := by
  unfold SennottDP.Discounted.expCost
  rw [tsum_eq_single (fun _ : Fin 1 => i)]
  · rw [tsum_eq_single (Fin.elim0 : Fin 0 → Act)]
    · simp [SennottDP.Discounted.histProb]
    · intro as has; exact (has (Subsingleton.elim _ _)).elim
  · intro s hs
    have h0 : s 0 ≠ i := by
      intro h; apply hs; ext k; fin_cases k; exact h
    simp [SennottDP.Discounted.histProb, h0]

lemma histProb_eq_zero_of_ne (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M)
    (j : S) : ∀ (t : ℕ) (s : Fin (t + 1) → S) (as : Fin t → Act),
    s 0 ≠ j → SennottDP.Discounted.histProb M θ j t s as = 0
  | 0, s, _, hne => by simp [SennottDP.Discounted.histProb, hne]
  | k + 1, s, as, hne => by
      simp only [SennottDP.Discounted.histProb]
      rw [histProb_eq_zero_of_ne M θ j k (Fin.init s) (Fin.init as) hne]
      simp

lemma expCost_succ_eq (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M)
    (i : S) (t : ℕ) :
    SennottDP.Discounted.expCost M θ i (t + 1) =
      ∑ a ∈ M.A i, θ.dist 0 (fun _ => i) Fin.elim0 a *
        ∑' j : S, M.P i a j * SennottDP.Discounted.expCost M (shiftPolicy M θ i a) j t := by
  unfold SennottDP.Discounted.expCost
  -- Reindex s via Fin.consEquiv and as via Fin.consEquiv
  let es : (S × (Fin (t + 1) → S)) ≃ (Fin (t + 2) → S) :=
    Fin.consEquiv (fun _ : Fin (t + 2) => S)
  let ea : (Act × (Fin t → Act)) ≃ (Fin (t + 1) → Act) :=
    Fin.consEquiv (fun _ : Fin (t + 1) => Act)
  rw [← es.tsum_eq]
  simp_rw [← ea.tsum_eq]
  rw [ENNReal.tsum_prod']
  rw [tsum_eq_single i]
  · simp_rw [ENNReal.tsum_prod']
    rw [ENNReal.tsum_comm]
    rw [tsum_eq_sum (s := M.A i)]
    · apply Finset.sum_congr rfl
      intro a _
      have hpeel : ∀ (s' : Fin (t + 1) → S) (as' : Fin t → Act),
          SennottDP.Discounted.histProb M θ i (t + 1) (es (i, s')) (ea (a, as')) =
            θ.dist 0 (fun _ => i) Fin.elim0 a * M.P i a (s' 0) *
              SennottDP.Discounted.histProb M (shiftPolicy M θ i a) (s' 0) t s' as' := by
        intro s' as'
        rw [histProb_succ_peel]
        simp [es, ea, Fin.consEquiv]
      simp_rw [hpeel]
      have hlast : ∀ s' : Fin (t + 1) → S, es (i, s') (Fin.last (t + 1)) = s' (Fin.last t) := by
        intro s'; simp [es, Fin.consEquiv]
      simp_rw [hlast]
      have hdist : ∀ (s' : Fin (t + 1) → S) (as' : Fin t → Act) (b : Act),
          θ.dist (t + 1) (es (i, s')) (ea (a, as')) b =
            (shiftPolicy M θ i a).dist t s' as' b := by
        intro s' as' b; rfl
      simp_rw [hdist]
      -- Now match ∑' s', ∑' as', θ0 * P i a (s' 0) * histProb (s' 0) * cost
      -- with θ0 * ∑' j, P i a j * ∑' s', ∑' as', histProb j * cost
      have hfactor : ∀ (s' : Fin (t + 1) → S),
          ∑' as' : Fin t → Act,
            (θ.dist 0 (fun _ => i) Fin.elim0 a * M.P i a (s' 0) *
              SennottDP.Discounted.histProb M (shiftPolicy M θ i a) (s' 0) t s' as') *
            ∑ b ∈ M.A (s' (Fin.last t)), (shiftPolicy M θ i a).dist t s' as' b * (M.C (s' (Fin.last t)) b : ℝ≥0∞) =
          θ.dist 0 (fun _ => i) Fin.elim0 a * (M.P i a (s' 0) *
            ∑' as' : Fin t → Act,
              SennottDP.Discounted.histProb M (shiftPolicy M θ i a) (s' 0) t s' as' *
              ∑ b ∈ M.A (s' (Fin.last t)), (shiftPolicy M θ i a).dist t s' as' b * (M.C (s' (Fin.last t)) b : ℝ≥0∞)) := by
        intro s'
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        congr 1; ext as'; ring
      simp_rw [hfactor]
      rw [ENNReal.tsum_mul_left]
      congr 1
      -- Show ∑' s', P i a (s' 0) * F (s' 0) s' = ∑' j, P i a j * ∑' s', F j s'
      -- using the fact that histProb M _ j t s' as' = 0 when s' 0 ≠ j!
      calc ∑' s' : Fin (t + 1) → S, M.P i a (s' 0) *
              ∑' as' : Fin t → Act,
                SennottDP.Discounted.histProb M (shiftPolicy M θ i a) (s' 0) t s' as' *
                ∑ b ∈ M.A (s' (Fin.last t)), (shiftPolicy M θ i a).dist t s' as' b * (M.C (s' (Fin.last t)) b : ℝ≥0∞)
          = ∑' s' : Fin (t + 1) → S, ∑' j : S, if s' 0 = j then M.P i a j *
              ∑' as' : Fin t → Act,
                SennottDP.Discounted.histProb M (shiftPolicy M θ i a) j t s' as' *
                ∑ b ∈ M.A (s' (Fin.last t)), (shiftPolicy M θ i a).dist t s' as' b * (M.C (s' (Fin.last t)) b : ℝ≥0∞) else 0 := by
              congr 1; ext s'
              rw [tsum_eq_single (s' 0)]
              · simp
              · intro j hj; simp [hj.symm]
        _ = ∑' j : S, ∑' s' : Fin (t + 1) → S, if s' 0 = j then M.P i a j *
              ∑' as' : Fin t → Act,
                SennottDP.Discounted.histProb M (shiftPolicy M θ i a) j t s' as' *
                ∑ b ∈ M.A (s' (Fin.last t)), (shiftPolicy M θ i a).dist t s' as' b * (M.C (s' (Fin.last t)) b : ℝ≥0∞) else 0 :=
              ENNReal.tsum_comm
        _ = ∑' j : S, M.P i a j * ∑' s' : Fin (t + 1) → S, ∑' as' : Fin t → Act,
              SennottDP.Discounted.histProb M (shiftPolicy M θ i a) j t s' as' *
              ∑ b ∈ M.A (s' (Fin.last t)), (shiftPolicy M θ i a).dist t s' as' b * (M.C (s' (Fin.last t)) b : ℝ≥0∞) := by
              congr 1; ext j
              rw [← ENNReal.tsum_mul_left]
              congr 1; ext s'
              by_cases h : s' 0 = j
              · simp [h]
              · simp only [h, ↓reduceIte]
                symm; apply mul_eq_zero_of_right
                apply ENNReal.tsum_eq_zero.mpr; intro as'
                rw [histProb_eq_zero_of_ne M (shiftPolicy M θ i a) j t s' as' h, zero_mul]
    · intro a ha
      apply ENNReal.tsum_eq_zero.mpr; intro s'
      apply ENNReal.tsum_eq_zero.mpr; intro as'
      rw [histProb_succ_peel]
      have hdist0 : θ.dist 0 (fun _ => i) Fin.elim0 a = 0 := θ.dist_supp 0 (fun _ => i) Fin.elim0 a ha
      simp [es, ea, Fin.consEquiv, hdist0]
  · intro j hj
    apply ENNReal.tsum_eq_zero.mpr; intro s'
    apply ENNReal.tsum_eq_zero.mpr; intro as
    rw [histProb_succ_peel]
    simp [es, Fin.consEquiv, hj]

lemma ennreal_tsum_finset_sum {α ι : Type*} (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    ∑' a : α, ∑ i ∈ s, f i a = ∑ i ∈ s, ∑' a : α, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp_rw [Finset.sum_insert hi]
      rw [ENNReal.tsum_add, ih]

lemma inf'_doeQ_le_discValue (M : SennottDP.Discounted.MDC S Act) (α : ℝ) (i : S) :
    (M.A i).inf' (M.A_nonempty i) (doeQ M α i) ≤ discValue M α i := by
  refine le_iInf fun θ => ?_
  unfold discCost
  rw [← ennr_sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one, pow_zero, one_mul, expCost_zero_eq]
  simp_rw [pow_succ', mul_assoc, ENNReal.tsum_mul_left, expCost_succ_eq]
  have h1 : ∀ a ∈ M.A i,
      θ.dist 0 (fun _ => i) Fin.elim0 a * (M.C i a : ℝ≥0∞) +
        ENNReal.ofReal α *
          ∑' t : ℕ, ENNReal.ofReal α ^ t *
            (θ.dist 0 (fun _ => i) Fin.elim0 a *
              ∑' j : S, M.P i a j * SennottDP.Discounted.expCost M (shiftPolicy M θ i a) j t) =
      θ.dist 0 (fun _ => i) Fin.elim0 a *
        ((M.C i a : ℝ≥0∞) + ENNReal.ofReal α * ∑' j : S, M.P i a j * discCost M (shiftPolicy M θ i a) α j) := by
    intro a _
    have hinner :
        ∑' t : ℕ, ENNReal.ofReal α ^ t *
          (θ.dist 0 (fun _ => i) Fin.elim0 a *
            ∑' j : S, M.P i a j * SennottDP.Discounted.expCost M (shiftPolicy M θ i a) j t) =
        θ.dist 0 (fun _ => i) Fin.elim0 a *
          ∑' j : S, M.P i a j * discCost M (shiftPolicy M θ i a) α j := by
      calc ∑' t : ℕ, ENNReal.ofReal α ^ t *
              (θ.dist 0 (fun _ => i) Fin.elim0 a *
                ∑' j : S, M.P i a j * SennottDP.Discounted.expCost M (shiftPolicy M θ i a) j t)
          = ∑' t : ℕ, θ.dist 0 (fun _ => i) Fin.elim0 a *
              ∑' j : S, M.P i a j * (ENNReal.ofReal α ^ t * SennottDP.Discounted.expCost M (shiftPolicy M θ i a) j t) := by
              congr 1; ext t
              rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
              congr 1; ext j; ring
        _ = θ.dist 0 (fun _ => i) Fin.elim0 a *
              ∑' t : ℕ, ∑' j : S, M.P i a j *
                (ENNReal.ofReal α ^ t * SennottDP.Discounted.expCost M (shiftPolicy M θ i a) j t) := by
              rw [ENNReal.tsum_mul_left]
        _ = θ.dist 0 (fun _ => i) Fin.elim0 a *
              ∑' j : S, ∑' t : ℕ, M.P i a j *
                (ENNReal.ofReal α ^ t * SennottDP.Discounted.expCost M (shiftPolicy M θ i a) j t) := by
              rw [ENNReal.tsum_comm]
        _ = θ.dist 0 (fun _ => i) Fin.elim0 a *
              ∑' j : S, M.P i a j * discCost M (shiftPolicy M θ i a) α j := by
              congr 1; congr 1; ext j; rw [ENNReal.tsum_mul_left]; rfl
    rw [hinner]
    ring
  calc (M.A i).inf' (M.A_nonempty i) (doeQ M α i)
      = (∑ a ∈ M.A i, θ.dist 0 (fun _ => i) Fin.elim0 a) *
          (M.A i).inf' (M.A_nonempty i) (doeQ M α i) := by
          rw [θ.dist_sum 0 (fun _ => i) Fin.elim0, one_mul]
    _ = ∑ a ∈ M.A i, θ.dist 0 (fun _ => i) Fin.elim0 a *
          (M.A i).inf' (M.A_nonempty i) (doeQ M α i) := Finset.sum_mul _ _ _
    _ ≤ ∑ a ∈ M.A i, θ.dist 0 (fun _ => i) Fin.elim0 a * doeQ M α i a := by
          gcongr with a ha
          exact Finset.inf'_le (doeQ M α i) ha
    _ ≤ ∑ a ∈ M.A i, θ.dist 0 (fun _ => i) Fin.elim0 a *
          ((M.C i a : ℝ≥0∞) + ENNReal.ofReal α * ∑' j : S, M.P i a j * discCost M (shiftPolicy M θ i a) α j) := by
          gcongr with a _
          unfold doeQ
          gcongr with j
          exact iInf_le (fun ψ => discCost M ψ α j) (shiftPolicy M θ i a)
    _ = ∑ a ∈ M.A i, (θ.dist 0 (fun _ => i) Fin.elim0 a * (M.C i a : ℝ≥0∞) +
          ENNReal.ofReal α *
            (∑' t : ℕ, ENNReal.ofReal α ^ t *
              (θ.dist 0 (fun _ => i) Fin.elim0 a *
                ∑' j : S, M.P i a j * SennottDP.Discounted.expCost M (shiftPolicy M θ i a) j t))) := by
          exact Finset.sum_congr rfl (fun a ha => (h1 a ha).symm)
    _ = (∑ a ∈ M.A i, θ.dist 0 (fun _ => i) Fin.elim0 a * (M.C i a : ℝ≥0∞)) +
          ENNReal.ofReal α * ∑' t : ℕ, ENNReal.ofReal α ^ t *
            ∑ a ∈ M.A i, θ.dist 0 (fun _ => i) Fin.elim0 a *
              ∑' j : S, M.P i a j * SennottDP.Discounted.expCost M (shiftPolicy M θ i a) j t := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 2
          simp_rw [Finset.mul_sum]
          rw [ennreal_tsum_finset_sum]

/-! Stationary policy Markov identities -/

open Classical in
lemma stateProb_zero (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M)
    (i j : S) : stateProb M θ i 0 j = if j = i then 1 else 0 := by
  unfold stateProb
  rw [tsum_eq_single (fun _ : Fin 1 => i)]
  · rw [tsum_eq_single (Fin.elim0 : Fin 0 → Act)]
    · by_cases h : j = i
      · simp [h, SennottDP.Discounted.histProb]
      · have h' : i ≠ j := Ne.symm h
        simp [h, h']
    · intro as has; exact (has (Subsingleton.elim _ _)).elim
  · intro s hs
    have h0 : s 0 ≠ i := by
      intro h; apply hs; ext k; fin_cases k; exact h
    simp [SennottDP.Discounted.histProb, h0]

lemma stateProb_succ_stationary (M : SennottDP.Discounted.MDC S Act) (e : StationaryPolicy M)
    (i : S) (n : ℕ) (k : S) :
    stateProb M e.toPolicy i (n + 1) k =
      ∑' j : S, stateProb M e.toPolicy i n j * M.P j (e.1 j) k := by
  unfold stateProb
  let es : ((Fin (n + 1) → S) × S) ≃ (Fin (n + 2) → S) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun s => (Fin.init s, s (Fin.last (n + 1)))
      left_inv := fun ⟨s', x⟩ => by ext m; simp [Fin.init_snoc]; simp [Fin.snoc_last]
      right_inv := fun s => Fin.snoc_init_self s }
  let ea : ((Fin n → Act) × Act) ≃ (Fin (n + 1) → Act) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun as => (Fin.init as, as (Fin.last n))
      left_inv := fun ⟨as', a⟩ => by ext m; simp [Fin.init_snoc]; simp [Fin.snoc_last]
      right_inv := fun as => Fin.snoc_init_self as }
  rw [← es.tsum_eq]
  simp_rw [← ea.tsum_eq, ENNReal.tsum_prod']
  -- Evaluate the inner sum over x : S (collapses to k) and a : Act (collapses to e.1 (s' (last n)))
  have hinner : ∀ s' : Fin (n + 1) → S,
      ∑' x : S, ∑' as' : Fin n → Act, ∑' a : Act,
        (if es (s', x) (Fin.last (n + 1)) = k then
          SennottDP.Discounted.histProb M e.toPolicy i (n + 1) (es (s', x)) (ea (as', a)) else 0) =
      (∑' as' : Fin n → Act, SennottDP.Discounted.histProb M e.toPolicy i n s' as') *
        M.P (s' (Fin.last n)) (e.1 (s' (Fin.last n))) k := by
    intro s'
    rw [tsum_eq_single k]
    · simp only [es, Equiv.coe_fn_mk, Fin.snoc_last, ↓reduceIte]
      rw [← ENNReal.tsum_mul_right]
      congr 1; ext as'
      rw [tsum_eq_single (e.1 (s' (Fin.last n)))]
      · simp only [SennottDP.Discounted.histProb, ea, Equiv.coe_fn_mk, Fin.init_snoc, Fin.snoc_last,
          Fin.snoc_castSucc, StationaryPolicy.toPolicy, ↓reduceIte, mul_one]
      · intro a ha
        simp only [SennottDP.Discounted.histProb, ea, Equiv.coe_fn_mk, Fin.init_snoc, Fin.snoc_last,
          StationaryPolicy.toPolicy, if_neg ha, mul_zero, zero_mul]
    · intro x hx
      simp [es, Fin.snoc_last, hx]
  simp_rw [hinner]
  -- Group by j = s' (Fin.last n)
  calc ∑' s' : Fin (n + 1) → S,
          (∑' as' : Fin n → Act, SennottDP.Discounted.histProb M e.toPolicy i n s' as') *
            M.P (s' (Fin.last n)) (e.1 (s' (Fin.last n))) k
      = ∑' s' : Fin (n + 1) → S, ∑' j : S,
          (if s' (Fin.last n) = j then
            (∑' as' : Fin n → Act, SennottDP.Discounted.histProb M e.toPolicy i n s' as') *
              M.P j (e.1 j) k else 0) := by
          congr 1; ext s'
          rw [tsum_eq_single (s' (Fin.last n))]
          · simp
          · intro j hj; simp [hj.symm]
    _ = ∑' j : S, ∑' s' : Fin (n + 1) → S,
          (if s' (Fin.last n) = j then
            (∑' as' : Fin n → Act, SennottDP.Discounted.histProb M e.toPolicy i n s' as') *
              M.P j (e.1 j) k else 0) := ENNReal.tsum_comm
    _ = ∑' j : S, (∑' s' : Fin (n + 1) → S, ∑' as' : Fin n → Act,
          if s' (Fin.last n) = j then SennottDP.Discounted.histProb M e.toPolicy i n s' as' else 0) *
          M.P j (e.1 j) k := by
          congr 1; ext j
          rw [← ENNReal.tsum_mul_right]
          congr 1; ext s'
          by_cases h : s' (Fin.last n) = j
          · simp [h]
          · simp [h]

lemma tsum_stateProb_stationary (M : SennottDP.Discounted.MDC S Act) (e : StationaryPolicy M)
    (i : S) : ∀ n : ℕ, ∑' j : S, stateProb M e.toPolicy i n j = 1
  | 0 => by
      simp_rw [stateProb_zero]
      rw [tsum_eq_single i]
      · simp
      · intro j hj; simp [hj]
  | n + 1 => by
      simp_rw [stateProb_succ_stationary]
      rw [ENNReal.tsum_comm]
      calc ∑' j : S, ∑' k : S, stateProb M e.toPolicy i n j * M.P j (e.1 j) k
          = ∑' j : S, stateProb M e.toPolicy i n j * ∑' k : S, M.P j (e.1 j) k := by
              congr 1; ext j; rw [ENNReal.tsum_mul_left]
        _ = ∑' j : S, stateProb M e.toPolicy i n j * 1 := by
              congr 1; ext j; rw [M.P_sum j (e.1 j) (e.2 j)]
        _ = 1 := by simp [tsum_stateProb_stationary M e i n]

lemma expCost_stationary (M : SennottDP.Discounted.MDC S Act) (e : StationaryPolicy M)
    (i : S) (n : ℕ) :
    SennottDP.Discounted.expCost M e.toPolicy i n =
      ∑' j : S, stateProb M e.toPolicy i n j * (M.C j (e.1 j) : ℝ≥0∞) := by
  unfold SennottDP.Discounted.expCost stateProb
  have hsum_a : ∀ (s : Fin (n + 1) → S) (as : Fin n → Act),
      ∑ a ∈ M.A (s (Fin.last n)), e.toPolicy.dist n s as a * (M.C (s (Fin.last n)) a : ℝ≥0∞) =
        (M.C (s (Fin.last n)) (e.1 (s (Fin.last n))) : ℝ≥0∞) := by
    intro s as
    simp [StationaryPolicy.toPolicy, e.2 (s (Fin.last n))]
  simp_rw [hsum_a]
  calc ∑' s : Fin (n + 1) → S, ∑' as : Fin n → Act,
          SennottDP.Discounted.histProb M e.toPolicy i n s as *
            (M.C (s (Fin.last n)) (e.1 (s (Fin.last n))) : ℝ≥0∞)
      = ∑' s : Fin (n + 1) → S, ∑' j : S,
          if s (Fin.last n) = j then
            (∑' as : Fin n → Act, SennottDP.Discounted.histProb M e.toPolicy i n s as) *
              (M.C j (e.1 j) : ℝ≥0∞) else 0 := by
          congr 1; ext s
          rw [tsum_eq_single (s (Fin.last n))]
          · simp [ENNReal.tsum_mul_right]
          · intro j hj; simp [hj.symm]
    _ = ∑' j : S, ∑' s : Fin (n + 1) → S,
          if s (Fin.last n) = j then
            (∑' as : Fin n → Act, SennottDP.Discounted.histProb M e.toPolicy i n s as) *
              (M.C j (e.1 j) : ℝ≥0∞) else 0 := ENNReal.tsum_comm
    _ = ∑' j : S, (∑' s : Fin (n + 1) → S, ∑' as : Fin n → Act,
          if s (Fin.last n) = j then SennottDP.Discounted.histProb M e.toPolicy i n s as else 0) *
          (M.C j (e.1 j) : ℝ≥0∞) := by
          congr 1; ext j
          rw [← ENNReal.tsum_mul_right]
          congr 1; ext s
          by_cases h : s (Fin.last n) = j
          · simp [h]
          · simp [h]

/-! ### Section 3: Basic `(H)` consequences and Fatou-ACOI step -/

lemma ereal_coe_ennreal_eq_toReal {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    (x : EReal) = ((x.toReal : ℝ) : EReal) := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hx]
  rw [EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg]

lemma discValue_z_ne_top_of_SEN1 {M : SennottDP.Discounted.MDC S Act} {z : S}
    (h1 : SEN1 M z) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    discValue M α z ≠ ⊤ := by
  obtain ⟨B, hB⟩ := h1
  intro htop
  have hle := hB α hα
  rw [htop] at hle
  have hpos : ENNReal.ofReal (1 - α) ≠ 0 := (ENNReal.ofReal_pos.mpr (sub_pos.mpr hα.2)).ne'
  rw [ENNReal.mul_top hpos] at hle
  exact not_le_of_gt ENNReal.coe_lt_top hle

lemma discValue_ne_top_of_H {M : SennottDP.Discounted.MDC S Act} {z : S} {Mf : S → ℝ}
    (h1 : SEN1 M z) (h2 : SEN2 M z Mf) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) (i : S) :
    discValue M α i ≠ ⊤ := by
  have hz : discValue M α z ≠ ⊤ := discValue_z_ne_top_of_SEN1 h1 hα
  intro htop
  have hle := h2.2 α hα i
  unfold hRel at hle
  rw [htop, ereal_coe_ennreal_eq_toReal hz, EReal.coe_ennreal_top, EReal.top_sub_coe] at hle
  exact not_le_of_gt (EReal.coe_lt_top _) hle

lemma hRel_eq_coe_sub {M : SennottDP.Discounted.MDC S Act} {z : S} {α : ℝ} {i : S}
    (hi : discValue M α i ≠ ⊤) (hz : discValue M α z ≠ ⊤) :
    hRel M z α i = (((discValue M α i).toReal - (discValue M α z).toReal : ℝ) : EReal) := by
  unfold hRel
  rw [ereal_coe_ennreal_eq_toReal hi, ereal_coe_ennreal_eq_toReal hz, EReal.coe_sub]

lemma hRel_toReal_bounds {M : SennottDP.Discounted.MDC S Act} {z : S} {Mf Lf : S → ℝ}
    (h1 : SEN1 M z) (h2 : SEN2 M z Mf) (h3 : H3 M z Lf)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) (i : S) :
    -Lf i ≤ (discValue M α i).toReal - (discValue M α z).toReal ∧
      (discValue M α i).toReal - (discValue M α z).toReal ≤ Mf i := by
  have hi := discValue_ne_top_of_H h1 h2 hα i
  have hz := discValue_z_ne_top_of_SEN1 h1 hα
  have heq := hRel_eq_coe_sub hi hz
  have hlo := h3.2 α hα i
  have hhi := h2.2 α hα i
  rw [heq] at hlo hhi
  exact ⟨EReal.coe_le_coe_iff.mp hlo, EReal.coe_le_coe_iff.mp hhi⟩

lemma tendsto_discValue_of_tendsto_z {M : SennottDP.Discounted.MDC S Act} {z : S} {Mf Lf : S → ℝ}
    (h1 : SEN1 M z) (h2 : SEN2 M z Mf) (h3 : H3 M z Lf) {J : ℝ≥0}
    (hz_lim : Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * discValue M α z) (𝓝[<] 1) (𝓝 (J : ℝ≥0∞)))
    (i : S) :
    Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * discValue M α i) (𝓝[<] 1) (𝓝 (J : ℝ≥0∞)) := by
  have hz_real : Tendsto (fun α : ℝ => (1 - α) * (discValue M α z).toReal) (𝓝[<] 1) (𝓝 (J : ℝ)) := by
    have hto := (ENNReal.continuousAt_toReal (ENNReal.coe_ne_top (r := J))).tendsto.comp hz_lim
    refine hto.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with α hα
    simp only [Function.comp_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_pos.mpr hα.2).le]
  have hdiff_zero : Tendsto (fun α : ℝ => (1 - α) * ((discValue M α i).toReal - (discValue M α z).toReal))
      (𝓝[<] 1) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun α : ℝ => (1 - α) * max (Lf i) (Mf i)) (𝓝[<] 1) (𝓝 0) by
      have hsub : Tendsto (fun α : ℝ => 1 - α) (𝓝[<] 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      rw [sub_self] at hsub
      simpa using hsub.mul_const (max (Lf i) (Mf i)))
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with α hα
    have hb := hRel_toReal_bounds h1 h2 h3 hα i
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (sub_pos.mpr hα.2)]
    apply mul_le_mul_of_nonneg_left _ (sub_pos.mpr hα.2).le
    rw [abs_le]
    constructor
    · linarith [le_max_left (Lf i) (Mf i)]
    · linarith [le_max_right (Lf i) (Mf i)]
  have hi_real : Tendsto (fun α : ℝ => (1 - α) * (discValue M α i).toReal) (𝓝[<] 1) (𝓝 (J : ℝ)) := by
    have hadd := hz_real.add hdiff_zero
    rw [add_zero] at hadd
    refine hadd.congr fun α => by ring
  have hcomp : Tendsto (ENNReal.ofReal ∘ fun α : ℝ => (1 - α) * (discValue M α i).toReal)
      (𝓝[<] 1) (𝓝 (ENNReal.ofReal (J : ℝ))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hi_real
  rw [ENNReal.ofReal_coe_nnreal] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with α hα
  have hi_nt := discValue_ne_top_of_H h1 h2 hα i
  simp only [Function.comp_def]
  rw [ENNReal.ofReal_mul (sub_pos.mpr hα.2).le, ENNReal.ofReal_toReal hi_nt]

lemma ennreal_le_liminf_add (u v : ℕ → ℝ≥0∞) :
    liminf u atTop + liminf v atTop ≤ liminf (fun n => u n + v n) atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat,
      Filter.liminf_eq_iSup_iInf_of_nat]
  rw [ENNReal.iSup_add]
  refine iSup_le fun N1 => ?_
  rw [ENNReal.add_iSup]
  refine iSup_le fun N2 => ?_
  refine le_iSup_of_le (max N1 N2) ?_
  refine le_iInf fun n => le_iInf fun hn => ?_
  exact add_le_add (iInf_le_of_le n (iInf_le _ (le_trans (le_max_left N1 N2) hn)))
    (iInf_le_of_le n (iInf_le _ (le_trans (le_max_right N1 N2) hn)))

/-- Fatou's lemma for `tsum` in `ℝ≥0∞`. -/
lemma ennreal_tsum_liminf_le {ι : Type*} (f : ℕ → ι → ℝ≥0∞) :
    ∑' j : ι, liminf (fun n => f n j) atTop ≤ liminf (fun n => ∑' j : ι, f n j) atTop := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  have hF : ∑ j ∈ F, liminf (fun n => f n j) atTop ≤ liminf (fun n => ∑ j ∈ F, f n j) atTop := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        simp_rw [Finset.sum_insert ha]
        exact le_trans (add_le_add_right ih _) (ennreal_le_liminf_add _ _)
  refine le_trans hF (liminf_le_liminf (Eventually.of_forall fun n => ?_))
  exact ENNReal.sum_le_tsum F

lemma ofReal_add_ofReal_eq_ofReal_add_ofReal_neg {x L : ℝ} (hL : 0 ≤ L) (hx : -L ≤ x) :
    ENNReal.ofReal x + ENNReal.ofReal L = ENNReal.ofReal (x + L) + ENNReal.ofReal (-x) := by
  by_cases h : 0 ≤ x
  · have hneg : ENNReal.ofReal (-x) = 0 := ENNReal.ofReal_of_nonpos (by linarith)
    rw [hneg, add_zero, ENNReal.ofReal_add h hL]
  · push Not at h
    have hpos : ENNReal.ofReal x = 0 := ENNReal.ofReal_of_nonpos h.le
    rw [hpos, zero_add, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1; ring

lemma acoi_step_of_doe_le {M : SennottDP.Discounted.MDC S Act} {z : S} {Mf Lf : S → ℝ}
    (h1 : SEN1 M z) (h2 : SEN2 M z Mf) (h3 : H3 M z Lf) (h4 : H4 M Lf)
    (βs : ℕ → ℝ) (hβ_mem : ∀ n, βs n ∈ Set.Ioo (0 : ℝ) 1) (hβ_lim : Tendsto βs atTop (𝓝 1))
    (g : ℝ≥0) (hg_lim : Tendsto (fun n => ENNReal.ofReal (1 - βs n) * discValue M (βs n) z) atTop (𝓝 (g : ℝ≥0∞)))
    (h : S → ℝ) (hh_lim : ∀ j, Tendsto (fun n => hRel M z (βs n) j) atTop (𝓝 (h j : EReal)))
    (i : S) (a : Act) (ha : a ∈ M.A i)
    (hdoe : ∀ᶠ n in atTop, doeQ M (βs n) i a ≤ discValue M (βs n) i) :
    ((M.C i a : ℝ) : EReal) + wsum (M.P i a) h ≤ (((g : ℝ) + h i : ℝ) : EReal) := by
  have hh_bounds : ∀ j, -Lf j ≤ h j ∧ h j ≤ Mf j := fun j => by
    constructor
    · exact EReal.coe_le_coe_iff.mp (ge_of_tendsto (hh_lim j) (Eventually.of_forall fun n => h3.2 (βs n) (hβ_mem n) j))
    · exact EReal.coe_le_coe_iff.mp (le_of_tendsto (hh_lim j) (Eventually.of_forall fun n => h2.2 (βs n) (hβ_mem n) j))
  have hh_real_lim : ∀ j, Tendsto (fun n => (discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal)
      atTop (𝓝 (h j)) := fun j => by
    have heq : (fun n => (((discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal : ℝ) : EReal)) =
        (fun n => hRel M z (βs n) j) := by
      ext n
      exact (hRel_eq_coe_sub (discValue_ne_top_of_H h1 h2 (hβ_mem n) j)
        (discValue_z_ne_top_of_SEN1 h1 (hβ_mem n))).symm
    have hlim' := hh_lim j
    rw [← heq] at hlim'
    exact EReal.tendsto_coe.mp hlim'
  set Lsum : ℝ≥0∞ := ∑' j, M.P i a j * ENNReal.ofReal (Lf j)
  have hLsum_ne_top : Lsum ≠ ⊤ := h4 i a ha
  -- Step 1: For eventually all n, derive the ENNReal inequality without subtraction
  have hineq_n : ∀ᶠ n in atTop,
      (M.C i a : ℝ≥0∞) +
        ENNReal.ofReal (βs n) *
          ∑' j, M.P i a j * ENNReal.ofReal (((discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal) + Lf j) +
        ENNReal.ofReal (Lf i) ≤
      ENNReal.ofReal (1 - βs n) * discValue M (βs n) z +
        ENNReal.ofReal (((discValue M (βs n) i).toReal - (discValue M (βs n) z).toReal) + Lf i) +
        ENNReal.ofReal (βs n) * Lsum := by
    filter_upwards [hdoe] with n hdoe_n
    set α := βs n
    have hα := hβ_mem n
    have hz_nt := discValue_z_ne_top_of_SEN1 h1 hα
    have hshift_eq : ∀ j, discValue M α j + ENNReal.ofReal (Lf j) =
        discValue M α z + ENNReal.ofReal (((discValue M α j).toReal - (discValue M α z).toReal) + Lf j) := by
      intro j
      have hj_nt := discValue_ne_top_of_H h1 h2 hα j
      have hbd := (hRel_toReal_bounds h1 h2 h3 hα j).1
      conv_lhs => arg 1; rw [← ENNReal.ofReal_toReal hj_nt]
      conv_rhs => arg 1; rw [← ENNReal.ofReal_toReal hz_nt]
      rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg (h3.1 j),
          ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by linarith)]
      congr 1; ring
    have htsum_eq : (∑' j, M.P i a j * discValue M α j) + Lsum =
        discValue M α z +
          ∑' j, M.P i a j * ENNReal.ofReal (((discValue M α j).toReal - (discValue M α z).toReal) + Lf j) := by
      rw [← ENNReal.tsum_add]
      calc ∑' j, (M.P i a j * discValue M α j + M.P i a j * ENNReal.ofReal (Lf j))
          = ∑' j, M.P i a j * (discValue M α j + ENNReal.ofReal (Lf j)) := by
              congr 1; ext j; ring
        _ = ∑' j, M.P i a j * (discValue M α z +
              ENNReal.ofReal (((discValue M α j).toReal - (discValue M α z).toReal) + Lf j)) := by
              congr 1; ext j; rw [hshift_eq j]
        _ = (∑' j, M.P i a j * discValue M α z) +
              ∑' j, M.P i a j * ENNReal.ofReal (((discValue M α j).toReal - (discValue M α z).toReal) + Lf j) := by
              rw [← ENNReal.tsum_add]; congr 1; ext j; ring
        _ = discValue M α z +
              ∑' j, M.P i a j * ENNReal.ofReal (((discValue M α j).toReal - (discValue M α z).toReal) + Lf j) := by
              rw [ENNReal.tsum_mul_right, M.P_sum i a ha, one_mul]
    have hsplit_z : discValue M α z =
        ENNReal.ofReal α * discValue M α z + ENNReal.ofReal (1 - α) * discValue M α z := by
      rw [← add_mul, ← ENNReal.ofReal_add hα.1.le (sub_pos.mpr hα.2).le]
      simp
    have hcancel_ne_top : ENNReal.ofReal α * discValue M α z ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hz_nt
    refine (ENNReal.add_le_add_iff_left hcancel_ne_top).mp ?_
    calc ENNReal.ofReal α * discValue M α z +
          ((M.C i a : ℝ≥0∞) +
            ENNReal.ofReal α *
              ∑' j, M.P i a j * ENNReal.ofReal (((discValue M α j).toReal - (discValue M α z).toReal) + Lf j) +
            ENNReal.ofReal (Lf i))
        = (M.C i a : ℝ≥0∞) +
            ENNReal.ofReal α * (discValue M α z +
              ∑' j, M.P i a j * ENNReal.ofReal (((discValue M α j).toReal - (discValue M α z).toReal) + Lf j)) +
            ENNReal.ofReal (Lf i) := by ring
      _ = (M.C i a : ℝ≥0∞) + ENNReal.ofReal α * ((∑' j, M.P i a j * discValue M α j) + Lsum) +
            ENNReal.ofReal (Lf i) := by rw [htsum_eq]
      _ = doeQ M α i a + ENNReal.ofReal (Lf i) + ENNReal.ofReal α * Lsum := by
            unfold doeQ; ring
      _ ≤ discValue M α i + ENNReal.ofReal (Lf i) + ENNReal.ofReal α * Lsum := by gcongr
      _ = discValue M α z +
            ENNReal.ofReal (((discValue M α i).toReal - (discValue M α z).toReal) + Lf i) +
            ENNReal.ofReal α * Lsum := by rw [hshift_eq i]
      _ = ENNReal.ofReal α * discValue M α z +
            (ENNReal.ofReal (1 - α) * discValue M α z +
              ENNReal.ofReal (((discValue M α i).toReal - (discValue M α z).toReal) + Lf i) +
              ENNReal.ofReal α * Lsum) := by
            nth_rw 1 [hsplit_z]
            ring
  -- Step 2: Take liminf on LHS (using Fatou) and limit on RHS
  have hβ_ennr : Tendsto (fun n => ENNReal.ofReal (βs n)) atTop (𝓝 1) := by
    have hcomp := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hβ_lim
    simpa [Function.comp_def] using hcomp
  have hrhs_lim : Tendsto (fun n =>
      ENNReal.ofReal (1 - βs n) * discValue M (βs n) z +
        ENNReal.ofReal (((discValue M (βs n) i).toReal - (discValue M (βs n) z).toReal) + Lf i) +
        ENNReal.ofReal (βs n) * Lsum)
      atTop (𝓝 ((g : ℝ≥0∞) + ENNReal.ofReal (h i + Lf i) + Lsum)) := by
    refine (hg_lim.add ?_).add ?_
    · have hcomp := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((hh_real_lim i).add (tendsto_const_nhds (x := Lf i)))
      simpa [Function.comp_def] using hcomp
    · simpa [one_mul] using ENNReal.Tendsto.mul_const hβ_ennr (Or.inr hLsum_ne_top)
  have hfatou : ∑' j, M.P i a j * ENNReal.ofReal (h j + Lf j) ≤
      liminf (fun n => ENNReal.ofReal (βs n) *
        ∑' j, M.P i a j * ENNReal.ofReal (((discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal) + Lf j))
        atTop := by
    calc ∑' j, M.P i a j * ENNReal.ofReal (h j + Lf j)
        = ∑' j, liminf (fun n => ENNReal.ofReal (βs n) *
            (M.P i a j * ENNReal.ofReal (((discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal) + Lf j)))
            atTop := by
            congr 1; ext j
            symm; apply Tendsto.liminf_eq
            have h1' : Tendsto (fun n => ENNReal.ofReal (((discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal) + Lf j))
                atTop (𝓝 (ENNReal.ofReal (h j + Lf j))) := by
              have hcomp := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
                ((hh_real_lim j).add (tendsto_const_nhds (x := Lf j)))
              simpa [Function.comp_def] using hcomp
            have hP_nt : M.P i a j ≠ ⊤ := by
              have hle : M.P i a j ≤ ∑' k, M.P i a k := ENNReal.le_tsum j
              rw [M.P_sum i a ha] at hle
              exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
            have h2' : Tendsto (fun n => M.P i a j * ENNReal.ofReal (((discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal) + Lf j))
                atTop (𝓝 (M.P i a j * ENNReal.ofReal (h j + Lf j))) :=
              ENNReal.Tendsto.const_mul h1' (Or.inr hP_nt)
            have h3' : Tendsto (fun n => ENNReal.ofReal (βs n) *
                (M.P i a j * ENNReal.ofReal (((discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal) + Lf j)))
                atTop (𝓝 (1 * (M.P i a j * ENNReal.ofReal (h j + Lf j)))) :=
              ENNReal.Tendsto.mul hβ_ennr (Or.inl one_ne_zero) h2' (Or.inr ENNReal.one_ne_top)
            simpa [one_mul] using h3'
      _ ≤ liminf (fun n => ∑' j, ENNReal.ofReal (βs n) *
            (M.P i a j * ENNReal.ofReal (((discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal) + Lf j)))
            atTop := ennreal_tsum_liminf_le _
      _ = liminf (fun n => ENNReal.ofReal (βs n) *
            ∑' j, M.P i a j * ENNReal.ofReal (((discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal) + Lf j))
            atTop := by
            congr 1; ext n; rw [ENNReal.tsum_mul_left]
  have hlim_ineq :
      (M.C i a : ℝ≥0∞) + (∑' j, M.P i a j * ENNReal.ofReal (h j + Lf j)) + ENNReal.ofReal (Lf i) ≤
        (g : ℝ≥0∞) + ENNReal.ofReal (h i + Lf i) + Lsum := by
    calc (M.C i a : ℝ≥0∞) + (∑' j, M.P i a j * ENNReal.ofReal (h j + Lf j)) + ENNReal.ofReal (Lf i)
        ≤ (M.C i a : ℝ≥0∞) +
            liminf (fun n => ENNReal.ofReal (βs n) *
              ∑' j, M.P i a j * ENNReal.ofReal (((discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal) + Lf j))
              atTop +
            ENNReal.ofReal (Lf i) := by gcongr
      _ ≤ liminf (fun n => (M.C i a : ℝ≥0∞) +
            ENNReal.ofReal (βs n) *
              ∑' j, M.P i a j * ENNReal.ofReal (((discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal) + Lf j) +
            ENNReal.ofReal (Lf i)) atTop := by
            have h1' : (M.C i a : ℝ≥0∞) +
                liminf (fun n => ENNReal.ofReal (βs n) *
                  ∑' j, M.P i a j * ENNReal.ofReal (((discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal) + Lf j))
                  atTop ≤
                liminf (fun n => (M.C i a : ℝ≥0∞) +
                  ENNReal.ofReal (βs n) *
                    ∑' j, M.P i a j * ENNReal.ofReal (((discValue M (βs n) j).toReal - (discValue M (βs n) z).toReal) + Lf j))
                  atTop := by
              nth_rw 1 [← liminf_const (f := (atTop : Filter ℕ)) (b := (M.C i a : ℝ≥0∞))]
              exact ennreal_le_liminf_add _ _
            refine le_trans (add_le_add_left h1' _) ?_
            nth_rw 1 [← liminf_const (f := (atTop : Filter ℕ)) (b := ENNReal.ofReal (Lf i))]
            exact ennreal_le_liminf_add _ _
      _ ≤ liminf (fun n => ENNReal.ofReal (1 - βs n) * discValue M (βs n) z +
            ENNReal.ofReal (((discValue M (βs n) i).toReal - (discValue M (βs n) z).toReal) + Lf i) +
            ENNReal.ofReal (βs n) * Lsum) atTop := liminf_le_liminf hineq_n
      _ = (g : ℝ≥0∞) + ENNReal.ofReal (h i + Lf i) + Lsum := hrhs_lim.liminf_eq
  -- Step 3: Convert to wsum in EReal
  set posSum : ℝ≥0∞ := ∑' j, M.P i a j * ENNReal.ofReal (h j)
  set negSum : ℝ≥0∞ := ∑' j, M.P i a j * ENNReal.ofReal (-h j)
  have hpos_L : posSum + Lsum = (∑' j, M.P i a j * ENNReal.ofReal (h j + Lf j)) + negSum := by
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    congr 1; ext j
    rw [← mul_add, ← mul_add, ofReal_add_ofReal_eq_ofReal_add_ofReal_neg (h3.1 j) (hh_bounds j).1]
  have hneg_ne_top : negSum ≠ ⊤ := by
    apply ne_of_lt
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hLsum_ne_top)
    apply ENNReal.tsum_le_tsum; intro j
    gcongr
    linarith [(hh_bounds j).1]
  have hrhs_ne_top : (g : ℝ≥0∞) + ENNReal.ofReal (h i + Lf i) + Lsum ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.ofReal_ne_top⟩, hLsum_ne_top⟩
  have hshift_ne_top : ∑' j, M.P i a j * ENNReal.ofReal (h j + Lf j) ≠ ⊤ := by
    intro htop
    simp [htop] at hlim_ineq
    exact hLsum_ne_top hlim_ineq
  have hpos_ne_top : posSum ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hpos_L
    exact (ENNReal.add_ne_top.mpr ⟨hshift_ne_top, hneg_ne_top⟩) hpos_L.symm
  have hreal_ineq : (M.C i a : ℝ) + (posSum.toReal - negSum.toReal) ≤ (g : ℝ) + h i := by
    have h1_r := ENNReal.toReal_mono hrhs_ne_top hlim_ineq
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, hshift_ne_top⟩) ENNReal.ofReal_ne_top,
        ENNReal.toReal_add ENNReal.coe_ne_top hshift_ne_top,
        ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.ofReal_ne_top⟩) hLsum_ne_top,
        ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.ofReal_ne_top,
        ENNReal.coe_toReal, ENNReal.coe_toReal,
        ENNReal.toReal_ofReal (h3.1 i), ENNReal.toReal_ofReal (by linarith [(hh_bounds i).1])] at h1_r
    have h2_r := congrArg ENNReal.toReal hpos_L
    rw [ENNReal.toReal_add hpos_ne_top hLsum_ne_top, ENNReal.toReal_add hshift_ne_top hneg_ne_top] at h2_r
    linarith
  unfold wsum
  rw [ereal_coe_ennreal_eq_toReal hpos_ne_top, ereal_coe_ennreal_eq_toReal hneg_ne_top,
      ← EReal.coe_sub, ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr hreal_ineq

lemma acoiMin_le_of_seq {M : SennottDP.Discounted.MDC S Act} {z : S} {Mf Lf : S → ℝ}
    (h1 : SEN1 M z) (h2 : SEN2 M z Mf) (h3 : H3 M z Lf) (h4 : H4 M Lf)
    (βs : ℕ → ℝ) (hβ_mem : ∀ n, βs n ∈ Set.Ioo (0 : ℝ) 1) (hβ_lim : Tendsto βs atTop (𝓝 1))
    (g : ℝ≥0) (hg_lim : Tendsto (fun n => ENNReal.ofReal (1 - βs n) * discValue M (βs n) z) atTop (𝓝 (g : ℝ≥0∞)))
    (h : S → ℝ) (hh_lim : ∀ j, Tendsto (fun n => hRel M z (βs n) j) atTop (𝓝 (h j : EReal)))
    (i : S) :
    acoiMin M h i ≤ (((g : ℝ) + h i : ℝ) : EReal) := by
  -- For each n, pick a_n ∈ M.A i attaining inf' doeQ ≤ discValue
  have hex : ∀ n : ℕ, ∃ a : M.A i, doeQ M (βs n) i a.1 ≤ discValue M (βs n) i := fun n => by
    obtain ⟨a, ha, hmin⟩ := Finset.exists_mem_eq_inf' (M.A_nonempty i) (doeQ M (βs n) i)
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [← hmin]
    exact inf'_doeQ_le_discValue M (βs n) i
  choose aseq haseq using hex
  obtain ⟨a, ha_inf⟩ := Finite.exists_infinite_fiber aseq
  -- Extract a strictly monotone subsequence ψ along which aseq (ψ k) = a
  have hfreq : ∃ᶠ n in atTop, aseq n = a := by
    rw [Filter.frequently_atTop]
    intro N
    have hinf_set : (aseq ⁻¹' {a}).Infinite := Set.infinite_coe_iff.mp ha_inf
    obtain ⟨n, hn_mem, hn_gt⟩ := hinf_set.exists_gt N
    exact ⟨n, hn_gt.le, hn_mem⟩
  obtain ⟨ψ, hψ_mono, hψ_eq⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hstep := acoi_step_of_doe_le h1 h2 h3 h4 (βs ∘ ψ)
    (fun k => hβ_mem (ψ k)) (hβ_lim.comp hψ_mono.tendsto_atTop) g
    (hg_lim.comp hψ_mono.tendsto_atTop) h
    (fun j => (hh_lim j).comp hψ_mono.tendsto_atTop) i a.1 a.2
    (Eventually.of_forall fun k => by
      have := haseq (ψ k)
      rwa [hψ_eq k] at this)
  exact le_trans (Finset.inf'_le (fun b => ((M.C i b : ℝ) : EReal) + wsum (M.P i b) h) a.2) hstep

/-! ### Section 4: Iterated ACOI under `(H4)` and `(H5)` -/

omit [Countable S] in
lemma wsum_neg_ne_top_of_bot_lt {p : S → ℝ≥0∞} {h : S → ℝ}
    (hbot : ⊥ < wsum p h) : ∑' j, p j * ENNReal.ofReal (-h j) ≠ ⊤ := by
  intro htop
  unfold wsum at hbot
  rw [htop, EReal.coe_ennreal_top] at hbot
  have hsub : ((∑' j, p j * ENNReal.ofReal (h j) : ℝ≥0∞) : EReal) - (⊤ : EReal) = ⊥ := by
    rw [sub_eq_add_neg, EReal.neg_top, EReal.add_bot]
  rw [hsub] at hbot
  exact lt_irrefl ⊥ hbot

omit [Countable S] in
lemma wsum_pos_ne_top_of_lt_top {p : S → ℝ≥0∞} {h : S → ℝ}
    (hneg : ∑' j, p j * ENNReal.ofReal (-h j) ≠ ⊤)
    (htop : wsum p h < ⊤) : ∑' j, p j * ENNReal.ofReal (h j) ≠ ⊤ := by
  intro hpos
  unfold wsum at htop
  rw [hpos, EReal.coe_ennreal_top, ereal_coe_ennreal_eq_toReal hneg, EReal.top_sub_coe] at htop
  exact lt_irrefl ⊤ htop

lemma iterated_acoi_bound {M : SennottDP.Discounted.MDC S Act} {Lf : S → ℝ}
    (h4 : H4 M Lf) (h : S → ℝ) (hh_lo : ∀ j, -Lf j ≤ h j)
    (e : StationaryPolicy M) (g : ℝ≥0)
    (hh5 : ∀ i, ∀ n : ℕ, 2 ≤ n → ⊥ < expReal M e.toPolicy i n h)
    (hacoi : ∀ j, ((M.C j (e.1 j) : ℝ) : EReal) + wsum (M.P j (e.1 j)) h ≤ (((g : ℝ) + h j : ℝ) : EReal)) :
    ∀ (i : S) (n : ℕ), 1 ≤ n →
      horizonCost M e.toPolicy n i ≠ ⊤ ∧
      (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (h j) ≠ ⊤) ∧
      (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (-h j) ≠ ⊤) ∧
      (horizonCost M e.toPolicy n i : EReal) + expReal M e.toPolicy i n h ≤
        ((((n : ℝ) * (g : ℝ) + h i : ℝ) : EReal)) := by
  -- First, extract the one-step ENNReal inequality for every state j
  have hstep_ennr : ∀ j,
      (M.C j (e.1 j) : ℝ≥0∞) +
        (∑' k, M.P j (e.1 j) k * ENNReal.ofReal (h k)) + ENNReal.ofReal (-h j) ≤
      (g : ℝ≥0∞) + ENNReal.ofReal (h j) +
        (∑' k, M.P j (e.1 j) k * ENNReal.ofReal (-h k)) := by
    intro j
    have hneg_nt : ∑' k, M.P j (e.1 j) k * ENNReal.ofReal (-h k) ≠ ⊤ := by
      apply ne_of_lt
      refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr (h4 j (e.1 j) (e.2 j)))
      apply ENNReal.tsum_le_tsum; intro k; gcongr
      linarith [hh_lo k]
    have hw_lt : wsum (M.P j (e.1 j)) h < ⊤ := by
      have h1 := hacoi j
      by_contra hnt; push Not at hnt
      have htop : wsum (M.P j (e.1 j)) h = ⊤ := top_unique hnt
      rw [htop, EReal.coe_add_top] at h1
      exact not_le_of_gt (EReal.coe_lt_top _) h1
    have hpos_nt := wsum_pos_ne_top_of_lt_top hneg_nt hw_lt
    have hreal : (M.C j (e.1 j) : ℝ) +
        ((∑' k, M.P j (e.1 j) k * ENNReal.ofReal (h k)).toReal -
          (∑' k, M.P j (e.1 j) k * ENNReal.ofReal (-h k)).toReal) ≤ (g : ℝ) + h j := by
      have h1 := hacoi j
      unfold wsum at h1
      rw [ereal_coe_ennreal_eq_toReal hpos_nt, ereal_coe_ennreal_eq_toReal hneg_nt,
          ← EReal.coe_sub, ← EReal.coe_add] at h1
      exact EReal.coe_le_coe_iff.mp h1
    have hj_eq : h j = (ENNReal.ofReal (h j)).toReal - (ENNReal.ofReal (-h j)).toReal := by
      by_cases h0 : 0 ≤ h j
      · rw [ENNReal.toReal_ofReal h0, ENNReal.ofReal_of_nonpos (by linarith), ENNReal.toReal_zero, sub_zero]
      · push Not at h0
        rw [ENNReal.ofReal_of_nonpos h0.le, ENNReal.toReal_zero, ENNReal.toReal_ofReal (by linarith)]
        ring
    have hlhs_nt : (M.C j (e.1 j) : ℝ≥0∞) +
        (∑' k, M.P j (e.1 j) k * ENNReal.ofReal (h k)) + ENNReal.ofReal (-h j) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, hpos_nt⟩, ENNReal.ofReal_ne_top⟩
    have hrhs_nt : (g : ℝ≥0∞) + ENNReal.ofReal (h j) +
        (∑' k, M.P j (e.1 j) k * ENNReal.ofReal (-h k)) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.ofReal_ne_top⟩, hneg_nt⟩
    rw [← ENNReal.toReal_le_toReal hlhs_nt hrhs_nt,
        ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, hpos_nt⟩) ENNReal.ofReal_ne_top,
        ENNReal.toReal_add ENNReal.coe_ne_top hpos_nt,
        ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.ofReal_ne_top⟩) hneg_nt,
        ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.ofReal_ne_top,
        ENNReal.coe_toReal, ENNReal.coe_toReal]
    linarith
  intro i n hn
  induction n, hn using Nat.le_induction with
  | base =>
      have hhor1 : horizonCost M e.toPolicy 1 i = (M.C i (e.1 i) : ℝ≥0∞) := by
        unfold horizonCost
        rw [Finset.sum_range_one, expCost_stationary]
        simp_rw [stateProb_zero]
        rw [tsum_eq_single i]
        · simp
        · intro j hj; simp [hj]
      have hsp1 : ∀ k, stateProb M e.toPolicy i 1 k = M.P i (e.1 i) k := fun k => by
        rw [stateProb_succ_stationary]
        simp_rw [stateProb_zero]
        rw [tsum_eq_single i]
        · simp
        · intro j hj; simp [hj]
      have hneg1 : ∑' j, stateProb M e.toPolicy i 1 j * ENNReal.ofReal (-h j) ≠ ⊤ := by
        simp_rw [hsp1]
        apply ne_of_lt
        refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr (h4 i (e.1 i) (e.2 i)))
        apply ENNReal.tsum_le_tsum; intro k; gcongr
        linarith [hh_lo k]
      have hexp1 : expReal M e.toPolicy i 1 h = wsum (M.P i (e.1 i)) h := by
        unfold expReal; congr 1; ext k; exact hsp1 k
      have hw1_lt : wsum (M.P i (e.1 i)) h < ⊤ := by
        have h1 := hacoi i
        by_contra hnt; push Not at hnt
        have htop : wsum (M.P i (e.1 i)) h = ⊤ := top_unique hnt
        rw [htop, EReal.coe_add_top] at h1
        exact not_le_of_gt (EReal.coe_lt_top _) h1
      have hpos1 : ∑' j, stateProb M e.toPolicy i 1 j * ENNReal.ofReal (h j) ≠ ⊤ := by
        simp_rw [hsp1]
        have hneg1' : ∑' j, M.P i (e.1 i) j * ENNReal.ofReal (-h j) ≠ ⊤ := by
          simpa [hsp1] using hneg1
        exact wsum_pos_ne_top_of_lt_top hneg1' hw1_lt
      refine ⟨by rw [hhor1]; exact ENNReal.coe_ne_top, hpos1, hneg1, ?_⟩
      rw [hhor1, hexp1, ereal_coe_ennreal_eq_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
      simpa using hacoi i
  | succ n hn ih =>
      obtain ⟨hhor_nt, hpos_nt, hneg_nt, hle_n⟩ := ih
      have hneg_succ : ∑' k, stateProb M e.toPolicy i (n + 1) k * ENNReal.ofReal (-h k) ≠ ⊤ :=
        wsum_neg_ne_top_of_bot_lt (hh5 i (n + 1) (by omega))
      -- Sum hstep_ennr weighted by stateProb M e.toPolicy i n j
      have hsum_step :
          SennottDP.Discounted.expCost M e.toPolicy i n +
            (∑' k, stateProb M e.toPolicy i (n + 1) k * ENNReal.ofReal (h k)) +
            (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (-h j)) ≤
          (g : ℝ≥0∞) +
            (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (h j)) +
            (∑' k, stateProb M e.toPolicy i (n + 1) k * ENNReal.ofReal (-h k)) := by
        have h1 : ∑' j, stateProb M e.toPolicy i n j *
            ((M.C j (e.1 j) : ℝ≥0∞) +
              (∑' k, M.P j (e.1 j) k * ENNReal.ofReal (h k)) + ENNReal.ofReal (-h j)) ≤
          ∑' j, stateProb M e.toPolicy i n j *
            ((g : ℝ≥0∞) + ENNReal.ofReal (h j) +
              (∑' k, M.P j (e.1 j) k * ENNReal.ofReal (-h k))) := by
          apply ENNReal.tsum_le_tsum; intro j
          exact mul_le_mul_right (hstep_ennr j) _
        have hlhs_eq : ∑' j, stateProb M e.toPolicy i n j *
            ((M.C j (e.1 j) : ℝ≥0∞) +
              (∑' k, M.P j (e.1 j) k * ENNReal.ofReal (h k)) + ENNReal.ofReal (-h j)) =
          SennottDP.Discounted.expCost M e.toPolicy i n +
            (∑' k, stateProb M e.toPolicy i (n + 1) k * ENNReal.ofReal (h k)) +
            (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (-h j)) := by
          simp_rw [mul_add, ENNReal.tsum_add]
          rw [expCost_stationary]
          congr 2
          simp_rw [← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          congr 1; ext k
          rw [stateProb_succ_stationary, ← ENNReal.tsum_mul_right]
          congr 1; ext j; ring
        have hrhs_eq : ∑' j, stateProb M e.toPolicy i n j *
            ((g : ℝ≥0∞) + ENNReal.ofReal (h j) +
              (∑' k, M.P j (e.1 j) k * ENNReal.ofReal (-h k))) =
          (g : ℝ≥0∞) +
            (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (h j)) +
            (∑' k, stateProb M e.toPolicy i (n + 1) k * ENNReal.ofReal (-h k)) := by
          simp_rw [mul_add, ENNReal.tsum_add]
          rw [ENNReal.tsum_mul_right, tsum_stateProb_stationary M e i n, one_mul]
          congr 1
          simp_rw [← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          congr 1; ext k
          rw [stateProb_succ_stationary, ← ENNReal.tsum_mul_right]
          congr 1; ext j; ring
        rwa [hlhs_eq, hrhs_eq] at h1
      have hrhs_nt : (g : ℝ≥0∞) +
          (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (h j)) +
          (∑' k, stateProb M e.toPolicy i (n + 1) k * ENNReal.ofReal (-h k)) ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, hpos_nt⟩, hneg_succ⟩
      have hlhs_nt : SennottDP.Discounted.expCost M e.toPolicy i n +
          (∑' k, stateProb M e.toPolicy i (n + 1) k * ENNReal.ofReal (h k)) +
          (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (-h j)) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt hsum_step (lt_top_iff_ne_top.mpr hrhs_nt))
      have hexp_nt : SennottDP.Discounted.expCost M e.toPolicy i n ≠ ⊤ :=
        (ENNReal.add_ne_top.mp (ENNReal.add_ne_top.mp hlhs_nt).1).1
      have hpos_succ : ∑' k, stateProb M e.toPolicy i (n + 1) k * ENNReal.ofReal (h k) ≠ ⊤ :=
        (ENNReal.add_ne_top.mp (ENNReal.add_ne_top.mp hlhs_nt).1).2
      have hhor_succ : horizonCost M e.toPolicy (n + 1) i =
          horizonCost M e.toPolicy n i + SennottDP.Discounted.expCost M e.toPolicy i n := by
        unfold horizonCost; rw [Finset.sum_range_succ]
      have hhor_succ_nt : horizonCost M e.toPolicy (n + 1) i ≠ ⊤ := by
        rw [hhor_succ]; exact ENNReal.add_ne_top.mpr ⟨hhor_nt, hexp_nt⟩
      refine ⟨hhor_succ_nt, hpos_succ, hneg_succ, ?_⟩
      -- Convert everything to ℝ and combine with hle_n
      have hstep_r := ENNReal.toReal_mono hrhs_nt hsum_step
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hexp_nt, hpos_succ⟩) hneg_nt,
          ENNReal.toReal_add hexp_nt hpos_succ,
          ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, hpos_nt⟩) hneg_succ,
          ENNReal.toReal_add ENNReal.coe_ne_top hpos_nt,
          ENNReal.coe_toReal] at hstep_r
      have hle_n_r : (horizonCost M e.toPolicy n i).toReal +
          ((∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (h j)).toReal -
            (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (-h j)).toReal) ≤
          (n : ℝ) * (g : ℝ) + h i := by
        unfold expReal wsum at hle_n
        rw [ereal_coe_ennreal_eq_toReal hhor_nt, ereal_coe_ennreal_eq_toReal hpos_nt,
            ereal_coe_ennreal_eq_toReal hneg_nt, ← EReal.coe_sub, ← EReal.coe_add] at hle_n
        exact EReal.coe_le_coe_iff.mp hle_n
      unfold expReal wsum
      rw [ereal_coe_ennreal_eq_toReal hhor_succ_nt, ereal_coe_ennreal_eq_toReal hpos_succ,
          ereal_coe_ennreal_eq_toReal hneg_succ, ← EReal.coe_sub, ← EReal.coe_add]
      apply EReal.coe_le_coe_iff.mpr
      rw [hhor_succ, ENNReal.toReal_add hhor_nt hexp_nt]
      push_cast
      linarith

lemma avgCost_le_of_acoi {M : SennottDP.Discounted.MDC S Act} {Lf : S → ℝ}
    (h4 : H4 M Lf) (h : S → ℝ) (hh_lo : ∀ j, -Lf j ≤ h j)
    (e : StationaryPolicy M) (g : ℝ≥0)
    (hh5_bot : ∀ i, ∀ n : ℕ, 2 ≤ n → ⊥ < expReal M e.toPolicy i n h)
    (hh5_liminf : ∀ i, 0 ≤ liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M e.toPolicy i n h) atTop)
    (hacoi : ∀ j, ((M.C j (e.1 j) : ℝ) : EReal) + wsum (M.P j (e.1 j)) h ≤ (((g : ℝ) + h j : ℝ) : EReal))
    (i : S) :
    avgCost M e.toPolicy i ≤ (g : ℝ≥0∞) := by
  have hiter := iterated_acoi_bound h4 h hh_lo e g hh5_bot hacoi i
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε_pos : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
  -- Eventually (1/n) * expReal ≥ -ε/2
  have hneg_lt : (((-(ε : ℝ) / 2 : ℝ) : EReal)) <
      liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M e.toPolicy i n h) atTop := by
    refine lt_of_lt_of_le ?_ (hh5_liminf i)
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hev1 : ∀ᶠ n : ℕ in atTop,
      (((-(ε : ℝ) / 2 : ℝ) : EReal)) < (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M e.toPolicy i n h :=
    eventually_lt_of_lt_liminf hneg_lt
  -- Eventually (1/n) * h i ≤ ε/2
  have hev2 : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * h i < (ε : ℝ) / 2 := by
    have ht : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * h i) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (h i)
    exact ht.eventually (gt_mem_nhds (by linarith))
  have hev_bound : ∀ᶠ n : ℕ in atTop, horizonCost M e.toPolicy n i / (n : ℝ≥0∞) ≤ (g : ℝ≥0∞) + (ε : ℝ≥0∞) := by
    filter_upwards [hev1, hev2, eventually_ge_atTop 1] with n hn1 hn2 hn_ge
    obtain ⟨hhor_nt, hpos_nt, hneg_nt, hle⟩ := hiter n hn_ge
    have hn_pos : (0 : ℝ) < n := by positivity
    set E : ℝ := (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (h j)).toReal -
      (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (-h j)).toReal
    have hexp_eq : expReal M e.toPolicy i n h = (E : EReal) := by
      unfold expReal wsum
      rw [ereal_coe_ennreal_eq_toReal hpos_nt, ereal_coe_ennreal_eq_toReal hneg_nt, ← EReal.coe_sub]
    have hE_lo : -(ε : ℝ) / 2 < (n : ℝ)⁻¹ * E := by
      rw [hexp_eq, ← EReal.coe_mul] at hn1
      exact EReal.coe_lt_coe_iff.mp hn1
    have hle_r : (horizonCost M e.toPolicy n i).toReal + E ≤ (n : ℝ) * (g : ℝ) + h i := by
      rw [hexp_eq, ereal_coe_ennreal_eq_toReal hhor_nt, ← EReal.coe_add] at hle
      exact EReal.coe_le_coe_iff.mp hle
    have hdiv_r : (horizonCost M e.toPolicy n i).toReal / (n : ℝ) ≤ (g : ℝ) + (ε : ℝ) := by
      have h1 : (n : ℝ)⁻¹ * ((horizonCost M e.toPolicy n i).toReal + E) ≤
          (n : ℝ)⁻¹ * ((n : ℝ) * (g : ℝ) + h i) :=
        mul_le_mul_of_nonneg_left hle_r (inv_nonneg.mpr hn_pos.le)
      have h2 : (n : ℝ)⁻¹ * ((n : ℝ) * (g : ℝ) + h i) = (g : ℝ) + (n : ℝ)⁻¹ * h i := by
        field_simp
      rw [mul_add, h2] at h1
      rw [div_eq_inv_mul]
      linarith
    have hdiv_nt : horizonCost M e.toPolicy n i / (n : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.div_ne_top hhor_nt (by positivity)
    rw [← ENNReal.toReal_le_toReal hdiv_nt (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.coe_ne_top⟩),
        ENNReal.toReal_div, ENNReal.toReal_natCast,
        ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top,
        ENNReal.coe_toReal, ENNReal.coe_toReal]
    exact hdiv_r
  unfold avgCost
  exact le_trans (limsup_le_limsup hev_bound) (by rw [limsup_const])

lemma tendsto_inv_mul_expReal_zero {M : SennottDP.Discounted.MDC S Act} {Lf : S → ℝ}
    (h4 : H4 M Lf) (h : S → ℝ) (hh_lo : ∀ j, -Lf j ≤ h j)
    (e : StationaryPolicy M) (g : ℝ≥0)
    (hh5_bot : ∀ i, ∀ n : ℕ, 2 ≤ n → ⊥ < expReal M e.toPolicy i n h)
    (hh5_liminf : ∀ i, 0 ≤ liminf (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M e.toPolicy i n h) atTop)
    (hacoi : ∀ j, ((M.C j (e.1 j) : ℝ) : EReal) + wsum (M.P j (e.1 j)) h ≤ (((g : ℝ) + h j : ℝ) : EReal))
    (i : S)
    (hlim : Tendsto (fun n : ℕ => horizonCost M e.toPolicy n i / (n : ℝ≥0∞)) atTop (𝓝 (g : ℝ≥0∞))) :
    Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M e.toPolicy i n h) atTop (𝓝 0) := by
  have hiter := iterated_acoi_bound h4 h hh_lo e g hh5_bot hacoi i
  refine tendsto_of_le_liminf_of_limsup_le (hh5_liminf i) ?_
  have hle_eps : ∀ ε : ℝ, 0 < ε →
      limsup (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M e.toPolicy i n h) atTop ≤ (ε : EReal) := by
    intro ε hε
    -- Eventually horizonCost / n > g - ε/2
    have hev1 : ∀ᶠ n : ℕ in atTop, (g : ℝ) - ε / 2 < (horizonCost M e.toPolicy n i / (n : ℝ≥0∞)).toReal := by
      have hreal_lim : Tendsto (fun n : ℕ => (horizonCost M e.toPolicy n i / (n : ℝ≥0∞)).toReal)
          atTop (𝓝 (g : ℝ)) := by
        have hcomp := (ENNReal.continuousAt_toReal (ENNReal.coe_ne_top (r := g))).tendsto.comp hlim
        simpa [Function.comp_def] using hcomp
      exact hreal_lim.eventually (lt_mem_nhds (by linarith))
    -- Eventually (1/n) * h i < ε/2
    have hev2 : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * h i < ε / 2 := by
      have ht : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * h i) atTop (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (h i)
      exact ht.eventually (gt_mem_nhds (by linarith))
    have hev_le : ∀ᶠ n : ℕ in atTop,
        (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M e.toPolicy i n h ≤ (ε : EReal) := by
      filter_upwards [hev1, hev2, eventually_ge_atTop 1] with n hn1 hn2 hn_ge
      obtain ⟨hhor_nt, hpos_nt, hneg_nt, hle⟩ := hiter n hn_ge
      have hn_pos : (0 : ℝ) < n := by positivity
      set E : ℝ := (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (h j)).toReal -
        (∑' j, stateProb M e.toPolicy i n j * ENNReal.ofReal (-h j)).toReal
      have hexp_eq : expReal M e.toPolicy i n h = (E : EReal) := by
        unfold expReal wsum
        rw [ereal_coe_ennreal_eq_toReal hpos_nt, ereal_coe_ennreal_eq_toReal hneg_nt, ← EReal.coe_sub]
      have hle_r : (horizonCost M e.toPolicy n i).toReal + E ≤ (n : ℝ) * (g : ℝ) + h i := by
        rw [hexp_eq, ereal_coe_ennreal_eq_toReal hhor_nt, ← EReal.coe_add] at hle
        exact EReal.coe_le_coe_iff.mp hle
      rw [ENNReal.toReal_div, ENNReal.toReal_natCast,
          div_eq_inv_mul (horizonCost M e.toPolicy n i).toReal] at hn1
      have h1 : (n : ℝ)⁻¹ * ((horizonCost M e.toPolicy n i).toReal + E) ≤
          (n : ℝ)⁻¹ * ((n : ℝ) * (g : ℝ) + h i) :=
        mul_le_mul_of_nonneg_left hle_r (inv_nonneg.mpr hn_pos.le)
      have h2 : (n : ℝ)⁻¹ * ((n : ℝ) * (g : ℝ) + h i) = (g : ℝ) + (n : ℝ)⁻¹ * h i := by
        field_simp
      rw [mul_add, h2] at h1
      rw [hexp_eq, ← EReal.coe_mul]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    exact le_trans (limsup_le_limsup hev_le) (by rw [limsup_const])
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr0, hr_lt⟩ := EReal.exists_between_coe_real hlt
  have hr_pos : 0 < r := EReal.coe_lt_coe_iff.mp (by simpa using hr0)
  exact not_lt_of_ge (hle_eps r hr_pos) hr_lt

/-! ### Section 5: Main helper for extracting a liminf sequence along `𝓝[<] 1` -/

lemma exists_seq_tendsto_liminf_nhdsLT (f : ℝ → ℝ≥0∞) {B : ℝ≥0}
    (hB : ∀ α ∈ Set.Ioo (0 : ℝ) 1, f α ≤ (B : ℝ≥0∞)) :
    ∃ αs : ℕ → ℝ, (∀ n, αs n ∈ Set.Ioo (0 : ℝ) 1) ∧ Tendsto αs atTop (𝓝 1) ∧
      Tendsto (fun n => f (αs n)) atTop (𝓝 (liminf f (𝓝[<] 1))) := by
  set g := liminf f (𝓝[<] 1)
  have hg_le_B : g ≤ (B : ℝ≥0∞) := by
    have hev : ∀ᶠ α in 𝓝[<] 1, f α ≤ (B : ℝ≥0∞) := by
      filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with α hα
      exact hB α hα
    exact le_trans (liminf_le_liminf hev) (by rw [liminf_const])
  have hg_ne_top : g ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hg_le_B ENNReal.coe_lt_top)
  have hex : ∀ n : ℕ, ∃ α : ℝ, α ∈ Set.Ioo (1 - ((n + 2 : ℕ) : ℝ)⁻¹) 1 ∧
      f α < g + (((n + 1 : ℕ) : ℝ≥0∞))⁻¹ := by
    intro n
    have hlt : g < g + (((n + 1 : ℕ) : ℝ≥0∞))⁻¹ :=
      ENNReal.lt_add_right hg_ne_top (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
    have hfreq : ∃ᶠ α in 𝓝[<] 1, f α < g + (((n + 1 : ℕ) : ℝ≥0∞))⁻¹ :=
      frequently_lt_of_liminf_lt (h := hlt)
    have hmem : Set.Ioo (1 - ((n + 2 : ℕ) : ℝ)⁻¹) 1 ∈ 𝓝[<] 1 :=
      Ioo_mem_nhdsLT (by
        have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ)⁻¹ := by positivity
        linarith)
    obtain ⟨α, h1, h2⟩ := (hfreq.and_eventually (Filter.eventually_of_mem hmem fun _ hx => hx)).exists
    exact ⟨α, h2, h1⟩
  choose αs hαs_mem hαs_lt using hex
  have hαs_Ioo : ∀ n, αs n ∈ Set.Ioo (0 : ℝ) 1 := fun n => by
    have h1 := (hαs_mem n).1
    have h2 : ((n + 2 : ℕ) : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right; exact_mod_cast (by omega : 1 ≤ n + 2)
    exact ⟨by linarith, (hαs_mem n).2⟩
  have hαs_lim : Tendsto αs atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
      (fun n => (hαs_mem n).1.le) (fun n => (hαs_mem n).2.le)
    have hinv : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    simpa using tendsto_const_nhds.sub hinv
  have hαs_nhdsLT : Tendsto αs atTop (𝓝[<] 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hαs_lim
      (Eventually.of_forall fun n => (hαs_mem n).2)
  refine ⟨αs, hαs_Ioo, hαs_lim, ?_⟩
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
    have hev : ∀ᶠ α in 𝓝[<] 1, b < f α := eventually_lt_of_lt_liminf hb
    have hev_n : ∀ᶠ n in atTop, b ≤ f (αs n) :=
      (hαs_nhdsLT.eventually hev).mono fun _ h => h.le
    exact le_liminf_of_le (by isBoundedDefault) hev_n
  · calc limsup (fun n => f (αs n)) atTop
        ≤ limsup (fun n => g + (((n + 1 : ℕ) : ℝ≥0∞))⁻¹) atTop :=
          limsup_le_limsup (Eventually.of_forall fun n => (hαs_lt n).le)
      _ = g := by
          apply Tendsto.limsup_eq
          have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ≥0∞))⁻¹) atTop (𝓝 0) := by
            have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)) atTop (𝓝 ⊤) :=
              ENNReal.tendsto_nat_nhds_top.comp (tendsto_add_atTop_nat 1)
            simpa using tendsto_inv_iff.mpr h1
          simpa using tendsto_const_nhds.add hinv

end MDC

end SennottProp772

open SennottDP.SEN SennottProp772

/-- Sennott (1999), Proposition 7.7.2, p. 158. -/
theorem solution {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) (z : S)
    (Mf Lf : S → ℝ) (hH : SennottDP.SEN.HAssumptions M z Mf Lf) :
    ∃ J : ℝ≥0,
      -- (i)
      (∀ i, Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * discValue M α i) (𝓝[<] 1)
        (𝓝 (J : ℝ≥0∞))) ∧
      -- (ii)
      (∃ h : S → ℝ, IsLimitFunction M z h) ∧
      (∀ h : S → ℝ, IsLimitFunction M z h →
        (∀ i, -Lf i ≤ h i ∧ h i ≤ Mf i) ∧
        (∀ i, acoiMin M h i ≤ (((J : ℝ) + h i : ℝ) : EReal)) ∧
        ∀ e : StationaryPolicy M, RealizesACOI M h e →
          IsAverageOptimal M e.toPolicy ∧ (∀ i, avgCost M e.toPolicy i = (J : ℝ≥0∞)) ∧
          ∀ i, Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M e.toPolicy i n h)
            atTop (𝓝 0)) ∧
      -- (iii)
      (∀ fam : ℝ → StationaryPolicy M, (∀ α ∈ Set.Ioo (0 : ℝ) 1, RealizesDOE M α (fam α)) →
        ∀ f : StationaryPolicy M, IsLimitPoint M fam f →
          IsAverageOptimal M f.toPolicy ∧
          (∃ h : S → ℝ, IsAssociated M z fam f h) ∧
          ∀ h : S → ℝ, IsAssociated M z fam f h →
            (∀ i, ((M.C i (f.1 i) : ℝ) : EReal) + wsum (M.P i (f.1 i)) h ≤
              (((J : ℝ) + h i : ℝ) : EReal)) ∧
            ∀ i, Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M f.toPolicy i n h)
              atTop (𝓝 0)) ∧
      -- (iv)
      (∀ ψ : SennottDP.Discounted.Policy M, IsAverageOptimal M ψ → ∀ i,
        Tendsto (fun n : ℕ => horizonCost M ψ n i / (n : ℝ≥0∞)) atTop (𝓝 (avgCost M ψ i))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hH
  have hz_nt : ∀ α ∈ Set.Ioo (0 : ℝ) 1, discValue M α z ≠ ⊤ := fun α hα =>
    discValue_z_ne_top_of_SEN1 h1 hα
  -- Step 1: Extract a sequence αs → 1⁻ attaining g_inf = liminf (1-α) V_α(z)
  obtain ⟨B, hB⟩ := h1
  set g_inf := liminf (fun α : ℝ => ENNReal.ofReal (1 - α) * discValue M α z) (𝓝[<] 1)
  set g_sup := limsup (fun α : ℝ => ENNReal.ofReal (1 - α) * discValue M α z) (𝓝[<] 1)
  have hginf_le_B : g_inf ≤ (B : ℝ≥0∞) := by
    have hev : ∀ᶠ α in 𝓝[<] 1, ENNReal.ofReal (1 - α) * discValue M α z ≤ (B : ℝ≥0∞) := by
      filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with α hα
      exact hB α hα
    exact le_trans (liminf_le_liminf hev) (by rw [liminf_const])
  have hginf_ne_top : g_inf ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hginf_le_B ENNReal.coe_lt_top)
  set J : ℝ≥0 := g_inf.toNNReal
  have hJ_eq : (J : ℝ≥0∞) = g_inf := ENNReal.coe_toNNReal hginf_ne_top
  obtain ⟨αs0, hαs0_mem, hαs0_lim, hαs0_val⟩ :=
    exists_seq_tendsto_liminf_nhdsLT (fun α => ENNReal.ofReal (1 - α) * discValue M α z) hB
  -- Step 2: Apply Prop B.6 to get a limit function h0 along a subsequence of αs0
  let u0 : ℕ → S → ℝ := fun r i => (discValue M (αs0 r) i).toReal - (discValue M (αs0 r) z).toReal
  have hu0 : ∀ r i, -Lf i ≤ u0 r i ∧ u0 r i ≤ Mf i := fun r i =>
    hRel_toReal_bounds ⟨B, hB⟩ h2 h3 (hαs0_mem r) i
  obtain ⟨rk0, hrk0_mono, h0, hh0_bd, hh0_lim⟩ :=
    prop_B_6_bounded_subsequence Lf Mf h3.1 h2.1 u0 hu0
  have hh0_islim : IsLimitFunction M z h0 := by
    refine ⟨hz_nt, αs0, rk0, hαs0_mem, hαs0_lim, hrk0_mono, fun i => ?_⟩
    have hcomp := EReal.tendsto_coe.mpr (hh0_lim i)
    refine hcomp.congr fun n => ?_
    simp only [u0]
    exact (hRel_eq_coe_sub (discValue_ne_top_of_H ⟨B, hB⟩ h2 (hαs0_mem (rk0 n)) i)
      (hz_nt (αs0 (rk0 n)) (hαs0_mem (rk0 n)))).symm
  -- Step 3: ACOI for h0 with constant J, pick stationary policy e0 realizing it
  have hh0_acoi : ∀ i, acoiMin M h0 i ≤ (((J : ℝ) + h0 i : ℝ) : EReal) := fun i =>
    acoiMin_le_of_seq ⟨B, hB⟩ h2 h3 h4 (αs0 ∘ rk0)
      (fun n => hαs0_mem (rk0 n)) (hαs0_lim.comp hrk0_mono.tendsto_atTop) J
      (by rw [hJ_eq]; exact hαs0_val.comp hrk0_mono.tendsto_atTop) h0
      (fun j => by
        have hcomp := EReal.tendsto_coe.mpr (hh0_lim j)
        refine hcomp.congr fun n => ?_
        simp only [u0]
        exact (hRel_eq_coe_sub (discValue_ne_top_of_H ⟨B, hB⟩ h2 (hαs0_mem (rk0 n)) j)
          (hz_nt (αs0 (rk0 n)) (hαs0_mem (rk0 n)))).symm) i
  have he0_ex : ∀ i, ∃ a ∈ M.A i, ((M.C i a : ℝ) : EReal) + wsum (M.P i a) h0 = acoiMin M h0 i := fun i => by
    obtain ⟨a, ha, heq⟩ := Finset.exists_mem_eq_inf' (M.A_nonempty i)
      (fun a => ((M.C i a : ℝ) : EReal) + wsum (M.P i a) h0)
    exact ⟨a, ha, heq.symm⟩
  choose e0_fn he0_mem he0_eq using he0_ex
  let e0 : StationaryPolicy M := ⟨e0_fn, he0_mem⟩
  have he0_avg : ∀ i, avgCost M e0.toPolicy i ≤ (J : ℝ≥0∞) := fun i =>
    avgCost_le_of_acoi h4 h0 (fun j => (hh0_bd j).1) e0 J
      (fun j => (h5 h0 hh0_islim e0 j).1)
      (fun j => (h5 h0 hh0_islim e0 j).2)
      (fun j => by rw [he0_eq j]; exact hh0_acoi j) i
  -- Step 4: Tauberian inequality gives g_sup ≤ avgCost e0 z ≤ J = g_inf, hence (i)!
  have hgsup_le_J : g_sup ≤ (J : ℝ≥0∞) := by
    calc g_sup
        ≤ limsup (fun α : ℝ => ENNReal.ofReal (1 - α) * discCost M e0.toPolicy α z) (𝓝[<] 1) :=
          limsup_le_limsup (Eventually.of_forall fun α =>
            mul_le_mul_right (iInf_le (fun ψ => discCost M ψ α z) e0.toPolicy) _)
      _ ≤ avgCost M e0.toPolicy z := tauberian_limsup_le (SennottDP.Discounted.expCost M e0.toPolicy z)
      _ ≤ (J : ℝ≥0∞) := he0_avg z
  have hz_tendsto : Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * discValue M α z) (𝓝[<] 1) (𝓝 (J : ℝ≥0∞)) :=
    tendsto_of_le_liminf_of_limsup_le (le_of_eq hJ_eq) hgsup_le_J
  have h_part_i : ∀ i, Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * discValue M α i) (𝓝[<] 1) (𝓝 (J : ℝ≥0∞)) :=
    fun i => tendsto_discValue_of_tendsto_z ⟨B, hB⟩ h2 h3 hz_tendsto i
  -- Step 5: J ≤ avgCost ψ i for all policies ψ and all i, so avgValue M i = J
  have hJ_le_avgCost : ∀ (ψ : SennottDP.Discounted.Policy M) (i : S), (J : ℝ≥0∞) ≤ avgCost M ψ i := by
    intro ψ i
    calc (J : ℝ≥0∞)
        = limsup (fun α : ℝ => ENNReal.ofReal (1 - α) * discValue M α i) (𝓝[<] 1) :=
          (h_part_i i).limsup_eq.symm
      _ ≤ limsup (fun α : ℝ => ENNReal.ofReal (1 - α) * discCost M ψ α i) (𝓝[<] 1) :=
          limsup_le_limsup (Eventually.of_forall fun α =>
            mul_le_mul_right (iInf_le (fun θ => discCost M θ α i) ψ) _)
      _ ≤ avgCost M ψ i := tauberian_limsup_le (SennottDP.Discounted.expCost M ψ i)
  have havgVal_eq : ∀ i, avgValue M i = (J : ℝ≥0∞) := fun i => by
    apply le_antisymm
    · exact le_trans (iInf_le (fun ψ => avgCost M ψ i) e0.toPolicy) (he0_avg i)
    · exact le_iInf fun ψ => hJ_le_avgCost ψ i
  -- Step 6: Prove (iv) first!
  have h_part_iv : ∀ ψ : SennottDP.Discounted.Policy M, IsAverageOptimal M ψ → ∀ i,
      Tendsto (fun n : ℕ => horizonCost M ψ n i / (n : ℝ≥0∞)) atTop (𝓝 (avgCost M ψ i)) := by
    intro ψ hopt i
    have hψ_eq : avgCost M ψ i = (J : ℝ≥0∞) := by rw [hopt i, havgVal_eq i]
    rw [hψ_eq]
    refine tauberian_tendsto_of_limsup_le_of_le_liminf (SennottDP.Discounted.expCost M ψ i) J
      (by exact hψ_eq.le) ?_
    calc (J : ℝ≥0∞)
        = liminf (fun α : ℝ => ENNReal.ofReal (1 - α) * discValue M α i) (𝓝[<] 1) :=
          (h_part_i i).liminf_eq.symm
      _ ≤ liminf (fun α : ℝ => ENNReal.ofReal (1 - α) * discCost M ψ α i) (𝓝[<] 1) :=
          liminf_le_liminf (Eventually.of_forall fun α =>
            mul_le_mul_right (iInf_le (fun θ => discCost M θ α i) ψ) _)
  -- Helper: any stationary policy e + limit function h satisfying ACOI for e is average optimal with cost J and (7.10)/(7.12)
  have h_stat_opt : ∀ (h : S → ℝ), IsLimitFunction M z h → (∀ j, -Lf j ≤ h j) →
      ∀ (e : StationaryPolicy M),
        (∀ j, ((M.C j (e.1 j) : ℝ) : EReal) + wsum (M.P j (e.1 j)) h ≤ (((J : ℝ) + h j : ℝ) : EReal)) →
        IsAverageOptimal M e.toPolicy ∧ (∀ i, avgCost M e.toPolicy i = (J : ℝ≥0∞)) ∧
        ∀ i, Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M e.toPolicy i n h) atTop (𝓝 0) := by
    intro h hh_lim hh_lo e he_acoi
    have he_le : ∀ i, avgCost M e.toPolicy i ≤ (J : ℝ≥0∞) := fun i =>
      avgCost_le_of_acoi h4 h hh_lo e J
        (fun j => (h5 h hh_lim e j).1) (fun j => (h5 h hh_lim e j).2) he_acoi i
    have he_eq : ∀ i, avgCost M e.toPolicy i = (J : ℝ≥0∞) := fun i =>
      le_antisymm (he_le i) (hJ_le_avgCost e.toPolicy i)
    have he_opt : IsAverageOptimal M e.toPolicy := fun i => by rw [he_eq i, havgVal_eq i]
    refine ⟨he_opt, he_eq, fun i => ?_⟩
    have hlim_i : Tendsto (fun n : ℕ => horizonCost M e.toPolicy n i / (n : ℝ≥0∞)) atTop (𝓝 (J : ℝ≥0∞)) := by
      rw [← he_eq i]; exact h_part_iv e.toPolicy he_opt i
    exact tendsto_inv_mul_expReal_zero h4 h hh_lo e J
      (fun j => (h5 h hh_lim e j).1) (fun j => (h5 h hh_lim e j).2) he_acoi i hlim_i
  -- Step 7: Assemble (i), (ii), (iii), (iv)
  refine ⟨J, h_part_i, ⟨h0, hh0_islim⟩, ?_, ?_, h_part_iv⟩
  -- Part (ii)
  · intro h hh_islim
    have hh_islim' := hh_islim
    obtain ⟨_, αs, φ, hα_mem, hα_lim, hφ_mono, hh_lim⟩ := hh_islim'
    have hh_bd : ∀ i, -Lf i ≤ h i ∧ h i ≤ Mf i := fun i => by
      constructor
      · exact EReal.coe_le_coe_iff.mp (ge_of_tendsto (hh_lim i)
          (Eventually.of_forall fun n => h3.2 (αs (φ n)) (hα_mem (φ n)) i))
      · exact EReal.coe_le_coe_iff.mp (le_of_tendsto (hh_lim i)
          (Eventually.of_forall fun n => h2.2 (αs (φ n)) (hα_mem (φ n)) i))
    have hβ_nhdsLT : Tendsto (αs ∘ φ) atTop (𝓝[<] 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hα_lim.comp hφ_mono.tendsto_atTop)
        (Eventually.of_forall fun n => (hα_mem (φ n)).2)
    have hh_acoi : ∀ i, acoiMin M h i ≤ (((J : ℝ) + h i : ℝ) : EReal) := fun i =>
      acoiMin_le_of_seq ⟨B, hB⟩ h2 h3 h4 (αs ∘ φ)
        (fun n => hα_mem (φ n)) (hα_lim.comp hφ_mono.tendsto_atTop) J
        (hz_tendsto.comp hβ_nhdsLT) h hh_lim i
    refine ⟨hh_bd, hh_acoi, fun e he_real => ?_⟩
    exact h_stat_opt h hh_islim (fun j => (hh_bd j).1) e (fun j => by rw [he_real j]; exact hh_acoi j)
  -- Part (iii)
  · intro fam hfam f hf_lp
    obtain ⟨αs, φ, hα_mem, hα_lim, hφ_mono, hf_ev⟩ := hf_lp
    -- Construct an associated limit function h_f via Prop B.6
    let u : ℕ → S → ℝ := fun r i => (discValue M (αs (φ r)) i).toReal - (discValue M (αs (φ r)) z).toReal
    have hu : ∀ r i, -Lf i ≤ u r i ∧ u r i ≤ Mf i := fun r i =>
      hRel_toReal_bounds ⟨B, hB⟩ h2 h3 (hα_mem (φ r)) i
    obtain ⟨rk, hrk_mono, hf_h, _, hfh_lim⟩ :=
      prop_B_6_bounded_subsequence Lf Mf h3.1 h2.1 u hu
    have hfh_assoc : IsAssociated M z fam f hf_h := by
      refine ⟨hz_nt, fun n => αs (φ (rk n)), fun n => hα_mem (φ (rk n)),
        (hα_lim.comp hφ_mono.tendsto_atTop).comp hrk_mono.tendsto_atTop, fun i => ?_, fun i => ?_⟩
      · have hcomp := EReal.tendsto_coe.mpr (hfh_lim i)
        refine hcomp.congr fun n => ?_
        simp only [u]
        exact (hRel_eq_coe_sub (discValue_ne_top_of_H ⟨B, hB⟩ h2 (hα_mem (φ (rk n))) i)
          (hz_nt (αs (φ (rk n))) (hα_mem (φ (rk n))))).symm
      · exact hrk_mono.tendsto_atTop.eventually (hf_ev i)
    -- Prove properties for ANY associated h
    have hassoc_props : ∀ h : S → ℝ, IsAssociated M z fam f h →
        IsAverageOptimal M f.toPolicy ∧
        (∀ i, ((M.C i (f.1 i) : ℝ) : EReal) + wsum (M.P i (f.1 i)) h ≤ (((J : ℝ) + h i : ℝ) : EReal)) ∧
        ∀ i, Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * expReal M f.toPolicy i n h) atTop (𝓝 0) := by
      intro h hh_assoc
      obtain ⟨_, βs, hβ_mem, hβ_lim, hh_lim, hf_β⟩ := hh_assoc
      have hh_islim : IsLimitFunction M z h :=
        ⟨hz_nt, βs, id, hβ_mem, hβ_lim, strictMono_id, hh_lim⟩
      have hh_lo : ∀ j, -Lf j ≤ h j := fun j =>
        EReal.coe_le_coe_iff.mp (ge_of_tendsto (hh_lim j)
          (Eventually.of_forall fun n => h3.2 (βs n) (hβ_mem n) j))
      have hβ_nhdsLT : Tendsto βs atTop (𝓝[<] 1) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hβ_lim
          (Eventually.of_forall fun n => (hβ_mem n).2)
      have hf_acoi : ∀ i, ((M.C i (f.1 i) : ℝ) : EReal) + wsum (M.P i (f.1 i)) h ≤
          (((J : ℝ) + h i : ℝ) : EReal) := fun i => by
        refine acoi_step_of_doe_le ⟨B, hB⟩ h2 h3 h4 βs hβ_mem hβ_lim J
          (hz_tendsto.comp hβ_nhdsLT) h hh_lim i (f.1 i) (f.2 i) ?_
        filter_upwards [hf_β i] with n hn
        rw [← hn, hfam (βs n) (hβ_mem n) i]
        exact inf'_doeQ_le_discValue M (βs n) i
      obtain ⟨hopt, _, hzero⟩ := h_stat_opt h hh_islim hh_lo f hf_acoi
      exact ⟨hopt, hf_acoi, hzero⟩
    exact ⟨(hassoc_props hf_h hfh_assoc).1, ⟨hf_h, hfh_assoc⟩,
      fun h hh => ⟨(hassoc_props h hh).2.1, (hassoc_props h hh).2.2⟩⟩



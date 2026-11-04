-- Prove2me | solution 1 for SelfStructIS.LogEff.lemma_A_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:31:43.544779+00:00
-- url     : https://prove2.me/submissions/199b0d78-4f80-408b-b2f0-5d8f06665782

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
import Definitions.Def_SelfStructIS_LogEff_Tail

open MeasureTheory Filter Topology

namespace SSISA9

open SelfStructIS.LogEff

lemma hazard_nonneg {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (i : Fin d)
    (s : ℝ) : 0 ≤ hazard μ i s := by
  unfold hazard survival
  have h0 : 0 ≤ (μ {y | s < y i}).toReal := ENNReal.toReal_nonneg
  have h1 : (μ {y | s < y i}).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have := Real.log_nonpos h0 h1
  linarith

/-- Uniform smallness of `L` near the origin, integer scale. -/
lemma claim_int {d : ℕ} (L Lstar : (Fin d → ℝ) → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hb : ∀ (xs : ℕ → Fin d → ℝ) (x : Fin d → ℝ), (∀ n i, 0 ≤ xs n i) →
      Tendsto xs atTop (𝓝 x) →
      Tendsto (fun n : ℕ => L ((n : ℝ) • xs n) / (n : ℝ) ^ ρ) atTop (𝓝 (Lstar x))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ w : Fin d → ℝ, (∀ i, 0 ≤ w i) → ‖w‖ ≤ δ →
      L ((n : ℝ) • w) < (n : ℝ) ^ ρ := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ ρ) atTop atTop :=
    (tendsto_rpow_atTop hρ).comp tendsto_natCast_atTop_atTop
  have hL0 : Lstar 0 = 0 := by
    have h1 := hb (fun _ => 0) 0 (fun _ _ => le_rfl) tendsto_const_nhds
    simp only [smul_zero] at h1
    have h2 : Tendsto (fun n : ℕ => L 0 / (n : ℝ) ^ ρ) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hpow
    exact tendsto_nhds_unique h1 h2
  by_contra hcon
  push Not at hcon
  have hfreq : ∀ k : ℕ, ∃ᶠ n : ℕ in atTop, ∃ w : Fin d → ℝ, (∀ i, 0 ≤ w i) ∧
      ‖w‖ ≤ 1 / ((k : ℝ) + 1) ∧ (n : ℝ) ^ ρ ≤ L ((n : ℝ) • w) := by
    intro k
    exact hcon (1 / ((k : ℝ) + 1)) (by positivity)
  obtain ⟨φ, hφ, hP⟩ := extraction_forall_of_frequently hfreq
  choose w hw0 hwn hwL using hP
  classical
  let xs : ℕ → Fin d → ℝ := fun n => if h : ∃ k, φ k = n then w (Classical.choose h) else 0
  have hxsφ : ∀ k, xs (φ k) = w k := by
    intro k
    have h : ∃ k', φ k' = φ k := ⟨k, rfl⟩
    simp only [xs, dif_pos h]
    rw [hφ.injective (Classical.choose_spec h)]
  have hxs0 : ∀ n i, 0 ≤ xs n i := by
    intro n i
    simp only [xs]
    split_ifs with h
    · exact hw0 _ i
    · simp
  have hxs_t : Tendsto xs atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
    refine ⟨φ K + 1, fun n hn => ?_⟩
    rw [dist_zero_right]
    simp only [xs]
    split_ifs with h
    · have hk := Classical.choose_spec h
      set k := Classical.choose h
      have hkK : K < k := by
        by_contra hle
        push Not at hle
        have := hφ.monotone hle
        omega
      calc ‖w k‖ ≤ 1 / ((k : ℝ) + 1) := hwn k
        _ ≤ 1 / ((K : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          have : (K : ℝ) < k := by exact_mod_cast hkK
          linarith
        _ < ε := hK
    · simpa using hε
  have hlim := hb xs 0 hxs0 hxs_t
  rw [hL0] at hlim
  have hlim' := hlim.comp hφ.tendsto_atTop
  have hge : ∀ᶠ k in atTop, (1 : ℝ) ≤ ((fun n : ℕ => L ((n : ℝ) • xs n) / (n : ℝ) ^ ρ) ∘ φ) k := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    simp only [Function.comp, hxsφ]
    have hφk : 1 ≤ φ k := le_trans hk (hφ.id_le k)
    have hpos : 0 < (φ k : ℝ) ^ ρ := Real.rpow_pos_of_pos (by exact_mod_cast hφk) _
    rw [le_div_iff₀ hpos, one_mul]
    exact hwL k
  have := ge_of_tendsto hlim' hge
  linarith

end SSISA9

open SelfStructIS.LogEff in
theorem solution (d : ℕ) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (α : Fin d → ℝ) (h31 : Assumption31 μ α)
    (L Lstar : (Fin d → ℝ) → ℝ) (ρ : ℝ) (h21 : Assumption21 μ L ρ Lstar) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ u in atTop, ∀ q : Fin d → ℝ, (∀ i, 0 < q i) →
      qvec μ (tfun μ ρ u • q) ∈ μ.support → 1 ≤ Lu μ L ρ u q → γ < ‖q‖ := by
  obtain ⟨hρ, ha, hb, -⟩ := h21
  obtain ⟨δ0, hδ0, hN⟩ := SSISA9.claim_int L Lstar ρ hρ hb
  obtain ⟨N, hN⟩ := eventually_atTop.1 hN
  -- real-scale version
  have hreal : ∀ v : ℝ, (N : ℝ) + 1 ≤ v → ∀ z : Fin d → ℝ, (∀ i, 0 ≤ z i) → ‖z‖ ≤ δ0 / 2 →
      L (v • z) < v ^ ρ := by
    intro v hv z hz0 hz
    have hv1 : 1 ≤ v := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    set n := ⌊v⌋₊ with hn
    have hnv : (n : ℝ) ≤ v := Nat.floor_le (by linarith)
    have hvn : v < n + 1 := Nat.lt_floor_add_one v
    have hNn : N ≤ n := Nat.le_floor (by linarith)
    have hn1 : 1 ≤ n := Nat.le_floor (by simpa using hv1)
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < n := by linarith
    have hratio : v / n ≤ 2 := by rw [div_le_iff₀ hnpos]; linarith
    have hratio0 : 0 ≤ v / n := by positivity
    have hw0 : ∀ i, 0 ≤ ((v / n) • z) i := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hratio0 (hz0 i)
    have hw : ‖(v / n) • z‖ ≤ δ0 := by
      rw [norm_smul, Real.norm_of_nonneg hratio0]
      calc v / n * ‖z‖ ≤ 2 * (δ0 / 2) :=
            mul_le_mul hratio hz (norm_nonneg _) (by norm_num)
        _ = δ0 := by ring
    have h1 := hN n hNn _ hw0 hw
    rw [smul_smul, mul_div_cancel₀ _ hnpos.ne'] at h1
    exact lt_of_lt_of_le h1 (Real.rpow_le_rpow hnpos.le hnv hρ.le)
  set δ1 := min (δ0 / 2) 1 with hδ1
  have hδ1pos : 0 < δ1 := lt_min (by linarith) one_pos
  have hδ1le : δ1 ≤ 1 := min_le_right _ _
  set S := ∑ i, α i with hS
  set γ := δ1 ^ S / 2 with hγ
  have hγpos : 0 < γ := by positivity
  have hγi : ∀ i, γ < δ1 ^ α i := by
    intro i
    have hSi : α i ≤ S := Finset.single_le_sum (f := α) (fun j _ => (h31 j).1.le)
      (Finset.mem_univ i)
    have := Real.rpow_le_rpow_of_exponent_ge hδ1pos hδ1le hSi
    have : 0 < δ1 ^ S := by positivity
    rw [hγ]; linarith
  refine ⟨γ, hγpos, ?_⟩
  have hv : Tendsto (fun u : ℝ => u ^ (1 / ρ)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have hRV : ∀ i, ∀ᶠ v : ℝ in atTop, γ * hazard μ i v ≤ hazard μ i (δ1 * v) := by
    intro i
    have h1 := ((h31 i).2.2.2.2 δ1 hδ1pos).eventually (lt_mem_nhds (hγi i))
    filter_upwards [h1, (h31 i).2.2.2.1] with v hv1 hv2
    rw [lt_div_iff₀ hv2] at hv1
    exact hv1.le
  filter_upwards [eventually_gt_atTop 0, ha,
    hv.eventually (eventually_ge_atTop ((N : ℝ) + 1)),
    eventually_all.2 fun i => hv.eventually (hRV i)] with u hu hau hvN hRVu
  intro q hq hsupp hLu
  set v := u ^ (1 / ρ) with hvdef
  have hvpos : 0 < v := Real.rpow_pos_of_pos hu _
  set t := tfun μ ρ u with htdef
  set x := qvec μ (t • q) with hxdef
  have huL : u ≤ L x := by
    have : 1 ≤ u⁻¹ * L x := hLu
    rw [le_inv_mul_iff₀ hu, mul_one] at this
    exact this
  have hx0 := hau x hsupp huL
  by_contra hqγ
  push Not at hqγ
  have ht0 : 0 ≤ t := by
    show 0 ≤ ⨅ i, hazard μ i v
    rcases isEmpty_or_nonempty (Fin d) with h | h
    · simp [Real.iInf_of_isEmpty]
    · exact le_ciInf fun i => SSISA9.hazard_nonneg μ i v
  have hxle : ∀ i, x i ≤ δ1 * v := by
    intro i
    have htle : t ≤ hazard μ i v := by
      show (⨅ k, hazard μ k v) ≤ _
      exact ciInf_le (Finite.bddBelow_range _) i
    have hqi : q i ≤ γ := le_trans (le_trans (le_abs_self _) (norm_le_pi_norm q i)) hqγ
    have ha' : t * q i ≤ hazard μ i (δ1 * v) :=
      calc t * q i ≤ t * γ := mul_le_mul_of_nonneg_left hqi ht0
        _ = γ * t := mul_comm _ _
        _ ≤ γ * hazard μ i v := mul_le_mul_of_nonneg_left htle hγpos.le
        _ ≤ _ := hRVu i
    show qinv μ i ((t • q) i) ≤ δ1 * v
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold qinv
    by_cases hbdd : BddBelow {y : ℝ | t * q i ≤ hazard μ i y}
    · exact csInf_le hbdd ha'
    · rw [Real.sInf_of_not_bddBelow hbdd]; positivity
  have hz0 : ∀ i, 0 ≤ (v⁻¹ • x) i := fun i => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hvpos.le) (hx0 i)
  have hz : ‖v⁻¹ • x‖ ≤ δ0 / 2 := by
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
    rw [Real.norm_of_nonneg (hz0 i)]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_le_iff₀ hvpos]
    calc x i ≤ δ1 * v := hxle i
      _ ≤ (δ0 / 2) * v := mul_le_mul_of_nonneg_right (min_le_left _ _) hvpos.le
      _ = v * (δ0 / 2) := mul_comm _ _
  have hlt := hreal v hvN _ hz0 hz
  rw [smul_inv_smul₀ hvpos.ne'] at hlt
  have hvρ : v ^ ρ = u := by
    rw [hvdef, ← Real.rpow_mul hu.le, one_div, inv_mul_cancel₀ hρ.ne', Real.rpow_one]
  rw [hvρ] at hlt
  linarith

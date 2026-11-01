-- Prove2me | solution 1 for SRPTManyServer.Collapse.erlang_integral_limit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:56:21.240149+00:00
-- url     : https://prove2.me/submissions/075fe481-f118-42d2-872c-9bc32e7bede2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang

open MeasureTheory Set Real

lemma srpt_int_pow_exp (k : ℕ) :
    ∫ t in Ioi (0:ℝ), t ^ k * Real.exp (-t) = (Nat.factorial k : ℝ) := by
  have h := Real.Gamma_eq_integral (s := (k:ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  simp only [add_sub_cancel_right, Real.rpow_natCast]
  ring

lemma srpt_intble_pow_exp (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-t)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (k:ℝ) + 1) (by positivity)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [add_sub_cancel_right, Real.rpow_natCast]
  ring

lemma srpt_int_expand (r : ℝ) (hr : 0 < r) (C : ℕ) :
    ∫ t in Ioi (0:ℝ), (1 + t / r) ^ C * Real.exp (-t) =
      ∑ m ∈ Finset.range (C + 1), (Nat.choose C m : ℝ) / r ^ m * (Nat.factorial m : ℝ) := by
  have hexp : ∀ t : ℝ, (1 + t / r) ^ C * Real.exp (-t) =
      ∑ m ∈ Finset.range (C + 1), ((Nat.choose C m : ℝ) / r ^ m) * (t ^ m * Real.exp (-t)) := by
    intro t
    rw [add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [div_pow]; field_simp; ring
  simp_rw [hexp]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [integral_const_mul, srpt_int_pow_exp]
  · intro m _
    exact (srpt_intble_pow_exp m).const_mul _

theorem srpt_erlang_identity :
    (∀ (r : ℝ), 0 < r → ∀ C : ℕ,
      KellyStochasticNetworks.erlang r C =
        (∫ t in Set.Ioi (0 : ℝ), (1 + t / r) ^ C * Real.exp (-t))⁻¹) ∧
    (∀ C : ℕ, 1 ≤ C →
      KellyStochasticNetworks.erlang (C : ℝ) C =
        (∫ t in Set.Ioi (0 : ℝ), (1 + t / (C : ℝ)) ^ C * Real.exp (-t))⁻¹) := by
  have main : ∀ (r : ℝ), 0 < r → ∀ C : ℕ,
      KellyStochasticNetworks.erlang r C =
        (∫ t in Set.Ioi (0 : ℝ), (1 + t / r) ^ C * Real.exp (-t))⁻¹ := by
    intro r hr C
    rw [srpt_int_expand r hr C, KellyStochasticNetworks.erlang]
    have key : (∑ m ∈ Finset.range (C + 1), (Nat.choose C m : ℝ) / r ^ m * (Nat.factorial m : ℝ))
        * (r ^ C / (Nat.factorial C : ℝ)) =
        ∑ j ∈ Finset.range (C + 1), r ^ j / (Nat.factorial j : ℝ) := by
      rw [Finset.sum_mul]
      conv_rhs => rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hmC : m ≤ C := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hsub : C + 1 - 1 - m = C - m := by omega
      rw [hsub]
      have hfac := Nat.choose_mul_factorial_mul_factorial hmC
      have hfac' : (Nat.choose C m : ℝ) * (Nat.factorial m : ℝ) * (Nat.factorial (C - m) : ℝ)
          = (Nat.factorial C : ℝ) := by exact_mod_cast hfac
      have hrC : r ^ C = r ^ m * r ^ (C - m) := by rw [← pow_add]; congr 1; omega
      have h1 : (Nat.factorial C : ℝ) ≠ 0 := by positivity
      have h2 : (Nat.factorial (C - m) : ℝ) ≠ 0 := by positivity
      have h3 : r ^ m ≠ 0 := by positivity
      have h4 : (Nat.choose C m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmC).ne'
      rw [hrC, ← hfac']
      field_simp
    have hpos : 0 < r ^ C / (Nat.factorial C : ℝ) := by positivity
    rw [← key]
    have hI : (∑ m ∈ Finset.range (C + 1), (Nat.choose C m : ℝ) / r ^ m * (Nat.factorial m : ℝ))
        ≠ 0 := by
      apply ne_of_gt
      refine Finset.sum_pos' (fun m _ => by positivity) ⟨0, by simp, by simp⟩
    field_simp
  refine ⟨main, fun C hC => main (C : ℝ) (by exact_mod_cast hC) C⟩

lemma srpt_intble_f (r : ℝ) (C : ℕ) :
    IntegrableOn (fun t : ℝ => (1 + t / r) ^ C * Real.exp (-t)) (Ioi 0) := by
  have hexp : (fun t : ℝ => (1 + t / r) ^ C * Real.exp (-t)) = fun t =>
      ∑ m ∈ Finset.range (C + 1), ((Nat.choose C m : ℝ) / r ^ m) * (t ^ m * Real.exp (-t)) := by
    funext t
    rw [add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [div_pow]; ring
  rw [hexp]
  exact integrable_finset_sum _ (fun m _ => (srpt_intble_pow_exp m).const_mul _)

lemma srpt_lower (s : ℕ) (hs : 1 ≤ s) :
    Real.sqrt ((s:ℝ) / 2) / 2 ≤ ∫ t in Ioi (0:ℝ), (1 + t / (s:ℝ)) ^ s * Real.exp (-t) := by
  set a := Real.sqrt ((s:ℝ) / 2) with ha
  have hs' : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hspos : (0:ℝ) < s := by linarith
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = (s:ℝ) / 2 := Real.sq_sqrt (by positivity)
  have has : a ≤ s := by nlinarith
  have hpt : ∀ t ∈ Ioc (0:ℝ) a, (1/2 : ℝ) ≤ (1 + t / (s:ℝ)) ^ s * Real.exp (-t) := by
    intro t ht
    obtain ⟨ht0, hta⟩ := ht
    have hts : t ≤ s := hta.trans has
    have h1 : 0 ≤ 1 - t / s := by
      rw [sub_nonneg, div_le_one hspos]; exact hts
    have h2 : (1 - t / s) ^ s ≤ Real.exp (-t) := by
      have h3 : 1 - t / s ≤ Real.exp (-(t / s)) := by
        have := Real.add_one_le_exp (-(t / s)); linarith
      calc (1 - t / s) ^ s ≤ (Real.exp (-(t / s))) ^ s := pow_le_pow_left₀ h1 h3 s
        _ = Real.exp (-t) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
    have h4 : (1 + t / (s:ℝ)) ^ s * (1 - t / s) ^ s ≤ (1 + t / (s:ℝ)) ^ s * Real.exp (-t) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : (1 + t / (s:ℝ)) ^ s * (1 - t / s) ^ s = (1 + (-(t / s) ^ 2)) ^ s := by
      rw [← mul_pow]; ring
    have hb : (-2:ℝ) ≤ -(t / s) ^ 2 := by
      have : (t / s) ≤ 1 := by rw [div_le_one hspos]; exact hts
      have : 0 ≤ t / s := by positivity
      nlinarith
    have h6 := one_add_mul_le_pow hb s
    have h7 : (s:ℝ) * (-(t / s) ^ 2) = -(t ^ 2 / s) := by field_simp
    have h8 : t ^ 2 ≤ a ^ 2 := by nlinarith
    have h9 : t ^ 2 / s ≤ 1 / 2 := by
      rw [div_le_iff₀ hspos]; nlinarith
    linarith
  calc a / 2 = ∫ t in Ioc (0:ℝ) a, (1/2 : ℝ) := by
        rw [setIntegral_const]; simp [Real.volume_Ioc, ha0]; ring
    _ ≤ ∫ t in Ioc (0:ℝ) a, (1 + t / (s:ℝ)) ^ s * Real.exp (-t) := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc hpt
        · exact integrableOn_const (by simp [Real.volume_Ioc]) (by simp)
        · exact (srpt_intble_f (s:ℝ) s).mono_set Ioc_subset_Ioi_self
    _ ≤ ∫ t in Ioi (0:ℝ), (1 + t / (s:ℝ)) ^ s * Real.exp (-t) := by
        refine setIntegral_mono_set (srpt_intble_f (s:ℝ) s) ?_ ?_
        · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
          intro t ht
          have : 0 < t := ht
          positivity
        · exact Filter.Eventually.of_forall Ioc_subset_Ioi_self

open Filter Topology in
theorem solution :
    Tendsto (fun s : ℕ => (∫ t in Set.Ioi (0 : ℝ), (1 + t / (s : ℝ)) ^ s * Real.exp (-t))⁻¹)
      atTop (𝓝 0) ∧
    Tendsto (fun s : ℕ => KellyStochasticNetworks.erlang (s : ℝ) s) atTop (𝓝 0) := by
  have hsq : Tendsto (fun s : ℕ => Real.sqrt ((s:ℝ) / 2) / 2) atTop atTop := by
    refine Tendsto.atTop_div_const (by norm_num) ?_
    refine Real.tendsto_sqrt_atTop.comp ?_
    exact Tendsto.atTop_div_const (by norm_num) tendsto_natCast_atTop_atTop
  have hI : Tendsto (fun s : ℕ => ∫ t in Set.Ioi (0 : ℝ), (1 + t / (s : ℝ)) ^ s * Real.exp (-t))
      atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hsq
    filter_upwards [eventually_ge_atTop 1] with s hs
    exact srpt_lower s hs
  have h1 := hI.inv_tendsto_atTop
  refine ⟨h1, ?_⟩
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with s hs
  exact ((srpt_erlang_identity).2 s hs).symm

-- Prove2me | solution 1 for ScheduledQueue.Diffusion.maximal_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T18:08:04.808978+00:00
-- url     : https://prove2.me/submissions/7be6698a-e103-40f2-bf94-4fe4908699a5

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting
import Theorems.Thm_ScheduledQueue_Diffusion_early_exp_moment
import Theorems.Thm_ScheduledQueue_Diffusion_late_exp_moment
import Theorems.Thm_ScheduledQueue_Diffusion_increment_moments

open Set Filter Topology MeasureTheory ProbabilityTheory

/-- Chernoff + union bound: logarithmic growth of maxima of identically distributed
variables with all exponential moments. -/
lemma SQM_maxlog {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℕ) (Y0 : Ω → ℕ) (hid : ∀ k, IdentDistrib (Y k) Y0 P P)
    (hexp : ∀ θ : ℝ, 0 < θ → ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (Y0 ω : ℝ))) ∂P < ⊤)
    (s : ℕ → Finset ℕ) (hs : ∀ n, (s n).card ≤ n + 2) :
    TendstoInMeasure P (fun (n : ℕ) ω => (Real.log n)⁻¹ * (((s n).sup fun k => Y k ω : ℕ) : ℝ))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  set θ : ℝ := 2 / ε with hθ
  have hθ0 : 0 < θ := by positivity
  set C : ENNReal := ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (Y0 ω : ℝ))) ∂P with hC
  have hCt : C ≠ ⊤ := (hexp θ hθ0).ne
  have hY0m : AEMeasurable Y0 P := (hid 0).aemeasurable_snd
  -- Markov bound for a single variable
  have hmarkov : ∀ x : ℝ, P {ω | x ≤ (Y0 ω : ℝ)} ≤ C * ENNReal.ofReal (Real.exp (-(θ * x))) := by
    intro x
    have hf : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (θ * (Y0 ω : ℝ)))) P := by
      have : Measurable (fun m : ℕ => ENNReal.ofReal (Real.exp (θ * (m : ℝ)))) :=
        measurable_from_nat
      exact this.comp_aemeasurable hY0m
    have h1 := mul_meas_ge_le_lintegral₀ hf (ENNReal.ofReal (Real.exp (θ * x)))
    have hsub : {ω | x ≤ (Y0 ω : ℝ)} ⊆
        {ω | ENNReal.ofReal (Real.exp (θ * x)) ≤ ENNReal.ofReal (Real.exp (θ * (Y0 ω : ℝ)))} := by
      intro ω hω
      simp only [mem_setOf_eq] at hω ⊢
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hθ0.le))
    have h2 : ENNReal.ofReal (Real.exp (θ * x)) * P {ω | x ≤ (Y0 ω : ℝ)} ≤ C :=
      le_trans (mul_le_mul_right (measure_mono hsub) _) h1
    have hpos : ENNReal.ofReal (Real.exp (θ * x)) ≠ 0 := by
      simp [Real.exp_pos]
    have hfin : ENNReal.ofReal (Real.exp (θ * x)) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc P {ω | x ≤ (Y0 ω : ℝ)}
        = (ENNReal.ofReal (Real.exp (θ * x)))⁻¹ *
            (ENNReal.ofReal (Real.exp (θ * x)) * P {ω | x ≤ (Y0 ω : ℝ)}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hpos hfin, one_mul]
      _ ≤ (ENNReal.ofReal (Real.exp (θ * x)))⁻¹ * C := mul_le_mul_right h2 _
      _ = C * ENNReal.ofReal (Real.exp (-(θ * x))) := by
          rw [mul_comm, Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]
  -- the bound for large n
  have hbound : ∀ n : ℕ, 2 ≤ n →
      P {ω | ε ≤ dist ((Real.log n)⁻¹ * (((s n).sup fun k => Y k ω : ℕ) : ℝ)) 0} ≤
        ENNReal.ofReal (3 / n) * C := by
    intro n hn
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    set x : ℝ := ε * Real.log n with hx
    have hx0 : 0 < x := by positivity
    have hsub : {ω | ε ≤ dist ((Real.log n)⁻¹ * (((s n).sup fun k => Y k ω : ℕ) : ℝ)) 0} ⊆
        ⋃ k ∈ s n, {ω | x ≤ (Y k ω : ℝ)} := by
      intro ω hω
      simp only [mem_setOf_eq, Real.dist_eq, sub_zero] at hω
      rw [abs_of_nonneg (by positivity), inv_mul_eq_div, le_div_iff₀ hlog] at hω
      by_contra hc
      simp only [mem_iUnion, mem_setOf_eq, not_exists, not_le] at hc
      have hlt : ((s n).sup fun k => Y k ω) < ⌈x⌉₊ := by
        rw [Finset.sup_lt_iff (by simpa using Nat.ceil_pos.mpr hx0)]
        intro k hk
        exact Nat.lt_ceil.mpr (hc k hk)
      have := Nat.lt_ceil.mp hlt
      rw [mul_comm] at hω
      linarith
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    calc P {ω | ε ≤ dist ((Real.log n)⁻¹ * (((s n).sup fun k => Y k ω : ℕ) : ℝ)) 0}
        ≤ P (⋃ k ∈ s n, {ω | x ≤ (Y k ω : ℝ)}) := measure_mono hsub
      _ ≤ ∑ k ∈ s n, P {ω | x ≤ (Y k ω : ℝ)} := measure_biUnion_finset_le _ _
      _ = ∑ k ∈ s n, P {ω | x ≤ (Y0 ω : ℝ)} := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          have hm : MeasurableSet {m : ℕ | x ≤ (m : ℝ)} := MeasurableSet.of_discrete
          exact (hid k).measure_mem_eq hm
      _ = (s n).card * P {ω | x ≤ (Y0 ω : ℝ)} := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n + 2 : ℕ) : ENNReal) * (C * ENNReal.ofReal (Real.exp (-(θ * x)))) := by
          gcongr
          · exact_mod_cast hs n
          · exact hmarkov x
      _ = ENNReal.ofReal ((n + 2 : ℝ) * Real.exp (-(θ * x))) * C := by
          rw [ENNReal.ofReal_mul (by positivity)]
          have : ((n + 2 : ℕ) : ENNReal) = ENNReal.ofReal ((n : ℝ) + 2) := by
            rw [← ENNReal.ofReal_natCast]; push_cast; rfl
          rw [this]; ring
      _ ≤ ENNReal.ofReal (3 / n) * C := by
          gcongr
          have hexp : Real.exp (-(θ * x)) = ((n : ℝ) ^ 2)⁻¹ := by
            rw [hx, hθ]
            have : 2 / ε * (ε * Real.log n) = 2 * Real.log n := by field_simp
            rw [this, ← Real.log_rpow hn0, Real.exp_neg, Real.exp_log (by positivity)]
            norm_cast
          rw [hexp]
          rw [div_eq_mul_inv, show ((n : ℝ) ^ 2)⁻¹ = (n : ℝ)⁻¹ * (n : ℝ)⁻¹ by ring, ← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [← div_eq_mul_inv, div_le_iff₀ hn0]
          have : (2 : ℝ) ≤ n := by exact_mod_cast hn
          linarith
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (3 / n) * C) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (3 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 3
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (3 / n)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal h1
      simpa using this
    have := ENNReal.Tendsto.mul_const h2 (Or.inr hCt)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun n => bot_le)) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact hbound n hn

lemma SQM_encard_meas {α : Type*} [MeasurableSpace α] (A : ℤ → Set α)
    (hA : ∀ j, MeasurableSet (A j)) : Measurable (fun p => {j : ℤ | p ∈ A j}.encard) := by
  set Ψ : α → ENNReal := fun p => ∑' j : ℤ, {j : ℤ | p ∈ A j}.indicator 1 j with hΨ
  have hΨm : Measurable Ψ := by
    refine Measurable.ennreal_tsum (fun j => ?_)
    have : (fun p : α => {j : ℤ | p ∈ A j}.indicator (1 : ℤ → ENNReal) j) = (A j).indicator 1 := by
      funext p; simp [Set.indicator]
    rw [this]
    exact measurable_const.indicator (hA j)
  have hΨeq : ∀ p, Ψ p = (({j : ℤ | p ∈ A j}.encard : ℕ∞) : ENNReal) := by
    intro p
    simp only [hΨ]
    rw [← tsum_subtype]; simp only [Pi.one_apply]; rw [ENNReal.tsum_set_one]
  apply measurable_to_countable'
  intro n
  have : (fun p => {j : ℤ | p ∈ A j}.encard) ⁻¹' {n} = Ψ ⁻¹' {(n : ENNReal)} := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, hΨeq, ENat.toENNReal_inj]
  rw [this]
  exact hΨm (measurableSet_singleton _)

lemma SQM_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) (k : ℤ) :
    IdentDistrib (fun ω => (U ω, fun j => ξ (j + k) ω)) (fun ω => (U ω, fun j => ξ j ω)) P P := by
  have hshift : Measurable (fun (x : ℤ → ℝ) (j : ℤ) => x (j + k)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (j + k))
  have hUm : AEMeasurable U P := hin.uniform.aemeasurable
  have hξm : Measurable (fun ω j => ξ j ω) := measurable_pi_lambda _ hin.measurable
  have hξkm : Measurable (fun ω j => ξ (j + k) ω) := hshift.comp hξm
  have hind_k : IndepFun U (fun ω j => ξ (j + k) ω) P :=
    hin.indep_shift.comp measurable_id hshift
  have hbij : Function.Bijective (fun j : ℤ => j + k) := (Equiv.addRight k).bijective
  have hiind : iIndepFun (fun j => ξ (j + k)) P := hin.indep.precomp hbij.injective
  have hmap_k : P.map (fun ω j => ξ (j + k) ω) = P.map (fun ω j => ξ j ω) := by
    rw [hiind.map_fun_eq_infinitePi_map (fun j => hin.measurable _),
      hin.indep.map_fun_eq_infinitePi_map hin.measurable]
    congr 1
    funext j
    rw [(hin.identDistrib (j + k)).map_eq, (hin.identDistrib j).map_eq]
  refine ⟨hUm.prodMk hξkm.aemeasurable, hUm.prodMk hξm.aemeasurable, ?_⟩
  rw [(indepFun_iff_map_prod_eq_prod_map_map hUm hξkm.aemeasurable).mp hind_k,
    (indepFun_iff_map_prod_eq_prod_map_map hUm hξm.aemeasurable).mp hin.indep_shift, hmap_k]

open ScheduledQueue.Diffusion in
lemma SQM_early_shift {Ω : Type*} (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (k : ℤ) (ω : Ω) :
    early h ξ U ((k : ℝ) * h) ω =
      {m : ℤ | (U ω, fun j => ξ (j + k) ω) ∈
        {p : ℝ × (ℤ → ℝ) | (0:ℝ) < m * h + p.1 * h ∧ m * h + p.1 * h + p.2 m ≤ 0}}.encard := by
  simp only [early, mem_setOf_eq]
  have : {i : ℤ | (k : ℝ) * h < i * h + U ω * h ∧ i * h + U ω * h + ξ i ω ≤ k * h} =
      (fun m : ℤ => m + k) '' {m : ℤ | (0:ℝ) < m * h + U ω * h ∧ m * h + U ω * h + ξ (m + k) ω ≤ 0} := by
    ext j
    simp only [mem_setOf_eq, mem_image]
    constructor
    · intro hj
      refine ⟨j - k, ?_, by ring⟩
      have e : j - k + k = j := by ring
      rw [e]; push_cast
      constructor <;> nlinarith [hj.1, hj.2]
    · rintro ⟨m, hm, rfl⟩
      push_cast
      constructor <;> nlinarith [hm.1, hm.2]
  rw [this, (add_left_injective k).encard_image]

open ScheduledQueue.Diffusion in
lemma SQM_late_shift {Ω : Type*} (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (k : ℤ) (ω : Ω) :
    late h ξ U ((k : ℝ) * h) ω =
      {m : ℤ | (U ω, fun j => ξ (j + k) ω) ∈
        {p : ℝ × (ℤ → ℝ) | m * h + p.1 * h < 0 ∧ (0:ℝ) ≤ m * h + p.1 * h + p.2 m}}.encard := by
  simp only [late, mem_setOf_eq]
  have : {i : ℤ | i * h + U ω * h < (k : ℝ) * h ∧ (k : ℝ) * h ≤ i * h + U ω * h + ξ i ω} =
      (fun m : ℤ => m + k) '' {m : ℤ | m * h + U ω * h < 0 ∧ (0:ℝ) ≤ m * h + U ω * h + ξ (m + k) ω} := by
    ext j
    simp only [mem_setOf_eq, mem_image]
    constructor
    · intro hj
      refine ⟨j - k, ?_, by ring⟩
      have e : j - k + k = j := by ring
      rw [e]; push_cast
      constructor <;> nlinarith [hj.1, hj.2]
    · rintro ⟨m, hm, rfl⟩
      push_cast
      constructor <;> nlinarith [hm.1, hm.2]
  rw [this, (add_left_injective k).encard_image]

open ScheduledQueue.Diffusion in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    TendstoInMeasure P
        (fun (n : ℕ) ω => (Real.log n)⁻¹ *
          (((Finset.Icc 1 (n + 1)).sup fun k => (early h ξ U ((k : ℝ) * h) ω).toNat : ℕ) : ℝ))
        atTop (fun _ => 0) ∧
    TendstoInMeasure P
        (fun (n : ℕ) ω => (Real.log n)⁻¹ *
          (((Finset.range (n + 1)).sup fun k => (late h ξ U ((k : ℝ) * h) ω).toNat : ℕ) : ℝ))
        atTop (fun _ => 0) ∧
    TendstoInMeasure P
        (fun (n : ℕ) ω => (Real.log n)⁻¹ *
          (((Finset.range (n + 2)).sup fun k =>
              (arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h) ω).toNat : ℕ) : ℝ))
        atTop (fun _ => 0) := by
  have hEm : Measurable (fun p : ℝ × (ℤ → ℝ) => {m : ℤ | p ∈
      {p : ℝ × (ℤ → ℝ) | (0:ℝ) < m * h + p.1 * h ∧ m * h + p.1 * h + p.2 m ≤ 0}}.encard) := by
    apply SQM_encard_meas
    intro m
    have hf1 : Measurable (fun p : ℝ × (ℤ → ℝ) => (m : ℝ) * h + p.1 * h) := by fun_prop
    have hf2 : Measurable (fun p : ℝ × (ℤ → ℝ) => (m : ℝ) * h + p.1 * h + p.2 m) := by fun_prop
    exact (measurableSet_lt measurable_const hf1).inter (measurableSet_le hf2 measurable_const)
  have hLm : Measurable (fun p : ℝ × (ℤ → ℝ) => {m : ℤ | p ∈
      {p : ℝ × (ℤ → ℝ) | m * h + p.1 * h < 0 ∧ (0:ℝ) ≤ m * h + p.1 * h + p.2 m}}.encard) := by
    apply SQM_encard_meas
    intro m
    have hf1 : Measurable (fun p : ℝ × (ℤ → ℝ) => (m : ℝ) * h + p.1 * h) := by fun_prop
    have hf2 : Measurable (fun p : ℝ × (ℤ → ℝ) => (m : ℝ) * h + p.1 * h + p.2 m) := by fun_prop
    exact (measurableSet_lt hf1 measurable_const).inter (measurableSet_le measurable_const hf2)
  have htn : Measurable (fun x : ℕ∞ => x.toNat) := Measurable.of_discrete
  refine ⟨?_, ?_, ?_⟩
  · refine SQM_maxlog P (fun k ω => (early h ξ U ((k : ℝ) * h) ω).toNat)
      (fun ω => (early h ξ U 0 ω).toNat) (fun k => ?_) (fun θ hθ => ?_)
      (fun n => Finset.Icc 1 (n + 1)) (fun n => by simp)
    · have e1 : (fun ω => (early h ξ U ((k : ℝ) * h) ω).toNat) = (fun x : ℕ∞ => x.toNat) ∘
          (fun p : ℝ × (ℤ → ℝ) => {m : ℤ | p ∈
            {p : ℝ × (ℤ → ℝ) | (0:ℝ) < m * h + p.1 * h ∧ m * h + p.1 * h + p.2 m ≤ 0}}.encard) ∘
          (fun ω => (U ω, fun j => ξ (j + (k : ℤ)) ω)) := by
        funext ω
        have := SQM_early_shift h ξ U (k : ℤ) ω
        simp only [Int.cast_natCast] at this
        simp only [Function.comp_apply, this]
      have e0 : (fun ω => (early h ξ U 0 ω).toNat) = (fun x : ℕ∞ => x.toNat) ∘
          (fun p : ℝ × (ℤ → ℝ) => {m : ℤ | p ∈
            {p : ℝ × (ℤ → ℝ) | (0:ℝ) < m * h + p.1 * h ∧ m * h + p.1 * h + p.2 m ≤ 0}}.encard) ∘
          (fun ω => (U ω, fun j => ξ j ω)) := by
        funext ω; rfl
      rw [e1, e0]
      exact ((SQM_law P ξ U hin (k : ℤ)).comp hEm).comp htn
    · exact lt_of_le_of_lt (ScheduledQueue.Diffusion.early_exp_moment P h hh ξ U hin θ hθ).2
        ENNReal.ofReal_lt_top
  · refine SQM_maxlog P (fun k ω => (late h ξ U ((k : ℝ) * h) ω).toNat)
      (fun ω => (late h ξ U 0 ω).toNat) (fun k => ?_) (fun θ hθ => ?_)
      (fun n => Finset.range (n + 1)) (fun n => by simp)
    · have e1 : (fun ω => (late h ξ U ((k : ℝ) * h) ω).toNat) = (fun x : ℕ∞ => x.toNat) ∘
          (fun p : ℝ × (ℤ → ℝ) => {m : ℤ | p ∈
            {p : ℝ × (ℤ → ℝ) | m * h + p.1 * h < 0 ∧ (0:ℝ) ≤ m * h + p.1 * h + p.2 m}}.encard) ∘
          (fun ω => (U ω, fun j => ξ (j + (k : ℤ)) ω)) := by
        funext ω
        have := SQM_late_shift h ξ U (k : ℤ) ω
        simp only [Int.cast_natCast] at this
        simp only [Function.comp_apply, this]
      have e0 : (fun ω => (late h ξ U 0 ω).toNat) = (fun x : ℕ∞ => x.toNat) ∘
          (fun p : ℝ × (ℤ → ℝ) => {m : ℤ | p ∈
            {p : ℝ × (ℤ → ℝ) | m * h + p.1 * h < 0 ∧ (0:ℝ) ≤ m * h + p.1 * h + p.2 m}}.encard) ∘
          (fun ω => (U ω, fun j => ξ j ω)) := by
        funext ω; rfl
      rw [e1, e0]
      exact ((SQM_law P ξ U hin (k : ℤ)).comp hLm).comp htn
    · exact lt_of_le_of_lt (ScheduledQueue.Diffusion.late_exp_moment P h hh ξ U hin θ hθ).2
        ENNReal.ofReal_lt_top
  · have hinc := ScheduledQueue.Diffusion.increment_moments P h hh ξ U hin
    refine SQM_maxlog P (fun k ω => (arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h) ω).toNat)
      (fun ω => (arrivalsIn h ξ U 0 h ω).toNat) (fun k => ?_) (fun θ hθ => ?_)
      (fun n => Finset.range (n + 2)) (fun n => by simp)
    · exact (hinc.1 k).comp htn
    · exact ((hinc.2 θ hθ).2)

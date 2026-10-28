-- Prove2me | solution 1 for ScheduledQueue.Diffusion.increment_moments
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T18:03:12.509971+00:00
-- url     : https://prove2.me/submissions/1b82b753-8f7b-4889-adc9-a997550bec32

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

open Set Filter Topology MeasureTheory ProbabilityTheory

lemma SQI_tsum_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Integrable Y P) (hYm : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) :
    ∑' k : ℕ, P {ω | (k : ℝ) ≤ Y ω} ≤ ENNReal.ofReal (∫ ω, Y ω ∂P + 1) := by
  have hms : ∀ k : ℕ, MeasurableSet {ω | (k : ℝ) ≤ Y ω} :=
    fun k => measurableSet_le measurable_const hYm
  have hpt : ∀ ω, ∑' k : ℕ, ({ω | (k : ℝ) ≤ Y ω}.indicator (1 : Ω → ENNReal) ω)
      ≤ ENNReal.ofReal (Y ω + 1) := by
    intro ω
    rw [tsum_eq_sum (s := Finset.range (⌊Y ω⌋₊ + 1))]
    · calc ∑ k ∈ Finset.range (⌊Y ω⌋₊ + 1), ({ω | (k : ℝ) ≤ Y ω}.indicator (1 : Ω → ENNReal) ω)
          ≤ ∑ k ∈ Finset.range (⌊Y ω⌋₊ + 1), (1 : ENNReal) := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            simp only [Set.indicator, mem_setOf_eq, Pi.one_apply]
            split_ifs <;> simp
        _ = ((⌊Y ω⌋₊ + 1 : ℕ) : ENNReal) := by simp
        _ ≤ ENNReal.ofReal (Y ω + 1) := by
            rw [← ENNReal.ofReal_natCast]
            apply ENNReal.ofReal_le_ofReal
            push_cast
            linarith [Nat.floor_le (hY0 ω)]
    · intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      have : Y ω < (k : ℝ) := by
        have h1 := Nat.lt_floor_add_one (Y ω)
        have h2 : ((⌊Y ω⌋₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
        push_cast at h2; linarith
      simp [Set.indicator, not_le.mpr this]
  calc ∑' k : ℕ, P {ω | (k : ℝ) ≤ Y ω}
      = ∑' k : ℕ, ∫⁻ ω, ({ω | (k : ℝ) ≤ Y ω}.indicator (1 : Ω → ENNReal) ω) ∂P := by
        congr 1; funext k; rw [lintegral_indicator_one (hms k)]
    _ = ∫⁻ ω, ∑' k : ℕ, ({ω | (k : ℝ) ≤ Y ω}.indicator (1 : Ω → ENNReal) ω) ∂P := by
        rw [lintegral_tsum]
        intro k
        exact (measurable_const.indicator (hms k)).aemeasurable
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Y ω + 1) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (∫ ω, (Y ω + 1) ∂P) := by
        have hI : Integrable (fun ω => Y ω + 1) P := hY.add (integrable_const 1)
        rw [ofReal_integral_eq_lintegral_ofReal hI
          (Eventually.of_forall (fun ω => by have := hY0 ω; simp only [Pi.zero_apply]; linarith))]
    _ = ENNReal.ofReal (∫ ω, Y ω ∂P + 1) := by
        rw [integral_add hY (integrable_const 1)]; simp

/-- exponential moments of a count dominated by `d` plus a summable independent Bernoulli sum -/
lemma SQI_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (a : ℕ → ℝ) (hZm : ∀ k, Measurable (Z k))
    (hind : iIndepFun Z P) (hs : ∑' k : ℕ, P {ω | a k ≤ Z k ω} ≠ ⊤)
    (d : ℕ) (N : Ω → ℕ∞) (hN : ∀ᵐ ω ∂P, N ω ≤ d + {k : ℕ | a k ≤ Z k ω}.encard)
    (θ : ℝ) (hθ : 0 < θ) :
    (∀ᵐ ω ∂P, N ω ≠ ⊤) ∧
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * ((N ω).toNat : ℝ))) ∂P < ⊤ := by
  classical
  set B : ℝ := (∑' k : ℕ, P {ω | a k ≤ Z k ω}).toReal with hBdef
  have hms : ∀ k : ℕ, MeasurableSet {ω | a k ≤ Z k ω} :=
    fun k => measurableSet_le measurable_const (hZm k)
  have hfin : ∀ᵐ ω ∂P, {k : ℕ | a k ≤ Z k ω}.Finite :=
    ae_finite_setOfPred_mem (s := fun k : ℕ => {ω | a k ≤ Z k ω}) hs
  set X : ℕ → Ω → ℝ := fun k ω => if a k ≤ Z k ω then 1 else 0 with hXdef
  have hXm : ∀ k, Measurable (X k) := fun k =>
    Measurable.ite (hms k) measurable_const measurable_const
  have hXind : iIndepFun X P := by
    have := hind.comp (fun k (x : ℝ) => if a k ≤ x then (1 : ℝ) else 0)
      (fun k => Measurable.ite (measurableSet_le measurable_const measurable_id)
        measurable_const measurable_const)
    exact this
  have hX01 : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1 := by
    intro k ω; simp only [hXdef]; split_ifs <;> norm_num
  set c : ℝ := Real.exp θ - 1 with hc
  have hc0 : 0 < c := by rw [hc, sub_pos]; exact Real.one_lt_exp_iff.mpr hθ
  have hmgf1 : ∀ k, mgf (X k) P θ ≤ Real.exp (P.real {ω | a k ≤ Z k ω} * c) := by
    intro k
    have hpt : (fun ω => Real.exp (θ * X k ω)) =
        fun ω => 1 + c * ({ω | a k ≤ Z k ω}.indicator 1 ω) := by
      funext ω
      simp only [hXdef, Set.indicator, mem_setOf_eq, Pi.one_apply, hc]
      split_ifs <;> simp
    have hval : mgf (X k) P θ = 1 + c * P.real {ω | a k ≤ Z k ω} := by
      rw [mgf, hpt, integral_add (integrable_const 1), integral_const_mul,
        integral_indicator_one (hms k)]
      · simp
      · exact ((integrable_const (1:ℝ)).indicator (hms k)).const_mul c
    rw [hval]
    have := Real.add_one_le_exp (P.real {ω | a k ≤ Z k ω} * c)
    linarith
  have hpsum : ∀ n : ℕ, ∑ k ∈ Finset.range n, P.real {ω | a k ≤ Z k ω} ≤ B := by
    intro n
    simp only [measureReal_def]
    rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top P _), hBdef]
    exact ENNReal.toReal_mono hs (ENNReal.sum_le_tsum _)
  set S : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, X k ω with hSdef
  have hSm : ∀ n, Measurable (S n) := fun n =>
    Finset.measurable_sum _ (fun k _ => hXm k)
  have hSle : ∀ n ω, S n ω ≤ n := by
    intro n ω
    calc S n ω ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum (fun k _ => (hX01 k ω).2)
      _ = n := by simp
  have hmgfS : ∀ n, mgf (S n) P θ ≤ Real.exp (c * B) := by
    intro n
    have e : S n = ∑ k ∈ Finset.range n, X k := by
      funext ω; simp [hSdef, Finset.sum_apply]
    rw [e, hXind.mgf_sum hXm]
    calc ∏ k ∈ Finset.range n, mgf (X k) P θ
        ≤ ∏ k ∈ Finset.range n, Real.exp (P.real {ω | a k ≤ Z k ω} * c) :=
          Finset.prod_le_prod (fun k _ => mgf_nonneg) (fun k _ => hmgf1 k)
      _ = Real.exp ((∑ k ∈ Finset.range n, P.real {ω | a k ≤ Z k ω}) * c) := by
          rw [← Real.exp_sum, Finset.sum_mul]
      _ ≤ Real.exp (c * B) := by
          apply Real.exp_le_exp.mpr
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (hpsum n) hc0.le
  have hdom : ∀ᵐ ω ∂P, N ω ≠ ⊤ ∧ ENNReal.ofReal (Real.exp (θ * ((N ω).toNat : ℝ))) ≤
      ⨆ n : ℕ, ENNReal.ofReal (Real.exp (θ * (d + S n ω))) := by
    filter_upwards [hN, hfin] with ω hNω hfω
    set F := {k : ℕ | a k ≤ Z k ω} with hF
    have hNt : N ω ≠ ⊤ := ne_top_of_le_ne_top
      (by rw [hfω.cast_ncard_eq.symm]; exact ENat.natCast_ne_top (d + F.ncard) |> fun h => by
            simpa using h) hNω
    refine ⟨hNt, ?_⟩
    obtain ⟨M, hM⟩ := hfω.bddAbove
    have hFeq : F = ↑((Finset.range (M + 1)).filter (fun k : ℕ => a k ≤ Z k ω)) := by
      ext k
      simp only [hF, mem_setOf_eq, Finset.coe_filter, Finset.mem_range]
      constructor
      · intro hk; exact ⟨Nat.lt_succ_of_le (hM hk), hk⟩
      · intro hk; exact hk.2
    have hSF : S (M + 1) ω = (F.ncard : ℝ) := by
      rw [hFeq, Set.ncard_coe_finset]
      simp [hSdef, hXdef, Finset.sum_boole]
    have hNle : ((N ω).toNat : ℝ) ≤ d + (F.ncard : ℝ) := by
      have h1 : N ω ≤ ((d + F.ncard : ℕ) : ℕ∞) := by
        rw [← hfω.cast_ncard_eq] at hNω; push_cast; exact hNω
      have h2 : (N ω).toNat ≤ d + F.ncard := by
        have := ENat.toNat_le_toNat h1 (ENat.natCast_ne_top _)
        rwa [ENat.toNat_natCast] at this
      exact_mod_cast h2
    refine le_iSup_of_le (M + 1) ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    rw [hSF]
    exact mul_le_mul_of_nonneg_left hNle hθ.le
  refine ⟨hdom.mono (fun ω hω => hω.1), ?_⟩
  have hmono : Monotone (fun n : ℕ => fun ω => ENNReal.ofReal (Real.exp (θ * (d + S n ω)))) := by
    intro n m hnm ω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hθ.le
    have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
      (fun k _ _ => (hX01 k ω).1) (f := fun k => X k ω)
    simp only [hSdef]; linarith
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * ((N ω).toNat : ℝ))) ∂P
      ≤ ∫⁻ ω, ⨆ n : ℕ, ENNReal.ofReal (Real.exp (θ * (d + S n ω))) ∂P :=
        lintegral_mono_ae (hdom.mono (fun ω hω => hω.2))
    _ = ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (d + S n ω))) ∂P := by
        exact lintegral_iSup (f := fun n ω => ENNReal.ofReal (Real.exp (θ * (d + S n ω))))
          (fun n => (Real.measurable_exp.comp
            ((measurable_const.add (hSm n)).const_mul θ)).ennreal_ofReal) hmono
    _ ≤ ENNReal.ofReal (Real.exp (θ * d) * Real.exp (c * B)) := by
        refine iSup_le (fun n => ?_)
        have hint' : Integrable (fun ω => Real.exp (θ * S n ω)) P := by
          refine Integrable.of_bound (Real.measurable_exp.comp
            ((hSm n).const_mul θ)).aestronglyMeasurable (Real.exp (θ * n)) ?_
          filter_upwards with ω
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hSle n ω) hθ.le)
        have e : (fun ω => ENNReal.ofReal (Real.exp (θ * (d + S n ω)))) =
            fun ω => ENNReal.ofReal (Real.exp (θ * d)) * ENNReal.ofReal (Real.exp (θ * S n ω)) := by
          funext ω
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_add]
        rw [e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← ofReal_integral_eq_lintegral_ofReal hint'
            (Eventually.of_forall (fun ω => (Real.exp_pos _).le)),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left (hmgfS n) (Real.exp_pos _).le
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- the count of perturbed lattice points in `(0, h]`, as a function of the shift and the
perturbation sequence -/
noncomputable def SQI_Phi (h : ℝ) (p : ℝ × (ℤ → ℝ)) : ℕ∞ :=
  {j : ℤ | (j : ℝ) * h + h * p.1 + p.2 j ∈ Ioc 0 h}.encard

lemma SQI_Phi_measurable (h : ℝ) : Measurable (SQI_Phi h) := by
  have hms : ∀ j : ℤ, MeasurableSet {p : ℝ × (ℤ → ℝ) | (j : ℝ) * h + h * p.1 + p.2 j ∈ Ioc 0 h} := by
    intro j
    have : Measurable (fun p : ℝ × (ℤ → ℝ) => (j : ℝ) * h + h * p.1 + p.2 j) := by
      fun_prop
    exact this measurableSet_Ioc
  set Ψ : ℝ × (ℤ → ℝ) → ENNReal := fun p => ∑' j : ℤ,
    {j : ℤ | (j : ℝ) * h + h * p.1 + p.2 j ∈ Ioc 0 h}.indicator 1 j with hΨ
  have hΨm : Measurable Ψ := by
    refine Measurable.ennreal_tsum (fun j => ?_)
    have : (fun p : ℝ × (ℤ → ℝ) => {j : ℤ | (j : ℝ) * h + h * p.1 + p.2 j ∈ Ioc 0 h}.indicator
        (1 : ℤ → ENNReal) j) = {p : ℝ × (ℤ → ℝ) | (j : ℝ) * h + h * p.1 + p.2 j ∈ Ioc 0 h}.indicator 1 := by
      funext p; simp [Set.indicator]
    rw [this]
    exact measurable_const.indicator (hms j)
  have hΨeq : ∀ p, Ψ p = (SQI_Phi h p : ENNReal) := by
    intro p
    simp only [hΨ, SQI_Phi]
    rw [← tsum_subtype]; simp only [Pi.one_apply]; rw [ENNReal.tsum_set_one]
  apply measurable_to_countable'
  intro n
  have : SQI_Phi h ⁻¹' {n} = Ψ ⁻¹' {(n : ENNReal)} := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, hΨeq, ENat.toENNReal_inj]
  rw [this]
  exact hΨm (measurableSet_singleton _)

lemma SQI_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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

lemma SQI_arrivals_eq {Ω : Type*} (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (k : ℤ)
    (ω : Ω) :
    ScheduledQueue.Diffusion.arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h) ω =
      SQI_Phi h (U ω, fun j => ξ (j + k) ω) := by
  simp only [ScheduledQueue.Diffusion.arrivalsIn, SQI_Phi, ScheduledQueue.Stability.arrival]
  have : {j : ℤ | (j : ℝ) * h + h * U ω + ξ j ω ∈ Ioc ((k : ℝ) * h) (((k : ℝ) + 1) * h)} =
      (fun m : ℤ => m + k) '' {m : ℤ | (m : ℝ) * h + h * U ω + ξ (m + k) ω ∈ Ioc 0 h} := by
    ext j
    simp only [mem_setOf_eq, mem_image, mem_Ioc]
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
    (∀ k : ℕ, IdentDistrib (arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h))
        (arrivalsIn h ξ U 0 h) P P) ∧
    ∀ θ : ℝ, 0 < θ →
      (∀ᵐ ω ∂P, arrivalsIn h ξ U 0 h ω ≠ ⊤) ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * ((arrivalsIn h ξ U 0 h ω).toNat : ℝ))) ∂P < ⊤ := by
  constructor
  · intro k
    have e1 : arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h) =
        fun ω => SQI_Phi h (U ω, fun j => ξ (j + (k : ℤ)) ω) := by
      funext ω
      have := SQI_arrivals_eq h hh ξ U (k : ℤ) ω
      simpa using this
    have e0 : arrivalsIn h ξ U 0 h = fun ω => SQI_Phi h (U ω, fun j => ξ j ω) := by
      funext ω
      have := SQI_arrivals_eq h hh ξ U 0 ω
      simpa using this
    rw [e1, e0]
    exact (SQI_law P ξ U hin (k : ℤ)).comp (SQI_Phi_measurable h)
  · intro θ hθ
    have hU : ∀ᵐ ω ∂P, U ω ∈ Icc (0:ℝ) 1 := by
      rw [ae_iff]
      rw [hin.uniform.measure_eq (p := fun v => v ∉ Icc (0:ℝ) 1) measurableSet_Icc.compl]
      show (volume.restrict (Icc (0:ℝ) 1)) (Icc (0:ℝ) 1)ᶜ = 0
      rw [Measure.restrict_apply measurableSet_Icc.compl]
      simp
    set g : ℕ → ℤ := fun k => if k % 2 = 0 then ((k / 2 : ℕ) : ℤ) + 1 else -(((k / 2 : ℕ) : ℤ) + 1)
      with hg
    have hginj : Function.Injective g := by
      intro a b hab
      simp only [hg] at hab
      split_ifs at hab <;> omega
    set Z : ℕ → Ω → ℝ := fun k ω => if k % 2 = 0 then -ξ (g k) ω else ξ (g k) ω with hZ
    set a : ℕ → ℝ := fun k => ((k / 2 : ℕ) : ℝ) * h with ha
    have hZm : ∀ k, Measurable (Z k) := by
      intro k
      simp only [hZ]
      split_ifs
      · exact (hin.measurable _).neg
      · exact hin.measurable _
    have hind : iIndepFun Z P := by
      have := (hin.indep.precomp hginj).comp (fun k (x : ℝ) => if k % 2 = 0 then -x else x)
        (fun k => by
          by_cases hk : k % 2 = 0
          · simp only [hk, if_true]; exact measurable_neg
          · simp only [hk, if_false]; exact measurable_id)
      convert this using 1
      funext k ω
      simp only [hZ, Function.comp_apply]
    -- summability
    set Y : Ω → ℝ := fun ω => |ξ 0 ω| / h with hY
    have hYm : Measurable Y := (hin.measurable 0).abs.div_const h
    have hYi : Integrable Y P := hin.integrable.abs.div_const h
    have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => div_nonneg (abs_nonneg _) hh.le
    set f : ℕ → ENNReal := fun j => P {ω | (j : ℝ) ≤ Y ω} with hf
    have hterm : ∀ k, P {ω | a k ≤ Z k ω} ≤ f (k / 2) := by
      intro k
      have e : P {ω | a k ≤ |ξ (g k) ω|} = P {ω | a k ≤ |ξ 0 ω|} := by
        have := ((hin.identDistrib (g k)).comp (measurable_abs)).measure_mem_eq
          (s := Ici (a k)) measurableSet_Ici
        exact this
      calc P {ω | a k ≤ Z k ω} ≤ P {ω | a k ≤ |ξ (g k) ω|} := by
            refine measure_mono (fun ω hω => ?_)
            simp only [mem_setOf_eq, hZ] at hω ⊢
            split_ifs at hω
            · exact le_trans hω (neg_le_abs _)
            · exact le_trans hω (le_abs_self _)
        _ = P {ω | a k ≤ |ξ 0 ω|} := e
        _ = f (k / 2) := by
            simp only [hf, hY, ha]
            congr 1; ext ω; simp only [mem_setOf_eq]; rw [le_div_iff₀ hh]
    have hsum : ∑' k : ℕ, P {ω | a k ≤ Z k ω} ≠ ⊤ := by
      have h1 : ∑' k : ℕ, f (k / 2) = 2 * ∑' j : ℕ, f j := by
        rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
        have e1 : ∀ k : ℕ, (2 * k) / 2 = k := fun k => by omega
        have e2 : ∀ k : ℕ, (2 * k + 1) / 2 = k := fun k => by omega
        simp only [e1, e2]; ring
      have h2 := SQI_tsum_le P Y hYi hYm hY0
      refine ne_top_of_le_ne_top ?_ ((ENNReal.tsum_le_tsum hterm).trans h1.le)
      exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2)
    -- domination
    have hN : ∀ᵐ ω ∂P, arrivalsIn h ξ U 0 h ω ≤ ((1 : ℕ) : ℕ∞) + {k : ℕ | a k ≤ Z k ω}.encard := by
      filter_upwards [hU] with ω hu
      have hsub : {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈ Ioc 0 h} ⊆
          insert 0 (g '' {k : ℕ | a k ≤ Z k ω}) := by
        intro j hj
        simp only [mem_setOf_eq, ScheduledQueue.Stability.arrival, mem_Ioc] at hj
        rcases lt_trichotomy j 0 with hj0 | hj0 | hj0
        · right
          set n := (-j - 1).toNat with hn
          have hnj : (n : ℤ) = -j - 1 := Int.toNat_of_nonneg (by omega)
          refine ⟨2 * n + 1, ?_, ?_⟩
          · simp only [mem_setOf_eq, hZ, ha]
            have h1 : (2 * n + 1) % 2 ≠ 0 := by omega
            have h2 : (2 * n + 1) / 2 = n := by omega
            have h3 : g (2 * n + 1) = j := by simp only [hg, h1, if_false, h2]; omega
            rw [if_neg h1, h2, h3]
            have : (n : ℝ) = -(j : ℝ) - 1 := by exact_mod_cast hnj
            rw [this]; nlinarith [hu.2]
          · have h1 : (2 * n + 1) % 2 ≠ 0 := by omega
            have h2 : (2 * n + 1) / 2 = n := by omega
            simp only [hg, h1, if_false, h2]; omega
        · left; exact hj0
        · right
          set n := (j - 1).toNat with hn
          have hnj : (n : ℤ) = j - 1 := Int.toNat_of_nonneg (by omega)
          refine ⟨2 * n, ?_, ?_⟩
          · simp only [mem_setOf_eq, hZ, ha]
            have h1 : (2 * n) % 2 = 0 := by omega
            have h2 : (2 * n) / 2 = n := by omega
            have h3 : g (2 * n) = j := by simp only [hg, h1, if_true, h2]; omega
            rw [if_pos h1, h2, h3]
            have : (n : ℝ) = (j : ℝ) - 1 := by exact_mod_cast hnj
            rw [this]; nlinarith [hu.1]
          · have h1 : (2 * n) % 2 = 0 := by omega
            have h2 : (2 * n) / 2 = n := by omega
            simp only [hg, h1, if_true, h2]; omega
      calc arrivalsIn h ξ U 0 h ω
          = {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈ Ioc 0 h}.encard := rfl
        _ ≤ (insert 0 (g '' {k : ℕ | a k ≤ Z k ω})).encard := Set.encard_le_encard hsub
        _ ≤ (g '' {k : ℕ | a k ≤ Z k ω}).encard + 1 := Set.encard_insert_le _ _
        _ = ((1 : ℕ) : ℕ∞) + {k : ℕ | a k ≤ Z k ω}.encard := by
            rw [hginj.encard_image, add_comm]; rfl
    exact SQI_core P Z a hZm hind hsum 1 (arrivalsIn h ξ U 0 h) hN θ hθ

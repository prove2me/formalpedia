-- Prove2me | solution 1 for ServiceParts.Shortfall.stationary_shortfall_exists
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T09:51:49.200972+00:00
-- url     : https://prove2.me/submissions/19b3d087-1988-4303-b501-63733a471121

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_ShortfallModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal


namespace ServiceParts.Shortfall

noncomputable def sfL (c : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max (sfL c n x + x (n + 1) - c) 0

noncomputable def sfS (c : ℝ) (k : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range k, (x (i + 1) - c)

noncomputable def sfM (c : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max (sfM c n x) (sfS c (n + 1) x)

def sfR (n i : ℕ) : ℕ := if 1 ≤ i ∧ i ≤ n then n + 1 - i else i

lemma sfR_invol (n : ℕ) : Function.Involutive (sfR n) := by
  intro i; unfold sfR; split_ifs <;> omega

lemma sfS_succ (c : ℝ) (k : ℕ) (x : ℕ → ℝ) :
    sfS c (k + 1) x = (x 1 - c) + sfS c k (fun j => x (j + 1)) := by
  unfold sfS; rw [Finset.sum_range_succ']; ring

lemma sfS_congr (c : ℝ) (n : ℕ) (x y : ℕ → ℝ) (h : ∀ j, 1 ≤ j → j ≤ n → x j = y j)
    (k : ℕ) (hk : k ≤ n) : sfS c k x = sfS c k y := by
  unfold sfS; refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi; rw [h (i+1) (by omega) (by omega)]

lemma sfM_congr (c : ℝ) (n : ℕ) (x y : ℕ → ℝ) (h : ∀ j, 1 ≤ j → j ≤ n → x j = y j) :
    sfM c n x = sfM c n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sfM]
    rw [ih (fun j h1 h2 => h j h1 (by omega)), sfS_congr c (n+1) x y h (n+1) le_rfl]

lemma sfM_first (c : ℝ) (n : ℕ) (y : ℕ → ℝ) :
    sfM c (n + 1) y = max 0 (y 1 - c + sfM c n (fun j => y (j + 1))) := by
  induction n with
  | zero => simp [sfM, sfS]
  | succ n ih =>
    show max (sfM c (n + 1) y) (sfS c (n + 1 + 1) y) = _
    rw [ih, sfS_succ]
    simp only [sfM]
    rw [max_assoc, ← max_add_add_left]

lemma sfL_eq (c : ℝ) (n : ℕ) (x : ℕ → ℝ) : sfL c n x = sfM c n (x ∘ sfR n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show max (sfL c n x + x (n + 1) - c) 0 = _
    rw [sfM_first, ih]
    have h1 : sfR (n+1) 1 = n + 1 := by unfold sfR; split_ifs <;> omega
    have h2 : sfM c n (fun j => (x ∘ sfR (n+1)) (j+1)) = sfM c n (x ∘ sfR n) := by
      apply sfM_congr; intro j hj1 hj2
      simp only [Function.comp]; congr 1; unfold sfR; split_ifs <;> omega
    simp only [Function.comp] at h2 ⊢
    rw [h1, h2, max_comm]; ring_nf

lemma sfL_congr (c : ℝ) (n : ℕ) (x y : ℕ → ℝ) (h : ∀ j, j ≤ n → x j = y j) :
    sfL c n x = sfL c n y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sfL]; rw [ih (fun j hj => h j (by omega)), h (n+1) le_rfl]

lemma sfS_le_sfM (c : ℝ) (n : ℕ) (x : ℕ → ℝ) (k : ℕ) (hk : k ≤ n) : sfS c k x ≤ sfM c n x := by
  induction n with
  | zero => obtain rfl : k = 0 := by omega
            simp [sfS, sfM]
  | succ n ih =>
    simp only [sfM]
    rcases Nat.lt_or_ge k (n+1) with h | h
    · exact le_trans (ih (by omega)) (le_max_left _ _)
    · obtain rfl : k = n + 1 := by omega
      exact le_max_right _ _

lemma sfM_attained (c : ℝ) (n : ℕ) (x : ℕ → ℝ) : ∃ k ≤ n, sfM c n x = sfS c k x := by
  induction n with
  | zero => exact ⟨0, le_rfl, by simp [sfS, sfM]⟩
  | succ n ih =>
    obtain ⟨k, hk, he⟩ := ih
    simp only [sfM]
    rcases le_total (sfM c n x) (sfS c (n+1) x) with h | h
    · exact ⟨n+1, le_rfl, max_eq_right h⟩
    · exact ⟨k, by omega, (max_eq_left h).trans he⟩

lemma sfM_nonneg (c : ℝ) (n : ℕ) (x : ℕ → ℝ) : 0 ≤ sfM c n x := by
  simpa [sfS] using sfS_le_sfM c n x 0 (Nat.zero_le _)

lemma sfM_mono (c : ℝ) (x : ℕ → ℝ) : Monotone (fun n => sfM c n x) :=
  monotone_nat_of_le_succ fun n => by simp only [sfM]; exact le_max_left _ _

lemma sfL_meas (c : ℝ) (n : ℕ) : Measurable (sfL c n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    show Measurable (fun x => max (sfL c n x + x (n + 1) - c) 0)
    exact (((ih.add (measurable_pi_apply _)).sub_const c).max measurable_const)

lemma sfS_meas (c : ℝ) (k : ℕ) : Measurable (sfS c k) := by
  unfold sfS; fun_prop

lemma sfM_meas (c : ℝ) (n : ℕ) : Measurable (sfM c n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.max (sfS_meas c _)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma sf_shortfall_eq (M : ShortfallModel Ω P) (n : ℕ) (ω : Ω) :
    M.shortfall n ω = sfL M.capacity n (fun i => M.demand i ω) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ShortfallModel.shortfall, sfL, ih]

lemma sf_walk_eq (M : ShortfallModel Ω P) (n : ℕ) (ω : Ω) :
    M.walk n ω = sfS M.capacity n (fun i => M.demand i ω) := by
  unfold ShortfallModel.walk sfS
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma sf_law (M : ShortfallModel Ω P) : P.map (fun ω i => M.demand i ω) =
    Measure.infinitePi (fun _ : ℕ => P.map (M.demand 1)) := by
  rw [M.demand_indep.map_fun_eq_infinitePi_map₀
    (measurable_pi_lambda _ M.demand_measurable).aemeasurable]
  congr 1; funext i; exact (M.demand_identDistrib i).map_eq

lemma sf_perm (μ : Measure ℝ) [IsProbabilityMeasure μ] (e : ℕ ≃ ℕ) :
    (Measure.infinitePi (fun _ : ℕ => μ)).map (fun x => x ∘ e) =
      Measure.infinitePi (fun _ : ℕ => μ) := by
  have := Measure.infinitePi_map_piCongrLeft (X := fun _ : ℕ => ℝ) (μ := fun _ : ℕ => μ) e.symm
  convert this using 2
  funext x; ext i; simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

lemma sf_meas_shortfall (M : ShortfallModel Ω P) (n : ℕ) : Measurable (M.shortfall n) := by
  have : M.shortfall n = sfL M.capacity n ∘ (fun ω i => M.demand i ω) :=
    funext (sf_shortfall_eq M n)
  rw [this]; exact (sfL_meas _ n).comp (measurable_pi_lambda _ M.demand_measurable)

lemma sf_law_eq (M : ShortfallModel Ω P) (n : ℕ) : P.map (M.shortfall n) =
    P.map (fun ω => sfM M.capacity n (fun i => M.demand i ω)) := by
  have hD : Measurable (fun ω i => M.demand i ω) := measurable_pi_lambda _ M.demand_measurable
  have e1 : M.shortfall n = sfL M.capacity n ∘ (fun ω i => M.demand i ω) :=
    funext (sf_shortfall_eq M n)
  have e2 : (fun ω => sfM M.capacity n (fun i => M.demand i ω)) =
      sfM M.capacity n ∘ (fun ω i => M.demand i ω) := rfl
  have hperm : Measurable (fun x : ℕ → ℝ => x ∘ sfR n) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  haveI : IsProbabilityMeasure (P.map (M.demand 1)) :=
    Measure.isProbabilityMeasure_map (M.demand_measurable 1).aemeasurable
  rw [e1, e2, ← Measure.map_map (sfL_meas _ _) hD, ← Measure.map_map (sfM_meas _ _) hD, sf_law]
  have : sfL M.capacity n = sfM M.capacity n ∘ (fun x => x ∘ sfR n) := funext (sfL_eq _ n)
  have hp := sf_perm (P.map (M.demand 1)) (sfR_invol n).toPerm
  simp only [Function.Involutive.coe_toPerm] at hp
  rw [this, ← Measure.map_map (sfM_meas _ _) hperm, hp]

lemma sf_finite (M : ShortfallModel Ω P) : ∀ᵐ ω ∂P, M.walkMax ω ≠ ⊤ := by
  set c := M.capacity
  let X : ℕ → Ω → ℝ := fun i ω => M.demand (i+1) ω - c
  have hint : Integrable (X 0) P := M.demand_integrable.sub (integrable_const c)
  have hind : Pairwise (fun i j => IndepFun (X i) (X j) P) := by
    intro i j hij
    exact (M.demand_indep.indepFun (by omega : i+1 ≠ j+1)).comp (measurable_sub_const c)
      (measurable_sub_const c)
  have hid : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ((M.demand_identDistrib (i+1)).trans (M.demand_identDistrib 1).symm).comp
      (measurable_sub_const c)
  have hmean : P[X 0] < 0 := by
    simp only [X]; rw [integral_sub M.demand_integrable (integrable_const c)]
    simp; linarith [M.mean_lt_capacity]
  filter_upwards [strong_law_ae X hint hind hid] with ω hω
  have hev : ∀ᶠ n : ℕ in atTop, (n:ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω) < 0 :=
    hω.eventually (gt_mem_nhds hmean)
  obtain ⟨N, hN⟩ := (hev.and (eventually_gt_atTop 0)).exists_forall_of_atTop
  have hle : ∀ n, ENNReal.ofReal (M.walk n ω) ≤
      ENNReal.ofReal (sfM c N (fun i => M.demand i ω)) := by
    intro n
    rw [sf_walk_eq]
    rcases le_or_gt n N with h | h
    · exact ENNReal.ofReal_le_ofReal (sfS_le_sfM _ _ _ _ h)
    · have h0 := hN n h.le
      have h1 := h0.1
      have h2 : (0:ℝ) < n := by exact_mod_cast h0.2
      simp only [smul_eq_mul] at h1
      have h3 : ∑ i ∈ Finset.range n, X i ω < 0 := by
        by_contra hc; push_neg at hc
        have := mul_nonneg (inv_nonneg.mpr h2.le) hc; linarith
      have h4 : sfS c n (fun i => M.demand i ω) < 0 := by simpa [sfS, X] using h3
      rw [ENNReal.ofReal_of_nonpos h4.le]; simp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le hle : M.walkMax ω ≤ _)

lemma sf_tendsto (M : ShortfallModel Ω P) (ω : Ω) (hω : M.walkMax ω ≠ ⊤) :
    Tendsto (fun n => sfM M.capacity n (fun i => M.demand i ω)) atTop
      (𝓝 (M.stationaryShortfall ω)) ∧
    ∀ n, sfM M.capacity n (fun i => M.demand i ω) ≤ M.stationaryShortfall ω := by
  have hle : ∀ n, ENNReal.ofReal (sfM M.capacity n (fun i => M.demand i ω)) ≤ M.walkMax ω := by
    intro n; obtain ⟨k, -, hk⟩ := sfM_attained M.capacity n (fun i => M.demand i ω)
    rw [hk, ← sf_walk_eq]; exact le_iSup (fun k => ENNReal.ofReal (M.walk k ω)) k
  have hsup : ⨆ n, ENNReal.ofReal (sfM M.capacity n (fun i => M.demand i ω)) = M.walkMax ω := by
    apply le_antisymm (iSup_le hle)
    apply iSup_le; intro k
    rw [sf_walk_eq]
    exact le_trans (ENNReal.ofReal_le_ofReal (sfS_le_sfM _ k _ k le_rfl))
      (le_iSup (fun n => ENNReal.ofReal (sfM M.capacity n (fun i => M.demand i ω))) k)
  have hmono : Monotone fun n => ENNReal.ofReal (sfM M.capacity n (fun i => M.demand i ω)) :=
    fun a b h => ENNReal.ofReal_le_ofReal (sfM_mono _ _ h)
  have ht := tendsto_atTop_iSup hmono
  rw [hsup] at ht
  have ht2 := (ENNReal.tendsto_toReal hω).comp ht
  refine ⟨?_, fun n => ?_⟩
  · refine ht2.congr fun n => ?_
    simp [ENNReal.toReal_ofReal (sfM_nonneg _ n _)]
  · exact (ENNReal.ofReal_le_iff_le_toReal hω).mp (hle n)

lemma sf_indep (M : ShortfallModel Ω P) (n : ℕ) :
    IndepFun (M.shortfall n) (M.demand (n+1)) P := by
  classical
  have h := M.demand_indep.indepFun_finset (Finset.range (n+1)) {n+1} (by simp)
    M.demand_measurable
  let ext : ((i : Finset.range (n+1)) → ℝ) → (ℕ → ℝ) :=
    fun y i => if h : i ∈ Finset.range (n+1) then y ⟨i, h⟩ else 0
  have hext : Measurable ext := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases hi : i ∈ Finset.range (n+1)
    · simp only [ext, hi, dite_true]; exact measurable_pi_apply _
    · simp only [ext, hi, dite_false]; exact measurable_const
  have h2 := h.comp ((sfL_meas M.capacity n).comp hext)
    (measurable_pi_apply (⟨n+1, by simp⟩ : ({n+1} : Finset ℕ)))
  convert h2 using 1
  · funext ω
    simp only [Function.comp, sf_shortfall_eq]
    apply sfL_congr; intro j hj
    have hj' : j ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
    simp [ext]; intro h; omega
  · rfl

theorem stationary_core (M : ShortfallModel Ω P) :
    P {ω | M.walkMax ω = ⊤} = 0 ∧
    (∀ v : ℝ, Tendsto (fun n : ℕ => P {ω | v < M.shortfall n ω}) atTop
        (𝓝 (P {ω | v < M.stationaryShortfall ω}))) ∧
    (∀ v : ℝ, P {ω | v < M.stationaryShortfall ω} =
        ∫⁻ ω, (P.map (M.demand 1))
          {d : ℝ | v < max (M.stationaryShortfall ω + d - M.capacity) 0} ∂P) := by
  set c := M.capacity with hc
  have hD : Measurable (fun ω i => M.demand i ω) := measurable_pi_lambda _ M.demand_measurable
  have hMn : ∀ n, Measurable (fun ω => sfM c n (fun i => M.demand i ω)) :=
    fun n => (sfM_meas c n).comp hD
  have hfin := sf_finite M
  have part2 : ∀ v : ℝ, Tendsto (fun n : ℕ => P {ω | v < M.shortfall n ω}) atTop
      (𝓝 (P {ω | v < M.stationaryShortfall ω})) := by
    intro v
    have e : ∀ n, P {ω | v < M.shortfall n ω} =
        P {ω | v < sfM c n (fun i => M.demand i ω)} := by
      intro n
      have := congrArg (fun m => m (Set.Ioi v)) (sf_law_eq M n)
      rwa [Measure.map_apply (sf_meas_shortfall M n) measurableSet_Ioi,
        Measure.map_apply (hMn n) measurableSet_Ioi] at this
    simp_rw [e]
    have hmono : Monotone (fun n => {ω | v < sfM c n (fun i => M.demand i ω)}) :=
      fun a b h ω hω => lt_of_lt_of_le hω (sfM_mono c _ h)
    have := tendsto_measure_iUnion_atTop (μ := P) hmono
    have hU : P {ω | v < M.stationaryShortfall ω} =
        P (⋃ n, {ω | v < sfM c n (fun i => M.demand i ω)}) := ?_
    · rw [hU]; exact this
    apply measure_congr
    rw [Filter.eventuallyEq_set]
    filter_upwards [hfin] with ω hω
    obtain ⟨ht, hle⟩ := sf_tendsto M ω hω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h; exact (ht.eventually (lt_mem_nhds h)).exists
    · rintro ⟨n, hn⟩; exact lt_of_lt_of_le hn (hle n)
  refine ⟨by simpa using ae_iff.mp hfin, part2, fun v => ?_⟩
  haveI : IsProbabilityMeasure (P.map (M.demand 1)) :=
    Measure.isProbabilityMeasure_map (M.demand_measurable 1).aemeasurable
  set S : Set (ℝ × ℝ) := {p | v < max (p.1 + p.2 - c) 0} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
  have step : ∀ n, P {ω | v < M.shortfall (n+1) ω} =
      ∫⁻ ω, (P.map (M.demand 1)) (Prod.mk (sfM c n (fun i => M.demand i ω)) ⁻¹' S) ∂P := by
    intro n
    have hprod := (indepFun_iff_map_prod_eq_prod_map_map (sf_meas_shortfall M n).aemeasurable
      (M.demand_measurable (n+1)).aemeasurable).mp (sf_indep M n)
    have e1 : {ω | v < M.shortfall (n+1) ω} =
        (fun ω => (M.shortfall n ω, M.demand (n+1) ω)) ⁻¹' S := rfl
    rw [e1, ← Measure.map_apply ((sf_meas_shortfall M n).prodMk (M.demand_measurable _)) hSm,
      hprod, Measure.prod_apply hSm, (M.demand_identDistrib (n+1)).map_eq, sf_law_eq M n,
      lintegral_map (measurable_measure_prodMk_left hSm) (hMn n)]
  have hL : Tendsto (fun n => P {ω | v < M.shortfall (n+1) ω}) atTop
      (𝓝 (P {ω | v < M.stationaryShortfall ω})) := (part2 v).comp (tendsto_add_atTop_nat 1)
  have hR : Tendsto (fun n => ∫⁻ ω, (P.map (M.demand 1))
      (Prod.mk (sfM c n (fun i => M.demand i ω)) ⁻¹' S) ∂P) atTop
      (𝓝 (∫⁻ ω, (P.map (M.demand 1)) (Prod.mk (M.stationaryShortfall ω) ⁻¹' S) ∂P)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n; exact ((measurable_measure_prodMk_left hSm).comp (hMn n)).aemeasurable
    · refine Filter.Eventually.of_forall fun ω a b hab => measure_mono ?_
      intro d hd
      simp only [Set.mem_preimage, hS, Set.mem_setOf_eq] at hd ⊢
      have := sfM_mono c (fun i => M.demand i ω) hab
      simp only at this
      exact lt_of_lt_of_le hd (max_le_max (by linarith) le_rfl)
    · filter_upwards [hfin] with ω hω
      obtain ⟨ht, hle⟩ := sf_tendsto M ω hω
      have hm : Monotone (fun n => Prod.mk (sfM c n (fun i => M.demand i ω)) ⁻¹' S) := by
        intro a b hab d hd
        simp only [Set.mem_preimage, hS, Set.mem_setOf_eq] at hd ⊢
        have := sfM_mono c (fun i => M.demand i ω) hab
        simp only at this
        exact lt_of_lt_of_le hd (max_le_max (by linarith) le_rfl)
      have := tendsto_measure_iUnion_atTop (μ := P.map (M.demand 1)) hm
      have hU : Prod.mk (M.stationaryShortfall ω) ⁻¹' S =
          ⋃ n, Prod.mk (sfM c n (fun i => M.demand i ω)) ⁻¹' S := ?_
      · rw [hU]; exact this
      ext d; simp only [Set.mem_preimage, Set.mem_iUnion, hS, Set.mem_setOf_eq]
      constructor
      · intro h
        have hc' : Tendsto (fun n => max (sfM c n (fun i => M.demand i ω) + d - c) 0) atTop
            (𝓝 (max (M.stationaryShortfall ω + d - c) 0)) :=
          ((ht.add_const d).sub_const c).max tendsto_const_nhds
        exact (hc'.eventually (lt_mem_nhds h)).exists
      · rintro ⟨n, hn⟩
        exact lt_of_lt_of_le hn (max_le_max (by linarith [hle n]) le_rfl)
  simp_rw [step] at hL
  exact tendsto_nhds_unique hL hR

end ServiceParts.Shortfall

open ServiceParts.Shortfall


theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) :
    P {ω | M.walkMax ω = ⊤} = 0 ∧
    (∀ v : ℝ, Tendsto (fun n : ℕ => P {ω | v < M.shortfall n ω}) atTop
        (𝓝 (P {ω | v < M.stationaryShortfall ω}))) ∧
    (∀ v : ℝ, P {ω | v < M.stationaryShortfall ω} =
        ∫⁻ ω, (P.map (M.demand 1))
          {d : ℝ | v < max (M.stationaryShortfall ω + d - M.capacity) 0} ∂P) := by
  exact stationary_core M

-- Prove2me | solution 1 for ScheduledQueue.Diffusion.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T18:16:05.492+00:00
-- url     : https://prove2.me/submissions/af4813ef-537c-4d3b-9cad-40fcbd227497

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting
import Theorems.Thm_ScheduledQueue_Diffusion_count_decomposition
import Theorems.Thm_ScheduledQueue_Diffusion_maximal_bounds

open Set Filter Topology MeasureTheory ProbabilityTheory

/-- combining convergences in probability under a domination -/
lemma SQP_comb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y1 Y2 Y3 Y4 : ℕ → Ω → ℝ) (C : ℝ) (hC : 0 < C) (n0 : ℕ)
    (hb : ∀ᵐ ω ∂P, ∀ n, n0 ≤ n → 0 ≤ X n ω ∧ X n ω ≤ C * (Y1 n ω + Y2 n ω + Y3 n ω + Y4 n ω))
    (h1 : TendstoInMeasure P Y1 atTop (fun _ => 0)) (h2 : TendstoInMeasure P Y2 atTop (fun _ => 0))
    (h3 : TendstoInMeasure P Y3 atTop (fun _ => 0)) (h4 : TendstoInMeasure P Y4 atTop (fun _ => 0)) :
    TendstoInMeasure P X atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at *
  intro ε hε
  set δ := ε / (4 * C) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨G, hG, hGm⟩ : ∃ G : Set Ω, P Gᶜ = 0 ∧ ∀ ω ∈ G, ∀ n, n0 ≤ n →
      0 ≤ X n ω ∧ X n ω ≤ C * (Y1 n ω + Y2 n ω + Y3 n ω + Y4 n ω) := by
    refine ⟨{ω | ∀ n, n0 ≤ n → 0 ≤ X n ω ∧ X n ω ≤ C * (Y1 n ω + Y2 n ω + Y3 n ω + Y4 n ω)},
      ?_, fun ω hω => hω⟩
    rw [ae_iff] at hb
    exact hb
  have hlim := (((h1 δ hδ0).add (h2 δ hδ0)).add (h3 δ hδ0)).add (h4 δ hδ0)
  simp only [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun n => bot_le)) ?_
  filter_upwards [eventually_ge_atTop n0] with n hn
  have hsub : {ω | ε ≤ dist (X n ω) 0} ⊆ Gᶜ ∪ (((({ω | δ ≤ dist (Y1 n ω) 0} ∪
      {ω | δ ≤ dist (Y2 n ω) 0}) ∪ {ω | δ ≤ dist (Y3 n ω) 0}) ∪ {ω | δ ≤ dist (Y4 n ω) 0})) := by
    intro ω hω
    by_cases hωG : ω ∈ G
    · right
      obtain ⟨hX0, hXle⟩ := hGm ω hωG n hn
      simp only [mem_setOf_eq, Real.dist_eq, sub_zero, abs_of_nonneg hX0] at hω
      simp only [mem_union, mem_setOf_eq, Real.dist_eq, sub_zero]
      by_contra hc
      simp only [not_or, not_le] at hc
      obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
      have e1 := le_abs_self (Y1 n ω)
      have e2 := le_abs_self (Y2 n ω)
      have e3 := le_abs_self (Y3 n ω)
      have e4 := le_abs_self (Y4 n ω)
      have hsum : Y1 n ω + Y2 n ω + Y3 n ω + Y4 n ω < 4 * δ := by linarith
      have : C * (Y1 n ω + Y2 n ω + Y3 n ω + Y4 n ω) < C * (4 * δ) :=
        mul_lt_mul_of_pos_left hsum hC
      have hCδ : C * (4 * δ) = ε := by rw [hδ]; field_simp
      linarith
    · left; exact hωG
  calc P {ω | ε ≤ dist (X n ω) 0}
      ≤ P (Gᶜ ∪ (((({ω | δ ≤ dist (Y1 n ω) 0} ∪ {ω | δ ≤ dist (Y2 n ω) 0}) ∪
          {ω | δ ≤ dist (Y3 n ω) 0}) ∪ {ω | δ ≤ dist (Y4 n ω) 0}))) := measure_mono hsub
    _ ≤ P Gᶜ + (((P {ω | δ ≤ dist (Y1 n ω) 0} + P {ω | δ ≤ dist (Y2 n ω) 0}) +
          P {ω | δ ≤ dist (Y3 n ω) 0}) + P {ω | δ ≤ dist (Y4 n ω) 0}) := by
        refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ = _ := by rw [hG, zero_add]

open ScheduledQueue.Diffusion in
/-- pathwise bound between grid points -/
lemma SQP_path {Ω : Type*} (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (ω : Ω)
    (hfin : ∀ k : ℕ, {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈ Ioc 0 ((k : ℝ) * h)}.Finite)
    (hdec : ∀ k : ℕ, (ScheduledQueue.Stability.count h ξ U ((k : ℝ) * h) ω : ℤ) =
      (k : ℤ) + (((early h ξ U ((k : ℝ) * h) ω).toNat : ℤ) - ((late h ξ U ((k : ℝ) * h) ω).toNat : ℤ))
        - (((early h ξ U 0 ω).toNat : ℤ) - ((late h ξ U 0 ω).toNat : ℤ)))
    (t : ℝ) (ht : 0 ≤ t) :
    |h * (ScheduledQueue.Stability.count h ξ U t ω : ℝ) - t| ≤
      h * (((early h ξ U ((⌊t / h⌋₊ : ℕ) * h) ω).toNat : ℝ)
        + ((late h ξ U ((⌊t / h⌋₊ : ℕ) * h) ω).toNat : ℝ)
        + ((early h ξ U 0 ω).toNat : ℝ) + ((late h ξ U 0 ω).toNat : ℝ)
        + ((arrivalsIn h ξ U ((⌊t / h⌋₊ : ℕ) * h) (((⌊t / h⌋₊ : ℕ) + 1) * h) ω).toNat : ℝ) + 1) := by
  set k := ⌊t / h⌋₊ with hk
  set S : ℝ → Set ℤ := fun τ => {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈ Ioc 0 τ}
    with hS
  set A : Set ℤ := {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈
    Ioc ((k : ℝ) * h) (((k : ℝ) + 1) * h)} with hA
  have hkt : (k : ℝ) * h ≤ t := by
    have := Nat.floor_le (div_nonneg ht hh.le)
    rw [← hk] at this
    rwa [le_div_iff₀ hh] at this
  have htk : t < ((k : ℝ) + 1) * h := by
    have := Nat.lt_floor_add_one (t / h)
    rw [← hk] at this
    rwa [div_lt_iff₀ hh] at this
  have hfin1 : (S (((k + 1 : ℕ) : ℝ) * h)).Finite := hfin (k + 1)
  have hsub1 : S t ⊆ S (((k + 1 : ℕ) : ℝ) * h) := by
    intro j hj
    simp only [hS, mem_setOf_eq, mem_Ioc] at hj ⊢
    push_cast; exact ⟨hj.1, by linarith [hj.2]⟩
  have hfint : (S t).Finite := hfin1.subset hsub1
  have hsub0 : S ((k : ℝ) * h) ⊆ S t := by
    intro j hj
    simp only [hS, mem_setOf_eq, mem_Ioc] at hj ⊢
    exact ⟨hj.1, by linarith [hj.2]⟩
  have hsub2 : S t ⊆ S ((k : ℝ) * h) ∪ A := by
    intro j hj
    simp only [hS, hA, mem_setOf_eq, mem_Ioc, mem_union] at hj ⊢
    by_cases hc : ScheduledQueue.Stability.arrival h ξ U j ω ≤ (k : ℝ) * h
    · left; exact ⟨hj.1, hc⟩
    · right; push Not at hc; exact ⟨hc, by linarith [hj.2]⟩
  have hAfin : A.Finite := by
    refine hfin1.subset (fun j hj => ?_)
    simp only [hS, hA, mem_setOf_eq, mem_Ioc] at hj ⊢
    push_cast
    refine ⟨?_, hj.2⟩
    have : (0 : ℝ) ≤ (k : ℝ) * h := by positivity
    linarith [hj.1]
  have hN0 : (ScheduledQueue.Stability.count h ξ U ((k : ℝ) * h) ω) ≤
      ScheduledQueue.Stability.count h ξ U t ω := Set.ncard_le_ncard hsub0 hfint
  have hN1 : ScheduledQueue.Stability.count h ξ U t ω ≤
      ScheduledQueue.Stability.count h ξ U ((k : ℝ) * h) ω +
        (arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h) ω).toNat := by
    have e : (arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h) ω).toNat = A.ncard := by
      simp only [arrivalsIn, hA, Set.ncard_def]
    rw [e]
    calc ScheduledQueue.Stability.count h ξ U t ω = (S t).ncard := rfl
      _ ≤ (S ((k : ℝ) * h) ∪ A).ncard :=
          Set.ncard_le_ncard hsub2 ((hfin k).union hAfin)
      _ ≤ (S ((k : ℝ) * h)).ncard + A.ncard := Set.ncard_union_le _ _
      _ = _ := rfl
  have hd := hdec k
  have hdR : (ScheduledQueue.Stability.count h ξ U ((k : ℝ) * h) ω : ℝ) =
      (k : ℝ) + (((early h ξ U ((k : ℝ) * h) ω).toNat : ℝ) - ((late h ξ U ((k : ℝ) * h) ω).toNat : ℝ))
        - (((early h ξ U 0 ω).toNat : ℝ) - ((late h ξ U 0 ω).toNat : ℝ)) := by
    exact_mod_cast hd
  have hN0R : (ScheduledQueue.Stability.count h ξ U ((k : ℝ) * h) ω : ℝ) ≤
      (ScheduledQueue.Stability.count h ξ U t ω : ℝ) := by exact_mod_cast hN0
  have hN1R : (ScheduledQueue.Stability.count h ξ U t ω : ℝ) ≤
      (ScheduledQueue.Stability.count h ξ U ((k : ℝ) * h) ω : ℝ) +
        ((arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h) ω).toNat : ℝ) := by exact_mod_cast hN1
  set e1 := ((early h ξ U ((k : ℝ) * h) ω).toNat : ℝ)
  set l1 := ((late h ξ U ((k : ℝ) * h) ω).toNat : ℝ)
  set e0 := ((early h ξ U 0 ω).toNat : ℝ)
  set l0 := ((late h ξ U 0 ω).toNat : ℝ)
  set i1 := ((arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h) ω).toNat : ℝ)
  have he1 : 0 ≤ e1 := Nat.cast_nonneg _
  have hl1 : 0 ≤ l1 := Nat.cast_nonneg _
  have he0 : 0 ≤ e0 := Nat.cast_nonneg _
  have hl0 : 0 ≤ l0 := Nat.cast_nonneg _
  have hi1 : 0 ≤ i1 := Nat.cast_nonneg _
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

lemma SQP_encard_meas {α : Type*} [MeasurableSpace α] (A : ℤ → Set α)
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

lemma SQP_sched {Ω : Type*} (h : ℝ) (hh : 0 < h) (U : Ω → ℝ) (ω : Ω) (hu : U ω ∈ Ioo (0:ℝ) 1)
    (k : ℕ) : ScheduledQueue.Diffusion.scheduled h U ((k : ℝ) * h) ω = k := by
  simp only [ScheduledQueue.Diffusion.scheduled]
  have : {i : ℤ | (i : ℝ) * h + U ω * h ∈ Ioc 0 ((k : ℝ) * h)} = ↑(Finset.Ico (0 : ℤ) k) := by
    ext i
    simp only [mem_setOf_eq, mem_Ioc, Finset.coe_Ico, mem_Ico]
    obtain ⟨hu0, hu1⟩ := hu
    constructor
    · rintro ⟨h1, h2⟩
      have a1 : (-1 : ℝ) < i := by
        by_contra hc; push Not at hc; nlinarith
      have a2 : (i : ℝ) < k := by
        by_contra hc; push Not at hc; nlinarith
      have b1 : (-1 : ℤ) < i := by exact_mod_cast a1
      have b2 : i < (k : ℤ) := by exact_mod_cast a2
      omega
    · rintro ⟨h1, h2⟩
      have a1 : (0 : ℝ) ≤ i := by exact_mod_cast h1
      have a2 : (i : ℝ) + 1 ≤ k := by
        have : i + 1 ≤ (k : ℤ) := by omega
        exact_mod_cast this
      constructor <;> nlinarith
  rw [this, Set.ncard_coe_finset, Int.card_Ico]
  simp


open ScheduledQueue.Diffusion in
lemma SQP_E0_meas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    AEMeasurable (fun ω => ((early h ξ U 0 ω).toNat : ℝ)) P := by
  set G : ℝ × (ℤ → ℝ) → ℕ∞ := fun p => {m : ℤ | p ∈
      {p : ℝ × (ℤ → ℝ) | (0:ℝ) < m * h + p.1 * h ∧ m * h + p.1 * h + p.2 m ≤ 0}}.encard with hGdef
  have hG : Measurable G := by
    apply SQP_encard_meas
    intro m
    have hf1 : Measurable (fun p : ℝ × (ℤ → ℝ) => (m : ℝ) * h + p.1 * h) := by fun_prop
    have hf2 : Measurable (fun p : ℝ × (ℤ → ℝ) => (m : ℝ) * h + p.1 * h + p.2 m) := by fun_prop
    exact (measurableSet_lt measurable_const hf1).inter (measurableSet_le hf2 measurable_const)
  have hpair : AEMeasurable (fun ω => (U ω, fun j => ξ j ω)) P :=
    hin.uniform.aemeasurable.prodMk (measurable_pi_lambda _ hin.measurable).aemeasurable
  have htn : Measurable (fun x : ℕ∞ => ((x.toNat : ℕ) : ℝ)) := Measurable.of_discrete
  have e : (fun ω => ((early h ξ U 0 ω).toNat : ℝ)) =
      (fun x : ℕ∞ => ((x.toNat : ℕ) : ℝ)) ∘ G ∘ (fun ω => (U ω, fun j => ξ j ω)) := by
    funext ω
    simp only [Function.comp_apply, hGdef, early, mem_setOf_eq]
  rw [e]
  exact (htn.comp hG).comp_aemeasurable hpair

open ScheduledQueue.Diffusion in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (Real.log n)⁻¹ *
        ⨆ s : Icc (0 : ℝ) 1, |h * (ScheduledQueue.Stability.count h ξ U ((n : ℝ) * s) ω : ℝ) - (n : ℝ) * s|)
      atTop (fun _ => 0) := by
  obtain ⟨hA, hB, hC⟩ := maximal_bounds P h hh ξ U hin
  set m : ℕ → ℕ := fun n => ⌈(n : ℝ) / h⌉₊ with hm
  have hmt : Tendsto m atTop atTop := by
    exact tendsto_nat_ceil_atTop.comp ((tendsto_natCast_atTop_atTop).atTop_div_const hh)
  have hA' := hA.comp hmt
  have hB' := hB.comp hmt
  have hC' := hC.comp hmt
  set E0 : Ω → ℝ := fun ω => ((early h ξ U 0 ω).toNat : ℝ) with hE0
  have hE0m : AEMeasurable E0 P := SQP_E0_meas P h ξ U hin
  set Yd : ℕ → Ω → ℝ := fun n ω => (Real.log n)⁻¹ * (2 * E0 ω + 1) with hYd
  have hD : TendstoInMeasure P Yd atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (((hE0m.const_mul 2).add_const 1).const_mul _).aestronglyMeasurable
    · filter_upwards with ω
      have h1 : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      have := h1.mul_const (2 * E0 ω + 1)
      simpa using this
  -- the good event
  have hU : ∀ᵐ ω ∂P, U ω ∈ Ioo (0:ℝ) 1 := by
    rw [ae_iff]
    rw [hin.uniform.measure_eq (p := fun v => v ∉ Ioo (0:ℝ) 1) measurableSet_Ioo.compl]
    show (volume.restrict (Icc (0:ℝ) 1)) (Ioo (0:ℝ) 1)ᶜ = 0
    rw [Measure.restrict_apply measurableSet_Ioo.compl]
    refine measure_mono_null (t := {0, 1}) ?_ ?_
    · intro x hx
      simp only [mem_inter_iff, mem_compl_iff, mem_Ioo, mem_Icc, not_and, not_lt] at hx
      simp only [mem_insert_iff, mem_singleton_iff]
      rcases hx with ⟨hx1, ⟨hx2, hx3⟩⟩
      by_cases h0 : x = 0
      · left; exact h0
      · right
        have : 0 < x := lt_of_le_of_ne hx2 (Ne.symm h0)
        have := hx1 this; linarith
    · exact (Set.toFinite _).measure_zero _
  have hCD : ∀ᵐ ω ∂P, ∀ k : ℕ,
      early h ξ U ((k : ℝ) * h) ω ≠ ⊤ ∧ late h ξ U ((k : ℝ) * h) ω ≠ ⊤ ∧
      early h ξ U 0 ω ≠ ⊤ ∧ late h ξ U 0 ω ≠ ⊤ ∧
      {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈ Ioc 0 ((k : ℝ) * h)}.Finite ∧
      (ScheduledQueue.Stability.count h ξ U ((k : ℝ) * h) ω : ℤ) =
        (scheduled h U ((k : ℝ) * h) ω : ℤ)
          + (((early h ξ U ((k : ℝ) * h) ω).toNat : ℤ) - ((late h ξ U ((k : ℝ) * h) ω).toNat : ℤ))
          - (((early h ξ U 0 ω).toNat : ℤ) - ((late h ξ U 0 ω).toNat : ℤ)) :=
    ae_all_iff.2 (fun k => count_decomposition P h hh ξ U hin ((k : ℝ) * h) (by positivity))
  -- threshold
  set n0 : ℕ := ⌈h⌉₊ + ⌈1 / h⌉₊ + 3 with hn0
  refine SQP_comb P _ _ _ _ Yd (4 * h) (by positivity) n0 ?_ hA' hB' hC' hD
  filter_upwards [hU, hCD] with ω hu hcd
  intro n hn
  have hfin : ∀ k : ℕ,
      {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈ Ioc 0 ((k : ℝ) * h)}.Finite :=
    fun k => (hcd k).2.2.2.2.1
  have hdec : ∀ k : ℕ, (ScheduledQueue.Stability.count h ξ U ((k : ℝ) * h) ω : ℤ) =
      (k : ℤ) + (((early h ξ U ((k : ℝ) * h) ω).toNat : ℤ) - ((late h ξ U ((k : ℝ) * h) ω).toNat : ℤ))
        - (((early h ξ U 0 ω).toNat : ℤ) - ((late h ξ U 0 ω).toNat : ℤ)) := by
    intro k
    have := (hcd k).2.2.2.2.2
    rw [SQP_sched h hh U ω hu k] at this
    exact this
  -- numeric facts about `n`
  have hnR : ((n0 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0R : (n0 : ℝ) = (⌈h⌉₊ : ℝ) + (⌈1 / h⌉₊ : ℝ) + 3 := by rw [hn0]; push_cast; ring
  have hc1 : h ≤ (⌈h⌉₊ : ℝ) := Nat.le_ceil h
  have hc2 : 1 / h ≤ (⌈1 / h⌉₊ : ℝ) := Nat.le_ceil _
  have hc1' : (0:ℝ) ≤ (⌈h⌉₊ : ℝ) := Nat.cast_nonneg _
  have hc2' : (0:ℝ) ≤ (⌈1 / h⌉₊ : ℝ) := Nat.cast_nonneg _
  have hn2 : (2 : ℝ) ≤ n := by linarith
  have hnh : h + 1 ≤ (n : ℝ) := by linarith
  have hnh' : 1 / h + 1 ≤ (n : ℝ) := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hmge : (n : ℝ) / h ≤ (m n : ℝ) := Nat.le_ceil _
  have hmle : (m n : ℝ) < (n : ℝ) / h + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm1 : (1 : ℝ) < (m n : ℝ) := by
    have : 1 < (n : ℝ) / h := by rw [lt_div_iff₀ hh]; linarith
    linarith
  have hlogm : 0 < Real.log (m n) := Real.log_pos hm1
  have hmn2 : (m n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (n : ℝ) / h + 1 ≤ (n : ℝ) ^ 2 := by
      have e : (n : ℝ) / h = (n : ℝ) * (1 / h) := by ring
      rw [e]; nlinarith
    linarith
  have hlogmn : Real.log (m n) ≤ 2 * Real.log n := by
    have e2 : Real.log ((n : ℝ) ^ 2) = 2 * Real.log n := by rw [Real.log_pow]; push_cast; ring
    rw [← e2]
    exact Real.log_le_log (by linarith) hmn2
  have hinv : (Real.log n)⁻¹ ≤ 2 * (Real.log (m n))⁻¹ := by
    rw [inv_le_comm₀ hlogn (by positivity), mul_inv, inv_inv]
    have : Real.log (m n) * 2⁻¹ ≤ Real.log n := by linarith
    linarith
  -- maxima
  set ME : ℝ := (((Finset.Icc 1 (m n + 1)).sup fun k => (early h ξ U ((k : ℝ) * h) ω).toNat : ℕ) : ℝ)
    with hME
  set ML : ℝ := (((Finset.range (m n + 1)).sup fun k => (late h ξ U ((k : ℝ) * h) ω).toNat : ℕ) : ℝ)
    with hML
  set MI : ℝ := (((Finset.range (m n + 2)).sup fun k =>
      (arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h) ω).toNat : ℕ) : ℝ) with hMI
  have hME0 : 0 ≤ ME := Nat.cast_nonneg _
  have hML0 : 0 ≤ ML := Nat.cast_nonneg _
  have hMI0 : 0 ≤ MI := Nat.cast_nonneg _
  have hE00 : 0 ≤ E0 ω := Nat.cast_nonneg _
  set B : ℝ := h * (ME + 2 * ML + MI + 2 * E0 ω + 1) with hBdef
  have hpt : ∀ s : Icc (0 : ℝ) 1,
      |h * (ScheduledQueue.Stability.count h ξ U ((n : ℝ) * s) ω : ℝ) - (n : ℝ) * s| ≤ B := by
    rintro ⟨s, hs0, hs1⟩
    have ht : 0 ≤ (n : ℝ) * s := by positivity
    have hpath := SQP_path h hh ξ U ω hfin hdec ((n : ℝ) * s) ht
    set k := ⌊(n : ℝ) * s / h⌋₊ with hk
    have hkm : k ≤ m n := by
      have : (n : ℝ) * s / h ≤ (n : ℝ) / h := by
        apply div_le_div_of_nonneg_right _ hh.le
        nlinarith
      exact (Nat.floor_le_floor this).trans (Nat.floor_le_ceil _)
    have hEk : ((early h ξ U ((k : ℝ) * h) ω).toNat : ℝ) ≤ ME + E0 ω := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0]; simp only [Nat.cast_zero, zero_mul, hE0]; linarith
      · have : (early h ξ U ((k : ℝ) * h) ω).toNat ≤
            (Finset.Icc 1 (m n + 1)).sup fun k => (early h ξ U ((k : ℝ) * h) ω).toNat :=
          Finset.le_sup (f := fun j : ℕ => (early h ξ U ((j : ℝ) * h) ω).toNat)
            (Finset.mem_Icc.mpr ⟨hk0, by omega⟩)
        have : ((early h ξ U ((k : ℝ) * h) ω).toNat : ℝ) ≤ ME := by rw [hME]; exact_mod_cast this
        linarith
    have hLk : ((late h ξ U ((k : ℝ) * h) ω).toNat : ℝ) ≤ ML := by
      have : (late h ξ U ((k : ℝ) * h) ω).toNat ≤
          (Finset.range (m n + 1)).sup fun k => (late h ξ U ((k : ℝ) * h) ω).toNat :=
        Finset.le_sup (f := fun j : ℕ => (late h ξ U ((j : ℝ) * h) ω).toNat)
          (Finset.mem_range.mpr (by omega))
      rw [hML]; exact_mod_cast this
    have hL0 : ((late h ξ U 0 ω).toNat : ℝ) ≤ ML := by
      have : (late h ξ U (((0 : ℕ) : ℝ) * h) ω).toNat ≤
          (Finset.range (m n + 1)).sup fun k => (late h ξ U ((k : ℝ) * h) ω).toNat :=
        Finset.le_sup (f := fun j : ℕ => (late h ξ U ((j : ℝ) * h) ω).toNat)
          (Finset.mem_range.mpr (by omega))
      simp only [Nat.cast_zero, zero_mul] at this
      rw [hML]; exact_mod_cast this
    have hIk : ((arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h) ω).toNat : ℝ) ≤ MI := by
      have : (arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h) ω).toNat ≤
          (Finset.range (m n + 2)).sup fun k =>
            (arrivalsIn h ξ U ((k : ℝ) * h) (((k : ℝ) + 1) * h) ω).toNat :=
        Finset.le_sup (f := fun j : ℕ => (arrivalsIn h ξ U ((j : ℝ) * h) (((j : ℝ) + 1) * h) ω).toNat)
          (Finset.mem_range.mpr (by omega))
      rw [hMI]; exact_mod_cast this
    refine hpath.trans ?_
    rw [hBdef]
    apply mul_le_mul_of_nonneg_left _ hh.le
    simp only [hE0] at hEk ⊢
    linarith
  have hne : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, by simp⟩⟩
  have hsup_le : (⨆ s : Icc (0 : ℝ) 1,
      |h * (ScheduledQueue.Stability.count h ξ U ((n : ℝ) * s) ω : ℝ) - (n : ℝ) * s|) ≤ B :=
    ciSup_le hpt
  have hsup_ge : 0 ≤ (⨆ s : Icc (0 : ℝ) 1,
      |h * (ScheduledQueue.Stability.count h ξ U ((n : ℝ) * s) ω : ℝ) - (n : ℝ) * s|) := by
    have hbdd : BddAbove (Set.range fun s : Icc (0 : ℝ) 1 =>
        |h * (ScheduledQueue.Stability.count h ξ U ((n : ℝ) * s) ω : ℝ) - (n : ℝ) * s|) := by
      refine ⟨B, ?_⟩
      rintro _ ⟨s, rfl⟩
      exact hpt s
    exact le_ciSup_of_le hbdd ⟨0, by simp⟩ (abs_nonneg _)
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hlogn.le) hsup_ge
  · simp only [Function.comp_apply, hYd]
    rw [← hME, ← hML, ← hMI]
    have hinvm : 0 ≤ (Real.log (m n))⁻¹ := inv_nonneg.mpr hlogm.le
    have hinvn : 0 ≤ (Real.log n)⁻¹ := inv_nonneg.mpr hlogn.le
    calc (Real.log n)⁻¹ * (⨆ s : Icc (0 : ℝ) 1,
          |h * (ScheduledQueue.Stability.count h ξ U ((n : ℝ) * s) ω : ℝ) - (n : ℝ) * s|)
        ≤ (Real.log n)⁻¹ * B := mul_le_mul_of_nonneg_left hsup_le hinvn
      _ = h * ((Real.log n)⁻¹ * (ME + 2 * ML + MI)) + h * ((Real.log n)⁻¹ * (2 * E0 ω + 1)) := by
          rw [hBdef]; ring
      _ ≤ h * (2 * (Real.log (m n))⁻¹ * (ME + 2 * ML + MI)) +
            h * ((Real.log n)⁻¹ * (2 * E0 ω + 1)) := by
          gcongr
      _ ≤ 4 * h * ((Real.log (m n))⁻¹ * ME + (Real.log (m n))⁻¹ * ML +
            (Real.log (m n))⁻¹ * MI + (Real.log n)⁻¹ * (2 * E0 ω + 1)) := by
          have a1 : 0 ≤ (Real.log (m n))⁻¹ * ME := mul_nonneg hinvm hME0
          have a2 : 0 ≤ (Real.log (m n))⁻¹ * ML := mul_nonneg hinvm hML0
          have a3 : 0 ≤ (Real.log (m n))⁻¹ * MI := mul_nonneg hinvm hMI0
          have a4 : 0 ≤ (Real.log n)⁻¹ * (2 * E0 ω + 1) := mul_nonneg hinvn (by linarith)
          nlinarith

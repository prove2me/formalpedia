-- Prove2me | solution 1 for PalmQueueing.Ergodic.pointwise_flow
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:23:16.703639+00:00
-- url     : https://prove2.me/submissions/ae33b391-7f46-4fe1-9556-63e3c7a0037b

import Mathlib
import Definitions.Def_PalmQueueing_Ergodic_DiscreteFlow



namespace PalmQueueing.Ergodic

open MeasureTheory Filter Topology
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

section FlowFacts

variable (θ : Flow Ω)

lemma flow_nat (n : ℕ) : θ (n : ℝ) = (θ 1)^[n] := by
  induction n with
  | zero => simp [θ.map_zero]
  | succ n ih =>
    rw [Nat.cast_succ, add_comm, θ.map_add, ih, Function.iterate_succ']

lemma flow_comp_cancel (s : ℝ) (ω : Ω) : θ (-s) (θ s ω) = ω := by
  have := congrFun (θ.map_add (-s) s) ω
  simp only [neg_add_cancel, θ.map_zero, id_eq, Function.comp_apply] at this
  exact this.symm

lemma preimage_iterate_eq_self (T : Ω → Ω) (B : Set Ω) (hB : T ⁻¹' B = B) (n : ℕ) :
    T^[n] ⁻¹' B = B := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ, Set.preimage_comp, ih, hB]

lemma flow_int_preimage (B : Set Ω) (hB : θ 1 ⁻¹' B = B) (m : ℤ) :
    θ (m : ℝ) ⁻¹' B = B := by
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg m
  · subst hn
    simp only [Int.cast_natCast]
    rw [flow_nat]
    exact preimage_iterate_eq_self (θ 1) B hB n
  · subst hn
    simp only [Int.cast_neg, Int.cast_natCast]
    have hn' : θ (n : ℝ) ⁻¹' B = B := by
      rw [flow_nat]; exact preimage_iterate_eq_self (θ 1) B hB n
    ext ω
    constructor
    · intro h
      have : θ (n : ℝ) (θ (-(n : ℝ)) ω) ∈ B := by
        rw [← Set.mem_preimage, hn']; exact h
      have e := congrFun (θ.map_add (n : ℝ) (-(n : ℝ))) ω
      simp only [add_neg_cancel, θ.map_zero, id_eq, Function.comp_apply] at e
      rw [← e] at this
      exact this
    · intro h
      show θ (-(n : ℝ)) ω ∈ B
      rw [← hn', Set.mem_preimage]
      have e := congrFun (θ.map_add (n : ℝ) (-(n : ℝ))) ω
      simp only [add_neg_cancel, θ.map_zero, id_eq, Function.comp_apply] at e
      rw [← e]; exact h

lemma flow_apply_add (s t : ℝ) (ω : Ω) : θ (t + s) ω = θ t (θ s ω) := by
  have := congrFun (θ.map_add t s) ω
  simpa using this

/-- Change of variables along the flow (unconditional). -/
lemma shift_integral (g : Ω → ℝ) (ω : Ω) (s a b : ℝ) :
    ∫ t in a..b, g (θ t (θ s ω)) = ∫ t in a + s..b + s, g (θ t ω) := by
  rw [← intervalIntegral.integral_comp_add_right (fun t => g (θ t ω)) s]
  congr 1
  ext t
  rw [flow_apply_add]

lemma measurable_flow_swap (g : Ω → ℝ) (hg : Measurable g) :
    Measurable (fun p : Ω × ℝ => g (θ p.2 p.1)) := by
  have : (fun p : Ω × ℝ => g (θ p.2 p.1)) =
      g ∘ (fun p : ℝ × Ω => θ p.1 p.2) ∘ Prod.swap := by
    funext p; rfl
  rw [this]
  exact hg.comp (θ.measurable_uncurry.comp measurable_swap)

lemma integrable_comp_flow (P : Measure Ω) (hinv : θ.Invariant P)
    (h : Ω → ℝ) (hh : Measurable h) (hint : Integrable h P) (t : ℝ) :
    Integrable (fun ω => h (θ t ω)) P := by
  have : Integrable h (Measure.map (θ t) P) := by rwa [hinv t]
  exact (integrable_map_measure hh.aestronglyMeasurable (θ.measurable' t).aemeasurable).1 this

lemma integral_comp_flow (P : Measure Ω) (hinv : θ.Invariant P)
    (h : Ω → ℝ) (hh : Measurable h) (t : ℝ) : ∫ ω, h (θ t ω) ∂P = ∫ ω, h ω ∂P := by
  conv_rhs => rw [← hinv t]
  rw [integral_map (θ.measurable' t).aemeasurable hh.aestronglyMeasurable]

lemma integrable_prod_flow (P : Measure Ω) [IsProbabilityMeasure P] (hinv : θ.Invariant P)
    (g : Ω → ℝ) (hg : Measurable g) (hgi : Integrable g P) (a b : ℝ) :
    Integrable (fun p : Ω × ℝ => g (θ p.2 p.1)) (P.prod (volume.restrict (Set.Ioc a b))) := by
  have hm := measurable_flow_swap θ g hg
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  constructor
  · exact ae_of_all _ fun t => integrable_comp_flow θ P hinv g hg hgi t
  · have : (fun t => ∫ ω, ‖g (θ t ω)‖ ∂P) = fun _ => ∫ ω, ‖g ω‖ ∂P := by
      funext t
      exact integral_comp_flow θ P hinv (fun ω => ‖g ω‖) hg.norm t
    rw [this]
    exact integrable_const _

/-- Almost every trajectory is locally integrable on `[0, n]` for every `n`. -/
lemma ae_locally_integrable (P : Measure Ω) [IsProbabilityMeasure P] (hinv : θ.Invariant P)
    (g : Ω → ℝ) (hg : Measurable g) (hgi : Integrable g P) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, IntervalIntegrable (fun t => g (θ t ω)) volume 0 n := by
  rw [ae_all_iff]
  intro n
  have := (integrable_prod_flow θ P hinv g hg hgi 0 n).prod_right_ae
  filter_upwards [this] with ω hω
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)]
  exact hω

/-- The averaged function `F ω = ∫_0^1 g(θ_t ω) dt`. -/
lemma avg_props (P : Measure Ω) [IsProbabilityMeasure P] (hinv : θ.Invariant P)
    (g : Ω → ℝ) (hg : Measurable g) (hgi : Integrable g P) :
    Measurable (fun ω => ∫ t in (0 : ℝ)..1, g (θ t ω)) ∧
    Integrable (fun ω => ∫ t in (0 : ℝ)..1, g (θ t ω)) P ∧
    ∫ ω, (∫ t in (0 : ℝ)..1, g (θ t ω)) ∂P = ∫ ω, g ω ∂P := by
  have hm := measurable_flow_swap θ g hg
  have hI := integrable_prod_flow θ P hinv g hg hgi 0 1
  have e : (fun ω => ∫ t in (0 : ℝ)..1, g (θ t ω)) =
      fun ω => ∫ t, (fun p : Ω × ℝ => g (θ p.2 p.1)) (ω, t) ∂(volume.restrict (Set.Ioc 0 1)) := by
    funext ω
    rw [intervalIntegral.integral_of_le zero_le_one]
  rw [e]
  refine ⟨hm.stronglyMeasurable.integral_prod_right'.measurable, hI.integral_prod_left, ?_⟩
  rw [← integral_prod _ hI, integral_prod_symm _ hI]
  have e2 : (fun t => ∫ ω, (fun p : Ω × ℝ => g (θ p.2 p.1)) (ω, t) ∂P) = fun _ => ∫ ω, g ω ∂P := by
    funext t
    exact integral_comp_flow θ P hinv g hg t
  rw [e2, integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc]
  simp

/-- Replacing `f` by an a.e.-equal measurable `g` does not change the time integrals, a.s. -/
lemma ae_time_integral_congr (P : Measure Ω) [IsProbabilityMeasure P] (hinv : θ.Invariant P)
    (f g : Ω → ℝ) (hfg : f =ᵐ[P] g) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, ∫ t in Set.Ioc (0 : ℝ) T, f (θ t ω) = ∫ t in Set.Ioc (0 : ℝ) T, g (θ t ω) := by
  have h0 : P {ω | f ω ≠ g ω} = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at hfg; exact hfg
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null h0
  have hE : MeasurableSet {p : ℝ × Ω | θ p.1 p.2 ∈ N} := θ.measurable_uncurry hNm
  have hEzero : (volume.prod P) {p : ℝ × Ω | θ p.1 p.2 ∈ N} = 0 := by
    rw [Measure.prod_apply hE]
    have : ∀ t : ℝ, P (Prod.mk t ⁻¹' {p : ℝ × Ω | θ p.1 p.2 ∈ N}) = 0 := by
      intro t
      have e : Prod.mk t ⁻¹' {p : ℝ × Ω | θ p.1 p.2 ∈ N} = θ t ⁻¹' N := by ext ω; simp
      rw [e, ← Measure.map_apply (θ.measurable' t) hNm, hinv t]
      exact hN0
    exact (lintegral_congr this).trans lintegral_zero
  rw [Measure.prod_apply_symm hE] at hEzero
  have hsec := (lintegral_eq_zero_iff (measurable_measure_prodMk_right hE)).1 hEzero
  filter_upwards [hsec] with ω hω T
  simp only [Pi.zero_apply] at hω
  apply integral_congr_ae
  apply ae_restrict_of_ae
  have : ∀ᵐ t ∂(volume : Measure ℝ), θ t ω ∉ N := by
    rw [ae_iff]
    simp only [not_not]
    exact hω
  filter_upwards [this] with t ht
  by_contra hne
  exact ht (hsub hne)

end FlowFacts

section Birkhoff

variable (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → Ω)

lemma exists_nat_one_div_lt' {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, 1 / ((k : ℝ) + 1) < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  refine ⟨k, ?_⟩
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  rw [div_lt_iff₀ hk1]
  have : 1 / ε < (k : ℝ) + 1 := by linarith
  rw [div_lt_iff₀ hε] at this
  linarith

lemma integral_comp_eq (hTm : Measurable T) (hinv : Measure.map T P = P)
    (h : Ω → ℝ) (hh : Measurable h) : ∫ ω, h (T ω) ∂P = ∫ ω, h ω ∂P := by
  conv_rhs => rw [← hinv]
  rw [integral_map hTm.aemeasurable hh.aestronglyMeasurable]

lemma integrable_comp_of (hTm : Measurable T) (hinv : Measure.map T P = P)
    (h : Ω → ℝ) (hh : Measurable h) (hint : Integrable h P) :
    Integrable (fun ω => h (T ω)) P := by
  have : Integrable h (Measure.map T P) := by rwa [hinv]
  exact (integrable_map_measure hh.aestronglyMeasurable hTm.aemeasurable).1 this

lemma measurable_birkhoffSum (hTm : Measurable T) (f : Ω → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffSum T f n) := by
  unfold birkhoffSum
  exact Finset.measurable_sum _ (fun k _ => hf.comp (hTm.iterate k))

/-- Garsia's auxiliary functions: `garsia T g N = max_{1 ≤ n ≤ N+1} S_n g`. -/
noncomputable def garsia (g : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => g
  | (N + 1) => fun ω => g ω + max (garsia g N (T ω)) 0

lemma garsia_succ (g : Ω → ℝ) (N : ℕ) (ω : Ω) :
    garsia T g (N + 1) ω = g ω + max (garsia T g N (T ω)) 0 := rfl

lemma garsia_measurable (hTm : Measurable T) (g : Ω → ℝ) (hg : Measurable g) :
    ∀ N, Measurable (garsia T g N)
  | 0 => hg
  | N + 1 => by
      show Measurable (fun ω => g ω + max (garsia T g N (T ω)) 0)
      exact hg.add (((garsia_measurable hTm g hg N).comp hTm).max measurable_const)

lemma garsia_integrable (hTm : Measurable T) (hinv : Measure.map T P = P)
    (g : Ω → ℝ) (hg : Measurable g) (hgi : Integrable g P) :
    ∀ N, Integrable (garsia T g N) P
  | 0 => hgi
  | N + 1 => by
      show Integrable (fun ω => g ω + max (garsia T g N (T ω)) 0) P
      exact hgi.add ((integrable_comp_of P T hTm hinv _ (garsia_measurable T hTm g hg N)
        (garsia_integrable hTm hinv g hg hgi N)).pos_part)

lemma garsia_mono (g : Ω → ℝ) : ∀ N ω, garsia T g N ω ≤ garsia T g (N + 1) ω
  | 0, ω => by
      show g ω ≤ g ω + max (garsia T g 0 (T ω)) 0
      linarith [le_max_right (garsia T g 0 (T ω)) 0]
  | N + 1, ω => by
      rw [garsia_succ, garsia_succ]
      exact add_le_add le_rfl (max_le_max (garsia_mono g N (T ω)) le_rfl)

lemma birkhoffSum_le_garsia (g : Ω → ℝ) :
    ∀ N n ω, 1 ≤ n → n ≤ N + 1 → birkhoffSum T g n ω ≤ garsia T g N ω
  | 0, n, ω, h1, h2 => by
      have : n = 1 := by omega
      subst this
      rw [birkhoffSum_one]
      exact le_rfl
  | N + 1, n, ω, h1, h2 => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [birkhoffSum_succ', garsia_succ]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [birkhoffSum_zero]
        linarith [le_max_right (garsia T g N (T ω)) 0]
      · exact add_le_add le_rfl
          ((birkhoffSum_le_garsia g N m (T ω) hm (by omega)).trans (le_max_left _ _))

lemma garsia_attained (g : Ω → ℝ) :
    ∀ N ω, ∃ n, 1 ≤ n ∧ n ≤ N + 1 ∧ garsia T g N ω = birkhoffSum T g n ω
  | 0, ω => ⟨1, le_rfl, le_rfl, by rw [birkhoffSum_one]; rfl⟩
  | N + 1, ω => by
      rw [garsia_succ]
      rcases le_or_gt 0 (garsia T g N (T ω)) with h | h
      · obtain ⟨n, h1, h2, h3⟩ := garsia_attained g N (T ω)
        refine ⟨n + 1, by omega, by omega, ?_⟩
        rw [birkhoffSum_succ', max_eq_left h, h3]
      · exact ⟨1, le_rfl, by omega, by rw [max_eq_right h.le, birkhoffSum_one, add_zero]⟩

/-- The maximal ergodic lemma (Garsia's proof). -/
theorem maximal_ergodic (hTm : Measurable T) (hinv : Measure.map T P = P)
    (g : Ω → ℝ) (hg : Measurable g) (hgi : Integrable g P) :
    0 ≤ ∫ ω in {ω | ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T g n ω}, g ω ∂P := by
  set A := {ω | ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T g n ω} with hA
  set AN : ℕ → Set Ω := fun N => {ω | 0 < garsia T g N ω} with hAN
  have hGm : ∀ N, Measurable (garsia T g N) := garsia_measurable T hTm g hg
  have hGi : ∀ N, Integrable (garsia T g N) P := garsia_integrable P T hTm hinv g hg hgi
  have hANm : ∀ N, MeasurableSet (AN N) := fun N => measurableSet_lt measurable_const (hGm N)
  have hANmono : Monotone AN := by
    intro M N hMN ω hω
    simp only [hAN, Set.mem_setOf_eq] at hω ⊢
    have hm : Monotone (fun N => garsia T g N ω) :=
      monotone_nat_of_le_succ (fun N => garsia_mono T g N ω)
    exact lt_of_lt_of_le hω (hm hMN)
  have hUnion : (⋃ N, AN N) = A := by
    ext ω
    simp only [Set.mem_iUnion, hAN, hA, Set.mem_setOf_eq]
    constructor
    · rintro ⟨N, hN⟩
      obtain ⟨n, h1, _, h3⟩ := garsia_attained T g N ω
      exact ⟨n, h1, by rw [← h3]; exact hN⟩
    · rintro ⟨n, h1, hn⟩
      exact ⟨n, lt_of_lt_of_le hn (birkhoffSum_le_garsia T g n n ω h1 (by omega))⟩
  have hkey : ∀ N, 0 ≤ ∫ ω in AN N, g ω ∂P := by
    intro N
    set Gp : Ω → ℝ := fun ω => max (garsia T g N ω) 0 with hGp
    have hGpm : Measurable Gp := (hGm N).max measurable_const
    have hGpi : Integrable Gp P := (hGi N).pos_part
    have hGpTi : Integrable (fun ω => Gp (T ω)) P :=
      integrable_comp_of P T hTm hinv Gp hGpm hGpi
    have hGpT : ∫ ω, Gp (T ω) ∂P = ∫ ω, Gp ω ∂P := integral_comp_eq P T hTm hinv Gp hGpm
    have h1 : ∫ ω in AN N, (Gp ω - Gp (T ω)) ∂P ≤ ∫ ω in AN N, g ω ∂P := by
      apply setIntegral_mono_on (hGpi.sub hGpTi).integrableOn hgi.integrableOn (hANm N)
      intro ω hω
      simp only [hAN, Set.mem_setOf_eq] at hω
      have e1 : garsia T g N ω ≤ garsia T g (N + 1) ω := garsia_mono T g N ω
      rw [garsia_succ] at e1
      simp only [Pi.sub_apply, hGp]
      rw [max_eq_left hω.le]
      linarith
    have h2 : ∫ ω in AN N, Gp ω ∂P = ∫ ω, Gp ω ∂P := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro ω hω
      simp only [hAN, Set.mem_setOf_eq, not_lt] at hω
      simp only [hGp]
      exact max_eq_right hω
    have h3 : ∫ ω in AN N, Gp (T ω) ∂P ≤ ∫ ω, Gp (T ω) ∂P := by
      apply setIntegral_le_integral hGpTi
      exact Filter.Eventually.of_forall (fun ω => le_max_right _ _)
    rw [integral_sub hGpi.integrableOn hGpTi.integrableOn, h2] at h1
    linarith
  have hlim : Tendsto (fun N => ∫ ω in AN N, g ω ∂P) atTop (𝓝 (∫ ω in ⋃ N, AN N, g ω ∂P)) :=
    tendsto_setIntegral_of_monotone hANm hANmono hgi.integrableOn
  rw [hUnion] at hlim
  exact ge_of_tendsto' hlim hkey

/-- `{ω | S_n f ω > n a  for infinitely many n}`. -/
def freqSet (f : Ω → ℝ) (a : ℝ) : Set Ω :=
  {ω | ∀ N : ℕ, ∃ n, N ≤ n ∧ (n : ℝ) * a < birkhoffSum T f n ω}

/-- `{ω | limsup S_n f ω / n ≥ a}`, written without limsup. -/
def limsupSet (f : Ω → ℝ) (a : ℝ) : Set Ω :=
  ⋂ k : ℕ, freqSet T f (a - 1 / ((k : ℝ) + 1))

lemma freqSet_measurable (hTm : Measurable T) (f : Ω → ℝ) (hf : Measurable f) (a : ℝ) :
    MeasurableSet (freqSet T f a) := by
  have : freqSet T f a = ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n),
      {ω | (n : ℝ) * a < birkhoffSum T f n ω} := by
    ext ω
    simp [freqSet]
  rw [this]
  refine MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_lt measurable_const (measurable_birkhoffSum T hTm f hf n)

lemma limsupSet_measurable (hTm : Measurable T) (f : Ω → ℝ) (hf : Measurable f) (a : ℝ) :
    MeasurableSet (limsupSet T f a) :=
  MeasurableSet.iInter fun k => freqSet_measurable T hTm f hf _

lemma freq_shift_fwd (f : Ω → ℝ) (a δ : ℝ) (hδ : 0 < δ) (ω : Ω)
    (h : ω ∈ freqSet T f (a - δ / 2)) : T ω ∈ freqSet T f (a - δ) := by
  intro N
  set M0 : ℕ := ⌈(f ω - a + δ) / (δ / 2)⌉₊ with hM0
  have hM0' : f ω - a + δ ≤ (M0 : ℝ) * (δ / 2) := by
    have := Nat.le_ceil ((f ω - a + δ) / (δ / 2))
    rw [div_le_iff₀ (by positivity)] at this
    exact this
  obtain ⟨m, hm, hlt⟩ := h (max (N + 1) M0)
  have hmN : N + 1 ≤ m := le_trans (le_max_left _ _) hm
  have hmM : M0 ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine ⟨n, by omega, ?_⟩
  rw [birkhoffSum_succ'] at hlt
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hlt
  have hM : (M0 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hmM
  have hprod : (M0 : ℝ) * (δ / 2) ≤ ((n : ℝ) + 1) * (δ / 2) :=
    mul_le_mul_of_nonneg_right hM (by positivity)
  nlinarith

lemma freq_shift_bwd (f : Ω → ℝ) (a δ : ℝ) (hδ : 0 < δ) (ω : Ω)
    (h : T ω ∈ freqSet T f (a - δ / 2)) : ω ∈ freqSet T f (a - δ) := by
  intro N
  set M0 : ℕ := ⌈(a - δ - f ω) / (δ / 2)⌉₊ with hM0
  have hM0' : a - δ - f ω ≤ (M0 : ℝ) * (δ / 2) := by
    have := Nat.le_ceil ((a - δ - f ω) / (δ / 2))
    rw [div_le_iff₀ (by positivity)] at this
    exact this
  obtain ⟨n, hn, hlt⟩ := h (max N M0)
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnM : M0 ≤ n := le_trans (le_max_right _ _) hn
  refine ⟨n + 1, by omega, ?_⟩
  rw [birkhoffSum_succ']
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hM : (M0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnM
  have hprod : (M0 : ℝ) * (δ / 2) ≤ (n : ℝ) * (δ / 2) :=
    mul_le_mul_of_nonneg_right hM (by positivity)
  nlinarith

lemma half_eq (k : ℕ) : (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ) + 1) = (1 / ((k : ℝ) + 1)) / 2 := by
  push_cast
  field_simp
  ring

lemma limsupSet_invariant (f : Ω → ℝ) (a : ℝ) : T ⁻¹' limsupSet T f a = limsupSet T f a := by
  ext ω
  simp only [Set.mem_preimage, limsupSet, Set.mem_iInter]
  constructor
  · intro h k
    have h' := h (2 * k + 1)
    rw [half_eq] at h'
    exact freq_shift_bwd T f a (1 / ((k : ℝ) + 1)) (by positivity) ω h'
  · intro h k
    have h' := h (2 * k + 1)
    rw [half_eq] at h'
    exact freq_shift_fwd T f a (1 / ((k : ℝ) + 1)) (by positivity) ω h'


theorem birkhoff_upper' (hTm : Measurable T) (hinv : Measure.map T P = P)
    (f : Ω → ℝ) (hf : Measurable f) (hfi : Integrable f P)
    (hL : ∀ a : ℝ, limsupSet T f a =ᵐ[P] (∅ : Set Ω) ∨ limsupSet T f a =ᵐ[P] Set.univ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, birkhoffSum T f n ω ≤ (n : ℝ) * ((∫ ω, f ω ∂P) + ε) := by
  set a : ℝ := (∫ ω, f ω ∂P) + ε with ha
  set L := limsupSet T f a with hL'
  rcases hL a with hempty | huniv
  · rw [ae_eq_empty] at hempty
    have hae : ∀ᵐ ω ∂P, ω ∉ L := by
      rw [ae_iff]
      simpa using hempty
    filter_upwards [hae] with ω hω
    simp only [hL', limsupSet, Set.mem_iInter, not_forall] at hω
    obtain ⟨k, hk⟩ := hω
    simp only [freqSet, Set.mem_setOf_eq, not_forall, not_exists, not_and, not_lt] at hk
    obtain ⟨N, hN⟩ := hk
    rw [eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    have h2 : (n : ℝ) * (a - 1 / ((k : ℝ) + 1)) ≤ (n : ℝ) * a := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    exact h1.trans h2
  · exfalso
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt' hε
    set a' : ℝ := a - 1 / ((k : ℝ) + 1) with ha'
    have ha'gt : (∫ ω, f ω ∂P) < a' := by rw [ha', ha]; linarith
    set g : Ω → ℝ := fun ω => f ω - a' with hg
    have hgm : Measurable g := hf.sub measurable_const
    have hgi : Integrable g P := hfi.sub (integrable_const _)
    have hgsum : ∀ n ω, birkhoffSum T g n ω = birkhoffSum T f n ω - (n : ℝ) * a' := by
      intro n ω
      have : g = f - fun _ => a' := by funext ω; simp [hg]
      rw [this, birkhoffSum_sub]
      congr 1
      simp [birkhoffSum]
    set A := {ω | ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T g n ω} with hA
    have hLA : L ⊆ A := by
      intro ω hω
      simp only [hL', limsupSet, Set.mem_iInter] at hω
      have := hω k 1
      obtain ⟨n, hn, hlt⟩ := this
      refine ⟨n, hn, ?_⟩
      rw [hgsum]
      linarith
    have hAuniv : A =ᵐ[P] (Set.univ : Set Ω) := by
      rw [ae_eq_univ] at huniv ⊢
      exact measure_mono_null (Set.compl_subset_compl.2 hLA) huniv
    have hmax := maximal_ergodic P T hTm hinv g hgm hgi
    rw [setIntegral_congr_set hAuniv, setIntegral_univ] at hmax
    have : ∫ ω, g ω ∂P = (∫ ω, f ω ∂P) - a' := by
      simp only [hg]
      rw [integral_sub hfi (integrable_const _)]
      simp
    linarith

theorem birkhoff_tendsto' (hTm : Measurable T) (hinv : Measure.map T P = P)
    (f : Ω → ℝ) (hf : Measurable f) (hfi : Integrable f P)
    (hL : ∀ a : ℝ, limsupSet T f a =ᵐ[P] (∅ : Set Ω) ∨ limsupSet T f a =ᵐ[P] Set.univ)
    (hLn : ∀ a : ℝ, limsupSet T (-f) a =ᵐ[P] (∅ : Set Ω) ∨ limsupSet T (-f) a =ᵐ[P] Set.univ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => birkhoffSum T f n ω / (n : ℝ)) atTop (𝓝 (∫ ω, f ω ∂P)) := by
  have hup : ∀ j : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      birkhoffSum T f n ω ≤ (n : ℝ) * ((∫ ω, f ω ∂P) + 1 / ((j : ℝ) + 1)) :=
    fun j => birkhoff_upper' P T hTm hinv f hf hfi hL _ (by positivity)
  have hlow : ∀ j : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * ((∫ ω, f ω ∂P) - 1 / ((j : ℝ) + 1)) ≤ birkhoffSum T f n ω := by
    intro j
    have := birkhoff_upper' P T hTm hinv (-f) hf.neg hfi.neg hLn (1 / ((j : ℝ) + 1))
      (by positivity)
    filter_upwards [this] with ω hω
    filter_upwards [hω] with n hn
    rw [birkhoffSum_neg] at hn
    have hneg : ∫ ω, (-f) ω ∂P = -∫ ω, f ω ∂P := by
      simp only [Pi.neg_apply]; exact integral_neg f
    rw [hneg] at hn
    linarith
  have hup' := ae_all_iff.2 hup
  have hlow' := ae_all_iff.2 hlow
  filter_upwards [hup', hlow'] with ω hu hl
  set I := ∫ ω, f ω ∂P with hI
  rw [tendsto_order]
  constructor
  · intro b hb
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt' (sub_pos.2 hb)
    have h1 := hl j
    filter_upwards [h1, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [lt_div_iff₀ hnpos]
    have : b < I - 1 / ((j : ℝ) + 1) := by linarith
    calc b * (n : ℝ) = (n : ℝ) * b := by ring
      _ < (n : ℝ) * (I - 1 / ((j : ℝ) + 1)) := mul_lt_mul_of_pos_left this hnpos
      _ ≤ _ := hn
  · intro b hb
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt' (sub_pos.2 hb)
    have h1 := hu j
    filter_upwards [h1, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_lt_iff₀ hnpos]
    have : I + 1 / ((j : ℝ) + 1) < b := by linarith
    calc birkhoffSum T f n ω ≤ (n : ℝ) * (I + 1 / ((j : ℝ) + 1)) := hn
      _ < (n : ℝ) * b := mul_lt_mul_of_pos_left this hnpos
      _ = b * (n : ℝ) := by ring

/-- Borel–Cantelli: `G ∘ T^n = o(n)` almost surely for an integrable non-negative `G`. -/
lemma iterate_eventually_le (hTm : Measurable T) (hinv : Measure.map T P = P)
    (G : Ω → ℝ) (hGm : Measurable G) (hGi : Integrable G P) (hG0 : ∀ ω, 0 ≤ G ω) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, G (T^[n] ω) ≤ (n : ℝ) / ((k : ℝ) + 1) := by
  rw [ae_all_iff]
  intro k
  set X : Ω → ℝ := fun ω => ((k : ℝ) + 1) * G ω with hX
  have hXi : Integrable X P := hGi.const_mul _
  have hX0 : 0 ≤ X := fun ω => by
    simp only [hX, Pi.zero_apply]
    exact mul_nonneg (by positivity) (hG0 ω)
  have hmp : MeasurePreserving T P P := ⟨hTm, hinv⟩
  set s : ℕ → Set Ω := fun n => T^[n] ⁻¹' {ω | X ω ∈ Set.Ioi (n : ℝ)} with hs
  have hsm : ∀ n : ℕ, MeasurableSet {ω | X ω ∈ Set.Ioi (n : ℝ)} :=
    fun n => (hGm.const_mul _) measurableSet_Ioi
  have hPs : ∀ n, P (s n) = P {ω | X ω ∈ Set.Ioi (n : ℝ)} := fun n => by
    simp only [hs]
    rw [← Measure.map_apply (hTm.iterate n) (hsm n), (hmp.iterate n).map_eq]
  have htsum : ∑' n, P (s n) ≠ ⊤ := by
    simp_rw [hPs]
    letI : MeasureSpace Ω := ⟨P⟩
    haveI : IsProbabilityMeasure (volume : Measure Ω) := ‹IsProbabilityMeasure P›
    exact (ProbabilityTheory.tsum_prob_mem_Ioi_lt_top hXi hX0).ne
  have := ae_eventually_notMem htsum
  filter_upwards [this] with ω hω
  filter_upwards [hω] with n hn
  simp only [hs, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioi, not_lt, hX] at hn
  rw [le_div_iff₀ (by positivity)]
  linarith

lemma tendsto_div_of_eventually_le (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n)
    (h : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, u n ≤ (n : ℝ) / ((k : ℝ) + 1)) :
    Tendsto (fun n : ℕ => u n / (n : ℝ)) atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact lt_of_lt_of_le hb (div_nonneg (hu0 n) this.le)
  · intro b hb
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt' hb
    filter_upwards [h k, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_lt_iff₀ hnpos]
    calc u n ≤ (n : ℝ) / ((k : ℝ) + 1) := hn
      _ = (n : ℝ) * (1 / ((k : ℝ) + 1)) := by ring
      _ < (n : ℝ) * b := mul_lt_mul_of_pos_left hk hnpos
      _ = b * n := by ring

/-- Transfer of the "frequently above `a - δ/2`" property to a sequence at bounded distance. -/
lemma freq_transfer (u v : ℕ → ℝ) (C : ℝ) (e : ℕ → ℝ) (hb : ∀ n, |u n - v n| ≤ C + e n)
    (he : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, e n ≤ (n : ℝ) / ((k : ℝ) + 1)) (a δ : ℝ) (hδ : 0 < δ)
    (h : ∀ N : ℕ, ∃ n, N ≤ n ∧ (n : ℝ) * (a - δ / 2) < u n) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧ (n : ℝ) * (a - δ) < v n := by
  intro N
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt' (show (0 : ℝ) < δ / 4 by positivity)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (he k)
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (4 * C / δ)
  obtain ⟨n, hn, hlt⟩ := h (max N (max N₁ N₂))
  refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : (N₂ : ℝ) ≤ n := by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have he' : e n ≤ (n : ℝ) * (δ / 4) := by
    calc e n ≤ (n : ℝ) / ((k : ℝ) + 1) := hN₁ n hn1
      _ = (n : ℝ) * (1 / ((k : ℝ) + 1)) := by ring
      _ ≤ (n : ℝ) * (δ / 4) := mul_le_mul_of_nonneg_left hk.le (Nat.cast_nonneg n)
  have hC : C ≤ (n : ℝ) * (δ / 4) := by
    have : 4 * C / δ ≤ n := hN₂.trans hn2
    rw [div_le_iff₀ hδ] at this
    linarith
  have := hb n
  rw [abs_le] at this
  nlinarith [this.1, this.2]

end Birkhoff

/-- A measurable set that is a.e. invariant under every `θ_t` is null or co-null for an ergodic
flow: replace it by the exactly invariant set `{ω | θ_t ω ∈ B for a.e. t}`. -/
lemma flow_ae_invariant_null_or_conull (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Flow Ω) (herg : IsErgodicFlow θ P) (B : Set Ω) (hB : MeasurableSet B)
    (hae : ∀ t : ℝ, P (B \ θ t ⁻¹' B) = 0 ∧ P (θ t ⁻¹' B \ B) = 0) :
    P B = 0 ∨ P Bᶜ = 0 := by
  have hS : MeasurableSet {p : ℝ × Ω | θ p.1 p.2 ∈ B} := θ.measurable_uncurry hB
  have hSc : MeasurableSet {p : ℝ × Ω | θ p.1 p.2 ∉ B} := θ.measurable_uncurry hB.compl
  have hB2 : MeasurableSet {p : ℝ × Ω | p.2 ∈ B} := measurable_snd hB
  set D : Set (ℝ × Ω) := ({p : ℝ × Ω | θ p.1 p.2 ∈ B} \ {p | p.2 ∈ B}) ∪
    ({p | p.2 ∈ B} \ {p : ℝ × Ω | θ p.1 p.2 ∈ B}) with hD
  have hDm : MeasurableSet D := (hS.diff hB2).union (hB2.diff hS)
  have hDzero : (volume.prod P) D = 0 := by
    rw [Measure.prod_apply hDm]
    have : ∀ t : ℝ, P (Prod.mk t ⁻¹' D) = 0 := by
      intro t
      have e : Prod.mk t ⁻¹' D = (θ t ⁻¹' B \ B) ∪ (B \ θ t ⁻¹' B) := by
        ext ω; simp [hD]
      rw [e]; exact measure_union_null (hae t).2 (hae t).1
    simp [this]
  have hsec : ∀ᵐ ω ∂P, volume ((fun t => (t, ω)) ⁻¹' D) = 0 := by
    rw [Measure.prod_apply_symm hDm] at hDzero
    have := (lintegral_eq_zero_iff (measurable_measure_prodMk_right hDm)).1 hDzero
    filter_upwards [this] with ω hω
    simpa using hω
  set B' : Set Ω :=
    {ω | volume ((fun t => (t, ω)) ⁻¹' {p : ℝ × Ω | θ p.1 p.2 ∉ B}) = 0} with hB'
  have hB'm : MeasurableSet B' :=
    measurable_measure_prodMk_right hSc (measurableSet_singleton 0)
  have hB'inv : ∀ s : ℝ, θ s ⁻¹' B' = B' := by
    intro s
    ext ω
    simp only [hB', Set.mem_preimage, Set.mem_setOf_eq]
    have e : (fun t => (t, θ s ω)) ⁻¹' {p : ℝ × Ω | θ p.1 p.2 ∉ B} =
        (fun t => t + s) ⁻¹' ((fun t => (t, ω)) ⁻¹' {p : ℝ × Ω | θ p.1 p.2 ∉ B}) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [θ.map_add]
      rfl
    rw [e, measure_preimage_add_right]
  have hBB' : ∀ᵐ ω ∂P, ω ∈ B ↔ ω ∈ B' := by
    filter_upwards [hsec] with ω hω
    constructor
    · intro hωB
      simp only [hB', Set.mem_setOf_eq]
      apply measure_mono_null _ hω
      intro t ht
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at ht
      simp only [hD, Set.mem_preimage, Set.mem_union, Set.mem_diff, Set.mem_setOf_eq]
      exact Or.inr ⟨hωB, ht⟩
    · intro hωB'
      by_contra hωB
      simp only [hB', Set.mem_setOf_eq] at hωB'
      have hsub : (fun t => (t, ω)) ⁻¹' {p : ℝ × Ω | θ p.1 p.2 ∈ B} ⊆
          (fun t => (t, ω)) ⁻¹' D := by
        intro t ht
        simp only [Set.mem_preimage, Set.mem_setOf_eq] at ht
        simp only [hD, Set.mem_preimage, Set.mem_union, Set.mem_diff, Set.mem_setOf_eq]
        exact Or.inl ⟨ht, hωB⟩
      have h0 : volume ((fun t => (t, ω)) ⁻¹' {p : ℝ × Ω | θ p.1 p.2 ∈ B}) = 0 :=
        measure_mono_null hsub hω
      have hcompl : (fun t => (t, ω)) ⁻¹' {p : ℝ × Ω | θ p.1 p.2 ∉ B} =
          ((fun t => (t, ω)) ⁻¹' {p : ℝ × Ω | θ p.1 p.2 ∈ B})ᶜ := by
        ext t; simp
      have := measure_univ_le_add_compl (μ := (volume : Measure ℝ))
        ((fun t => (t, ω)) ⁻¹' {p : ℝ × Ω | θ p.1 p.2 ∈ B})
      rw [h0, zero_add, ← hcompl, hωB', Real.volume_univ] at this
      exact absurd this (by simp)
  have hBeq : B =ᵐ[P] B' := by
    rw [ae_eq_set]
    constructor
    · have : ∀ᵐ ω ∂P, ω ∉ B \ B' := by
        filter_upwards [hBB'] with ω hω
        intro h; exact h.2 (hω.1 h.1)
      have := ae_iff.1 this
      simp only [not_not] at this
      exact this
    · have : ∀ᵐ ω ∂P, ω ∉ B' \ B := by
        filter_upwards [hBB'] with ω hω
        intro h; exact h.2 (hω.2 h.1)
      have := ae_iff.1 this
      simp only [not_not] at this
      exact this
  have hPB : P B = P B' := measure_congr hBeq
  have hPBc : P Bᶜ = P B'ᶜ := measure_congr hBeq.compl
  rcases herg.2 B' hB'm hB'inv with h | h
  · left; rw [hPB]; exact h
  · right; rw [hPBc, prob_compl_eq_one_sub hB'm, h, tsub_self]


section FlowBirkhoff

variable (θ : Flow Ω) (P : Measure Ω) [IsProbabilityMeasure P]

/-- `F ω = ∫_0^1 g(θ_t ω) dt`. -/
noncomputable def avgF (g : Ω → ℝ) (ω : Ω) : ℝ := ∫ t in (0 : ℝ)..1, g (θ t ω)

lemma avgF_abs_nonneg (g : Ω → ℝ) (ω : Ω) : 0 ≤ avgF θ (fun ω => |g ω|) ω :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)

lemma ii_sub (h : ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hca : c ≤ a) (hbd : b ≤ d)
    (hI : IntervalIntegrable h volume c d) : IntervalIntegrable h volume a b :=
  hI.mono_set (by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (hca.trans (hab.trans hbd))]
    exact Set.Icc_subset_Icc hca hbd)

lemma birkhoffSum_eq_time_integral (g : Ω → ℝ) (ω : Ω)
    (hloc : ∀ n : ℕ, IntervalIntegrable (fun t => g (θ t ω)) volume 0 n) (n : ℕ) :
    birkhoffSum (θ 1) (avgF θ g) n ω = ∫ t in (0 : ℝ)..n, g (θ t ω) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [birkhoffSum_succ, ih, ← flow_nat, avgF, shift_integral, zero_add, add_comm (1 : ℝ) (n : ℝ)]
    push_cast
    rw [intervalIntegral.integral_add_adjacent_intervals (hloc n)
      (ii_sub (fun t => g (θ t ω)) (n : ℝ) ((n : ℝ) + 1) 0 ((n : ℝ) + 1) (by linarith)
        (Nat.cast_nonneg n) le_rfl (by exact_mod_cast hloc (n + 1)))]

lemma loc_shift (g : Ω → ℝ) (ω : Ω) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hloc : ∀ n : ℕ, IntervalIntegrable (fun t => g (θ t ω)) volume 0 n) :
    ∀ n : ℕ, IntervalIntegrable (fun t => g (θ t (θ s ω))) volume 0 n := by
  intro n
  have h1 : IntervalIntegrable (fun t => g (θ t ω)) volume s (n + s) :=
    ii_sub (fun t => g (θ t ω)) s ((n : ℝ) + s) 0 ((n : ℝ) + 1) (by linarith) hs0 (by linarith)
      (by exact_mod_cast hloc (n + 1))
  have h2 := h1.comp_add_right s
  simp only [sub_self, add_sub_cancel_right] at h2
  have : (fun t => g (θ t (θ s ω))) = fun x => g (θ (x + s) ω) := by
    funext t; rw [flow_apply_add]
  rw [this]; exact h2

lemma abs_avgF_shift (g : Ω → ℝ) (ω : Ω) (n : ℕ) :
    ∫ t in (n : ℝ)..(n : ℝ) + 1, |g (θ t ω)| = avgF θ (fun ω => |g ω|) ((θ 1)^[n] ω) := by
  rw [avgF, ← flow_nat, shift_integral θ (fun ω => |g ω|) ω (n : ℝ) 0 1, zero_add, add_comm]

lemma shift_sum_bound (g : Ω → ℝ) (ω : Ω) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hloc : ∀ n : ℕ, IntervalIntegrable (fun t => g (θ t ω)) volume 0 n) (n : ℕ) :
    |birkhoffSum (θ 1) (avgF θ g) n (θ s ω) - birkhoffSum (θ 1) (avgF θ g) n ω| ≤
      avgF θ (fun ω => |g ω|) ω + avgF θ (fun ω => |g ω|) ((θ 1)^[n] ω) := by
  rw [birkhoffSum_eq_time_integral θ g _ (loc_shift θ g ω s hs0 hs1 hloc) n,
    birkhoffSum_eq_time_integral θ g ω hloc n, shift_integral, zero_add]
  have hI : IntervalIntegrable (fun t => g (θ t ω)) volume 0 ((n : ℝ) + 1) := by
    exact_mod_cast hloc (n + 1)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e1 : ∫ t in s..(n : ℝ) + s, g (θ t ω) =
      (∫ t in (0 : ℝ)..(n : ℝ) + s, g (θ t ω)) - ∫ t in (0 : ℝ)..s, g (θ t ω) :=
    (intervalIntegral.integral_interval_sub_left
      (ii_sub (fun t => g (θ t ω)) 0 ((n : ℝ) + s) 0 ((n : ℝ) + 1) (by linarith) le_rfl (by linarith) hI)
      (ii_sub (fun t => g (θ t ω)) 0 s 0 ((n : ℝ) + 1) hs0 le_rfl (by linarith) hI)).symm
  have e2 : ∫ t in (n : ℝ)..(n : ℝ) + s, g (θ t ω) =
      (∫ t in (0 : ℝ)..(n : ℝ) + s, g (θ t ω)) - ∫ t in (0 : ℝ)..(n : ℝ), g (θ t ω) :=
    (intervalIntegral.integral_interval_sub_left
      (ii_sub (fun t => g (θ t ω)) 0 ((n : ℝ) + s) 0 ((n : ℝ) + 1) (by linarith) le_rfl (by linarith) hI)
      (ii_sub (fun t => g (θ t ω)) 0 (n : ℝ) 0 ((n : ℝ) + 1) hn0 le_rfl (by linarith) hI)).symm
  have b1 : |∫ t in (0 : ℝ)..s, g (θ t ω)| ≤ avgF θ (fun ω => |g ω|) ω := by
    refine (intervalIntegral.abs_integral_le_integral_abs hs0).trans ?_
    rw [avgF]
    refine intervalIntegral.integral_mono_interval le_rfl hs0 hs1 ?_ ?_
    · exact ae_of_all _ fun t => abs_nonneg _
    · exact (ii_sub (fun t => g (θ t ω)) 0 1 0 ((n : ℝ) + 1) zero_le_one le_rfl (by linarith) hI).abs
  have b2 : |∫ t in (n : ℝ)..(n : ℝ) + s, g (θ t ω)| ≤ avgF θ (fun ω => |g ω|) ((θ 1)^[n] ω) := by
    refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans ?_
    rw [← abs_avgF_shift]
    refine intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith) ?_ ?_
    · exact ae_of_all _ fun t => abs_nonneg _
    · exact (ii_sub (fun t => g (θ t ω)) (n : ℝ) ((n : ℝ) + 1) 0 ((n : ℝ) + 1) (by linarith) hn0 le_rfl hI).abs
  have e3 : (∫ t in s..(n : ℝ) + s, g (θ t ω)) - ∫ t in (0 : ℝ)..(n : ℝ), g (θ t ω) =
      (∫ t in (n : ℝ)..(n : ℝ) + s, g (θ t ω)) - ∫ t in (0 : ℝ)..s, g (θ t ω) := by
    rw [e1, e2]; ring
  rw [e3]
  calc |(∫ t in (n : ℝ)..(n : ℝ) + s, g (θ t ω)) - ∫ t in (0 : ℝ)..s, g (θ t ω)|
      ≤ |∫ t in (n : ℝ)..(n : ℝ) + s, g (θ t ω)| + |∫ t in (0 : ℝ)..s, g (θ t ω)| := abs_sub _ _
    _ ≤ _ := by linarith

lemma limsupSet_ae_shift (hinv : θ.Invariant P)
    (g : Ω → ℝ) (hg : Measurable g) (hgi : Integrable g P) (a : ℝ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ᵐ ω ∂P, (ω ∈ limsupSet (θ 1) (avgF θ g) a ↔ θ s ω ∈ limsupSet (θ 1) (avgF θ g) a) := by
  obtain ⟨hGm, hGi, -⟩ := avg_props θ P hinv (fun ω => |g ω|) hg.abs hgi.abs
  have hBC := iterate_eventually_le P (θ 1) (θ.measurable' 1) (hinv 1)
    (avgF θ (fun ω => |g ω|)) hGm hGi (avgF_abs_nonneg θ g)
  filter_upwards [ae_locally_integrable θ P hinv g hg hgi, hBC] with ω hloc hG
  have hb := shift_sum_bound θ g ω s hs0 hs1 hloc
  constructor
  · intro h
    simp only [limsupSet, Set.mem_iInter] at h ⊢
    intro k
    have h' := h (2 * k + 1)
    rw [half_eq] at h'
    exact freq_transfer (fun n => birkhoffSum (θ 1) (avgF θ g) n ω)
      (fun n => birkhoffSum (θ 1) (avgF θ g) n (θ s ω)) _ _
      (fun n => by rw [abs_sub_comm]; exact hb n) hG a _ (by positivity) h'
  · intro h
    simp only [limsupSet, Set.mem_iInter] at h ⊢
    intro k
    have h' := h (2 * k + 1)
    rw [half_eq] at h'
    exact freq_transfer (fun n => birkhoffSum (θ 1) (avgF θ g) n (θ s ω))
      (fun n => birkhoffSum (θ 1) (avgF θ g) n ω) _ _ hb hG a _ (by positivity) h'

lemma limsupSet_null_or_conull (herg : IsErgodicFlow θ P)
    (g : Ω → ℝ) (hg : Measurable g) (hgi : Integrable g P) (a : ℝ) :
    limsupSet (θ 1) (avgF θ g) a =ᵐ[P] (∅ : Set Ω) ∨
      limsupSet (θ 1) (avgF θ g) a =ᵐ[P] Set.univ := by
  obtain ⟨hFm, -, -⟩ := avg_props θ P herg.1 g hg hgi
  set L := limsupSet (θ 1) (avgF θ g) a with hLdef
  have hLm : MeasurableSet L := limsupSet_measurable (θ 1) (θ.measurable' 1) _ hFm a
  have hL1 : θ 1 ⁻¹' L = L := limsupSet_invariant _ _ _
  have hae : ∀ s : ℝ, P (L \ θ s ⁻¹' L) = 0 ∧ P (θ s ⁻¹' L \ L) = 0 := by
    intro s
    have hsplit : θ s = θ (Int.fract s) ∘ θ ((⌊s⌋ : ℤ) : ℝ) := by
      conv_lhs => rw [← Int.fract_add_floor s]
      exact θ.map_add _ _
    have hint : θ ((⌊s⌋ : ℤ) : ℝ) ⁻¹' L = L := flow_int_preimage θ L hL1 ⌊s⌋
    have hfr := limsupSet_ae_shift θ P herg.1 g hg hgi a (Int.fract s) (Int.fract_nonneg s)
      (Int.fract_lt_one s).le
    have e1 : L \ θ s ⁻¹' L = θ ((⌊s⌋ : ℤ) : ℝ) ⁻¹' (L \ θ (Int.fract s) ⁻¹' L) := by
      rw [Set.preimage_sdiff, ← Set.preimage_comp, ← hsplit, hint]
    have e2 : θ s ⁻¹' L \ L = θ ((⌊s⌋ : ℤ) : ℝ) ⁻¹' (θ (Int.fract s) ⁻¹' L \ L) := by
      rw [Set.preimage_sdiff, ← Set.preimage_comp, ← hsplit, hint]
    have hm : MeasurableSet (θ (Int.fract s) ⁻¹' L) := θ.measurable' _ hLm
    rw [e1, e2, ← Measure.map_apply (θ.measurable' _) (hLm.diff hm),
      ← Measure.map_apply (θ.measurable' _) (hm.diff hLm), herg.1 _]
    constructor
    · have : ∀ᵐ ω ∂P, ω ∉ L \ θ (Int.fract s) ⁻¹' L := by
        filter_upwards [hfr] with ω hω
        intro h; exact h.2 (hω.1 h.1)
      have := ae_iff.1 this
      simp only [not_not] at this
      exact this
    · have : ∀ᵐ ω ∂P, ω ∉ θ (Int.fract s) ⁻¹' L \ L := by
        filter_upwards [hfr] with ω hω
        intro h; exact h.2 (hω.2 h.1)
      have := ae_iff.1 this
      simp only [not_not] at this
      exact this
  rcases flow_ae_invariant_null_or_conull P θ herg L hLm hae with h | h
  · left; exact ae_eq_empty.2 h
  · right; exact ae_eq_univ.2 h

theorem pointwise_flow_core (herg : IsErgodicFlow θ P)
    (f : Ω → ℝ) (hf : Integrable f P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun T : ℝ => (∫ t in Set.Ioc (0 : ℝ) T, f (θ t ω) ∂(volume : Measure ℝ)) / T)
      atTop (𝓝 (∫ ω, f ω ∂P)) := by
  set g : Ω → ℝ := hf.aestronglyMeasurable.mk f with hgdef
  have hgm : Measurable g := hf.aestronglyMeasurable.measurable_mk
  have hfg : f =ᵐ[P] g := hf.aestronglyMeasurable.ae_eq_mk
  have hgi : Integrable g P := hf.congr hfg
  have hinv : θ.Invariant P := herg.1
  obtain ⟨hFm, hFi, hFint⟩ := avg_props θ P hinv g hgm hgi
  obtain ⟨hGm, hGi, -⟩ := avg_props θ P hinv (fun ω => |g ω|) hgm.abs hgi.abs
  have hLf := fun a => limsupSet_null_or_conull θ P herg g hgm hgi a
  have hLnf : ∀ a : ℝ, limsupSet (θ 1) (-avgF θ g) a =ᵐ[P] (∅ : Set Ω) ∨
      limsupSet (θ 1) (-avgF θ g) a =ᵐ[P] Set.univ := by
    intro a
    have := limsupSet_null_or_conull θ P herg (-g) hgm.neg hgi.neg a
    have e : avgF θ (-g) = -avgF θ g := by
      funext ω; simp only [avgF, Pi.neg_apply]; exact intervalIntegral.integral_neg
    rwa [e] at this
  have hB := birkhoff_tendsto' P (θ 1) (θ.measurable' 1) (hinv 1) (avgF θ g) hFm hFi hLf hLnf
  have hFint' : ∫ ω, avgF θ g ω ∂P = ∫ ω, g ω ∂P := hFint
  rw [hFint'] at hB
  have hcongr := ae_time_integral_congr θ P hinv f g hfg
  have hloc := ae_locally_integrable θ P hinv g hgm hgi
  have hBC := iterate_eventually_le P (θ 1) (θ.measurable' 1) (hinv 1)
    (avgF θ (fun ω => |g ω|)) hGm hGi (avgF_abs_nonneg θ g)
  rw [integral_congr_ae hfg]
  filter_upwards [hB, hcongr, hloc, hBC] with ω hω hc hl hbc
  set I := ∫ ω, g ω ∂P with hI
  set G : Ω → ℝ := avgF θ (fun ω => |g ω|) with hGdef
  have hGt : Tendsto (fun n : ℕ => G ((θ 1)^[n] ω) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_div_of_eventually_le _ (fun n => avgF_abs_nonneg θ g _) hbc
  -- main term
  have h1 : Tendsto (fun T : ℝ => birkhoffSum (θ 1) (avgF θ g) ⌊T⌋₊ ω / (⌊T⌋₊ : ℝ) *
      ((⌊T⌋₊ : ℝ) / T)) atTop (𝓝 (I * 1)) :=
    (hω.comp tendsto_nat_floor_atTop).mul tendsto_nat_floor_div_atTop
  -- remainder term
  have h2 : Tendsto (fun T : ℝ => (∫ t in (⌊T⌋₊ : ℝ)..T, g (θ t ω)) / T) atTop (𝓝 0) := by
    have h2' : Tendsto (fun T : ℝ => G ((θ 1)^[⌊T⌋₊] ω) / (⌊T⌋₊ : ℝ)) atTop (𝓝 0) :=
      hGt.comp tendsto_nat_floor_atTop
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ h2'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    set n := ⌊T⌋₊ with hn
    have hn1 : 1 ≤ n := (Nat.one_le_floor_iff T).2 hT
    have hnT : (n : ℝ) ≤ T := Nat.floor_le (by linarith)
    have hTn : T ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one T).le
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hTpos : (0 : ℝ) < T := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hTpos]
    have hI : IntervalIntegrable (fun t => g (θ t ω)) volume 0 ((n : ℝ) + 1) := by
      exact_mod_cast hl (n + 1)
    have hb : |∫ t in (n : ℝ)..T, g (θ t ω)| ≤ G ((θ 1)^[n] ω) := by
      refine (intervalIntegral.abs_integral_le_integral_abs hnT).trans ?_
      rw [hGdef, ← abs_avgF_shift]
      refine intervalIntegral.integral_mono_interval le_rfl hnT hTn ?_ ?_
      · exact ae_of_all _ fun t => abs_nonneg _
      · exact (ii_sub (fun t => g (θ t ω)) (n : ℝ) ((n : ℝ) + 1) 0 ((n : ℝ) + 1) (by linarith) hnpos.le le_rfl hI).abs
    calc |∫ t in (n : ℝ)..T, g (θ t ω)| / T ≤ G ((θ 1)^[n] ω) / T :=
          div_le_div_of_nonneg_right hb hTpos.le
      _ ≤ G ((θ 1)^[n] ω) / n :=
          div_le_div_of_nonneg_left (avgF_abs_nonneg θ g _) hnpos hnT
  have h3 := h1.add h2
  rw [mul_one, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  set n := ⌊T⌋₊ with hn
  have hn1 : 1 ≤ n := (Nat.one_le_floor_iff T).2 hT
  have hnT : (n : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hTn : T ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one T).le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hTpos : (0 : ℝ) < T := by linarith
  have hI : IntervalIntegrable (fun t => g (θ t ω)) volume 0 ((n : ℝ) + 1) := by
    exact_mod_cast hl (n + 1)
  rw [hc T, ← intervalIntegral.integral_of_le hTpos.le,
    ← intervalIntegral.integral_add_adjacent_intervals (hl n)
      (ii_sub (fun t => g (θ t ω)) (n : ℝ) T 0 ((n : ℝ) + 1) hnT hnpos.le hTn hI),
    ← birkhoffSum_eq_time_integral θ g ω hl n]
  field_simp

end FlowBirkhoff

end PalmQueueing.Ergodic

open PalmQueueing.Ergodic
open MeasureTheory Filter Topology
open PalmQueueing.Palm
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Flow Ω) (herg : IsErgodicFlow θ P)
    (f : Ω → ℝ) (hf : Integrable f P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun T : ℝ => (∫ t in Set.Ioc (0 : ℝ) T, f (θ t ω) ∂(volume : Measure ℝ)) / T)
      atTop (𝓝 (∫ ω, f ω ∂P)) := by
  exact pointwise_flow_core θ P herg f hf

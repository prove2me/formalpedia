-- Prove2me | solution 1 for PalmQueueing.Ergodic.discrete_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:03:10.873984+00:00
-- url     : https://prove2.me/submissions/c1c9f0d5-e831-40f1-b808-eedd11bb21cf

import Mathlib
import Definitions.Def_PalmQueueing_Ergodic_DiscreteFlow



namespace PalmQueueing.Ergodic

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

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

theorem birkhoff_upper (hTm : Measurable T) (hinv : Measure.map T P = P) (herg : Ergodic T P)
    (f : Ω → ℝ) (hf : Measurable f) (hfi : Integrable f P) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, birkhoffSum T f n ω ≤ (n : ℝ) * ((∫ ω, f ω ∂P) + ε) := by
  set a : ℝ := (∫ ω, f ω ∂P) + ε with ha
  set L := limsupSet T f a with hL
  have hLm : MeasurableSet L := limsupSet_measurable T hTm f hf a
  have hLinv : T ⁻¹' L = L := limsupSet_invariant T f a
  rcases herg.ae_empty_or_univ hLm hLinv with hempty | huniv
  · -- a.e. ω is not in L
    rw [ae_eq_empty] at hempty
    have hae : ∀ᵐ ω ∂P, ω ∉ L := by
      rw [ae_iff]
      simpa using hempty
    filter_upwards [hae] with ω hω
    simp only [hL, limsupSet, Set.mem_iInter, not_forall] at hω
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
  · -- impossible: contradiction with the maximal ergodic lemma
    exfalso
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
      simp only [hL, limsupSet, Set.mem_iInter] at hω
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

lemma ergodic_symm (shift : Ω ≃ᵐ Ω) (h : Ergodic shift P) : Ergodic shift.symm P := by
  refine ⟨h.toMeasurePreserving.symm shift, ⟨?_⟩⟩
  intro s hs hinv
  have key : shift ⁻¹' s = s := by
    have : shift ⁻¹' s = (shift.symm ∘ shift) ⁻¹' s := by rw [Set.preimage_comp, hinv]
    rw [this, MeasurableEquiv.symm_comp_self, Set.preimage_id]
  exact h.toPreErgodic.aeconst_set hs key

theorem birkhoff_tendsto (hTm : Measurable T) (hinv : Measure.map T P = P) (herg : Ergodic T P)
    (f : Ω → ℝ) (hf : Measurable f) (hfi : Integrable f P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => birkhoffSum T f n ω / (n : ℝ)) atTop (𝓝 (∫ ω, f ω ∂P)) := by
  have hup : ∀ j : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      birkhoffSum T f n ω ≤ (n : ℝ) * ((∫ ω, f ω ∂P) + 1 / ((j : ℝ) + 1)) :=
    fun j => birkhoff_upper P T hTm hinv herg f hf hfi _ (by positivity)
  have hlow : ∀ j : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * ((∫ ω, f ω ∂P) - 1 / ((j : ℝ) + 1)) ≤ birkhoffSum T f n ω := by
    intro j
    have := birkhoff_upper P T hTm hinv herg (-f) hf.neg hfi.neg (1 / ((j : ℝ) + 1))
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

end Birkhoff

theorem discrete_pointwise_core (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (θ : Ω → Ω) (hθ : Measurable θ) (hbij : Function.Bijective θ) (herg : Ergodic θ P0)
    (f : Ω → ℝ) (hf : Integrable f P0) :
    ∀ᵐ ω ∂P0, Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, f (θ^[n] ω)) / (N : ℝ))
      atTop (𝓝 (∫ ω, f ω ∂P0)) := by
  have hinv : Measure.map θ P0 = P0 := herg.toMeasurePreserving.map_eq
  -- replace f by a measurable modification
  set g : Ω → ℝ := hf.aestronglyMeasurable.mk f with hg
  have hgm : Measurable g := hf.aestronglyMeasurable.measurable_mk
  have hfg : f =ᵐ[P0] g := hf.aestronglyMeasurable.ae_eq_mk
  have hgi : Integrable g P0 := hf.congr hfg
  have hqmp : Measure.QuasiMeasurePreserving θ P0 P0 := herg.toMeasurePreserving.quasiMeasurePreserving
  have hB := birkhoff_tendsto P0 θ hθ hinv herg g hgm hgi
  have hB' : ∀ᵐ ω ∂P0, Tendsto (fun n : ℕ => birkhoffSum θ g n (θ ω) / (n : ℝ)) atTop
      (𝓝 (∫ ω, g ω ∂P0)) := hqmp.ae hB
  have hiter : ∀ n : ℕ, ∀ᵐ ω ∂P0, f (θ^[n] ω) = g (θ^[n] ω) := by
    intro n
    have hq : Measure.QuasiMeasurePreserving (θ^[n]) P0 P0 := hqmp.iterate n
    exact hq.ae hfg
  have hall := ae_all_iff.2 hiter
  have hint : ∫ ω, f ω ∂P0 = ∫ ω, g ω ∂P0 := integral_congr_ae hfg
  rw [hint]
  filter_upwards [hB', hall] with ω hω hfω
  refine hω.congr fun N => ?_
  congr 1
  unfold birkhoffSum
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih, hfω,
      ← Function.iterate_succ_apply]

end PalmQueueing.Ergodic

open PalmQueueing.Ergodic
open MeasureTheory Filter Topology
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (θ : Ω → Ω) (hθ : Measurable θ) (hbij : Function.Bijective θ) (herg : Ergodic θ P0)
    (f : Ω → ℝ) (hf : Integrable f P0) :
    ∀ᵐ ω ∂P0, Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, f (θ^[n] ω)) / (N : ℝ))
      atTop (𝓝 (∫ ω, f ω ∂P0)) := by
  exact discrete_pointwise_core P0 θ hθ hbij herg f hf

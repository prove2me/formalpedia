-- Prove2me | solution 1 for PoissonDepTrials.MixInv.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:31:41.462685+00:00
-- url     : https://prove2.me/submissions/3e73541f-5219-4184-81ee-08ea5480a19e

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.MixInv

lemma phi_nonneg {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
    {X : ℕ → Ω → β} {φ : ℕ → ℝ} (hφ : IbragimovMixing P X φ) (k : ℕ) : 0 ≤ φ k :=
  Antitone.le_of_tendsto hφ.1 hφ.2.1 k

lemma sigmaIcc_le {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (X : ℕ → Ω → β)
    (hXm : ∀ i, Measurable (X i)) (a b : ℕ) : sigmaIcc X a b ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun i _ => (hXm i).comap_le

lemma sigmaIci_le {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (X : ℕ → Ω → β)
    (hXm : ∀ i, Measurable (X i)) (a : ℕ) : sigmaIci X a ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun i _ => (hXm i).comap_le


open scoped NNReal ENNReal
open TopologicalSpace

lemma tv_integral_le {S : Type*} [MeasurableSpace S] (κ ν : Measure S) [IsProbabilityMeasure κ]
    [IsProbabilityMeasure ν] (c : ℝ) (hB : ∀ B, MeasurableSet B → κ.real B - ν.real B ≤ c)
    (g : S → ℝ) (hg : Measurable g) (M : ℝ) (hM : ∀ x, |g x| ≤ M) :
    ∫ x, g x ∂κ - ∫ x, g x ∂ν ≤ 2 * M * c := by
  obtain ⟨x0, -⟩ : (Set.univ : Set S).Nonempty := nonempty_of_measure_ne_zero (μ := κ) (by simp)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x0)
  obtain ⟨H, hH, hH1, hH2⟩ := hahn_decomposition κ ν
  have hle1 : ν.restrict H ≤ κ.restrict H := by
    refine Measure.le_iff.mpr (fun s hs => ?_)
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hH1 _ (hs.inter hH) Set.inter_subset_right
  have hle2 : κ.restrict Hᶜ ≤ ν.restrict Hᶜ := by
    refine Measure.le_iff.mpr (fun s hs => ?_)
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hH2 _ (hs.inter hH.compl) Set.inter_subset_right
  have ig : ∀ μ : Measure S, IsFiniteMeasure μ → Integrable g μ := fun μ _ =>
    Integrable.of_bound hg.aestronglyMeasurable M (Filter.Eventually.of_forall (fun x => by simpa using hM x))
  have iMg : ∀ μ : Measure S, IsFiniteMeasure μ → Integrable (fun x => M - g x) μ := fun μ hμ =>
    (integrable_const M).sub (ig μ hμ)
  have igM : ∀ μ : Measure S, IsFiniteMeasure μ → Integrable (fun x => g x + M) μ := fun μ hμ =>
    (ig μ hμ).add (integrable_const M)
  have A1 : ∫ x in H, (M - g x) ∂ν ≤ ∫ x in H, (M - g x) ∂κ :=
    integral_mono_measure hle1 (Filter.Eventually.of_forall (fun x => by
      have := hM x; have := le_abs_self (g x); simp only [Pi.zero_apply]; linarith))
      (iMg _ inferInstance)
  have A2 : ∫ x in Hᶜ, (g x + M) ∂κ ≤ ∫ x in Hᶜ, (g x + M) ∂ν :=
    integral_mono_measure hle2 (Filter.Eventually.of_forall (fun x => by
      have := hM x; have := neg_abs_le (g x); simp only [Pi.zero_apply]; linarith))
      (igM _ inferInstance)
  rw [integral_sub (integrable_const M) (ig _ inferInstance), integral_sub (integrable_const M)
    (ig _ inferInstance), setIntegral_const, setIntegral_const] at A1
  rw [integral_add (ig _ inferInstance) (integrable_const M), integral_add (ig _ inferInstance)
    (integrable_const M), setIntegral_const, setIntegral_const] at A2
  simp only [smul_eq_mul] at A1 A2
  have e1 := integral_add_compl hH (ig κ inferInstance)
  have e2 := integral_add_compl hH (ig ν inferInstance)
  have hc1 := hB H hH
  have hc2 : ν.real Hᶜ - κ.real Hᶜ ≤ c := by
    rw [probReal_compl_eq_one_sub hH, probReal_compl_eq_one_sub hH]; linarith
  have m1 := mul_le_mul_of_nonneg_left hc1 hM0
  have m2 := mul_le_mul_of_nonneg_left hc2 hM0
  nlinarith

lemma tv_integral_abs {S : Type*} [MeasurableSpace S] (κ ν : Measure S) [IsProbabilityMeasure κ]
    [IsProbabilityMeasure ν] (c : ℝ) (hB : ∀ B, MeasurableSet B → κ.real B - ν.real B ≤ c)
    (g : S → ℝ) (hg : Measurable g) (M : ℝ) (hM : ∀ x, |g x| ≤ M) :
    |∫ x, g x ∂κ - ∫ x, g x ∂ν| ≤ 2 * M * c := by
  have h1 := tv_integral_le κ ν c hB g hg M hM
  have h2 := tv_integral_le κ ν c hB (fun x => - g x) hg.neg M (fun x => by rw [abs_neg]; exact hM x)
  rw [integral_neg, integral_neg] at h2
  rw [abs_le]; constructor <;> linarith

lemma open_bound {S : Type*} [TopologicalSpace S] [SecondCountableTopology S] [MeasurableSpace S]
    (κ ν : Measure S) (c : ℝ≥0∞)
    (hC : ∀ F : Finset (TopologicalSpace.countableBasis S),
      κ (⋃ b ∈ F, (b : Set S)) ≤ ν (⋃ b ∈ F, (b : Set S)) + c)
    (O : Set S) (hO : IsOpen O) : κ O ≤ ν O + c := by
  classical
  haveI := (TopologicalSpace.countable_countableBasis S).to_subtype
  let s : {F : Finset (TopologicalSpace.countableBasis S) // ∀ b ∈ F, (b : Set S) ⊆ O} → Set S :=
    fun F => ⋃ b ∈ F.1, (b : Set S)
  have hd : Directed (· ⊆ ·) s := by
    intro F G
    refine ⟨⟨F.1 ∪ G.1, ?_⟩, ?_, ?_⟩
    · intro b hb; rcases Finset.mem_union.mp hb with h | h
      exacts [F.2 b h, G.2 b h]
    · intro x hx; simp only [s, Set.mem_iUnion] at hx ⊢
      obtain ⟨b, hb, hx⟩ := hx; exact ⟨b, Finset.mem_union_left _ hb, hx⟩
    · intro x hx; simp only [s, Set.mem_iUnion] at hx ⊢
      obtain ⟨b, hb, hx⟩ := hx; exact ⟨b, Finset.mem_union_right _ hb, hx⟩
  have hU : (⋃ F, s F) = O := by
    apply Set.Subset.antisymm
    · intro x hx; simp only [s, Set.mem_iUnion] at hx
      obtain ⟨F, b, hb, hx⟩ := hx; exact F.2 b hb hx
    · intro x hx
      obtain ⟨b, hb, hxb, hbO⟩ :=
        (TopologicalSpace.isBasis_countableBasis S).exists_subset_of_mem_open hx hO
      refine Set.mem_iUnion.mpr ⟨⟨{⟨b, hb⟩}, ?_⟩, ?_⟩
      · intro b' hb'; rw [Finset.mem_singleton] at hb'; subst hb'; exact hbO
      · simp only [s, Set.mem_iUnion]; exact ⟨⟨b, hb⟩, Finset.mem_singleton_self _, hxb⟩
  rw [← hU, hd.measure_iUnion]
  refine iSup_le (fun F => (hC F.1).trans ?_)
  gcongr
  exact Set.subset_iUnion s F

lemma all_bound {S : Type*} [TopologicalSpace S] [PseudoMetrizableSpace S] [MeasurableSpace S]
    [BorelSpace S] (κ ν : Measure S) [IsFiniteMeasure ν] (c : ℝ≥0∞)
    (hO : ∀ O, IsOpen O → κ O ≤ ν O + c) (B : Set S) : κ B ≤ ν B + c := by
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  obtain ⟨U, hBU, hUo, hU⟩ := B.exists_isOpen_lt_add (μ := ν) (measure_ne_top ν B)
    (ε := (ε : ℝ≥0∞)) (by simpa using hε.ne')
  calc κ B ≤ κ U := measure_mono hBU
    _ ≤ ν U + c := hO U hUo
    _ ≤ ν B + ε + c := by gcongr
    _ = ν B + c + ε := by rw [add_right_comm]

lemma KTV {Ω β S1 S2 : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace S1]
    [TopologicalSpace S2] [SecondCountableTopology S2] [PseudoMetrizableSpace S2]
    [MeasurableSpace S2] [BorelSpace S2] [StandardBorelSpace S2] [Nonempty S2]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → β) (hXm : ∀ i, Measurable (X i))
    (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (U : Ω → S1) (hU : Measurable[sigmaIcc X 1 j] U) (V : Ω → S2) (hV : Measurable[sigmaIci X (j + k)] V)
    (F : S1 × S2 → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ x, |F x| ≤ M) :
    ∀ᵐ ω ∂P, |(P[fun ω => F (U ω, V ω) | MeasurableSpace.comap U inferInstance]) ω
      - ∫ z, F (U ω, z) ∂(P.map V)| ≤ 2 * M * φ k := by
  have hφ0 := phi_nonneg hφ k
  have hGle := sigmaIcc_le X hXm 1 j
  have hUm : Measurable U := hU.mono hGle le_rfl
  have hVm : Measurable V := hV.mono (sigmaIci_le X hXm _) le_rfl
  have hcomap : MeasurableSpace.comap U inferInstance ≤ sigmaIcc X 1 j := hU.comap_le
  haveI : IsProbabilityMeasure (P.map V) := Measure.isProbabilityMeasure_map hVm.aemeasurable
  have K1 : ∀ B, MeasurableSet B → ∀ᵐ ω ∂P,
      |(condDistrib V U P (U ω)).real B - (P.map V).real B| ≤ φ k := by
    intro B hB
    have h1 := condDistrib_ae_eq_condExp (μ := P) hUm hVm hB
    have hmix := hφ.2.2 j k hj hk (V ⁻¹' B) (hV hB)
    have h2 := condExp_condExp_of_le (μ := P) (f := (V ⁻¹' B).indicator (fun _ => (1:ℝ))) hcomap hGle
    have hb : ∀ᵐ ω ∂P, |(P[(V ⁻¹' B).indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]) ω
        - P.real (V ⁻¹' B)| ≤ ((⟨φ k, hφ0⟩ : ℝ≥0) : ℝ) := hmix
    have h3 := ae_bdd_condExp_of_ae_bdd (m := MeasurableSpace.comap U inferInstance) hb
    have h4 := condExp_sub (μ := P) (integrable_condExp (m := sigmaIcc X 1 j)
      (f := (V ⁻¹' B).indicator (fun _ => (1:ℝ))))
      (integrable_const (P.real (V ⁻¹' B))) (MeasurableSpace.comap U inferInstance)
    rw [condExp_const (hcomap.trans hGle)] at h4
    have hmapB : (P.map V).real B = P.real (V ⁻¹' B) := map_measureReal_apply hVm hB
    filter_upwards [h1, h2, h3, h4] with ω e1 e2 e3 e4
    rw [e1, hmapB, ← e2]
    have e5 : (P[P[(V ⁻¹' B).indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j] |
        MeasurableSpace.comap U inferInstance]) ω - P.real (V ⁻¹' B)
        = (P[P[(V ⁻¹' B).indicator (fun _ => (1:ℝ)) | sigmaIcc X 1 j]
          - (fun _ => P.real (V ⁻¹' B)) | MeasurableSpace.comap U inferInstance]) ω := by
      rw [e4]; rfl
    rw [e5]; exact e3
  haveI := (TopologicalSpace.countable_countableBasis S2).to_subtype
  have K1' : ∀ᵐ ω ∂P, ∀ Fs : Finset (TopologicalSpace.countableBasis S2),
      |(condDistrib V U P (U ω)).real (⋃ b ∈ Fs, (b : Set S2))
        - (P.map V).real (⋃ b ∈ Fs, (b : Set S2))| ≤ φ k := by
    rw [ae_all_iff]; intro Fs
    apply K1
    exact Finset.measurableSet_biUnion _ (fun b _ =>
      (TopologicalSpace.isOpen_of_mem_countableBasis b.2).measurableSet)
  have hFint : Integrable F (P.map (fun a => (U a, V a))) :=
    Integrable.of_bound hF.aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun x => by simpa using hM x))
  have hcd := condExp_prod_ae_eq_integral_condDistrib' (μ := P) hUm hVm.aemeasurable hFint
  filter_upwards [K1', hcd] with ω hω hc
  rw [hc]
  have hconv : ∀ C : Set S2, |(condDistrib V U P (U ω)).real C - (P.map V).real C| ≤ φ k →
      condDistrib V U P (U ω) C ≤ (P.map V) C + ENNReal.ofReal (φ k) := by
    intro C hC
    rw [← ofReal_measureReal (μ := condDistrib V U P (U ω)), ← ofReal_measureReal (μ := P.map V),
      ← ENNReal.ofReal_add measureReal_nonneg hφ0]
    apply ENNReal.ofReal_le_ofReal
    linarith [le_abs_self ((condDistrib V U P (U ω)).real C - (P.map V).real C)]
  have hO : ∀ O, IsOpen O → condDistrib V U P (U ω) O ≤ (P.map V) O + ENNReal.ofReal (φ k) :=
    open_bound _ _ _ (fun Fs => hconv _ (hω Fs))
  have hκB : ∀ B, MeasurableSet B → (condDistrib V U P (U ω)).real B - (P.map V).real B ≤ φ k := by
    intro B _
    have h := all_bound _ _ _ hO B
    have h' := ENNReal.toReal_mono (by finiteness) h
    rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hφ0] at h'
    rw [measureReal_def, measureReal_def]; linarith
  exact tv_integral_abs _ _ _ hκB (fun z => F (U ω, z)) (hF.comp measurable_prodMk_left) M
    (fun z => hM _)

theorem lemma_4_2_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (r s k m : ℕ) (hm : 1 ≤ m)
    (Y : Ω → (Fin r → ℝ)) (hY : Measurable[sigmaIcc X 1 k] Y)
    (Z : Ω → (Fin s → ℝ)) (hZ : Measurable[sigmaIci X (k + m)] Z)
    (f : (Fin r → ℝ) × (Fin s → ℝ) → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    ∀ᵐ ω ∂P, |(P[fun ω => f (Y ω, Z ω) | MeasurableSpace.comap Y inferInstance]) ω
      - ∫ z, f (Y ω, z) ∂(P.map Z)| ≤ 2 * M * φ m := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hφ0 := phi_nonneg hφ m
    have hbot : sigmaIcc X 1 0 = ⊥ := by simp [sigmaIcc]
    have hY0 := hY
    rw [hbot] at hY0
    obtain ⟨ω0, -⟩ : (Set.univ : Set Ω).Nonempty := nonempty_of_measure_ne_zero (μ := P) (by simp)
    have hc : ∀ ω, Y ω = Y ω0 := by
      intro ω
      have := hY0 (measurableSet_singleton (Y ω0))
      rcases MeasurableSpace.measurableSet_bot_iff.mp this with h | h
      · have : ω0 ∈ Y ⁻¹' {Y ω0} := rfl
        rw [h] at this; exact absurd this (Set.notMem_empty _)
      · have : ω ∈ Y ⁻¹' {Y ω0} := by rw [h]; trivial
        exact this
    have hcm : MeasurableSpace.comap Y inferInstance = ⊥ := le_bot_iff.mp (hbot ▸ hY.comap_le)
    have hZm : Measurable Z := hZ.mono (sigmaIci_le X hXm _) le_rfl
    rw [hcm, condExp_bot']
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simp only [probReal_univ, inv_one, one_smul, hc ω]
    have : ∫ x, f (Y x, Z x) ∂P = ∫ z, f (Y ω0, z) ∂(P.map Z) := by
      have hmap := integral_map (μ := P) hZm.aemeasurable (f := fun z => f (Y ω0, z))
        (hf.comp measurable_prodMk_left).aestronglyMeasurable
      rw [hmap]
      congr 1; funext x; rw [hc x]
    rw [this, sub_self, abs_zero]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Y ω0, Z ω0))
    exact mul_nonneg (mul_nonneg zero_le_two hM0) hφ0
  · exact KTV P X hXm φ hφ k m hk hm Y hY Z hZ f hf M hM

end PoissonDepTrials.MixInv

open PoissonDepTrials.MixInv


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (r s k m : ℕ) (hm : 1 ≤ m)
    (Y : Ω → (Fin r → ℝ)) (hY : Measurable[sigmaIcc X 1 k] Y)
    (Z : Ω → (Fin s → ℝ)) (hZ : Measurable[sigmaIci X (k + m)] Z)
    (f : (Fin r → ℝ) × (Fin s → ℝ) → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    ∀ᵐ ω ∂P, |(P[fun ω => f (Y ω, Z ω) | MeasurableSpace.comap Y inferInstance]) ω
      - ∫ z, f (Y ω, z) ∂(P.map Z)| ≤ 2 * M * φ m := by
  exact lemma_4_2_core P X hXm φ hφ r s k m hm Y hY Z hZ f hf M hM

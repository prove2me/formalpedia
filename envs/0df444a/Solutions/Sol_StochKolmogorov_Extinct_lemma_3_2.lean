-- Prove2me | solution 1 for StochKolmogorov.Extinct.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T17:32:04.312405+00:00
-- url     : https://prove2.me/submissions/da1130ca-c3ec-446b-89f1-c2fc7de6061f

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_2
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_sde_face_invariance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

set_option autoImplicit false

namespace ExtinctL32

open EthierKurtz StochKolmogorov.Extinct

/-- The same coefficients, read in the `Persist` copy of the model. -/
def toP {n : ℕ} (C : Coeffs n) : StochKolmogorov.Persist.Coeffs n :=
  ⟨C.f, C.g, C.Γ⟩

/-- Componentwise positive part, a continuous retraction onto the orthant. -/
noncomputable def pp {n : ℕ} (x : SDEState n) : SDEState n :=
  WithLp.toLp 2 (fun i => max (x i) 0)

theorem pp_apply {n : ℕ} (x : SDEState n) (i : Fin n) : pp x i = max (x i) 0 := rfl

theorem pp_mem {n : ℕ} (x : SDEState n) : pp x ∈ orthant n := fun i => by
  rw [pp_apply]; exact le_max_right _ _

theorem pp_of_mem {n : ℕ} {x : SDEState n} (hx : x ∈ orthant n) : pp x = x := by
  ext i
  rw [pp_apply]
  exact max_eq_left (hx i)

theorem continuous_pp {n : ℕ} : Continuous (pp (n := n)) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => (PiLp.continuous_apply 2 _ i).max continuous_const)

theorem isClosed_orthant {n : ℕ} : IsClosed (orthant n) := by
  have e : orthant n = ⋂ i, {x : SDEState n | 0 ≤ x i} := by
    ext x
    simp only [orthant, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [e]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

theorem continuous_base {n : ℕ} (c : SDEState n) :
    Continuous (fun y : SDEState n => 1 + ∑ i, c i * y i) :=
  continuous_const.add
    (continuous_finsetSum _ fun i _ => continuous_const.mul (PiLp.continuous_apply 2 _ i))

theorem one_le_base {n : ℕ} {c : SDEState n} (hc : c ∈ openOrthant n) {y : SDEState n}
    (hy : y ∈ orthant n) : 1 ≤ 1 + ∑ i, c i * y i := by
  have : 0 ≤ ∑ i, c i * y i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hc i)) (hy i))
  linarith

/-- Bochner form of a terminal moment bound given in lintegral form. -/
theorem bochner_of_lintegral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {F : Ω → ℝ} (hF : Measurable F) (hpos : ∀ᵐ ω ∂P, 0 ≤ F ω) {Bd : ℝ} (hBd0 : 0 ≤ Bd)
    (hle : ∫⁻ ω, ENNReal.ofReal (F ω) ∂P ≤ ENNReal.ofReal Bd) :
    Integrable F P ∧ ∫ ω, F ω ∂P ≤ Bd := by
  have hint : Integrable F P := by
    refine ⟨hF.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hpos]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hpos hF.aestronglyMeasurable]
  calc (∫⁻ ω, ENNReal.ofReal (F ω) ∂P).toReal ≤ (ENNReal.ofReal Bd).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = Bd := ENNReal.toReal_ofReal hBd0

/-- Time-space form: integrability on `[0,t] × Ω` and the iterated Bochner bound, from the
iterated lintegral bound, for a weight continuous on the orthant. -/
theorem timespace_of_lintegral {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℝ≥0 → Ω → SDEState n}
    (hYc : ∀ ω, Continuous fun t => Y t ω) (hYm : ∀ t, Measurable (Y t))
    (horth : ∀ᵐ ω ∂P, ∀ t, Y t ω ∈ orthant n)
    {Φ : SDEState n → ℝ} (hΦ : ContinuousOn Φ (orthant n)) (hΦpos : ∀ y ∈ orthant n, 0 ≤ Φ y)
    (t : ℝ≥0) {Bd : ℝ} (hBd0 : 0 ≤ Bd)
    (hle : ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Φ (Y s.toNNReal ω))) ∂P ≤
      ENNReal.ofReal Bd) :
    Integrable (fun q : ℝ × Ω => Φ (Y q.1.toNNReal q.2))
        ((volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod P) ∧
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, Φ (Y s.toNNReal ω) ∂P ≤ Bd := by
  have hYj : Measurable (fun q : ℝ × Ω => Y q.1.toNNReal q.2) :=
    (measurable_uncurry_of_continuous_of_measurable hYc hYm).comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hYo : ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod P),
      Y q.1.toNNReal q.2 ∈ orthant n :=
    (Measure.quasiMeasurePreserving_snd.ae horth).mono fun q hq => hq _
  have hΦ' : Continuous (fun y => Φ (pp y)) := hΦ.comp_continuous continuous_pp pp_mem
  have heq : (fun q : ℝ × Ω => Φ (pp (Y q.1.toNNReal q.2))) =ᵐ[
      (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod P] (fun q : ℝ × Ω => Φ (Y q.1.toNNReal q.2)) :=
    hYo.mono fun q hq => by simp only [pp_of_mem hq]
  have hG : AEStronglyMeasurable (fun q : ℝ × Ω => Φ (Y q.1.toNNReal q.2))
      ((volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod P) :=
    (hΦ'.measurable.comp hYj).aestronglyMeasurable.congr heq
  have hpos : ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod P),
      0 ≤ Φ (Y q.1.toNNReal q.2) := hYo.mono fun q hq => hΦpos _ hq
  have hlin : ∫⁻ q, ENNReal.ofReal (Φ (Y q.1.toNNReal q.2))
      ∂((volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod P) =
      ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Φ (Y s.toNNReal ω))) ∂P :=
    lintegral_prod_symm _ hG.aemeasurable.ennreal_ofReal
  have hle' : ∫⁻ q, ENNReal.ofReal (Φ (Y q.1.toNNReal q.2))
      ∂((volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod P) ≤ ENNReal.ofReal Bd := hlin ▸ hle
  have hint : Integrable (fun q : ℝ × Ω => Φ (Y q.1.toNNReal q.2))
      ((volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod P) := by
    refine ⟨hG, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hpos]
    exact lt_of_le_of_lt hle' ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have h0t : (0 : ℝ) ≤ (t : ℝ) := t.2
  rw [intervalIntegral.integral_of_le h0t, ← integral_Icc_eq_integral_Ioc]
  have hfub := integral_prod (fun q : ℝ × Ω => Φ (Y q.1.toNNReal q.2)) hint
  have hfub' : ∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ ω, Φ (Y s.toNNReal ω) ∂P =
      ∫ q, Φ (Y q.1.toNNReal q.2) ∂((volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod P) :=
    hfub.symm
  rw [hfub', integral_eq_lintegral_of_nonneg_ae hpos hG]
  calc (∫⁻ q, ENNReal.ofReal (Φ (Y q.1.toNNReal q.2))
        ∂((volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod P)).toReal
      ≤ (ENNReal.ofReal Bd).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle'
    _ = Bd := ENNReal.toReal_ofReal hBd0

/-- Tietze: a function continuous and bounded on the closed orthant agrees there with a bounded
continuous function on the whole space. -/
theorem exists_bcf_ext {n : ℕ} (h : SDEState n → ℝ) (hh : ContinuousOn h (orthant n))
    (K : ℝ) (hK : ∀ x ∈ orthant n, |h x| ≤ K) :
    ∃ g : SDEState n →ᵇ ℝ, ∀ x ∈ orthant n, g x = h x := by
  let f0 : orthant n →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun y : orthant n => h y) hh.domRestrict K
      (fun y => by rw [Real.norm_eq_abs]; exact hK y y.2)
  obtain ⟨g, -, hg⟩ :=
    BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding f0
      (isClosed_orthant.isClosedEmbedding_subtypeVal)
  refine ⟨g, fun x hx => ?_⟩
  have e := congrFun hg ⟨x, hx⟩
  exact e

theorem lemma_3_2_ext {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) :
    (∃ H₁ : ℝ, 0 < H₁ ∧ ∃ H₂ : ℝ, 0 < H₂ ∧
      ∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
        Integrable (fun ω => (1 + ∑ i, c i * X x t ω i) ^ δ₀) P ∧
        Integrable (fun q : ℝ × Ω =>
          (1 + ∑ i, c i * X x q.1.toNNReal q.2 i) ^ δ₀ *
            (1 + ∑ i, (|C.f i (X x q.1.toNNReal q.2)| +
              C.g i (X x q.1.toNNReal q.2) ^ 2)))
          ((volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod P) ∧
        (∫ ω, (1 + ∑ i, c i * X x t ω i) ^ δ₀ ∂P ≤
          H₁ + (1 + ∑ i, c i * x i) ^ δ₀ * Real.exp (-δ₀ * γb * (t : ℝ))) ∧
        (∫ s in (0 : ℝ)..(t : ℝ), ∫ ω,
          (1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
            (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + C.g i (X x s.toNNReal ω) ^ 2)) ∂P
          ≤ H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + (t : ℝ)))) ∧
    (∀ t : ℝ≥0, ∀ h : SDEState n → ℝ,
      ContinuousOn h (orthant n) →
      (∃ K : ℝ, ∀ x ∈ orthant n, |h x| ≤ K) →
      ContinuousOn (fun x => ∫ ω, h (X x t ω) ∂P) (orthant n)) := by
  have hX' := hX
  obtain ⟨hP, hB, hsol⟩ := hX'
  have hC : ∀ i, LocallyLipschitzOn (StochKolmogorov.Persist.orthant n) ((toP C).f i) ∧
      LocallyLipschitzOn (StochKolmogorov.Persist.orthant n) ((toP C).g i) := hA.2.1
  have horth : ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n := by
    intro x hx
    have hxf : x ∈ StochKolmogorov.Persist.faceOpen
        (Finset.univ.filter (fun i : Fin n => 0 < x i)) := by
      refine ⟨hx, ?_, ?_⟩
      · intro i hi
        have hn' : ¬ 0 < x i := fun h' => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h'⟩)
        exact le_antisymm (not_lt.mp hn') (hx i)
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
    filter_upwards [StochKolmogorov.Persist.kolmogorov_sde_face_invariance (P := P) (toP C)
      hB hC hxf (hsol x hx)] with ω hω t
    exact (hω t).1
  have hδP : StochKolmogorov.Persist.IsDelta0 (toP C) γb δ₀ :=
    ⟨hδ₀.1, lt_of_lt_of_le hδ₀.2.1 (min_le_left _ _), hδ₀.2.2⟩
  obtain ⟨H₁, H₂, hH₁, hH₂, h37, h38, hfel⟩ :=
    StochKolmogorov.Persist.lemma_3_2 hn P (toP C) B X hX c γb hA δ₀ hδP
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hbase0 : ∀ y ∈ orthant n, 0 ≤ (1 + ∑ i, c i * y i) ^ δ₀ := fun y hy =>
    Real.rpow_nonneg (le_trans zero_le_one (one_le_base hc hy)) _
  refine ⟨⟨H₁, hH₁, H₂, hH₂, fun x hx t ht => ?_⟩, ?_⟩
  · have hb1 : 0 ≤ H₁ + (1 + ∑ i, c i * x i) ^ δ₀ * Real.exp (-δ₀ * γb * (t : ℝ)) :=
      add_nonneg hH₁.le (mul_nonneg (hbase0 x hx) (Real.exp_pos _).le)
    have hF : Measurable (fun ω => (1 + ∑ i, c i * X x t ω i) ^ δ₀) :=
      ((continuous_base c).measurable.comp ((hsol x hx).1 t)).pow_const δ₀
    have hFpos : ∀ᵐ ω ∂P, 0 ≤ (1 + ∑ i, c i * X x t ω i) ^ δ₀ :=
      (horth x hx).mono fun ω hω => hbase0 _ (hω t)
    have hc1 := bochner_of_lintegral hF hFpos hb1 (h37 x hx t ht)
    -- the time-space weight
    have hfc : ∀ i, ContinuousOn (C.f i) (orthant n) := fun i => (hA.2.1 i).1.continuousOn
    have hgc : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hA.2.1 i).2.continuousOn
    have hΦ : ContinuousOn (fun y : SDEState n => (1 + ∑ i, c i * y i) ^ δ₀ *
        (1 + ∑ i, (|C.f i y| + C.g i y ^ 2))) (orthant n) := by
      refine ContinuousOn.mul ?_ ?_
      · exact ((continuous_base c).rpow_const (fun _ => Or.inr hδ₀.1.le)).continuousOn
      · refine continuousOn_const.add (continuousOn_finsetSum _ fun i _ => ?_)
        exact ((hfc i).abs).add ((hgc i).pow 2)
    have hΦpos : ∀ y ∈ orthant n, 0 ≤ (1 + ∑ i, c i * y i) ^ δ₀ *
        (1 + ∑ i, (|C.f i y| + C.g i y ^ 2)) := by
      intro y hy
      refine mul_nonneg (hbase0 y hy) ?_
      have : 0 ≤ ∑ i, (|C.f i y| + C.g i y ^ 2) :=
        Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (sq_nonneg _)
      linarith
    have hb2 : 0 ≤ H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + (t : ℝ)) :=
      mul_nonneg hH₂.le (add_nonneg (hbase0 x hx) t.2)
    have h38x := h38 x hx t ht
    simp only [sq_abs] at h38x
    have hc2 := timespace_of_lintegral (Y := X x) (hsol x hx).2.1 (hsol x hx).1 (horth x hx)
      hΦ hΦpos t hb2 h38x
    exact ⟨hc1.1, hc2.1, hc1.2, hc2.2⟩
  · intro t h hh hK
    obtain ⟨K, hK⟩ := hK
    obtain ⟨g, hg⟩ := exists_bcf_ext h hh K hK
    refine (hfel t g).congr fun x hx => ?_
    refine integral_congr_ae ?_
    filter_upwards [horth x hx] with ω hω
    exact (hg _ (hω t)).symm

end ExtinctL32

open StochKolmogorov.Extinct EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (M : ℝ) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) :
    (∃ H₁ : ℝ, 0 < H₁ ∧ ∃ H₂ : ℝ, 0 < H₂ ∧
      ∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
        Integrable (fun ω => (1 + ∑ i, c i * X x t ω i) ^ δ₀) P ∧
        Integrable (fun q : ℝ × Ω =>
          (1 + ∑ i, c i * X x q.1.toNNReal q.2 i) ^ δ₀ *
            (1 + ∑ i, (|C.f i (X x q.1.toNNReal q.2)| +
              C.g i (X x q.1.toNNReal q.2) ^ 2)))
          ((volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod P) ∧
        (∫ ω, (1 + ∑ i, c i * X x t ω i) ^ δ₀ ∂P ≤
          H₁ + (1 + ∑ i, c i * x i) ^ δ₀ * Real.exp (-δ₀ * γb * (t : ℝ))) ∧
        (∫ s in (0 : ℝ)..(t : ℝ), ∫ ω,
          (1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
            (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + C.g i (X x s.toNNReal ω) ^ 2)) ∂P
          ≤ H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + (t : ℝ)))) ∧
    (∀ t : ℝ≥0, ∀ h : SDEState n → ℝ,
      ContinuousOn h (orthant n) →
      (∃ K : ℝ, ∀ x ∈ orthant n, |h x| ≤ K) →
      ContinuousOn (fun x => ∫ ω, h (X x t ω) ∂P) (orthant n)) := by
  exact ExtinctL32.lemma_3_2_ext hn P C B X hX c γb hA δ₀ hδ₀

-- Prove2me | solution 1 for StochKolmogorov.Classify.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T09:42:14.594417+00:00
-- url     : https://prove2.me/submissions/b035c656-823d-44a6-8949-f4be6dde627c

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_4
import Theorems.Thm_StochKolmogorov_Persist_orthant_invariance_closed
import Theorems.Thm_StochKolmogorov_Classify_short_time_positivity

set_option autoImplicit false
set_option linter.all false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace L55

open StochKolmogorov.Classify EthierKurtz


variable {n : ℕ}

lemma continuous_posPart : Continuous (StochKolmogorov.Classify.posPart (n := n)) := by
  unfold StochKolmogorov.Classify.posPart
  first
  | fun_prop
  | exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).max
        continuous_const)

lemma posPart_mem (y : SDEState n) : StochKolmogorov.Classify.posPart y ∈ orthant n := by
  intro i; simp [StochKolmogorov.Classify.posPart]

lemma posPart_eq_of_mem {y : SDEState n} (hy : y ∈ orthant n) :
    StochKolmogorov.Classify.posPart y = y := by
  ext i; simp [StochKolmogorov.Classify.posPart, max_eq_left (hy i)]

lemma cont_comp_posPart {φ : SDEState n → ℝ} (h : ContinuousOn φ (orthant n)) :
    Continuous fun y => φ (StochKolmogorov.Classify.posPart y) :=
  h.comp_continuous continuous_posPart posPart_mem

lemma continuous_weight (C : Coeffs n) (c : SDEState n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hfc : ∀ i, ContinuousOn (C.f i) (orthant n)) (hgc : ∀ i, ContinuousOn (C.g i) (orthant n)) :
    Continuous fun y => growthWeight C c δ (StochKolmogorov.Classify.posPart y) := by
  have hco : ∀ i, Continuous fun y : SDEState n => (StochKolmogorov.Classify.posPart y) i :=
    fun i => (PiLp.continuous_apply 2 _ i).comp continuous_posPart
  have hf : ∀ i, Continuous fun y => C.f i (StochKolmogorov.Classify.posPart y) :=
    fun i => cont_comp_posPart (hfc i)
  have hg : ∀ i, Continuous fun y => C.g i (StochKolmogorov.Classify.posPart y) :=
    fun i => cont_comp_posPart (hgc i)
  simp only [growthWeight]
  exact Continuous.mul
    (Continuous.rpow_const (continuous_const.add
      (continuous_finset_sum _ fun i _ => continuous_const.mul (hco i))) (fun _ => Or.inr hδ))
    (continuous_const.add (continuous_finset_sum _ fun i _ => ((hf i).abs).add ((hg i).pow 2)))

theorem orthant_isClosed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; simp [orthant]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

theorem denseRange_rat_toNNReal : DenseRange fun q : ℚ => (q : ℝ).toNNReal := by
  have hs : DenseRange Real.toNNReal := Function.Surjective.denseRange fun x =>
    ⟨(x : ℝ), Real.toNNReal_coe⟩
  exact hs.comp Rat.denseRange_cast continuous_real_toNNReal

/-- Fixed-time invariance plus continuous paths gives invariance at all times at once. -/
theorem inv_all {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Y : ℝ≥0 → Ω → SDEState n}
    (hc : ∀ ω, Continuous fun t => Y t ω) (h1 : ∀ t, ∀ᵐ ω ∂P, Y t ω ∈ orthant n) :
    ∀ᵐ ω ∂P, ∀ u, Y u ω ∈ orthant n := by
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, Y ((q : ℝ).toNNReal) ω ∈ orthant n :=
    ae_all_iff.2 fun q => h1 _
  filter_upwards [hq] with ω hω u
  have hcl : IsClosed {s : ℝ≥0 | Y s ω ∈ orthant n} := orthant_isClosed.preimage (hc ω)
  have hsub : Set.range (fun q : ℚ => (q : ℝ).toNNReal) ⊆ {s : ℝ≥0 | Y s ω ∈ orthant n} := by
    rintro _ ⟨q, rfl⟩; exact hω q
  have := hcl.closure_subset_iff.2 hsub
  rw [denseRange_rat_toNNReal.closure_range] at this
  exact this (Set.mem_univ u)

/-- (5.18): from the linear growth of `∫ growthWeight` (Lemma 5.4), by Chebyshev, the path
spends at least half of its time in `{‖x‖ ≤ K̂₁}`. -/
theorem part1 (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (c : SDEState n) (hc : c ∈ openOrthant n)
    (hfc : ∀ i, ContinuousOn (C.f i) (orthant n)) (hgc : ∀ i, ContinuousOn (C.g i) (orthant n))
    (δ : ℝ) (hδ : 0 < δ) (Khat : ℝ) (hKhat : 0 < Khat)
    (hb : ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t))
    (hinv : ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ u, X x u ω ∈ orthant n)
    (hcont : ∀ x ∈ orthant n, ∀ ω, Continuous fun t => X x t ω) :
    ∃ Khat1 : ℝ, 1 < Khat1 ∧
      ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
        ENNReal.ofReal ((1 / 2 - ε) * t)
          ≤ volume {s : ℝ | s ∈ Set.Icc (0 : ℝ) t ∧ l1 (X x s.toNNReal ω) ≤ Khat1} := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set cm : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i => c i) with hcmdef
  have hcm : 0 < cm := (Finset.lt_inf'_iff _).2 fun i _ => hc i
  have hcmle : ∀ i, cm ≤ c i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  set A : ℝ := 2 * (Khat + 1) with hAdef
  have hA : 0 < A := by positivity
  set K1 : ℝ := max 2 (A ^ δ⁻¹ / cm) with hK1def
  set W0 : ℝ := (1 + cm * K1) ^ δ with hW0def
  have hAW : A ≤ W0 := by
    have h1 : A ^ δ⁻¹ ≤ cm * K1 := by
      have : A ^ δ⁻¹ / cm ≤ K1 := le_max_right _ _
      rw [div_le_iff₀ hcm] at this; linarith
    have h2 : 0 ≤ A ^ δ⁻¹ := Real.rpow_nonneg hA.le _
    calc A = (A ^ δ⁻¹) ^ δ := (Real.rpow_inv_rpow hA.le hδ.ne').symm
      _ ≤ W0 := Real.rpow_le_rpow h2 (by linarith) hδ.le
  have hW0 : 0 < W0 := lt_of_lt_of_le hA hAW
  -- lower bound of the weight far out
  have hlow : ∀ y ∈ orthant n, K1 < l1 y → W0 ≤ growthWeight C c δ y := by
    intro y hy hl
    have hl1 : l1 y = ∑ i, y i := Finset.sum_congr rfl fun i _ => abs_of_nonneg (hy i)
    have hcy : cm * K1 ≤ ∑ i, c i * y i := by
      calc cm * K1 ≤ cm * l1 y := mul_le_mul_of_nonneg_left hl.le hcm.le
        _ = ∑ i, cm * y i := by rw [hl1, Finset.mul_sum]
        _ ≤ ∑ i, c i * y i :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcmle i) (hy i)
    have hK10 : 0 ≤ K1 := le_trans (by norm_num) (le_max_left _ _)
    have hR : 1 ≤ 1 + ∑ i, (|C.f i y| + C.g i y ^ 2) := by
      have := Finset.sum_nonneg (s := Finset.univ)
        (fun i (_ : i ∈ Finset.univ) => add_nonneg (abs_nonneg (C.f i y)) (sq_nonneg (C.g i y)))
      linarith
    have hb1 : W0 ≤ (1 + ∑ i, c i * y i) ^ δ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hδ.le
    unfold growthWeight
    calc W0 ≤ (1 + ∑ i, c i * y i) ^ δ := hb1
      _ ≤ (1 + ∑ i, c i * y i) ^ δ * (1 + ∑ i, (|C.f i y| + C.g i y ^ 2)) :=
          le_mul_of_one_le_right (le_trans hW0.le hb1) hR
  refine ⟨K1, lt_of_lt_of_le one_lt_two (le_max_left _ _), fun x hx => ?_⟩
  filter_upwards [hb x hx, hinv x hx] with ω hω hin ε hε
  filter_upwards [hω 1 one_pos, eventually_ge_atTop 0] with t ht ht0
  set G : SDEState n → ℝ := fun y => growthWeight C c δ (StochKolmogorov.Classify.posPart y)
    with hGdef
  have hGc : Continuous G := continuous_weight C c δ hδ.le hfc hgc
  have hp : Continuous fun s : ℝ => X x s.toNNReal ω := (hcont x hx ω).comp continuous_real_toNNReal
  have hGp : Measurable fun s : ℝ => ENNReal.ofReal (G (X x s.toNNReal ω)) :=
    (hGc.comp hp).measurable.ennreal_ofReal
  have hlin : ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (G (X x s.toNNReal ω)) =
      ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ (X x s.toNNReal ω)) := by
    refine lintegral_congr fun s => ?_
    simp only [hGdef, posPart_eq_of_mem (hin _)]
  set Bs : Set ℝ := {s : ℝ | s ∈ Set.Icc (0 : ℝ) t ∧ K1 < l1 (X x s.toNNReal ω)} with hBs
  set As : Set ℝ := {s : ℝ | s ∈ Set.Icc (0 : ℝ) t ∧ l1 (X x s.toNNReal ω) ≤ K1} with hAs
  have hsub : Bs ⊆ {s | ENNReal.ofReal W0 ≤ ENNReal.ofReal (G (X x s.toNNReal ω))} ∩
      Set.Icc (0 : ℝ) t := by
    rintro s ⟨hs1, hs2⟩
    refine ⟨?_, hs1⟩
    show ENNReal.ofReal W0 ≤ ENNReal.ofReal (G (X x s.toNNReal ω))
    apply ENNReal.ofReal_le_ofReal
    simp only [hGdef, posPart_eq_of_mem (hin _)]
    exact hlow _ (hin _) hs2
  have hmk := mul_meas_ge_le_lintegral₀ (μ := volume.restrict (Set.Icc (0 : ℝ) t))
    hGp.aemeasurable (ENNReal.ofReal W0)
  have hW0ne : ENNReal.ofReal W0 ≠ 0 := by simpa using hW0
  have hBle : volume Bs ≤ ENNReal.ofReal (t / 2) := by
    have key : ENNReal.ofReal W0 * volume Bs ≤ ENNReal.ofReal W0 * ENNReal.ofReal (t / 2) := by
      calc ENNReal.ofReal W0 * volume Bs
          ≤ ENNReal.ofReal W0 * (volume.restrict (Set.Icc (0 : ℝ) t))
              {s | ENNReal.ofReal W0 ≤ ENNReal.ofReal (G (X x s.toNNReal ω))} :=
            mul_le_mul' le_rfl ((measure_mono hsub).trans (Measure.le_restrict_apply _ _))
        _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (G (X x s.toNNReal ω)) := hmk
        _ ≤ ENNReal.ofReal ((Khat + 1) * t) := hlin ▸ ht
        _ ≤ ENNReal.ofReal (W0 * (t / 2)) := by
            apply ENNReal.ofReal_le_ofReal
            have : (Khat + 1) * t = A * (t / 2) := by rw [hAdef]; ring
            rw [this]
            exact mul_le_mul_of_nonneg_right hAW (by linarith)
        _ = ENNReal.ofReal W0 * ENNReal.ofReal (t / 2) := ENNReal.ofReal_mul hW0.le
    exact (ENNReal.mul_le_mul_iff_right hW0ne ENNReal.ofReal_ne_top).1 key
  have hcover : Set.Icc (0 : ℝ) t ⊆ As ∪ Bs := by
    intro s hs
    by_cases h : l1 (X x s.toNNReal ω) ≤ K1
    · exact Or.inl ⟨hs, h⟩
    · exact Or.inr ⟨hs, lt_of_not_ge h⟩
  have hvol : volume (Set.Icc (0 : ℝ) t) = ENNReal.ofReal t := by
    rw [Real.volume_Icc, sub_zero]
  have h1 : ENNReal.ofReal t ≤ volume As + volume Bs := by
    rw [← hvol]; exact (measure_mono hcover).trans (measure_union_le _ _)
  have h2 : ENNReal.ofReal t - volume Bs ≤ volume As := tsub_le_iff_right.2 h1
  have h3 : ENNReal.ofReal (t / 2) = ENNReal.ofReal t - ENNReal.ofReal (t / 2) := by
    rw [← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ t / 2)]; congr 1; ring
  calc ENNReal.ofReal ((1 / 2 - ε) * t) ≤ ENNReal.ofReal (t / 2) :=
        ENNReal.ofReal_le_ofReal (by nlinarith)
    _ = ENNReal.ofReal t - ENNReal.ofReal (t / 2) := h3
    _ ≤ ENNReal.ofReal t - volume Bs := tsub_le_tsub_left hBle _
    _ ≤ volume As := h2

/-- `δ₀` of (3.2) exists (copied from 1733f857_lib ItoLib.exists_isDelta0, Classify coefficients). -/
theorem exists_isDelta0 (C : Coeffs n) (γb : ℝ) (hγ : 0 < γb) :
    ∃ δ₀ : ℝ, IsDelta0 C γb δ₀ := by
  set S : ℝ := ∑ i, ∑ j, |C.sig i j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsij : ∀ i j, |C.sig i j| ≤ S := by
    intro i j
    calc |C.sig i j| ≤ ∑ j', |C.sig i j'| :=
          Finset.single_le_sum (f := fun j' => |C.sig i j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ j', |C.sig i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hden : 0 < 3 * S * n + 3 := by positivity
  refine ⟨γb / (3 * S * n + 3), div_pos hγ hden, ?_, fun x _ => ?_⟩
  · rw [div_lt_div_iff₀ hden two_pos]
    nlinarith [mul_nonneg hS0 (Nat.cast_nonneg (α := ℝ) n)]
  · set δ := γb / (3 * S * n + 3) with hδ
    have hδ0 : 0 ≤ δ := (div_pos hγ hden).le
    set G : ℝ := ∑ i, C.g i x ^ 2 with hG
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hterm : ∀ i j, |C.g i x * C.g j x * C.sig i j|
        ≤ S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by
      intro i j
      rw [abs_mul, abs_mul]
      have h1 : |C.g i x| * |C.g j x| ≤ (C.g i x ^ 2 + C.g j x ^ 2) / 2 := by
        nlinarith [sq_nonneg (|C.g i x| - |C.g j x|), sq_abs (C.g i x), sq_abs (C.g j x)]
      calc |C.g i x| * |C.g j x| * |C.sig i j| ≤ ((C.g i x ^ 2 + C.g j x ^ 2) / 2) * S :=
            mul_le_mul h1 (hsij i j) (abs_nonneg _) (by positivity)
        _ = S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by ring
    have hsum : ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| ≤ S * n * G := by
      calc ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
          ≤ ∑ i : Fin n, ∑ j : Fin n, S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
        _ = S * n * G := by
            simp only [← Finset.mul_sum, add_div, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hG, ← Finset.sum_div]
            ring
    have hkey : δ * (3 * S * n + 3) = γb := by rw [hδ, div_mul_cancel₀ _ hden.ne']
    calc 3 * δ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| + δ * G
        ≤ 3 * δ * (S * n * G) + δ * G := by nlinarith
      _ ≤ δ * (3 * S * n + 3) * G := by nlinarith [mul_nonneg hδ0 hG0]
      _ = γb * G := by rw [hkey]

/-- Assumption 1.4 is monotone in `δ₁` (only large `‖x‖ ≥ 1` matters). -/
theorem a14_mono (C : Coeffs n) {δ₁ δ' : ℝ} (h14 : Assumption14 C δ₁)
    (hδ' : 0 < δ') (hle : δ' ≤ δ₁) : Assumption14 C δ' := by
  refine ⟨hδ', ?_⟩
  have hev : ∀ᶠ x in comap l1 atTop ⊓ 𝓟 (orthant n), 1 ≤ l1 x :=
    Filter.Eventually.filter_mono inf_le_left
      (Filter.tendsto_comap.eventually (eventually_ge_atTop 1))
  refine squeeze_zero' (Filter.Eventually.of_forall fun x => ?_) (hev.mono fun x hx => ?_) h14.2
  · have hl : 0 ≤ l1 x := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hD : 0 ≤ 1 + ∑ i, (|C.f i x| + C.g i x ^ 2) :=
      add_nonneg zero_le_one (Finset.sum_nonneg fun i _ =>
        add_nonneg (abs_nonneg _) (sq_nonneg _))
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hl _)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)) hD
  · have hD : 0 ≤ 1 + ∑ i, (|C.f i x| + C.g i x ^ 2) :=
      add_nonneg zero_le_one (Finset.sum_nonneg fun i _ =>
        add_nonneg (abs_nonneg _) (sq_nonneg _))
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hx hle) (Finset.sum_nonneg fun i _ => sq_nonneg _)) hD


/-- Assembly of Lemma 5.5 from Lemma 5.4 clause 1, fixed-time orthant invariance and
short-time positivity (5.19 at every radius). -/
theorem assemble (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁)
    (h54 : ∀ δ₀ : ℝ, IsDelta0 C γb δ₀ → ∀ δ₁ : ℝ, Assumption14 C δ₁ → δ₁ ≤ δ₀ →
      ∃ Khat : ℝ, 0 < Khat ∧ ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ t : ℝ in atTop,
          ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ₁ (X x s.toNNReal ω))
            ≤ ENNReal.ofReal ((Khat + ε) * t))
    (hinvt : ∀ x ∈ orthant n, ∀ t, ∀ᵐ ω ∂P, X x t ω ∈ orthant n)
    (hstp : ∀ R T : ℝ, 0 < T → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → ∃ β : ℝ, 0 < β ∧
      ∀ i, ∀ x ∈ orthant n, l1 x ≤ R → ε₂ < x i →
        1 - ε₁ < (P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T → β < X x t ω i}).toReal) :
    ∃ Khat1 : ℝ, 1 < Khat1 ∧
      (∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
        ENNReal.ofReal ((1 / 2 - ε) * t)
          ≤ volume {s : ℝ | s ∈ Set.Icc (0 : ℝ) t ∧ l1 (X x s.toNNReal ω) ≤ Khat1}) ∧
      ∀ T : ℝ, 0 < T → ∀ ε₁ : ℝ, 0 < ε₁ → ∀ ε₂ : ℝ, 0 < ε₂ → ∃ β : ℝ, 0 < β ∧
        ∀ i, ∀ x ∈ orthant n, l1 x ≤ Khat1 → ε₂ < x i →
          1 - ε₁ < (P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T → β < X x t ω i}).toReal := by
  obtain ⟨δ₀, hδ₀⟩ := exists_isDelta0 C γb hA.2.2.2.1
  have hδ' : 0 < min δ₁ δ₀ := lt_min h14.1 hδ₀.1
  have h14' : Assumption14 C (min δ₁ δ₀) := a14_mono C h14 hδ' (min_le_left _ _)
  obtain ⟨Khat, hK, hb⟩ := h54 δ₀ hδ₀ (min δ₁ δ₀) h14' (min_le_right _ _)
  have hcont : ∀ x ∈ orthant n, ∀ ω, Continuous fun t => X x t ω :=
    fun x hx => (hX.2.2 x hx).2.1
  have hinv : ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ u, X x u ω ∈ orthant n :=
    fun x hx => inv_all P (hcont x hx) (hinvt x hx)
  obtain ⟨K1, hK1, hp1⟩ := part1 hn P C X c hA.2.2.1
    (fun i => (hA.2.1 i).1.continuousOn) (fun i => (hA.2.1 i).2.continuousOn)
    (min δ₁ δ₀) hδ' Khat hK hb hinv hcont
  exact ⟨K1, hK1, hp1, fun T hT ε₁ hε₁ ε₂ hε₂ => hstp K1 T hT ε₁ ε₂ hε₁ hε₂⟩

end L55

open MeasureTheory ProbabilityTheory Filter ENNReal NNReal Topology BoundedContinuousFunction StochKolmogorov.Classify EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) :
    ∃ Khat1 : ℝ, 1 < Khat1 ∧
      (∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
        ENNReal.ofReal ((1 / 2 - ε) * t)
          ≤ volume {s : ℝ | s ∈ Set.Icc (0 : ℝ) t ∧ l1 (X x s.toNNReal ω) ≤ Khat1}) ∧
      ∀ T : ℝ, 0 < T → ∀ ε₁ : ℝ, 0 < ε₁ → ∀ ε₂ : ℝ, 0 < ε₂ → ∃ β : ℝ, 0 < β ∧
        ∀ i, ∀ x ∈ orthant n, l1 x ≤ Khat1 → ε₂ < x i →
          1 - ε₁ < (P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T → β < X x t ω i}).toReal := by
  haveI : IsProbabilityMeasure P := hX.1
  exact L55.assemble hn P C B X hX c γb hA δ₁ h14
    (fun δ₀ hδ₀ δ₁' h14' hle =>
      (StochKolmogorov.Classify.lemma_5_4 hn P C B X hX c γb hA δ₀ hδ₀ δ₁' h14' hle).1)
    (fun x hx t => StochKolmogorov.Persist.orthant_invariance_closed P ⟨C.f, C.g, C.Γ⟩ B hX.2.1
      hA.2.1 hx (hX.2.2 x hx) t)
    (StochKolmogorov.Classify.short_time_positivity P C B X hX c γb hA)

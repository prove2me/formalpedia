-- Prove2me | solution 1 for PrefRobustSR.WorstCase.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:34:02.329332+00:00
-- url     : https://prove2.me/submissions/e0356fce-43a8-4ee9-a66f-3f59d4f9b70b

import Mathlib
import Definitions.Def_PrefRobustSR_WorstCase_Model

set_option autoImplicit false
open MeasureTheory PrefRobustSR.WorstCase
open scoped ENNReal

namespace PRH

lemma tendsto_loss (l : ℝ → ℝ) (hl : l ∈ LossClass) : Filter.Tendsto l Filter.atTop Filter.atTop := by
  obtain ⟨hc, hm, z0, hz0, hs⟩ := hl
  have hs0 : 0 < l 1 - l 0 := by
    have : l 0 < l 1 := hs (show (0:ℝ) ∈ Set.Ici z0 from hz0.le) (show (1:ℝ) ∈ Set.Ici z0 from by
      simp only [Set.mem_Ici]; linarith) (by norm_num)
    linarith
  have key : ∀ x : ℝ, 1 < x → l 1 + (l 1 - l 0) * (x - 1) ≤ l x := by
    intro x hx
    have := hc.slope_mono_adjacent (x := 0) (y := 1) (z := x) (Set.mem_univ _) (Set.mem_univ _)
      (by norm_num) hx
    have hx' : 0 < x - 1 := by linarith
    simp only [sub_zero, div_one] at this
    rw [le_div_iff₀ hx'] at this
    linarith
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_atTop]
  refine ⟨max 2 (1 + (b - l 1) / (l 1 - l 0)), fun x hx => ?_⟩
  have h1 : 1 < x := by have := le_max_left 2 (1 + (b - l 1) / (l 1 - l 0)); linarith
  have h2 : (b - l 1) / (l 1 - l 0) ≤ x - 1 := by
    have := le_max_right 2 (1 + (b - l 1) / (l 1 - l 0)); linarith
  rw [div_le_iff₀ hs0] at h2
  have := key x h1
  nlinarith

lemma subgrad (l : ℝ → ℝ) (hc : ConvexOn ℝ Set.univ l) (hm : Monotone l) (a : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x, l a + c * (x - a) ≤ l x := by
  have hint : a ∈ interior (Set.univ : Set ℝ) := by simp
  refine ⟨derivWithin l (Set.Ioi a) a, ?_, ?_⟩
  · have h1 := hc.leftDeriv_le_rightDeriv_of_mem_interior hint
    have h2 := hc.slope_le_leftDeriv_of_mem_interior (x := a - 1) (y := a) (Set.mem_univ _) hint
      (by linarith)
    have h3 : 0 ≤ slope l (a - 1) a := by
      rw [slope_def_field]
      have := hm (show a - 1 ≤ a by linarith)
      simp only [sub_sub_cancel]
      rw [div_one]; linarith
    linarith
  · intro x
    rcases lt_trichotomy x a with hx | hx | hx
    · have h1 := hc.leftDeriv_le_rightDeriv_of_mem_interior hint
      have h2 := hc.slope_le_leftDeriv_of_mem_interior (x := x) (y := a) (Set.mem_univ _) hint hx
      rw [slope_def_field] at h2
      have hax : 0 < a - x := by linarith
      rw [div_le_iff₀ hax] at h2
      have h3 : (l a - l x) ≤ derivWithin l (Set.Ioi a) a * (a - x) := by
        have := mul_le_mul_of_nonneg_right h1 hax.le
        linarith
      nlinarith
    · subst hx; simp
    · have h2 := hc.rightDeriv_le_slope_of_mem_interior (x := a) (y := x) hint (Set.mem_univ _) hx
      rw [slope_def_field] at h2
      have hax : 0 < x - a := by linarith
      rw [le_div_iff₀ hax] at h2
      linarith

end PRH

namespace PRH

open DupacovaWets.Consistency

lemma expect_coe_unfold {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → ℝ) :
    expect P (fun ω => ((h ω : ℝ) : EReal)) =
      if ∫⁻ ω, ENNReal.ofReal (h ω) ∂P = ∞ then ⊤
      else ((∫⁻ ω, ENNReal.ofReal (h ω) ∂P : ℝ≥0∞) : EReal) -
        ((∫⁻ ω, ENNReal.ofReal (-h ω) ∂P : ℝ≥0∞) : EReal) := by
  unfold expect
  simp only [EReal.real_coe_toENNReal]
  congr 4

lemma expect_real_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h B : Ω → ℝ) (hh : AEMeasurable h P) (hB : Integrable B P) (hle : ∀ ω, B ω ≤ h ω) :
    expect P (fun ω => ((h ω : ℝ) : EReal)) =
      ((∫⁻ ω, ENNReal.ofReal (h ω - B ω) ∂P : ℝ≥0∞) : EReal) + ((∫ ω, B ω ∂P : ℝ) : EReal) := by
  rw [expect_coe_unfold]
  by_cases hU : ∫⁻ ω, ENNReal.ofReal (h ω - B ω) ∂P = ∞
  · have h1 : ∫⁻ ω, ENNReal.ofReal (h ω) ∂P = ∞ := by
      by_contra hne
      have hlt : ∫⁻ ω, ENNReal.ofReal (h ω) ∂P < ∞ := lt_top_iff_ne_top.2 hne
      have h2 : ∫⁻ ω, ENNReal.ofReal (h ω - B ω) ∂P ≤
          ∫⁻ ω, ENNReal.ofReal (h ω) ∂P + ∫⁻ ω, ENNReal.ofReal (-B ω) ∂P := by
        rw [← lintegral_add_left' hh.ennreal_ofReal]
        refine lintegral_mono fun ω => ?_
        calc ENNReal.ofReal (h ω - B ω) = ENNReal.ofReal (h ω + -B ω) := by rw [sub_eq_add_neg]
          _ ≤ _ := ENNReal.ofReal_add_le
      have h3 : ∫⁻ ω, ENNReal.ofReal (-B ω) ∂P < ∞ := hB.neg.lintegral_lt_top
      exact absurd hU (ne_of_lt (lt_of_le_of_lt h2 (ENNReal.add_lt_top.2 ⟨hlt, h3⟩)))
    rw [if_pos h1, hU]
    simp
  · have hU' : ∫⁻ ω, ENNReal.ofReal (h ω - B ω) ∂P < ∞ := lt_top_iff_ne_top.2 hU
    have hnn : 0 ≤ᵐ[P] fun ω => h ω - B ω := Filter.Eventually.of_forall fun ω => by
      simp only [Pi.zero_apply]; linarith [hle ω]
    have hint : Integrable (fun ω => h ω - B ω) P :=
      ⟨(hh.sub hB.aemeasurable).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal hnn).2 hU'⟩
    have hIh : Integrable h P := by
      have e : h = (fun ω => h ω - B ω) + B := by funext ω; simp
      rw [e]; exact hint.add hB
    have hp : ∫⁻ ω, ENNReal.ofReal (h ω) ∂P ≠ ∞ := hIh.lintegral_lt_top.ne
    have hn : ∫⁻ ω, ENNReal.ofReal (-h ω) ∂P ≠ ∞ := hIh.neg.lintegral_lt_top.ne
    rw [if_neg hp]
    have e1 := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hIh
    have e2 : ENNReal.ofReal (∫ ω, (h ω - B ω) ∂P) = ∫⁻ ω, ENNReal.ofReal (h ω - B ω) ∂P :=
      ofReal_integral_eq_lintegral_ofReal hint hnn
    have e3 : (∫ ω, h ω ∂P) = (∫ ω, (h ω - B ω) ∂P) + ∫ ω, B ω ∂P := by
      rw [← integral_add hint hB]; simp
    have e4 : 0 ≤ ∫ ω, (h ω - B ω) ∂P := integral_nonneg_of_ae hnn
    rw [← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
      ← EReal.coe_ennreal_toReal hU, ← e2, ENNReal.toReal_ofReal e4, ← EReal.coe_sub,
      ← EReal.coe_add]
    congr 1
    linarith

end PRH

namespace PRH

open DupacovaWets.Consistency

variable {Ω : Type*} [MeasurableSpace Ω]

lemma loss_cont (l : ℝ → ℝ) (hl : l ∈ LossClass) : Continuous l := by
  have := hl.1.continuousOn isOpen_univ
  exact continuousOn_univ.1 this

lemma loss_meas (P : Measure Ω) (l : ℝ → ℝ) (hl : l ∈ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) (t : ℝ) :
    AEMeasurable (fun ω => l (-Z ω - t)) P := by
  have h1 : AEStronglyMeasurable (fun ω => -Z ω - t) P :=
    hZ.aestronglyMeasurable.neg.sub aestronglyMeasurable_const
  exact ((loss_cont l hl).comp_aestronglyMeasurable h1).aemeasurable

lemma jensen (P : Measure Ω) [IsProbabilityMeasure P] (l : ℝ → ℝ) (hl : l ∈ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) (t : ℝ) :
    ((l (-(∫ ω, Z ω ∂P) - t) : ℝ) : EReal) ≤
      expect P (fun ω => ((l (-Z ω - t) : ℝ) : EReal)) := by
  obtain ⟨c, hc0, hc⟩ := subgrad l hl.1 hl.2.1 (-(∫ ω, Z ω ∂P) - t)
  set a := -(∫ ω, Z ω ∂P) - t with ha
  set B : Ω → ℝ := fun ω => (l a - c * t - c * a) + (-c) * Z ω with hB
  have hBi : Integrable B P := (integrable_const _).add (hZ.const_mul _)
  have hBint : ∫ ω, B ω ∂P = l a := by
    simp only [hB]
    rw [integral_add (integrable_const _) (hZ.const_mul _), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    have : (∫ ω, Z ω ∂P) = -a - t := by simp [ha]
    rw [this]; ring
  have hBle : ∀ ω, B ω ≤ l (-Z ω - t) := fun ω => by
    have := hc (-Z ω - t)
    simp only [hB]; nlinarith
  rw [expect_real_eq P _ B (loss_meas P l hl Z hZ t) hBi hBle, hBint]
  exact le_add_of_nonneg_left (by positivity)

end PRH

namespace PRH

open DupacovaWets.Consistency Filter

variable {Ω : Type*} [MeasurableSpace Ω]

lemma expect_mono (P : Measure Ω) (g1 g2 : Ω → EReal) (h : ∀ ω, g1 ω ≤ g2 ω) :
    expect P g1 ≤ expect P g2 := by
  unfold expect
  have ha : ∫⁻ ω, (g1 ω).toENNReal ∂P ≤ ∫⁻ ω, (g2 ω).toENNReal ∂P :=
    lintegral_mono fun ω => EReal.toENNReal_le_toENNReal (h ω)
  have hb : ∫⁻ ω, (-g2 ω).toENNReal ∂P ≤ ∫⁻ ω, (-g1 ω).toENNReal ∂P :=
    lintegral_mono fun ω => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (h ω))
  by_cases h2 : ∫⁻ ω, (g2 ω).toENNReal ∂P = ∞
  · rw [if_pos h2]; exact le_top
  · have h1 : ∫⁻ ω, (g1 ω).toENNReal ∂P ≠ ∞ := ne_top_of_le_ne_top h2 ha
    rw [if_neg h1, if_neg h2]
    exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2 ha)
      (EReal.coe_ennreal_le_coe_ennreal_iff.2 hb)

lemma gap_anti (P : Measure Ω) (l : ℝ → ℝ) (hl : l ∈ LossClass) (Z : Ω → ℝ) {t t' : ℝ}
    (h : t ≤ t') : gap P l Z t' ≤ gap P l Z t := by
  unfold gap
  refine EReal.sub_le_sub (expect_mono P _ _ fun ω => ?_) le_rfl
  exact_mod_cast hl.2.1 (by linarith : -Z ω - t' ≤ -Z ω - t)

lemma ereal_ennreal_le {U : ℝ≥0∞} {r : ℝ} (h : (U : EReal) ≤ (r : EReal)) : U ≤ ENNReal.ofReal r := by
  by_cases hr : r < 0
  · exfalso
    have : (0 : EReal) ≤ (U : EReal) := EReal.coe_ennreal_nonneg U
    have h2 : ((0 : ℝ) : EReal) ≤ (r : EReal) := by simpa using this.trans h
    have := EReal.coe_le_coe_iff.1 h2
    linarith
  · have h2 : (U : EReal) ≤ ((ENNReal.ofReal r : ℝ≥0∞) : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left (not_lt.1 hr)]; exact h
    exact EReal.coe_ennreal_le_coe_ennreal_iff.1 h2

lemma ennreal_ereal_le {U : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) (h : U ≤ ENNReal.ofReal r) :
    (U : EReal) ≤ (r : EReal) := by
  have := EReal.coe_ennreal_le_coe_ennreal_iff.2 h
  rwa [EReal.coe_ennreal_ofReal, max_eq_left hr] at this

lemma right_cont (P : Measure Ω) [IsProbabilityMeasure P] (l : ℝ → ℝ) (hl : l ∈ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) (th : ℝ)
    (hF : ∀ n : ℕ, gap P l Z (th + 1 / ((n : ℝ) + 1)) ≤ 0) : gap P l Z th ≤ 0 := by
  obtain ⟨c, hc0, hc⟩ := subgrad l hl.1 hl.2.1 0
  set B : Ω → ℝ := fun ω => (l 0 - c * th - c) + (-c) * Z ω with hB
  have hBi : Integrable B P := (integrable_const _).add (hZ.const_mul _)
  have hBle : ∀ t, t ≤ th + 1 → ∀ ω, B ω ≤ l (-Z ω - t) := fun t ht ω => by
    have h1 := hc (-Z ω - (th + 1))
    have h2 := hl.2.1 (show -Z ω - (th + 1) ≤ -Z ω - t by linarith)
    simp only [hB]; nlinarith
  set tn : ℕ → ℝ := fun n => th + 1 / ((n : ℝ) + 1) with htn
  have htn_le : ∀ n, tn n ≤ th + 1 := fun n => by
    simp only [htn]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith
  have hr : ∀ n, ((∫⁻ ω, ENNReal.ofReal (l (-Z ω - tn n) - B ω) ∂P : ℝ≥0∞) : EReal) ≤
      ((l 0 - ∫ ω, B ω ∂P : ℝ) : EReal) := by
    intro n
    have h1 := hF n
    unfold gap at h1
    rw [expect_real_eq P _ B (loss_meas P l hl Z hZ _) hBi (hBle _ (htn_le n))] at h1
    set U : EReal := ((∫⁻ ω, ENNReal.ofReal (l (-Z ω - tn n) - B ω) ∂P : ℝ≥0∞) : EReal)
    have h2 : U + ((∫ ω, B ω ∂P : ℝ) : EReal) ≤ ((l 0 : ℝ) : EReal) := EReal.sub_nonpos.1 h1
    have h3 : U ≤ ((l 0 : ℝ) : EReal) - ((∫ ω, B ω ∂P : ℝ) : EReal) :=
      (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).2 h2
    rw [← EReal.coe_sub] at h3
    exact h3
  set r : ℝ := l 0 - ∫ ω, B ω ∂P with hrdef
  have hr0 : 0 ≤ r := by
    have h0 := hr 0
    have h1 : (0 : EReal) ≤ ((∫⁻ ω, ENNReal.ofReal (l (-Z ω - tn 0) - B ω) ∂P : ℝ≥0∞) : EReal) :=
      EReal.coe_ennreal_nonneg _
    have := h1.trans h0
    exact_mod_cast this
  have hfat := lintegral_liminf_le' (μ := P) (u := atTop)
    (f := fun n ω => ENNReal.ofReal (l (-Z ω - tn n) - B ω))
    (fun n => ((loss_meas P l hl Z hZ _).sub hBi.aemeasurable).ennreal_ofReal)
  have hlim : ∀ ω, liminf (fun n => ENNReal.ofReal (l (-Z ω - tn n) - B ω)) atTop =
      ENNReal.ofReal (l (-Z ω - th) - B ω) := by
    intro ω
    apply Tendsto.liminf_eq
    apply ENNReal.tendsto_ofReal
    have h1 : Tendsto (fun n : ℕ => tn n) atTop (nhds th) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add th
      simpa [htn] using this
    have h2 : Tendsto (fun n : ℕ => -Z ω - tn n) atTop (nhds (-Z ω - th)) :=
      tendsto_const_nhds.sub h1
    exact (((loss_cont l hl).tendsto _).comp h2).sub_const _
  simp only [hlim] at hfat
  have hle : liminf (fun n => ∫⁻ ω, ENNReal.ofReal (l (-Z ω - tn n) - B ω) ∂P) atTop ≤
      ENNReal.ofReal r :=
    liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun n => ereal_ennreal_le (hr n))
  have hU := ennreal_ereal_le hr0 (hfat.trans hle)
  unfold gap
  rw [expect_real_eq P _ B (loss_meas P l hl Z hZ _) hBi (hBle _ (by linarith [(show (0:ℝ) ≤ 1 by norm_num)]))]
  refine EReal.sub_nonpos.2 ?_
  calc _ ≤ ((r : ℝ) : EReal) + ((∫ ω, B ω ∂P : ℝ) : EReal) := add_le_add_left hU _
    _ = ((l 0 : ℝ) : EReal) := by rw [← EReal.coe_add]; congr 1; simp [hrdef]

end PRH

namespace PRH

open DupacovaWets.Consistency Filter

variable {Ω : Type*} [MeasurableSpace Ω]

lemma gap_le_zero (P : Measure Ω) [IsProbabilityMeasure P] (l : ℝ → ℝ) (hl : l ∈ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) (th : ℝ) (hsr : SR P l Z ≤ (th : EReal)) :
    gap P l Z th ≤ 0 := by
  refine right_cont P l hl Z hZ th fun n => ?_
  have hpos : th < th + 1 / ((n : ℝ) + 1) := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hlt : SR P l Z < ((th + 1 / ((n : ℝ) + 1) : ℝ) : EReal) :=
    lt_of_le_of_lt hsr (by exact_mod_cast hpos)
  unfold SR at hlt
  obtain ⟨b, ⟨t, ht, rfl⟩, hbt⟩ := sInf_lt_iff.1 hlt
  have : t < th + 1 / ((n : ℝ) + 1) := EReal.coe_lt_coe_iff.1 hbt
  exact le_trans (gap_anti P l hl Z this.le) ht

lemma sr_bdd (P : Measure Ω) [IsProbabilityMeasure P] (l : ℝ → ℝ) (hl : l ∈ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) : ∃ T : ℝ, (T : EReal) ≤ SR P l Z := by
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.1
    ((tendsto_loss l hl).eventually_ge_atTop (l 0 + 1))
  refine ⟨-(∫ ω, Z ω ∂P) - Y, ?_⟩
  unfold SR
  refine le_sInf ?_
  rintro b ⟨t, ht, rfl⟩
  by_contra hlt
  have hlt' : t < -(∫ ω, Z ω ∂P) - Y := EReal.coe_lt_coe_iff.1 (not_le.1 hlt)
  have hy := hY (-(∫ ω, Z ω ∂P) - t) (by linarith)
  have hj := jensen P l hl Z hZ t
  have hg : (0 : EReal) < gap P l Z t := by
    calc (0 : EReal) < ((l (-(∫ ω, Z ω ∂P) - t) - l 0 : ℝ) : EReal) := by
          exact_mod_cast (by linarith)
      _ = ((l (-(∫ ω, Z ω ∂P) - t) : ℝ) : EReal) - ((l 0 : ℝ) : EReal) := EReal.coe_sub _ _
      _ ≤ gap P l Z t := EReal.sub_le_sub hj le_rfl
  exact absurd (show gap P l Z t ≤ 0 from ht) (not_le.2 hg)

end PRH

namespace PRH

open DupacovaWets.Consistency

lemma conv {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Set (ℝ → ℝ)) (hL : L ⊆ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) (th : ℝ)
    (hth : (⨆ l ∈ L, SR P l Z) = (th : EReal)) :
    (⨆ l ∈ L, gap P l Z th) ≤ 0 ∧ SRL P L Z ≤ (th : EReal) := by
  have h1 : (⨆ l ∈ L, gap P l Z th) ≤ 0 :=
    iSup₂_le fun l hl => gap_le_zero P l (hL hl) Z hZ th
      ((le_iSup₂ (f := fun l (_ : l ∈ L) => SR P l Z) l hl).trans hth.le)
  refine ⟨h1, ?_⟩
  unfold SRL
  exact sInf_le ⟨th, h1, rfl⟩

end PRH

namespace PRH

open DupacovaWets.Consistency

variable {Ω : Type*} [MeasurableSpace Ω]

lemma main (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Set (ℝ → ℝ)) (hL : L ⊆ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) : SRL P L Z = ⨆ l ∈ L, SR P l Z := by
  apply le_antisymm
  · by_cases htop : (⨆ l ∈ L, SR P l Z) = ⊤
    · rw [htop]; exact le_top
    by_cases hLne : L.Nonempty
    · obtain ⟨l₀, hl₀⟩ := hLne
      obtain ⟨T, hT⟩ := sr_bdd P l₀ (hL hl₀) Z hZ
      have hbot : (⨆ l ∈ L, SR P l Z) ≠ ⊥ := by
        intro hb
        have : (T : EReal) ≤ ⊥ :=
          hT.trans ((le_iSup₂ (f := fun l (_ : l ∈ L) => SR P l Z) l₀ hl₀).trans hb.le)
        exact absurd this (by simp)
      have hreal : (⨆ l ∈ L, SR P l Z) = (((⨆ l ∈ L, SR P l Z).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal htop hbot).symm
      have := (conv P L hL Z hZ _ hreal).2
      rwa [← hreal] at this
    · rw [Set.not_nonempty_iff_eq_empty] at hLne
      subst hLne
      simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, le_bot_iff]
      by_contra hne
      have hlt : (⊥ : EReal) < SRL P ∅ Z := bot_lt_iff_ne_bot.2 hne
      obtain ⟨x, -, hx⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
      have h1 : SRL P ∅ Z ≤ ((x - 1 : ℝ) : EReal) := by
        unfold SRL
        exact sInf_le ⟨x - 1, by simp, rfl⟩
      have h2 : ((x - 1 : ℝ) : EReal) < (x : EReal) := by exact_mod_cast (by linarith)
      exact absurd (lt_of_lt_of_le hx h1) (not_lt.2 h2.le)
  · refine iSup₂_le fun l hl => ?_
    unfold SR SRL
    apply sInf_le_sInf
    apply Set.image_mono
    intro t ht
    exact le_trans (le_iSup₂ (f := fun l (_ : l ∈ L) => gap P l Z t) l hl) ht

end PRH

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    (∀ L : Set (ℝ → ℝ), L ⊆ LossClass →
      ∀ Z : Ω → ℝ, MemLp Z p P →
        SRL P L Z = (⨆ l ∈ L, SR P l Z) ∧
        SRL P L Z = robustRisk ((fun l => SR P l) '' L) Z) ∧
    (∀ R : Set ((Ω → ℝ) → EReal),
      R ⊆ (fun l => SR P l) '' LossClass →
      ∀ Z : Ω → ℝ, MemLp Z p P →
        robustRisk R Z = SRL P {l | l ∈ LossClass ∧ SR P l ∈ R} Z) := by
  have hint : ∀ Z : Ω → ℝ, MemLp Z p P → Integrable Z P := fun Z hZ => hZ.integrable hp1
  refine ⟨fun L hL Z hZ => ?_, fun R hR Z hZ => ?_⟩
  · have h := PRH.main P L hL Z (hint Z hZ)
    refine ⟨h, ?_⟩
    rw [h]
    unfold robustRisk
    simp only [iSup_image]
  · rw [PRH.main P _ (fun l hl => hl.1) Z (hint Z hZ)]
    unfold robustRisk
    apply le_antisymm
    · refine iSup₂_le fun ρ hρ => ?_
      obtain ⟨l, hl, rfl⟩ := hR hρ
      exact le_iSup₂ (f := fun l (_ : l ∈ {l | l ∈ LossClass ∧ SR P l ∈ R}) => SR P l Z) l ⟨hl, hρ⟩
    · refine iSup₂_le fun l hl => ?_
      exact le_iSup₂ (f := fun ρ (_ : ρ ∈ R) => ρ Z) (SR P l) hl.2


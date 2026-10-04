-- Prove2me | solution 1 for SennottDP.Fatou.generalized_dominated_convergence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:40:52.630307+00:00
-- url     : https://prove2.me/submissions/4a5e5083-abcf-4505-b214-3b71386c6918

import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic
import Theorems.Thm_SennottDP_Fatou_liminf_tsum_ge

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

theorem gdc_low (A : ℕ → ℝ≥0∞) (a δ : ℝ≥0∞) (ha_top : a ≠ ⊤) (hδ : 0 < δ)
    (ha : a ≤ liminf A atTop) : ∀ᶠ N in atTop, a - δ ≤ A N := by
  by_cases h0 : a = 0
  · exact Eventually.of_forall fun N => by rw [h0, zero_tsub]; exact bot_le
  · have : a - δ < liminf A atTop :=
      lt_of_lt_of_le (ENNReal.sub_lt_self ha_top h0 hδ.ne') ha
    exact (eventually_lt_of_lt_liminf this).mono fun N h => h.le

theorem gdc_squeeze {X Y Z : ℕ → ℝ≥0∞} {Xl Yl Zl : ℝ≥0∞} (hXYZ : ∀ N, X N + Y N = Z N)
    (hZ : Tendsto Z atTop (𝓝 Zl)) (hZl : Zl ≠ ⊤) (hX : Xl ≤ liminf X atTop)
    (hY : Yl ≤ liminf Y atTop) (hl : Xl + Yl = Zl) : Tendsto X atTop (𝓝 Xl) := by
  have hXl : Xl ≠ ⊤ := ne_top_of_le_ne_top hZl (hl ▸ le_self_add)
  have hYl : Yl ≠ ⊤ := ne_top_of_le_ne_top hZl (hl ▸ le_add_self)
  rw [ENNReal.tendsto_nhds hXl]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have e1 : ∀ᶠ N in atTop, Z N < Zl + ε / 2 :=
    hZ.eventually (gt_mem_nhds (ENNReal.lt_add_right hZl hε2.ne'))
  filter_upwards [gdc_low X Xl ε hXl hε hX, e1, gdc_low Y Yl (ε / 2) hYl hε2 hY]
    with N h1 h2 h3
  refine ⟨h1, ?_⟩
  have hc : Yl - ε / 2 ≠ ⊤ := ne_top_of_le_ne_top hYl tsub_le_self
  have k1 : X N + (Yl - ε / 2) < (Xl + ε) + (Yl - ε / 2) := by
    calc X N + (Yl - ε / 2) ≤ X N + Y N := by gcongr
      _ = Z N := hXYZ N
      _ < Zl + ε / 2 := h2
      _ = Xl + Yl + ε / 2 := by rw [hl]
      _ ≤ Xl + ((Yl - ε / 2) + ε / 2) + ε / 2 := by gcongr; exact le_tsub_add
      _ = (Xl + (ε / 2 + ε / 2)) + (Yl - ε / 2) := by ring
      _ = (Xl + ε) + (Yl - ε / 2) := by rw [ENNReal.add_halves]
  exact ((ENNReal.add_lt_add_iff_right hc).mp k1).le

theorem gdc_eventually_mem {S : Type*} {P : S → ℝ≥0∞} {SN : ℕ → Set S} {Q : ℕ → S → ℝ≥0∞}
    (hA : ApproxDist P SN Q) (j : S) : ∀ᶠ N in atTop, j ∈ SN N := by
  have : j ∈ ⋃ N, SN N := hA.iUnion_eq ▸ Set.mem_univ j
  obtain ⟨N0, hN0⟩ := Set.mem_iUnion.mp this
  filter_upwards [eventually_ge_atTop N0] with N hN
  exact hA.mono hN hN0

theorem gdc_part {S : Type*} [Countable S] {P : S → ℝ≥0∞} {SN : ℕ → Set S}
    {Q : ℕ → S → ℝ≥0∞} (hA : ApproxDist P SN Q) (f g : S → ℕ → ℝ)
    (hfg : ∀ N, ∀ j ∈ SN N, |f j N| ≤ g j N) (fL gL : S → EReal)
    (hf : ∀ j, Tendsto (fun N => (f j N : EReal)) atTop (𝓝 (fL j)))
    (hg : ∀ j, Tendsto (fun N => (g j N : EReal)) atTop (𝓝 (gL j)))
    (hZ : Tendsto (fun N => ∑' j, (SN N).indicator (Q N) j * ENNReal.ofReal (g j N)) atTop
      (𝓝 (∑' j, P j * (gL j).toENNReal)))
    (hfin : ∑' j, P j * (gL j).toENNReal ≠ ⊤) :
    Tendsto (fun N => ∑' j, (SN N).indicator (Q N) j * ENNReal.ofReal (f j N)) atTop
      (𝓝 (∑' j, P j * (fL j).toENNReal)) := by
  set a : ℕ → S → ℝ≥0∞ := fun N j => (SN N).indicator (Q N) j with ha_def
  have hle : ∀ j, fL j ≤ gL j := fun j =>
    le_of_tendsto_of_tendsto (hf j) (hg j) ((gdc_eventually_mem hA j).mono fun N hN =>
      EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans (hfg N j hN)))
  have hleE : ∀ j, (fL j).toENNReal ≤ (gL j).toENNReal := fun j =>
    EReal.toENNReal_le_toENNReal (hle j)
  have hPtop : ∀ j, P j ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (by rw [hA.prob]; exact ENNReal.one_ne_top) (ENNReal.le_tsum j)
  have hgfin : ∀ j, P j ≠ 0 → (gL j).toENNReal ≠ ⊤ := by
    intro j hP hg
    apply hfin
    refine top_unique ?_
    calc (⊤ : ℝ≥0∞) = P j * (gL j).toENNReal := by rw [hg, ENNReal.mul_top hP]
      _ ≤ _ := ENNReal.le_tsum (f := fun j => P j * (gL j).toENNReal) j
  have ha_tend : ∀ j, Tendsto (fun N => a N j) atTop (𝓝 (P j)) := fun j =>
    (hA.tendsto j).congr' ((gdc_eventually_mem hA j).mono fun N hN => by
      simp [ha_def, Set.indicator_of_mem hN])
  have hof : ∀ (h : S → ℕ → ℝ) (hL : S → EReal),
      (∀ j, Tendsto (fun N => (h j N : EReal)) atTop (𝓝 (hL j))) →
      ∀ j, Tendsto (fun N => ENNReal.ofReal (h j N)) atTop (𝓝 (hL j).toENNReal) := by
    intro h hL hh j
    have := (EReal.continuous_toENNReal.tendsto _).comp (hh j)
    refine this.congr fun N => ?_
    simp [Function.comp]
  -- termwise Fatou bound
  have term : ∀ (c : ℕ → S → ℝ≥0∞) (cL : S → ℝ≥0∞), (∀ j, P j ≠ 0 → cL j ≠ ⊤) →
      (∀ j, P j ≠ 0 → Tendsto (fun N => c N j) atTop (𝓝 (cL j))) →
      ∑' j, P j * cL j ≤ liminf (fun N => ∑' j, a N j * c N j) atTop := by
    intro c cL hcL hc
    refine le_trans (ENNReal.tsum_le_tsum fun j => ?_)
      (liminf_tsum_ge (fun j N => a N j * c N j))
    by_cases hP : P j = 0
    · rw [hP, zero_mul]; exact bot_le
    · have := ENNReal.Tendsto.mul (ha_tend j) (Or.inr (hcL j hP)) (hc j hP) (Or.inr (hPtop j))
      rw [this.liminf_eq]
  have hsplit : ∀ N, (∑' j, a N j * ENNReal.ofReal (f j N)) +
      (∑' j, a N j * (ENNReal.ofReal (g j N) - ENNReal.ofReal (f j N))) =
      ∑' j, a N j * ENNReal.ofReal (g j N) := by
    intro N
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun j => ?_
    by_cases hj : j ∈ SN N
    · rw [← mul_add, add_tsub_cancel_of_le
        (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hfg N j hj)))]
    · simp [ha_def, Set.indicator_of_notMem hj]
  have hlsum : (∑' j, P j * (fL j).toENNReal) +
      (∑' j, P j * ((gL j).toENNReal - (fL j).toENNReal)) = ∑' j, P j * (gL j).toENNReal := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun j => by rw [← mul_add, add_tsub_cancel_of_le (hleE j)]
  refine gdc_squeeze hsplit hZ hfin ?_ ?_ hlsum
  · exact term _ _ (fun j hP => ne_top_of_le_ne_top (hgfin j hP) (hleE j))
      (fun j _ => hof f fL hf j)
  · refine term _ _ (fun j hP => ne_top_of_le_ne_top (hgfin j hP) tsub_le_self) fun j hP => ?_
    exact ENNReal.Tendsto.sub (hof g gL hg j) (hof f fL hf j) (Or.inl (hgfin j hP))

theorem gdc_ws {S : Type*} (c : S → ℝ≥0∞) (v : S → ℝ) :
    wsum c (fun j => (v j : EReal)) =
      ((∑' j, c j * ENNReal.ofReal (v j) : ℝ≥0∞) : EReal) -
        ((∑' j, c j * ENNReal.ofReal (-v j) : ℝ≥0∞) : EReal) := by
  unfold wsum
  congr 3

theorem gdc_sub_tendsto {X Y : ℕ → ℝ≥0∞} {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤)
    (hX : Tendsto X atTop (𝓝 x)) (hY : Tendsto Y atTop (𝓝 y)) :
    Tendsto (fun N => (X N : EReal) - (Y N : EReal)) atTop (𝓝 ((x : EReal) - (y : EReal))) := by
  have eX : ∀ᶠ N in atTop, X N ≠ ⊤ :=
    (hX.eventually (gt_mem_nhds (lt_top_iff_ne_top.mpr hx))).mono fun N h => h.ne
  have eY : ∀ᶠ N in atTop, Y N ≠ ⊤ :=
    (hY.eventually (gt_mem_nhds (lt_top_iff_ne_top.mpr hy))).mono fun N h => h.ne
  have hr := EReal.tendsto_coe.mpr (((ENNReal.tendsto_toReal hx).comp hX).sub
    ((ENNReal.tendsto_toReal hy).comp hY))
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal hx, EReal.coe_ennreal_toReal hy] at hr
  refine hr.congr' ?_
  filter_upwards [eX, eY] with N h1 h2
  simp only [Function.comp]
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal h1, EReal.coe_ennreal_toReal h2]

end SennottDP.Fatou

open SennottDP.Fatou in
theorem solution {S : Type*} [Countable S] {P : S → ℝ≥0∞}
    {SN : ℕ → Set S} {Q : ℕ → S → ℝ≥0∞} (hA : ApproxDist P SN Q)
    (u w : S → ℕ → ℝ) (hdom : ∀ N, ∀ j ∈ SN N, |u j N| ≤ w j N)
    (uL wL : S → EReal)
    (hu : ∀ j, Tendsto (fun N => (u j N : EReal)) atTop (𝓝 (uL j)))
    (hw : ∀ j, Tendsto (fun N => (w j N : EReal)) atTop (𝓝 (wL j)))
    (hsum : Tendsto (fun N => wsum ((SN N).indicator (Q N)) (fun j => (w j N : EReal))) atTop
      (𝓝 (wsum P wL)))
    (hfin : wsum P wL < ⊤) :
    Tendsto (fun N => wsum ((SN N).indicator (Q N)) (fun j => (u j N : EReal))) atTop
      (𝓝 (wsum P uL)) := by
  have hwnn : ∀ N, ∀ j ∈ SN N, 0 ≤ w j N := fun N j hj => (abs_nonneg _).trans (hdom N j hj)
  have hzero : ∀ N, ∑' j, (SN N).indicator (Q N) j * ENNReal.ofReal (-w j N) = 0 := by
    intro N
    refine ENNReal.tsum_eq_zero.mpr fun j => ?_
    by_cases hj : j ∈ SN N
    · rw [ENNReal.ofReal_of_nonpos (by linarith [hwnn N j hj]), mul_zero]
    · simp [Set.indicator_of_notMem hj]
  have hwL : ∀ j, 0 ≤ wL j := fun j =>
    ge_of_tendsto (hw j) ((gdc_eventually_mem hA j).mono fun N hN =>
      EReal.coe_nonneg.mpr (hwnn N j hN))
  have hzeroL : ∑' j, P j * (-wL j).toENNReal = 0 :=
    ENNReal.tsum_eq_zero.mpr fun j => by
      rw [EReal.toENNReal_of_nonpos (EReal.neg_le_zero.mpr (hwL j)), mul_zero]
  have hWL : wsum P wL = ((∑' j, P j * (wL j).toENNReal : ℝ≥0∞) : EReal) := by
    unfold wsum; rw [hzeroL]; simp
  have hZ : Tendsto (fun N => ∑' j, (SN N).indicator (Q N) j * ENNReal.ofReal (w j N)) atTop
      (𝓝 (∑' j, P j * (wL j).toENNReal)) := by
    rw [hWL] at hsum
    refine EReal.tendsto_coe_ennreal.mp (hsum.congr fun N => ?_)
    rw [gdc_ws, hzero]; simp
  have hfinE : ∑' j, P j * (wL j).toENNReal ≠ ⊤ := by
    rw [hWL] at hfin
    intro h; rw [h] at hfin; simp at hfin
  have hp := gdc_part hA u w hdom uL wL hu hw hZ hfinE
  have hm := gdc_part hA (fun j N => -u j N) w (fun N j hj => by rw [abs_neg]; exact hdom N j hj)
    (fun j => -uL j) wL (fun j => by
      have := (continuous_neg.tendsto (uL j)).comp (hu j)
      refine this.congr fun N => ?_
      simp [Function.comp]) hw hZ hfinE
  have hbound : ∀ (v : S → ℕ → ℝ) (vL : S → EReal), (∀ N, ∀ j ∈ SN N, v j N ≤ w j N) →
      Tendsto (fun N => ∑' j, (SN N).indicator (Q N) j * ENNReal.ofReal (v j N)) atTop
        (𝓝 (∑' j, P j * (vL j).toENNReal)) →
      ∑' j, P j * (vL j).toENNReal ≠ ⊤ := by
    intro v vL hvw hv
    refine ne_top_of_le_ne_top hfinE (le_of_tendsto_of_tendsto hv hZ (Eventually.of_forall
      fun N => ENNReal.tsum_le_tsum fun j => ?_))
    by_cases hj : j ∈ SN N
    · gcongr; exact hvw N j hj
    · simp [Set.indicator_of_notMem hj]
  have h1 := hbound u uL (fun N j hj => (le_abs_self _).trans (hdom N j hj)) hp
  have h2 := hbound (fun j N => -u j N) (fun j => -uL j)
    (fun N j hj => (neg_le_abs _).trans (hdom N j hj)) hm
  have := gdc_sub_tendsto h1 h2 hp hm
  refine (this.congr fun N => (gdc_ws _ _).symm).trans ?_
  unfold wsum
  exact le_rfl



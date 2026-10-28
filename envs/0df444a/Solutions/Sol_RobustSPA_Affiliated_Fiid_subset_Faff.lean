-- Prove2me | solution 1 for RobustSPA.Affiliated.Fiid_subset_Faff
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:10:30.688515+00:00
-- url     : https://prove2.me/submissions/5e44db7c-e188-4031-8a9c-65bb35121e10

import Mathlib
import Definitions.Def_RobustSPA_Affiliated_Setting

open MeasureTheory RobustSPA.IID RobustSPA.Affiliated
open scoped ENNReal

namespace RAffFKG

/-- The two-point inequality behind the four-functions theorem (real form). -/
lemma two_point_real {a1 a2 a3 a4 b1 b2 b3 b4 : ℝ} (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3)
    (h4 : 0 ≤ a4) (g1 : 0 ≤ b1) (g2 : 0 ≤ b2) (g3 : 0 ≤ b3) (g4 : 0 ≤ b4)
    (haa : a1 * a2 ≤ a3 * a4) (hbb : b1 * b2 ≤ b3 * b4) (hab : a1 * b2 ≤ b3 * a4)
    (hba : b1 * a2 ≤ b3 * a4) :
    a1 * b2 + b1 * a2 ≤ a3 * b4 + b3 * a4 := by
  have hc0 : 0 ≤ b3 * a4 := mul_nonneg g3 h4
  have hu : 0 ≤ a1 * b2 := mul_nonneg h1 g2
  have hw : 0 ≤ b1 * a2 := mul_nonneg g1 h2
  have hv : 0 ≤ a3 * b4 := mul_nonneg h3 g4
  rcases eq_or_lt_of_le hc0 with hc | hc
  · rw [← hc] at hab hba ⊢
    linarith
  · have key : (a1 * b2) * (b1 * a2) ≤ (a3 * b4) * (b3 * a4) := by
      calc (a1 * b2) * (b1 * a2) = (a1 * a2) * (b1 * b2) := by ring
        _ ≤ (a3 * a4) * (b3 * b4) :=
          mul_le_mul haa hbb (mul_nonneg g1 g2) (mul_nonneg h3 h4)
        _ = (a3 * b4) * (b3 * a4) := by ring
    have hprod : 0 ≤ (b3 * a4 - a1 * b2) * (b3 * a4 - b1 * a2) :=
      mul_nonneg (by linarith) (by linarith)
    by_contra hcon
    push_neg at hcon
    have : (b3 * a4) * (a3 * b4 + b3 * a4) < (b3 * a4) * (a1 * b2 + b1 * a2) :=
      mul_lt_mul_of_pos_left hcon hc
    nlinarith

/-- The two-point inequality for finite extended reals. -/
lemma two_point {a1 a2 a3 a4 b1 b2 b3 b4 : ℝ≥0∞} (h1 : a1 ≠ ⊤) (h2 : a2 ≠ ⊤) (h3 : a3 ≠ ⊤)
    (h4 : a4 ≠ ⊤) (g1 : b1 ≠ ⊤) (g2 : b2 ≠ ⊤) (g3 : b3 ≠ ⊤) (g4 : b4 ≠ ⊤)
    (haa : a1 * a2 ≤ a3 * a4) (hbb : b1 * b2 ≤ b3 * b4) (hab : a1 * b2 ≤ b3 * a4)
    (hba : b1 * a2 ≤ b3 * a4) :
    a1 * b2 + b1 * a2 ≤ a3 * b4 + b3 * a4 := by
  lift a1 to NNReal using h1
  lift a2 to NNReal using h2
  lift a3 to NNReal using h3
  lift a4 to NNReal using h4
  lift b1 to NNReal using g1
  lift b2 to NNReal using g2
  lift b3 to NNReal using g3
  lift b4 to NNReal using g4
  norm_cast at haa hbb hab hba ⊢
  have := two_point_real (a1 := (a1 : ℝ)) (a2 := a2) (a3 := a3) (a4 := a4) (b1 := b1) (b2 := b2)
    (b3 := b3) (b4 := b4) a1.2 a2.2 a3.2 a4.2 b1.2 b2.2 b3.2 b4.2
    (by exact_mod_cast haa) (by exact_mod_cast hbb) (by exact_mod_cast hab) (by exact_mod_cast hba)
  exact_mod_cast this

lemma ne_top_of_le_one {a : ℝ≥0∞} (h : a ≤ 1) : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h

/-- One-dimensional four-functions theorem for a probability measure on `ℝ`. -/
lemma fkg_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (f1 f2 f3 f4 : ℝ → ℝ≥0∞)
    (m1 : Measurable f1) (m2 : Measurable f2) (m3 : Measurable f3) (m4 : Measurable f4)
    (b1 : ∀ x, f1 x ≤ 1) (b2 : ∀ x, f2 x ≤ 1) (b3 : ∀ x, f3 x ≤ 1) (b4 : ∀ x, f4 x ≤ 1)
    (h : ∀ x y, f1 x * f2 y ≤ f3 (x ⊔ y) * f4 (x ⊓ y)) :
    (∫⁻ x, f1 x ∂ν) * (∫⁻ x, f2 x ∂ν) ≤ (∫⁻ x, f3 x ∂ν) * (∫⁻ x, f4 x ∂ν) := by
  have hpt : ∀ x y, f1 x * f2 y + f2 x * f1 y ≤ f3 x * f4 y + f4 x * f3 y := by
    intro x y
    rcases le_total x y with hxy | hxy
    · have haa := h x x
      have hbb := h y y
      have hab := h x y
      have hba := h y x
      simp only [sup_idem, inf_idem, sup_of_le_right hxy, inf_of_le_left hxy,
        sup_of_le_left hxy, inf_of_le_right hxy] at haa hbb hab hba
      have := two_point (ne_top_of_le_one (b1 x)) (ne_top_of_le_one (b2 x))
        (ne_top_of_le_one (b3 x)) (ne_top_of_le_one (b4 x)) (ne_top_of_le_one (b1 y))
        (ne_top_of_le_one (b2 y)) (ne_top_of_le_one (b3 y)) (ne_top_of_le_one (b4 y))
        haa hbb hab hba
      calc f1 x * f2 y + f2 x * f1 y = f1 x * f2 y + f1 y * f2 x := by rw [mul_comm (f2 x)]
        _ ≤ f3 x * f4 y + f3 y * f4 x := this
        _ = f3 x * f4 y + f4 x * f3 y := by rw [mul_comm (f3 y)]
    · have haa := h y y
      have hbb := h x x
      have hab := h y x
      have hba := h x y
      simp only [sup_idem, inf_idem, sup_of_le_right hxy, inf_of_le_left hxy,
        sup_of_le_left hxy, inf_of_le_right hxy] at haa hbb hab hba
      have := two_point (ne_top_of_le_one (b1 y)) (ne_top_of_le_one (b2 y))
        (ne_top_of_le_one (b3 y)) (ne_top_of_le_one (b4 y)) (ne_top_of_le_one (b1 x))
        (ne_top_of_le_one (b2 x)) (ne_top_of_le_one (b3 x)) (ne_top_of_le_one (b4 x))
        haa hbb hab hba
      calc f1 x * f2 y + f2 x * f1 y = f1 y * f2 x + f1 x * f2 y := by
            rw [add_comm, mul_comm (f2 x)]
        _ ≤ f3 y * f4 x + f3 x * f4 y := this
        _ = f3 x * f4 y + f4 x * f3 y := by rw [add_comm, mul_comm (f3 y)]
  have e1 : ∫⁻ z, (f1 z.1 * f2 z.2 + f2 z.1 * f1 z.2) ∂(ν.prod ν)
      = (∫⁻ x, f1 x ∂ν) * (∫⁻ x, f2 x ∂ν) + (∫⁻ x, f2 x ∂ν) * (∫⁻ x, f1 x ∂ν) := by
    rw [lintegral_add_left (by fun_prop), lintegral_prod_mul m1.aemeasurable m2.aemeasurable,
      lintegral_prod_mul m2.aemeasurable m1.aemeasurable]
  have e2 : ∫⁻ z, (f3 z.1 * f4 z.2 + f4 z.1 * f3 z.2) ∂(ν.prod ν)
      = (∫⁻ x, f3 x ∂ν) * (∫⁻ x, f4 x ∂ν) + (∫⁻ x, f4 x ∂ν) * (∫⁻ x, f3 x ∂ν) := by
    rw [lintegral_add_left (by fun_prop), lintegral_prod_mul m3.aemeasurable m4.aemeasurable,
      lintegral_prod_mul m4.aemeasurable m3.aemeasurable]
  have hmono := lintegral_mono (μ := ν.prod ν) (fun z => hpt z.1 z.2)
  rw [e1, e2, mul_comm (∫⁻ x, f2 x ∂ν), mul_comm (∫⁻ x, f4 x ∂ν), ← two_mul, ← two_mul] at hmono
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).mp hmono

lemma insertNth_sup {n : ℕ} (s t : ℝ) (x y : Fin n → ℝ) :
    (Fin.insertNth 0 s x : Fin (n + 1) → ℝ) ⊔ Fin.insertNth 0 t y = Fin.insertNth 0 (s ⊔ t) (x ⊔ y) := by
  ext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp

lemma insertNth_inf {n : ℕ} (s t : ℝ) (x y : Fin n → ℝ) :
    (Fin.insertNth 0 s x : Fin (n + 1) → ℝ) ⊓ Fin.insertNth 0 t y = Fin.insertNth 0 (s ⊓ t) (x ⊓ y) := by
  ext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp

/-- The four-functions (FKG/Harris) inequality for the product measure `νⁿ` on `ℝⁿ`. -/
theorem fkg_pi (ν : Measure ℝ) [IsProbabilityMeasure ν] : ∀ (n : ℕ)
    (f1 f2 f3 f4 : (Fin n → ℝ) → ℝ≥0∞),
    Measurable f1 → Measurable f2 → Measurable f3 → Measurable f4 →
    (∀ x, f1 x ≤ 1) → (∀ x, f2 x ≤ 1) → (∀ x, f3 x ≤ 1) → (∀ x, f4 x ≤ 1) →
    (∀ x y, f1 x * f2 y ≤ f3 (x ⊔ y) * f4 (x ⊓ y)) →
    (∫⁻ x, f1 x ∂(Measure.pi fun _ => ν)) * (∫⁻ x, f2 x ∂(Measure.pi fun _ => ν)) ≤
      (∫⁻ x, f3 x ∂(Measure.pi fun _ => ν)) * (∫⁻ x, f4 x ∂(Measure.pi fun _ => ν)) := by
  intro n
  induction n with
  | zero =>
    intro f1 f2 f3 f4 m1 m2 m3 m4 _ _ _ _ h
    rw [Measure.pi_of_empty (fun _ : Fin 0 => ν) isEmptyElim]
    rw [lintegral_dirac' _ m1, lintegral_dirac' _ m2, lintegral_dirac' _ m3, lintegral_dirac' _ m4]
    simpa using h (isEmptyElim : Fin 0 → ℝ) isEmptyElim
  | succ n ih =>
    intro f1 f2 f3 f4 m1 m2 m3 m4 b1 b2 b3 b4 h
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ => ν)
        (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    have hsymm : ∀ z : ℝ × (Fin n → ℝ), e.symm z = Fin.insertNth 0 z.1 z.2 := fun z => rfl
    -- reduce each integral to an iterated integral
    have hred : ∀ f : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable f →
        ∫⁻ x, f x ∂(Measure.pi fun _ => ν) =
          ∫⁻ t, ∫⁻ x, f (Fin.insertNth 0 t x) ∂(Measure.pi fun _ : Fin n => ν) ∂ν := by
      intro f hf
      rw [← (hmp.symm e).lintegral_comp_emb e.symm.measurableEmbedding f]
      rw [lintegral_prod (fun z => f (e.symm z)) (hf.comp e.symm.measurable).aemeasurable]
      rfl
    have hslice : ∀ f : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable f → ∀ t : ℝ,
        Measurable (fun x : Fin n → ℝ => f (Fin.insertNth 0 t x)) := by
      intro f hf t
      exact hf.comp (e.symm.measurable.comp measurable_prodMk_left)
    have hgm : ∀ f : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable f →
        Measurable (fun t => ∫⁻ x, f (Fin.insertNth 0 t x) ∂(Measure.pi fun _ : Fin n => ν)) := by
      intro f hf
      have : Measurable (fun z : ℝ × (Fin n → ℝ) => f (e.symm z)) := hf.comp e.symm.measurable
      exact this.lintegral_prod_right'
    have hgb : ∀ f : (Fin (n + 1) → ℝ) → ℝ≥0∞, (∀ x, f x ≤ 1) → ∀ t,
        ∫⁻ x, f (Fin.insertNth 0 t x) ∂(Measure.pi fun _ : Fin n => ν) ≤ 1 := by
      intro f hf t
      calc ∫⁻ x, f (Fin.insertNth 0 t x) ∂(Measure.pi fun _ : Fin n => ν)
          ≤ ∫⁻ _x, 1 ∂(Measure.pi fun _ : Fin n => ν) := lintegral_mono fun x => hf _
        _ = 1 := by simp
    rw [hred f1 m1, hred f2 m2, hred f3 m3, hred f4 m4]
    apply fkg_one ν _ _ _ _ (hgm f1 m1) (hgm f2 m2) (hgm f3 m3) (hgm f4 m4)
      (hgb f1 b1) (hgb f2 b2) (hgb f3 b3) (hgb f4 b4)
    intro s t
    apply ih _ _ _ _ (hslice f1 m1 s) (hslice f2 m2 t) (hslice f3 m3 (s ⊔ t))
      (hslice f4 m4 (s ⊓ t)) (fun x => b1 _) (fun x => b2 _) (fun x => b3 _) (fun x => b4 _)
    intro x y
    rw [← insertNth_sup, ← insertNth_inf]
    exact h _ _

end RAffFKG

open RAffFKG in
theorem solution (n : ℕ) : Fiid n ⊆ Faff n := by
  rintro μ ⟨G, hG, rfl⟩
  have hIcc : (G : Measure ℝ) (Set.Icc 0 1) = 1 :=
    (prob_compl_eq_zero_iff measurableSet_Icc).mp hG
  refine ⟨⟨⟨inferInstance, ?_⟩, ?_⟩, ?_⟩
  · -- support on the cube
    unfold cube
    rw [prob_compl_eq_zero_iff (MeasurableSet.univ_pi fun _ => measurableSet_Icc)]
    rw [Measure.pi_pi]
    simp [hIcc]
  · -- exchangeability
    intro σ
    have hm : Measurable (fun v : Fin n → ℝ => v ∘ σ) :=
      measurable_pi_iff.mpr fun i => measurable_pi_apply (σ i)
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have hpre : (fun v : Fin n → ℝ => v ∘ σ) ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun j => s (σ.symm j)) := by
      ext v
      simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
      constructor
      · intro hv j
        simpa using hv (σ.symm j)
      · intro hv i
        have := hv (σ i)
        rwa [Equiv.symm_apply_apply] at this
    rw [hpre, Measure.pi_pi]
    exact Equiv.prod_comp σ.symm (fun i => (G : Measure ℝ) (s i))
  · -- affiliation, from the four-functions inequality
    intro A B S hA hB hS hAu hBu hSl
    have key := fkg_pi (G : Measure ℝ) n ((A ∩ S).indicator 1) ((B ∩ S).indicator 1)
      ((A ∩ B ∩ S).indicator 1) (S.indicator 1)
      (measurable_one.indicator (hA.inter hS)) (measurable_one.indicator (hB.inter hS))
      (measurable_one.indicator ((hA.inter hB).inter hS)) (measurable_one.indicator hS)
      (fun x => Set.indicator_le_self' (fun _ _ => zero_le_one) x |>.trans (le_refl _))
      (fun x => Set.indicator_le_self' (fun _ _ => zero_le_one) x |>.trans (le_refl _))
      (fun x => Set.indicator_le_self' (fun _ _ => zero_le_one) x |>.trans (le_refl _))
      (fun x => Set.indicator_le_self' (fun _ _ => zero_le_one) x |>.trans (le_refl _)) ?_
    · rwa [lintegral_indicator_one (hA.inter hS), lintegral_indicator_one (hB.inter hS),
        lintegral_indicator_one ((hA.inter hB).inter hS), lintegral_indicator_one hS] at key
    · intro x y
      by_cases hx : x ∈ A ∩ S
      · by_cases hy : y ∈ B ∩ S
        · have hsl := hSl x hx.2 y hy.2
          have h1 : x ⊔ y ∈ A ∩ B ∩ S :=
            ⟨⟨hAu le_sup_left hx.1, hBu le_sup_right hy.1⟩, hsl.2⟩
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem h1,
            Set.indicator_of_mem hsl.1]
          simp
        · rw [Set.indicator_of_notMem hy]; simp
      · rw [Set.indicator_of_notMem hx]; simp

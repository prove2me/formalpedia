-- Prove2me | solution 1 for SethiChengSS.Infinite.appendix_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:19:04.309891+00:00
-- url     : https://prove2.me/submissions/2a97d6da-420f-418a-a7b2-ff6399ff2abf

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SethiChengSS.Infinite.Lip

open SethiChengSS.Infinite

variable {L : ℕ}

lemma snoc_lt' {β : Type*} {s : ℕ} (σ : Fin s → β) (j : β) (a : ℕ) (ha : a < s + 1) (h : a < s) :
    (Fin.snoc σ j : Fin (s + 1) → β) ⟨a, ha⟩ = σ ⟨a, h⟩ := by
  have : (⟨a, ha⟩ : Fin (s + 1)) = Fin.castSucc ⟨a, h⟩ := rfl
  rw [this, Fin.snoc_castSucc]

lemma stHist_snoc {k : ℕ} (σ : Fin (k + 1) → Fin L) (j : Fin L) (t : Fin k) :
    stHist (Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) t.castSucc = stHist σ t := by
  funext a
  simp only [stHist]
  exact snoc_lt' σ j _ _ (by have := a.2; have := t.2; simp [Fin.coe_castLE]; omega)

lemma dmHist_snoc {k : ℕ} (ξ : Fin k → ℝ) (z : ℝ) (t : Fin k) :
    dmHist (Fin.snoc ξ z : Fin (k + 1) → ℝ) t.castSucc = dmHist ξ t := by
  funext a
  simp only [dmHist]
  exact snoc_lt' ξ z _ _ (by have := a.2; have := t.2; simp [Fin.coe_castLE]; omega)

lemma delta_nonneg (z : ℝ) : 0 ≤ delta z := by
  unfold delta; split_ifs <;> norm_num

lemma orderCost_nonneg {D : Model L} (hD : Standing D) {k : ℕ} {j : Fin L} {u : ℝ}
    (hu : 0 ≤ u) : 0 ≤ orderCost D k j u :=
  add_nonneg (mul_nonneg (hD.2.2.2.2.2.2.2.1 k j) (delta_nonneg u))
    (mul_nonneg (hD.2.2.2.2.2.2.2.2.1 k j) hu)

lemma truncCost_snoc_ge {D : Model L} (hD : Standing D) {α : ℝ} (hα : 0 ≤ α) (n : ℕ)
    (U : Policy L) (hU : ∀ t σ ξ, 0 ≤ U t σ ξ) (x : ℝ) {k : ℕ}
    (σ : Fin (k + 1) → Fin L) (j : Fin L) (ξ : Fin k → ℝ) (z : ℝ) :
    truncCost D α n U x σ ξ ≤
      truncCost D α n U x (Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) (Fin.snoc ξ z : Fin (k + 1) → ℝ) := by
  unfold truncCost
  rw [Fin.sum_univ_castSucc]
  have e : ∀ t : Fin k,
      α ^ ((t.castSucc : Fin (k + 1)) : ℕ) *
        (orderCost D (n + (t.castSucc : Fin (k + 1)))
            ((Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) t.castSucc.castSucc)
            (U (t.castSucc : Fin (k + 1)) (stHist (Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) t.castSucc)
              (dmHist (Fin.snoc ξ z : Fin (k + 1) → ℝ) t.castSucc)) +
          D.f (n + (t.castSucc : Fin (k + 1)))
            ((Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) t.castSucc.castSucc)
            (surplus U x (t.castSucc : Fin (k + 1))
              (stHist (Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) t.castSucc)
              (dmHist (Fin.snoc ξ z : Fin (k + 1) → ℝ) t.castSucc))) =
      α ^ (t : ℕ) * (orderCost D (n + t) (σ t.castSucc) (U t (stHist σ t) (dmHist ξ t)) +
        D.f (n + t) (σ t.castSucc) (surplus U x t (stHist σ t) (dmHist ξ t))) := by
    intro t
    rw [stHist_snoc, dmHist_snoc, Fin.snoc_castSucc]
    rfl
  simp only [e]
  have hlast : 0 ≤ α ^ ((Fin.last k : Fin (k + 1)) : ℕ) *
      (orderCost D (n + (Fin.last k : Fin (k + 1)))
          ((Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) (Fin.last k).castSucc)
          (U (Fin.last k : Fin (k + 1)) (stHist (Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) (Fin.last k))
            (dmHist (Fin.snoc ξ z : Fin (k + 1) → ℝ) (Fin.last k))) +
        D.f (n + (Fin.last k : Fin (k + 1)))
          ((Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) (Fin.last k).castSucc)
          (surplus U x (Fin.last k : Fin (k + 1))
            (stHist (Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) (Fin.last k))
            (dmHist (Fin.snoc ξ z : Fin (k + 1) → ℝ) (Fin.last k)))) :=
    mul_nonneg (pow_nonneg hα _) (add_nonneg (orderCost_nonneg hD (hU _ _ _))
      (hD.2.2.2.2.2.2.2.2.2.2.1 _ _ _))
  linarith

lemma truncCost_nonneg {D : Model L} (hD : Standing D) {α : ℝ} (hα : 0 ≤ α) (n : ℕ)
    (U : Policy L) (hU : ∀ t σ ξ, 0 ≤ U t σ ξ) (x : ℝ) {k : ℕ}
    (σ : Fin (k + 1) → Fin L) (ξ : Fin k → ℝ) : 0 ≤ truncCost D α n U x σ ξ := by
  unfold truncCost
  exact Finset.sum_nonneg (fun t _ => mul_nonneg (pow_nonneg hα _)
    (add_nonneg (orderCost_nonneg hD (hU _ _ _)) (hD.2.2.2.2.2.2.2.2.2.2.1 _ _ _)))

lemma pathWeight_snoc (D : Model L) (n : ℕ) {t : ℕ} (σ : Fin (t + 1) → Fin L) (j : Fin L)
    (ξ : Fin t → ℝ) (z : ℝ) :
    pathWeight D n (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) (Fin.snoc ξ z : Fin (t + 1) → ℝ) =
      pathWeight D n σ ξ * (D.P (σ (Fin.last t)) j * D.φ (n + t) (σ (Fin.last t)) z) := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun k _ => ?_)
    have h1 : (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) k.castSucc.castSucc = σ k.castSucc :=
      Fin.snoc_castSucc ..
    have h2 : (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) k.castSucc.succ = σ k.succ := by
      show (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) ⟨k.1 + 1, by omega⟩ = σ ⟨k.1 + 1, by omega⟩
      exact snoc_lt' σ j _ _ _
    have h3 : (Fin.snoc ξ z : Fin (t + 1) → ℝ) k.castSucc = ξ k := Fin.snoc_castSucc ..
    simp only [h1, h2, h3, Fin.val_castSucc]
  · have h1 : (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) (Fin.last t).castSucc = σ (Fin.last t) :=
      Fin.snoc_castSucc ..
    have h2 : (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) (Fin.last t).succ = j := by
      show (Fin.snoc σ j : Fin (t + 1 + 1) → Fin L) (Fin.last (t + 1)) = j
      exact Fin.snoc_last ..
    have h3 : (Fin.snoc ξ z : Fin (t + 1) → ℝ) (Fin.last t) = z := Fin.snoc_last ..
    simp only [h1, h2, h3, Fin.val_last]

lemma sum_snoc {t : ℕ} (f : (Fin (t + 1 + 1) → Fin L) → ℝ≥0∞) :
    ∑ σ', f σ' = ∑ σ : Fin (t + 1) → Fin L, ∑ j : Fin L, f (Fin.snoc σ j) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (t + 1 + 1) => Fin L)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

lemma snoc_symm_eq (t : ℕ) (p : ℝ × (Fin t → ℝ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) (Fin.last t)).symm p =
      (Fin.snoc p.2 p.1 : Fin (t + 1) → ℝ) := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  rfl

lemma lintegral_snoc (t : ℕ) (G : (Fin (t + 1) → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ ξ', G ξ' = ∫⁻ ξ : Fin t → ℝ, ∫⁻ z : ℝ, G (Fin.snoc ξ z : Fin (t + 1) → ℝ) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) (Fin.last t)
  have h1 : ∫⁻ p, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) (Fin.last t)).symm p)
      ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin t => (volume : Measure ℝ))) =
      ∫⁻ ξ', G ξ' := (MeasurePreserving.symm _ hmp).lintegral_comp hG
  have h2 : ∫⁻ p, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => ℝ) (Fin.last t)).symm p)
      ∂((volume : Measure ℝ).prod (Measure.pi fun _ : Fin t => (volume : Measure ℝ))) =
      ∫⁻ ξ, ∫⁻ z, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => ℝ)
        (Fin.last t)).symm (z, ξ)) ∂(volume : Measure ℝ)
        ∂(Measure.pi fun _ : Fin t => (volume : Measure ℝ)) :=
    lintegral_prod_symm _ (hG.comp (MeasurableEquiv.measurable _)).aemeasurable
  rw [← h1, h2]
  simp only [snoc_symm_eq]
  rfl

lemma meas_init {m : ℕ} : Measurable (fun ξ : Fin (m + 1) → ℝ => Fin.init ξ) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

lemma meas_dmHist {m : ℕ} (t : Fin m) : Measurable (fun ξ : Fin m → ℝ => dmHist ξ t) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

lemma meas_surplus (U : Policy L) (x : ℝ) (hU : ∀ k σ, Measurable (U k σ)) :
    ∀ k, ∀ σ : Fin (k + 1) → Fin L, Measurable (surplus U x k σ) := by
  intro k
  induction k with
  | zero => intro σ; exact measurable_const
  | succ k ih =>
    intro σ
    exact (((ih _).comp meas_init).add ((hU k _).comp meas_init)).sub (measurable_pi_apply _)

lemma meas_delta : Measurable delta := by
  unfold delta
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

lemma meas_orderCost (D : Model L) (k : ℕ) (j : Fin L) : Measurable (orderCost D k j) := by
  unfold orderCost
  exact (measurable_const.mul meas_delta).add (measurable_const.mul measurable_id)

lemma continuous_of_convex_univ {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) : Continuous g := by
  have := hg.continuousOn_interior
  rw [interior_univ] at this
  exact continuousOn_univ.mp this

lemma meas_truncCost {D : Model L} (hD : Standing D) (α : ℝ) (n : ℕ) (U : Policy L) (x : ℝ)
    (hU : ∀ k σ, Measurable (U k σ)) {k : ℕ} (σ : Fin (k + 1) → Fin L) :
    Measurable (fun ξ => truncCost D α n U x σ ξ) := by
  unfold truncCost
  refine Finset.measurable_sum _ (fun t _ => ?_)
  exact measurable_const.mul (((meas_orderCost D _ _).comp ((hU _ _).comp (meas_dmHist t))).add
    ((continuous_of_convex_univ (hD.2.2.2.2.2.2.2.2.2.1 _ _)).measurable.comp
      ((meas_surplus U x hU _ _).comp (meas_dmHist t))))

lemma meas_pathWeight {D : Model L} (hD : Standing D) (n : ℕ) {t : ℕ}
    (σ : Fin (t + 1) → Fin L) : Measurable (fun ξ : Fin t → ℝ => pathWeight D n σ ξ) := by
  unfold pathWeight
  exact Finset.measurable_prod _ (fun k _ =>
    measurable_const.mul ((hD.2.2.1 _ _).comp (measurable_pi_apply _)))

lemma pathWeight_nonneg {D : Model L} (hD : Standing D) (n : ℕ) {t : ℕ}
    (σ : Fin (t + 1) → Fin L) (ξ : Fin t → ℝ) : 0 ≤ pathWeight D n σ ξ := by
  unfold pathWeight
  exact Finset.prod_nonneg (fun k _ => mul_nonneg (hD.1 _ _) (hD.2.2.2.1 _ _ _))


/-- Total weight of the paths started at `i`: it is a probability. -/
theorem weight_sum {D : Model L} (hD : Standing D) (n : ℕ) : ∀ k (i : Fin L),
    (∑ σ : Fin (k + 1) → Fin L, if σ 0 = i then
      ∫⁻ ξ : Fin k → ℝ, ENNReal.ofReal (pathWeight D n σ ξ) ∂(Measure.pi fun _ => volume)
      else 0) = 1 := by
  intro k
  induction k with
  | zero =>
    intro i
    rw [Fintype.sum_eq_single (fun _ => i)]
    · unfold pathWeight
      simp
    · intro σ hσ
      rw [if_neg]
      intro h
      apply hσ
      funext a
      obtain ⟨a, ha⟩ := a
      have : a = 0 := by omega
      subst this; exact h
  | succ k ih =>
    intro i
    rw [sum_snoc]
    rw [← ih i]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    have h0 : ∀ j : Fin L, (Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) 0 = σ 0 :=
      fun j => snoc_lt' σ j 0 (by omega) (by omega)
    simp only [h0]
    split_ifs with hσ
    swap
    · simp
    have hvol : (Measure.pi fun _ : Fin (k + 1) => (volume : Measure ℝ)) = volume := rfl
    have hvol' : (Measure.pi fun _ : Fin k => (volume : Measure ℝ)) = volume := rfl
    have hAm : Measurable (fun ξ : Fin k → ℝ => ENNReal.ofReal (pathWeight D n σ ξ)) :=
      ENNReal.measurable_ofReal.comp (meas_pathWeight hD n σ)
    have hstep : ∀ j : Fin L,
        ∫⁻ ξ' : Fin (k + 1) → ℝ, ENNReal.ofReal (pathWeight D n (Fin.snoc σ j) ξ')
          ∂(Measure.pi fun _ => volume) =
        ENNReal.ofReal (D.P (σ (Fin.last k)) j) *
          ∫⁻ ξ : Fin k → ℝ, ENNReal.ofReal (pathWeight D n σ ξ) ∂(Measure.pi fun _ => volume) := by
      intro j
      have hmj : Measurable (fun ξ' : Fin (k + 1) → ℝ =>
          ENNReal.ofReal (pathWeight D n (Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) ξ')) :=
        ENNReal.measurable_ofReal.comp (meas_pathWeight hD n _)
      rw [hvol, hvol', lintegral_snoc k _ hmj]
      rw [← lintegral_const_mul _ hAm]
      refine lintegral_congr (fun ξ => ?_)
      have m1 : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ (n + k) (σ (Fin.last k)) z)) :=
        ENNReal.measurable_ofReal.comp (hD.2.2.1 _ _)
      have m2 : Measurable (fun z : ℝ => ENNReal.ofReal (pathWeight D n σ ξ) *
          (ENNReal.ofReal (D.P (σ (Fin.last k)) j) *
            ENNReal.ofReal (D.φ (n + k) (σ (Fin.last k)) z))) := (m1.const_mul _).const_mul _
      have hw := pathWeight_nonneg hD n σ ξ
      have hP := hD.1 (σ (Fin.last k)) j
      have e : ∀ z, ENNReal.ofReal (pathWeight D n (Fin.snoc σ j : Fin (k + 1 + 1) → Fin L)
          (Fin.snoc ξ z : Fin (k + 1) → ℝ)) = ENNReal.ofReal (pathWeight D n σ ξ) *
          (ENNReal.ofReal (D.P (σ (Fin.last k)) j) *
            ENNReal.ofReal (D.φ (n + k) (σ (Fin.last k)) z)) := by
        intro z
        rw [pathWeight_snoc, ENNReal.ofReal_mul hw, ENNReal.ofReal_mul hP]
      simp only [e]
      rw [lintegral_const_mul _ (m1.const_mul _), lintegral_const_mul _ m1, hD.2.2.2.2.2.1]
      ring
    simp only [hstep]
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hD.1 _ j), hD.2.1,
      ENNReal.ofReal_one, one_mul]

lemma surplus_shift (U : Policy L) (x x' : ℝ) :
    ∀ t (σ : Fin (t + 1) → Fin L) (ξ : Fin t → ℝ),
      surplus U x' t σ ξ = surplus U x t σ ξ + (x' - x) := by
  intro t
  induction t with
  | zero => intro σ ξ; simp only [surplus]; ring
  | succ t ih => intro σ ξ; simp only [surplus, ih]; ring

/-- `f_k(i, ·)` is `C`-Lipschitz: it is convex with `0 ≤ f ≤ C(1 + |x|)`. -/
lemma f_lipschitz {D : Model L} (hD : Standing D) (k : ℕ) (j : Fin L) (a b : ℝ) :
    D.f k j b - D.f k j a ≤ D.C * |b - a| := by
  have hconv := hD.2.2.2.2.2.2.2.2.2.1 k j
  have hnn := hD.2.2.2.2.2.2.2.2.2.2.1 k j
  have hgr := hD.2.2.2.2.2.2.2.2.2.2.2.2.2 k j
  have hC := hD.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases lt_trichotomy a b with hab | hab | hab
  · -- slope to the right
    have hkey : ∀ t : ℝ, 0 < t → D.f k j b - D.f k j a ≤ (b - a) * (D.C * ((1 + |b|) / t + 1)) := by
      intro t ht
      have hs := hconv.slope_mono_adjacent (x := a) (y := b) (z := b + t) trivial trivial hab
        (by linarith)
      have e1 : b + t - b = t := by ring
      rw [e1] at hs
      have h1 : (D.f k j b - D.f k j a) ≤ (b - a) * ((D.f k j (b + t) - D.f k j b) / t) := by
        rw [div_le_iff₀ (by linarith)] at hs
        rw [mul_comm]; exact hs
      have h2 : (D.f k j (b + t) - D.f k j b) / t ≤ D.C * ((1 + |b|) / t + 1) := by
        rw [div_le_iff₀ ht]
        have := hgr (b + t); have := hnn b
        have : |b + t| ≤ |b| + t := by
          calc |b + t| ≤ |b| + |t| := abs_add_le _ _
            _ = |b| + t := by rw [abs_of_pos ht]
        have e : D.C * ((1 + |b|) / t + 1) * t = D.C * (1 + |b|) + D.C * t := by
          field_simp
        rw [e]; nlinarith
      calc D.f k j b - D.f k j a ≤ (b - a) * ((D.f k j (b + t) - D.f k j b) / t) := h1
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by linarith)
    have hlim : Tendsto (fun t : ℝ => (b - a) * (D.C * ((1 + |b|) / t + 1))) atTop
        (𝓝 ((b - a) * (D.C * (0 + 1)))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul
        ((tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds))
    have := ge_of_tendsto hlim (eventually_gt_atTop 0 |>.mono fun t ht => hkey t ht)
    rw [abs_of_pos (by linarith : 0 < b - a)]
    linarith
  · subst hab; simp
  · -- slope to the left
    have hkey : ∀ t : ℝ, 0 < t → D.f k j b - D.f k j a ≤ (a - b) * (D.C * ((1 + |b|) / t + 1)) := by
      intro t ht
      have hs := hconv.slope_mono_adjacent (x := b - t) (y := b) (z := a) trivial trivial
        (by linarith) hab
      have e1 : b - (b - t) = t := by ring
      rw [e1] at hs
      -- (f b - f (b - t)) / t ≤ (f a - f b) / (a - b)
      have h1 : D.f k j b - D.f k j a ≤ (a - b) * ((D.f k j (b - t) - D.f k j b) / t) := by
        have h3 : (D.f k j b - D.f k j (b - t)) / t * (a - b) ≤ D.f k j a - D.f k j b := by
          have := mul_le_mul_of_nonneg_right hs (by linarith : 0 ≤ a - b)
          rwa [div_mul_cancel₀ _ (by linarith : (a - b) ≠ 0)] at this
        have e : (a - b) * ((D.f k j (b - t) - D.f k j b) / t) =
            -((D.f k j b - D.f k j (b - t)) / t * (a - b)) := by ring
        rw [e]
        -- need: f b - f a ≤ -(slope * (a-b)) — use f a - f b ≥ slope*(a-b)? wrong sign: derive directly
        nlinarith [h3, hnn a, hnn b, hnn (b - t)]
      have h2 : (D.f k j (b - t) - D.f k j b) / t ≤ D.C * ((1 + |b|) / t + 1) := by
        rw [div_le_iff₀ ht]
        have := hgr (b - t); have := hnn b
        have : |b - t| ≤ |b| + t := by
          calc |b - t| ≤ |b| + |t| := abs_sub _ _
            _ = |b| + t := by rw [abs_of_pos ht]
        have e : D.C * ((1 + |b|) / t + 1) * t = D.C * (1 + |b|) + D.C * t := by
          field_simp
        rw [e]; nlinarith
      calc D.f k j b - D.f k j a ≤ (a - b) * ((D.f k j (b - t) - D.f k j b) / t) := h1
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by linarith)
    have hlim : Tendsto (fun t : ℝ => (a - b) * (D.C * ((1 + |b|) / t + 1))) atTop
        (𝓝 ((a - b) * (D.C * (0 + 1)))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul
        ((tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds))
    have := ge_of_tendsto hlim (eventually_gt_atTop 0 |>.mono fun t ht => hkey t ht)
    rw [abs_of_neg (by linarith : b - a < 0)]
    linarith

lemma geom_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    ∑ t : Fin k, α ^ (t : ℕ) ≤ 1 / (1 - α) := by
  rw [Fin.sum_univ_eq_sum_range (fun t => α ^ t), geom_sum_eq hα1.ne]
  have h1 : 0 < 1 - α := by linarith
  have e : (α ^ k - 1) / (α - 1) = (1 - α ^ k) / (1 - α) := by
    have hne1 : α - 1 ≠ 0 := by linarith
    have hne2 : 1 - α ≠ 0 := by linarith
    field_simp
    ring
  rw [e]
  apply div_le_div_of_nonneg_right _ h1.le
  have := pow_nonneg hα0.le k
  linarith

lemma truncCost_shift {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (U : Policy L) (x x' : ℝ) {k : ℕ} (σ : Fin (k + 1) → Fin L) (ξ : Fin k → ℝ) :
    truncCost D α n U x' σ ξ ≤ truncCost D α n U x σ ξ + D.C * |x' - x| / (1 - α) := by
  have hC := hD.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold truncCost
  have hterm : ∀ t : Fin k,
      α ^ (t : ℕ) * (orderCost D (n + t) (σ t.castSucc) (U t (stHist σ t) (dmHist ξ t)) +
        D.f (n + t) (σ t.castSucc) (surplus U x' t (stHist σ t) (dmHist ξ t))) ≤
      α ^ (t : ℕ) * (orderCost D (n + t) (σ t.castSucc) (U t (stHist σ t) (dmHist ξ t)) +
        D.f (n + t) (σ t.castSucc) (surplus U x t (stHist σ t) (dmHist ξ t))) +
      α ^ (t : ℕ) * (D.C * |x' - x|) := by
    intro t
    rw [surplus_shift U x x']
    have := f_lipschitz hD (n + t) (σ t.castSucc) (surplus U x t (stHist σ t) (dmHist ξ t))
      (surplus U x t (stHist σ t) (dmHist ξ t) + (x' - x))
    have e : surplus U x t (stHist σ t) (dmHist ξ t) + (x' - x) -
        surplus U x t (stHist σ t) (dmHist ξ t) = x' - x := by ring
    rw [e] at this
    have hp := pow_nonneg hα0.le (t : ℕ)
    nlinarith
  calc _ ≤ ∑ t : Fin k, (α ^ (t : ℕ) * (orderCost D (n + t) (σ t.castSucc)
          (U t (stHist σ t) (dmHist ξ t)) +
          D.f (n + t) (σ t.castSucc) (surplus U x t (stHist σ t) (dmHist ξ t))) +
        α ^ (t : ℕ) * (D.C * |x' - x|)) := Finset.sum_le_sum (fun t _ => hterm t)
    _ = _ + (∑ t : Fin k, α ^ (t : ℕ)) * (D.C * |x' - x|) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ _ := by
        have hg := geom_le hα0 hα1 k
        have : 0 ≤ D.C * |x' - x| := by positivity
        have h2 := mul_le_mul_of_nonneg_right hg this
        have e : 1 / (1 - α) * (D.C * |x' - x|) = D.C * |x' - x| / (1 - α) := by ring
        linarith

theorem Jtrunc_shift {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x x' : ℝ) (U : Policy L) :
    Jtrunc D α n k i x' U ≤
      Jtrunc D α n k i x U + ENNReal.ofReal (D.C * |x' - x| / (1 - α)) := by
  set B := D.C * |x' - x| / (1 - α)
  unfold Jtrunc
  calc _ ≤ ∑ σ : Fin (k + 1) → Fin L, ((if σ 0 = i then
        ∫⁻ ξ : Fin k → ℝ, ENNReal.ofReal (pathWeight D n σ ξ) *
          ENNReal.ofReal (truncCost D α n U x σ ξ) ∂(Measure.pi fun _ => volume) else 0) +
        ENNReal.ofReal B * (if σ 0 = i then
          ∫⁻ ξ : Fin k → ℝ, ENNReal.ofReal (pathWeight D n σ ξ) ∂(Measure.pi fun _ => volume)
          else 0)) := by
        refine Finset.sum_le_sum (fun σ _ => ?_)
        split_ifs with hσ
        · have hmw : Measurable (fun ξ : Fin k → ℝ => ENNReal.ofReal (pathWeight D n σ ξ)) :=
            ENNReal.measurable_ofReal.comp (meas_pathWeight hD n σ)
          rw [← lintegral_const_mul _ hmw, ← lintegral_add_right _ (hmw.const_mul _)]
          refine lintegral_mono (fun ξ => ?_)
          have h1 := ENNReal.ofReal_le_ofReal (truncCost_shift hD hα0 hα1 n U x x' σ ξ)
          have h2 := ENNReal.ofReal_add_le (p := truncCost D α n U x σ ξ) (q := B)
          calc ENNReal.ofReal (pathWeight D n σ ξ) * ENNReal.ofReal (truncCost D α n U x' σ ξ)
              ≤ ENNReal.ofReal (pathWeight D n σ ξ) *
                  (ENNReal.ofReal (truncCost D α n U x σ ξ) + ENNReal.ofReal B) := by
                gcongr; exact h1.trans h2
            _ = _ := by ring
        · simp
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, weight_sum hD n k i, mul_one]

lemma real_of_two (a b : ℝ≥0∞) (c : ℝ) (hc : 0 ≤ c) (h1 : a ≤ b + ENNReal.ofReal c)
    (h2 : b ≤ a + ENNReal.ofReal c) : |a.toReal - b.toReal| ≤ c := by
  by_cases ha : a = ⊤
  · have hb : b = ⊤ := by
      rw [ha] at h1
      by_contra hb
      exact absurd (top_le_iff.1 h1) (ENNReal.add_ne_top.2 ⟨hb, ENNReal.ofReal_ne_top⟩)
    simp [ha, hb, hc]
  · have hb : b ≠ ⊤ := by
      intro hb; rw [hb] at h2
      exact absurd (top_le_iff.1 h2) (ENNReal.add_ne_top.2 ⟨ha, ENNReal.ofReal_ne_top⟩)
    have e1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hb, ENNReal.ofReal_ne_top⟩) h1
    have e2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ha, ENNReal.ofReal_ne_top⟩) h2
    rw [ENNReal.toReal_add hb ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc] at e1
    rw [ENNReal.toReal_add ha ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc] at e2
    rw [abs_le]; constructor <;> linarith

theorem vTrunc_shift {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n k : ℕ) (i : Fin L) (x x' : ℝ) :
    vTrunc D α n k i x' ≤ vTrunc D α n k i x + ENNReal.ofReal (D.C * |x' - x| / (1 - α)) := by
  unfold vTrunc
  calc _ ≤ ⨅ (U : Policy L) (_ : Admissible U),
        (Jtrunc D α n k i x U + ENNReal.ofReal (D.C * |x' - x| / (1 - α))) :=
        iInf₂_mono fun U _ => Jtrunc_shift hD hα0 hα1 n k i x x' U
    _ = _ := by simp only [ENNReal.iInf_add]

theorem vLim_shift {D : Model L} (hD : Standing D) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (n : ℕ) (i : Fin L) (x x' : ℝ) :
    vLim D α n i x' ≤ vLim D α n i x + ENNReal.ofReal (D.C * |x' - x| / (1 - α)) := by
  unfold vLim
  calc _ ≤ ⨆ k : ℕ, (vTrunc D α n k i x + ENNReal.ofReal (D.C * |x' - x| / (1 - α))) :=
        iSup_mono fun k => vTrunc_shift hD hα0 hα1 n k i x x'
    _ = _ := by rw [ENNReal.iSup_add]

end SethiChengSS.Infinite.Lip

open SethiChengSS.Infinite SethiChengSS.Infinite.Lip

theorem solution {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (hα0 : 0 < α)
    (hα1 : α < 1) :
    (∀ n k i x x', |(vTrunc D α n k i x').toReal - (vTrunc D α n k i x).toReal| ≤
      D.C * |x' - x| / (1 - α)) ∧
    (∀ n i x x', |(vLim D α n i x').toReal - (vLim D α n i x).toReal| ≤
      D.C * |x' - x| / (1 - α)) := by
  have hC := hD.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc : ∀ x x' : ℝ, 0 ≤ D.C * |x' - x| / (1 - α) := fun x x' =>
    div_nonneg (mul_nonneg hC.le (abs_nonneg _)) (by linarith)
  refine ⟨fun n k i x x' => ?_, fun n i x x' => ?_⟩
  · refine real_of_two _ _ _ (hc x x') (vTrunc_shift hD hα0 hα1 n k i x x') ?_
    have := vTrunc_shift hD hα0 hα1 n k i x' x
    rwa [abs_sub_comm x x'] at this
  · refine real_of_two _ _ _ (hc x x') (vLim_shift hD hα0 hα1 n i x x') ?_
    have := vLim_shift hD hα0 hα1 n i x' x
    rwa [abs_sub_comm x x'] at this

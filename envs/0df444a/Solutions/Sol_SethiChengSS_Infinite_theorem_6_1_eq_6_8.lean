-- Prove2me | solution 1 for SethiChengSS.Infinite.theorem_6_1_eq_6_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:15:55.265195+00:00
-- url     : https://prove2.me/submissions/019172f1-1b27-4578-827c-5eb35aae69ce

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SethiChengSS.Infinite.Mono68

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

theorem Jtrunc_mono {D : Model L} (hD : Standing D) {α : ℝ} (hα : 0 ≤ α) (n k : ℕ) (i : Fin L)
    (x : ℝ) (U : Policy L) (hU : Admissible U) :
    Jtrunc D α n k i x U ≤ Jtrunc D α n (k + 1) i x U := by
  obtain ⟨hU0, hUm⟩ := hU
  unfold Jtrunc
  rw [sum_snoc]
  refine Finset.sum_le_sum (fun σ _ => ?_)
  have h0 : ∀ j : Fin L, (Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) 0 = σ 0 :=
    fun j => snoc_lt' σ j 0 (by omega) (by omega)
  simp only [h0]
  split_ifs with hσ
  swap
  · simp
  -- the `k`-period integrand
  set A : (Fin k → ℝ) → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal (pathWeight D n σ ξ) * ENNReal.ofReal (truncCost D α n U x σ ξ) with hA
  have hAm : Measurable A :=
    (ENNReal.measurable_ofReal.comp (meas_pathWeight hD n σ)).mul
      (ENNReal.measurable_ofReal.comp (meas_truncCost hD α n U x hUm σ))
  have hstep : ∀ j : Fin L,
      ∫⁻ ξ' : Fin (k + 1) → ℝ, ENNReal.ofReal (pathWeight D n (Fin.snoc σ j) ξ') *
          ENNReal.ofReal (truncCost D α n U x (Fin.snoc σ j) ξ') ∂(Measure.pi fun _ => volume) ≥
        ENNReal.ofReal (D.P (σ (Fin.last k)) j) * ∫⁻ ξ : Fin k → ℝ, A ξ ∂(Measure.pi fun _ => volume) := by
    intro j
    have hGm : Measurable (fun ξ' : Fin (k + 1) → ℝ =>
        ENNReal.ofReal (pathWeight D n (Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) ξ') *
          ENNReal.ofReal (truncCost D α n U x (Fin.snoc σ j : Fin (k + 1 + 1) → Fin L) ξ')) :=
      (ENNReal.measurable_ofReal.comp (meas_pathWeight hD n _)).mul
        (ENNReal.measurable_ofReal.comp (meas_truncCost hD α n U x hUm _))
    have hvol : (Measure.pi fun _ : Fin (k + 1) => (volume : Measure ℝ)) = volume := rfl
    have hvol' : (Measure.pi fun _ : Fin k => (volume : Measure ℝ)) = volume := rfl
    rw [hvol, hvol', lintegral_snoc k _ hGm]
    calc ENNReal.ofReal (D.P (σ (Fin.last k)) j) * ∫⁻ ξ : Fin k → ℝ, A ξ
        = ∫⁻ ξ : Fin k → ℝ, ∫⁻ z : ℝ, A ξ * (ENNReal.ofReal (D.P (σ (Fin.last k)) j) *
            ENNReal.ofReal (D.φ (n + k) (σ (Fin.last k)) z)) := by
          rw [← lintegral_const_mul _ hAm]
          refine lintegral_congr (fun ξ => ?_)
          have m1 : Measurable (fun z : ℝ => ENNReal.ofReal (D.φ (n + k) (σ (Fin.last k)) z)) :=
            ENNReal.measurable_ofReal.comp (hD.2.2.1 _ _)
          have m2 : Measurable (fun z : ℝ => ENNReal.ofReal (D.P (σ (Fin.last k)) j) *
              ENNReal.ofReal (D.φ (n + k) (σ (Fin.last k)) z)) := m1.const_mul _
          rw [lintegral_const_mul (A ξ) m2, lintegral_const_mul _ m1, hD.2.2.2.2.2.1]
          ring
      _ ≤ _ := by
          refine lintegral_mono (fun ξ => lintegral_mono (fun z => ?_))
          rw [pathWeight_snoc]
          have hw := pathWeight_nonneg hD n σ ξ
          have hP := hD.1 (σ (Fin.last k)) j
          have hφ := hD.2.2.2.1 (n + k) (σ (Fin.last k)) z
          simp only [hA]
          rw [ENNReal.ofReal_mul hw, ENNReal.ofReal_mul hP]
          have hc := ENNReal.ofReal_le_ofReal
            (truncCost_snoc_ge hD hα n U hU0 x σ j ξ z)
          calc ENNReal.ofReal (pathWeight D n σ ξ) * ENNReal.ofReal (truncCost D α n U x σ ξ) *
                (ENNReal.ofReal (D.P (σ (Fin.last k)) j) *
                  ENNReal.ofReal (D.φ (n + k) (σ (Fin.last k)) z))
              = ENNReal.ofReal (pathWeight D n σ ξ) * (ENNReal.ofReal (D.P (σ (Fin.last k)) j) *
                  ENNReal.ofReal (D.φ (n + k) (σ (Fin.last k)) z)) *
                  ENNReal.ofReal (truncCost D α n U x σ ξ) := by ring
            _ ≤ _ := by gcongr
  calc ∫⁻ ξ : Fin k → ℝ, A ξ ∂(Measure.pi fun _ => volume)
      = (∑ j : Fin L, ENNReal.ofReal (D.P (σ (Fin.last k)) j)) *
          ∫⁻ ξ : Fin k → ℝ, A ξ ∂(Measure.pi fun _ => volume) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hD.1 _ j), hD.2.1, ENNReal.ofReal_one,
          one_mul]
    _ = ∑ j : Fin L, ENNReal.ofReal (D.P (σ (Fin.last k)) j) *
          ∫⁻ ξ : Fin k → ℝ, A ξ ∂(Measure.pi fun _ => volume) := Finset.sum_mul ..
    _ ≤ _ := Finset.sum_le_sum (fun j _ => hstep j)

lemma zero_adm : Admissible (zeroPolicy : Policy L) :=
  ⟨fun _ _ _ => le_rfl, fun _ _ => measurable_const⟩

lemma Jtrunc_zero (D : Model L) (α : ℝ) (n : ℕ) (i : Fin L) (x : ℝ) (U : Policy L) :
    Jtrunc D α n 0 i x U = 0 := by
  unfold Jtrunc truncCost
  simp

end SethiChengSS.Infinite.Mono68

open SethiChengSS.Infinite SethiChengSS.Infinite.Mono68

theorem solution {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (hα0 : 0 < α)
    (hα1 : α < 1) :
    (∀ n i x, vTrunc D α n 0 i x = 0) ∧
    (∀ n k i x, vTrunc D α n k i x ≤ vTrunc D α n (k + 1) i x) ∧
    (∀ n k i x, vTrunc D α n k i x ≤ w D α n i x) := by
  refine ⟨fun n i x => ?_, fun n k i x => ?_, fun n k i x => ?_⟩
  · apply le_antisymm _ (by simp)
    calc vTrunc D α n 0 i x ≤ Jtrunc D α n 0 i x zeroPolicy :=
          iInf₂_le (f := fun U (_ : Admissible U) => Jtrunc D α n 0 i x U) _ zero_adm
      _ = 0 := Jtrunc_zero D α n i x _
  · exact iInf₂_mono fun U hU => Jtrunc_mono hD hα0.le n k i x U hU
  · calc vTrunc D α n k i x ≤ Jtrunc D α n k i x zeroPolicy :=
          iInf₂_le (f := fun U (_ : Admissible U) => Jtrunc D α n k i x U) _ zero_adm
      _ ≤ Jinf D α n i x zeroPolicy := le_iSup (fun k => Jtrunc D α n k i x zeroPolicy) k

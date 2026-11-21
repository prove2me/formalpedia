-- Prove2me | solution 1 for OptimalAgnosticPAC.Learner.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:42:41.041173+00:00
-- url     : https://prove2.me/submissions/144d7df4-03e3-4c1c-a64d-3b417efb9085

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Score
import Definitions.Def_HighDimProb_Chaining_VcDim
import Theorems.Thm_OptimalAgnosticPAC_Learner_theorem_3
import Theorems.Thm_OptimalAgnosticPAC_Learner_lemma_3_3
import Theorems.Thm_OptimalAgnosticPAC_Learner_eq_13_symmetrized_loo

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.T3
open OptimalAgnosticPAC.Learner

theorem loss_eq (a : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1) (y : Bool) :
    loss a y = (1 - sgn y * a) / 2 := by
  obtain ⟨h1, h2⟩ := ha
  unfold loss sgn
  cases y
  · simp only [Bool.false_eq_true, if_false]
    rw [abs_of_nonneg (by linarith)]; ring
  · simp only [if_true]
    rw [abs_of_nonpos (by linarith)]; ring

theorem measurable_loss {X : Type} [MeasurableSpace X] (g : X → ℝ) (hg : Measurable g) :
    Measurable (fun z : X × Bool => loss (g z.1) z.2) := by
  unfold loss
  have h1 : Measurable (fun z : X × Bool => sgn z.2) :=
    (measurable_from_top (f := sgn)).comp measurable_snd
  exact ((((hg.comp measurable_fst).sub h1).abs).div_const 2)

end OptimalAgnosticPAC.Dev.T3
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.T1

theorem split_mp {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P] (a m : ℕ) :
    MeasurePreserving
      (fun (S : Fin (a + m) → Z) =>
        ((fun i : Fin a => S (Fin.castAdd m i)), (fun j : Fin m => S (Fin.natAdd a j))))
      (Measure.pi fun _ => P)
      ((Measure.pi fun _ : Fin a => P).prod (Measure.pi fun _ : Fin m => P)) := by
  have h1 := measurePreserving_piCongrLeft (α := fun _ : Fin (a + m) => Z) (fun _ => P) finSumFinEquiv
  have h2 := (measurePreserving_sumPiEquivProdPi (X := fun _ : Fin a ⊕ Fin m => Z) (fun _ => P))
  have h3 := h2.comp h1.symm
  convert h3 using 1
  funext S
  simp only [Function.comp]
  refine Prod.ext ?_ ?_
  · funext i
    simp [MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft, Equiv.sumPiEquivProdPi,
      Equiv.piCongrLeft]
  · funext j
    simp [MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft, Equiv.sumPiEquivProdPi,
      Equiv.piCongrLeft]


theorem fst_le {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P] (a m : ℕ)
    (E : Set (Fin a → Z)) :
    Measure.pi (fun _ : Fin (a + m) => P) ((fun (S : Fin (a + m) → Z) (i : Fin a) => S (Fin.castAdd m i)) ⁻¹' E) ≤
      Measure.pi (fun _ : Fin a => P) E := by
  obtain ⟨C, hCsub, hCmeas, hCeq⟩ := exists_measurable_superset (Measure.pi (fun _ : Fin a => P)) E
  have hmp := split_mp P a m
  calc _ ≤ Measure.pi (fun _ : Fin (a + m) => P) ((fun (S : Fin (a + m) → Z) (i : Fin a) => S (Fin.castAdd m i)) ⁻¹' C) :=
        measure_mono (Set.preimage_mono hCsub)
    _ = Measure.pi (fun _ : Fin (a + m) => P) ((fun (S : Fin (a + m) → Z) =>
        ((fun i : Fin a => S (Fin.castAdd m i)), (fun j : Fin m => S (Fin.natAdd a j)))) ⁻¹' (C ×ˢ Set.univ)) := by
        congr 1; ext S; simp
    _ = _ := by
        rw [hmp.measure_preimage (hCmeas.prod MeasurableSet.univ).nullMeasurableSet, Measure.prod_prod]
        simp [hCeq]

theorem fubini_split {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P] (a m : ℕ)
    (F : Set ((Fin a → Z) × (Fin m → Z))) (hF : MeasurableSet F) :
    Measure.pi (fun _ : Fin (a + m) => P) ((fun (S : Fin (a + m) → Z) =>
        ((fun i : Fin a => S (Fin.castAdd m i)), (fun j : Fin m => S (Fin.natAdd a j)))) ⁻¹' F) =
      ∫⁻ w, Measure.pi (fun _ : Fin m => P) (Prod.mk w ⁻¹' F) ∂(Measure.pi (fun _ : Fin a => P)) := by
  rw [(split_mp P a m).measure_preimage hF.nullMeasurableSet, Measure.prod_apply hF]

end OptimalAgnosticPAC.Dev.T1
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.T1
open OptimalAgnosticPAC.Learner

variable {X : Type} [MeasurableSpace X]

noncomputable def cand (k : ℕ) (p : X → ℝ) (Sv : Fin k → X × Bool) (i : Fin (k + 1)) : X → Bool :=
  if h : i.val < k then fun x => decide (p (Sv ⟨i.val, h⟩).1 ≤ p x) else fun _ => false

noncomputable def errVec (k : ℕ) (p : X → ℝ) (Sv : Fin k → X × Bool) : Fin (k + 1) → ℕ :=
  fun i => errCount (cand k p Sv i) Sv

noncomputable def argminIdx {k : ℕ} (e : Fin (k + 1) → ℕ) : Fin (k + 1) :=
  if h : (Finset.univ.filter (fun j : Fin (k + 1) => ∀ i, e j ≤ e i)).Nonempty then
    (Finset.univ.filter (fun j : Fin (k + 1) => ∀ i, e j ≤ e i)).min' h else 0

theorem argminIdx_spec {k : ℕ} (e : Fin (k + 1) → ℕ) (i : Fin (k + 1)) : e (argminIdx e) ≤ e i := by
  have hne : (Finset.univ.filter (fun j : Fin (k + 1) => ∀ i, e j ≤ e i)).Nonempty := by
    obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
    exact ⟨j, by simpa using hj⟩
  unfold argminIdx
  rw [dif_pos hne]
  have := Finset.min'_mem _ hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this i

noncomputable def sel (k : ℕ) (p : X → ℝ) (Sv : Fin k → X × Bool) : X → Bool :=
  cand k p Sv (argminIdx (errVec k p Sv))

theorem errCount_congr {k : ℕ} (h h' : X → Bool) (S : Fin k → X × Bool)
    (hh : ∀ j, h (S j).1 = h' (S j).1) : errCount h S = errCount h' S := by
  unfold errCount
  congr 1
  refine Finset.filter_congr (fun j _ => ?_)
  rw [hh j]

theorem cand_mem {k : ℕ} (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc (-1 : ℝ) 1) (Sv : Fin k → X × Bool)
    (i : Fin (k + 1)) : cand k p Sv i ∈ thresholdClass p := by
  unfold cand
  split_ifs with h
  · exact Or.inl ⟨p (Sv ⟨i.val, h⟩).1, hp _, rfl⟩
  · exact Or.inr rfl

theorem exists_cand_le {k : ℕ} (p : X → ℝ) (Sv : Fin k → X × Bool) (h : X → Bool)
    (hh : h ∈ thresholdClass p) : ∃ i, errCount (cand k p Sv i) Sv ≤ errCount h Sv := by
  rcases hh with ⟨u, hu, rfl⟩ | rfl
  · by_cases hex : ∃ i : Fin k, u ≤ p (Sv i).1
    · obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun i : Fin k => u ≤ p (Sv i).1))
        (fun i => p (Sv i).1) (by obtain ⟨i, hi⟩ := hex; exact ⟨i, by simpa using hi⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi0 hmin
      refine ⟨⟨i0.val, by omega⟩, le_of_eq (errCount_congr _ _ _ (fun j => ?_))⟩
      simp only [cand, dif_pos i0.isLt]
      by_cases hj : u ≤ p (Sv j).1
      · have := hmin j hj
        simp [hj, this]
      · have : ¬ p (Sv i0).1 ≤ p (Sv j).1 := fun hc => hj (le_trans hi0 hc)
        simp [hj, this]
    · push_neg at hex
      refine ⟨⟨k, by omega⟩, le_of_eq (errCount_congr _ _ _ (fun j => ?_))⟩
      simp [cand, not_le.mpr (hex j)]
  · exact ⟨⟨k, by omega⟩, le_of_eq (errCount_congr _ _ _ (fun j => by simp [cand]))⟩

theorem sel_isERM {k : ℕ} (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc (-1 : ℝ) 1) :
    IsERM (thresholdClass p) (sel k p) := by
  intro Sv
  refine ⟨cand_mem p hp Sv _, fun h hh => ?_⟩
  obtain ⟨i, hi⟩ := exists_cand_le p Sv h hh
  exact le_trans (argminIdx_spec (errVec k p Sv) i) hi

theorem measurable_sel {W : Type} [MeasurableSpace W] (k : ℕ) (pp : W → X → ℝ)
    (hpp : Measurable (fun z : W × X => pp z.1 z.2)) (sv : W → Fin k → X × Bool) (hsv : Measurable sv) :
    Measurable (fun z : W × X => sel k (pp z.1) (sv z.1) z.2) := by
  have hsvj : ∀ j : Fin k, Measurable (fun w => (sv w j)) := fun j => (measurable_pi_apply j).comp hsv
  have hcand : ∀ i : Fin (k + 1), Measurable (fun z : W × X => cand k (pp z.1) (sv z.1) i z.2) := by
    intro i
    unfold cand
    by_cases h : i.val < k
    · simp only [dif_pos h]
      apply measurable_to_bool
      have h1 : Measurable (fun z : W × X => pp z.1 (sv z.1 ⟨i.val, h⟩).1) :=
        hpp.comp (measurable_fst.prodMk (measurable_fst.comp ((hsvj _).comp measurable_fst)))
      have : (fun z : W × X => decide (pp z.1 (sv z.1 ⟨i.val, h⟩).1 ≤ pp z.1 z.2)) ⁻¹' {true} =
          {z | pp z.1 (sv z.1 ⟨i.val, h⟩).1 ≤ pp z.1 z.2} := by ext z; simp
      rw [this]
      exact measurableSet_le h1 hpp
    · simp only [dif_neg h]
      exact measurable_const
  have herr : Measurable (fun w : W => errVec k (pp w) (sv w)) := by
    rw [measurable_pi_iff]
    intro i
    unfold errVec errCount
    have : ∀ w, (Finset.univ.filter (fun j : Fin k => cand k (pp w) (sv w) i (sv w j).1 ≠ (sv w j).2)).card =
        ∑ j : Fin k, if cand k (pp w) (sv w) i (sv w j).1 ≠ (sv w j).2 then 1 else 0 := by
      intro w; rw [Finset.card_filter]
    simp_rw [this]
    refine Finset.measurable_sum _ (fun j _ => ?_)
    have h1 : Measurable (fun w => cand k (pp w) (sv w) i (sv w j).1) :=
      (hcand i).comp (measurable_id.prodMk (measurable_fst.comp (hsvj j)))
    have h2 : Measurable (fun w => (sv w j).2) := measurable_snd.comp (hsvj j)
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (MeasurableSet.of_discrete (s := {q : Bool × Bool | q.1 ≠ q.2})).preimage (h1.prodMk h2)
  have hidx : Measurable (fun w : W => argminIdx (errVec k (pp w) (sv w))) :=
    (measurable_of_countable (argminIdx (k := k))).comp herr
  have hF : Measurable (fun q : (W × X) × Fin (k + 1) => cand k (pp q.1.1) (sv q.1.1) q.2 q.1.2) :=
    measurable_from_prod_countable_left (fun i => hcand i)
  exact hF.comp (measurable_id.prodMk (hidx.comp measurable_fst))

end OptimalAgnosticPAC.Dev.T1
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.T1
open OptimalAgnosticPAC.Learner

theorem slice_measure (a : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1) (y : Bool) :
    (volume.restrict (Set.Icc (-1 : ℝ) 1)) {u : ℝ | decide (u ≤ a) ≠ y} =
      ENNReal.ofReal (2 * loss a y) := by
  obtain ⟨h1, h2⟩ := ha
  rw [Dev.T3.loss_eq a ⟨h1, h2⟩ y]
  cases y
  · have : {u : ℝ | decide (u ≤ a) ≠ false} = Set.Iic a := by ext u; simp
    rw [this, Measure.restrict_apply measurableSet_Iic]
    have : Set.Iic a ∩ Set.Icc (-1 : ℝ) 1 = Set.Icc (-1) a := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h, h', _⟩; exact ⟨h', h⟩
      · rintro ⟨h, h'⟩; exact ⟨h', h, by linarith⟩
    rw [this, Real.volume_Icc]
    congr 1; simp [sgn]; ring
  · have : {u : ℝ | decide (u ≤ a) ≠ true} = Set.Ioi a := by ext u; simp
    rw [this, Measure.restrict_apply measurableSet_Ioi]
    have : Set.Ioi a ∩ Set.Icc (-1 : ℝ) 1 = Set.Ioc a 1 := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨h, _, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by linarith, h'⟩
    rw [this, Real.volume_Ioc]
    congr 1; simp [sgn]; ring

theorem minRisk_le_scoreRisk {X : Type} [MeasurableSpace X] (P : Measure (X × Bool))
    [IsProbabilityMeasure P] (p : X → ℝ) (hp : Measurable p) (hp1 : ∀ x, p x ∈ Set.Icc (-1 : ℝ) 1) :
    minRisk P (thresholdClass p) ≤ scoreRisk P p := by
  set s := scoreRisk P p with hsdef
  have hl0 : ∀ z : X × Bool, 0 ≤ loss (p z.1) z.2 := fun z => by unfold loss; positivity
  have hs0 : 0 ≤ s := integral_nonneg hl0
  have hint : Integrable (fun z : X × Bool => loss (p z.1) z.2) P := by
    refine Integrable.of_bound (Dev.T3.measurable_loss _ hp).aestronglyMeasurable 1 (Filter.Eventually.of_forall ?_)
    intro z
    rw [Real.norm_eq_abs, Dev.T3.loss_eq _ (hp1 z.1)]
    have := hp1 z.1
    unfold sgn
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith [this.1, this.2]
  let E : Set (ℝ × (X × Bool)) := {q | decide (q.1 ≤ p q.2.1) ≠ q.2.2}
  have hE : MeasurableSet E := by
    have h1 : Measurable (fun q : ℝ × (X × Bool) => decide (q.1 ≤ p q.2.1)) := by
      apply measurable_to_bool
      have : (fun q : ℝ × (X × Bool) => decide (q.1 ≤ p q.2.1)) ⁻¹' {true} = {q | q.1 ≤ p q.2.1} := by
        ext z; simp
      rw [this]
      exact measurableSet_le measurable_fst (hp.comp (measurable_fst.comp measurable_snd))
    exact (MeasurableSet.of_discrete (s := {q : Bool × Bool | q.1 ≠ q.2})).preimage
      (h1.prodMk (measurable_snd.comp measurable_snd))
  set μ : Measure ℝ := volume.restrict (Set.Icc (-1 : ℝ) 1) with hμ
  have : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩
  have hμuniv : μ Set.univ = ENNReal.ofReal 2 := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc]; norm_num
  have hA : (μ.prod P) E = ENNReal.ofReal (2 * s) := by
    rw [Measure.prod_apply_symm hE]
    have : ∀ z : X × Bool, μ ((fun u : ℝ => (u, z)) ⁻¹' E) = ENNReal.ofReal (2 * loss (p z.1) z.2) := by
      intro z
      exact slice_measure (p z.1) (hp1 z.1) z.2
    simp_rw [this]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul 2) (Filter.Eventually.of_forall
      (fun z => by have := hl0 z; positivity))]
    rw [integral_const_mul]; rfl
  by_contra hcon
  push Not at hcon
  have hall : ∀ u ∈ Set.Icc (-1 : ℝ) 1, s < risk P (fun x => decide (u ≤ p x)) := by
    intro u hu
    refine lt_of_lt_of_le hcon (csInf_le ⟨0, ?_⟩ ?_)
    · rintro _ ⟨h, _, rfl⟩; exact measureReal_nonneg
    · exact ⟨_, Or.inl ⟨u, hu, rfl⟩, rfl⟩
  have hB : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ENNReal.ofReal s < P (Prod.mk u ⁻¹' E) := by
    intro u hu
    have h1 := hall u hu
    have : P (Prod.mk u ⁻¹' E) = ENNReal.ofReal (risk P (fun x => decide (u ≤ p x))) := by
      unfold risk Measure.real
      rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rfl
    rw [this, ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    exact h1
  have hlt : ∫⁻ _u, ENNReal.ofReal s ∂μ < ∫⁻ u, P (Prod.mk u ⁻¹' E) ∂μ := by
    refine lintegral_strict_mono ?_ (measurable_measure_prodMk_left hE).aemeasurable ?_ ?_
    · intro h0; have := hμuniv; rw [h0] at this; simp at this
    · rw [lintegral_const, hμuniv]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu using hB u hu
  rw [lintegral_const, hμuniv, ← Measure.prod_apply hE, hA, ← ENNReal.ofReal_mul hs0] at hlt
  rw [mul_comm] at hlt
  exact lt_irrefl _ hlt

end OptimalAgnosticPAC.Dev.T1
end

section
namespace OptimalAgnosticPAC.Dev.T1

theorem real_chain (Ls Lt D ell k n : ℝ) (hLs : 0 ≤ Ls) (hell : 0 < ell) (hD : ell ≤ D) (hk : 0 < k)
    (hn : 0 < n) (hkn : n ≤ 6 * k) (hLt0 : 0 ≤ Lt)
    (hLt : Lt ≤ Ls + 17000 * (Real.sqrt (Ls * D / k) + D / k)) :
    Lt + 223000 * (Real.sqrt (Lt * ell / k) + ell / k) ≤
      Ls + 2 * 10 ^ 8 * (Real.sqrt (Ls * D / n) + D / n) := by
  have hD0 : 0 < D := lt_of_lt_of_le hell hD
  set s := Real.sqrt (Ls * D / k) with hs
  set t := D / k with ht
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := by positivity
  have hs2 : s ^ 2 = Ls * D / k := Real.sq_sqrt (by positivity)
  have hellk : ell / k ≤ t := by
    rw [ht]; exact div_le_div_of_nonneg_right hD hk.le
  have hLsell : Ls * ell / k ≤ s ^ 2 := by
    rw [hs2]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD hLs) hk.le
  have hellk0 : 0 ≤ ell / k := by positivity
  have hB0 : 0 ≤ s + t := by linarith
  have hu : Real.sqrt (Lt * ell / k) ≤ 132 * (s + t) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    have h1 : Lt * ell / k ≤ (Ls + 17000 * (s + t)) * ell / k :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hLt hell.le) hk.le
    have h2 : (Ls + 17000 * (s + t)) * ell / k = Ls * ell / k + 17000 * (s + t) * (ell / k) := by ring
    have h3 : (s + t) * (ell / k) ≤ (s + t) * (s + t) :=
      mul_le_mul_of_nonneg_left (by linarith) hB0
    nlinarith [mul_nonneg hs0 hs0, mul_nonneg hs0 ht0, mul_nonneg ht0 ht0]
  have hs6 : s ≤ 6 * Real.sqrt (Ls * D / n) := by
    rw [hs, ← Real.sqrt_sq (show (0:ℝ) ≤ 6 by norm_num), ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    have : Ls * D / k ≤ 6 * (Ls * D / n) := by
      rw [div_le_iff₀ hk]
      have : 0 ≤ Ls * D := by positivity
      calc Ls * D = (Ls * D / n) * n := by field_simp
        _ ≤ (Ls * D / n) * (6 * k) := mul_le_mul_of_nonneg_left hkn (by positivity)
        _ = 6 * (Ls * D / n) * k := by ring
    nlinarith [show 0 ≤ Ls * D / n by positivity]
  have ht6 : t ≤ 6 * (D / n) := by
    rw [ht, div_le_iff₀ hk]
    calc D = (D / n) * n := by field_simp
      _ ≤ (D / n) * (6 * k) := mul_le_mul_of_nonneg_left hkn (by positivity)
      _ = 6 * (D / n) * k := by ring
  have hsig : 0 ≤ Real.sqrt (Ls * D / n) + D / n := by positivity
  nlinarith [hsig]

end OptimalAgnosticPAC.Dev.T1
end

section
open MeasureTheory
open scoped Classical

namespace OptimalAgnosticPAC.Dev.T1
open OptimalAgnosticPAC.Learner

variable {X : Type} [MeasurableSpace X]

def s1 {Z : Type} (k n : ℕ) (h : 3 * k ≤ n) (S : Fin n → Z) : Fin (2 * k - 1) → Z :=
  fun i => S ⟨i.val, by have := i.isLt; omega⟩

def sv {Z : Type} (k n : ℕ) (h : 3 * k ≤ n) (S : Fin n → Z) : Fin k → Z :=
  fun j => S ⟨2 * k - 1 + j.val, by have := j.isLt; omega⟩

noncomputable def Aeff (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (k n : ℕ) (h : 3 * k ≤ n)
    (S : Fin n → X × Bool) (x : X) : Bool :=
  sel k (suffixAvg q k (s1 k n h S)) (sv k n h S) x

noncomputable def Alearn (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (n : ℕ)
    (S : Fin n → X × Bool) (x : X) : Bool :=
  if h : 6 ≤ n then Aeff q (n / 3) n (by omega) S x else false

theorem measurable_suffixAvg {H : Set (X → Bool)} {d : ℕ}
    {q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ} (hq : IsLOOScore H d q) (k : ℕ) :
    Measurable (fun z : (Fin (2 * k - 1) → X × Bool) × X => suffixAvg q k z.1 z.2) := by
  unfold suffixAvg
  refine measurable_const.mul (Finset.measurable_sum _ (fun j _ => ?_))
  have hpre : Measurable (fun w : Fin (2 * k - 1) → X × Bool =>
      prefixSample w (k + j) (by have := j.isLt; omega)) := by
    unfold prefixSample
    exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  exact (hq.measurable (k + j)).comp ((hpre.comp measurable_fst).prodMk measurable_snd)

theorem measurable_Aeff {H : Set (X → Bool)} {d : ℕ}
    {q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ} (hq : IsLOOScore H d q) (k n : ℕ) (h : 3 * k ≤ n) :
    Measurable (fun z : (Fin n → X × Bool) × X => Aeff q k n h z.1 z.2) := by
  have hs1 : Measurable (s1 (Z := X × Bool) k n h) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hsv : Measurable (sv (Z := X × Bool) k n h) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  exact measurable_sel k (fun w => suffixAvg q k (s1 k n h w))
    ((measurable_suffixAvg hq k).comp ((hs1.comp measurable_fst).prodMk measurable_snd)) _ hsv

theorem measurable_Alearn {H : Set (X → Bool)} {d : ℕ}
    {q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ} (hq : IsLOOScore H d q) (n : ℕ) :
    Measurable (fun z : (Fin n → X × Bool) × X => Alearn q n z.1 z.2) := by
  by_cases h : 6 ≤ n
  · unfold Alearn
    simp only [dif_pos h]
    exact measurable_Aeff hq (n / 3) n (by omega)
  · unfold Alearn
    simp only [dif_neg h]
    exact measurable_const

theorem measurable_scoreRisk_suffix {H : Set (X → Bool)} {d : ℕ}
    {q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ} (hq : IsLOOScore H d q) (P : Measure (X × Bool))
    [IsProbabilityMeasure P] (k : ℕ) :
    Measurable (fun w : Fin (2 * k - 1) → X × Bool => scoreRisk P (suffixAvg q k w)) := by
  unfold scoreRisk
  have hf : Measurable (fun z : (Fin (2 * k - 1) → X × Bool) × (X × Bool) =>
      loss (suffixAvg q k z.1 z.2.1) z.2.2) := by
    unfold loss
    have h1 : Measurable (fun z : (Fin (2 * k - 1) → X × Bool) × (X × Bool) => suffixAvg q k z.1 z.2.1) :=
      (measurable_suffixAvg hq k).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h2 : Measurable (fun z : (Fin (2 * k - 1) → X × Bool) × (X × Bool) => sgn z.2.2) :=
      (measurable_from_top (f := sgn)).comp (measurable_snd.comp measurable_snd)
    exact ((h1.sub h2).abs).div_const 2
  exact (hf.stronglyMeasurable.integral_prod_right').measurable

theorem measurable_risk_sel {H : Set (X → Bool)} {d : ℕ}
    {q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ} (hq : IsLOOScore H d q) (P : Measure (X × Bool))
    [IsProbabilityMeasure P] (k c : ℕ) :
    Measurable (fun w : (Fin (2 * k - 1) → X × Bool) × (Fin (k + c) → X × Bool) =>
      risk P (sel k (suffixAvg q k w.1) (fun j => w.2 (Fin.castAdd c j)))) := by
  have hG := measurable_sel (W := (Fin (2 * k - 1) → X × Bool) × (Fin (k + c) → X × Bool)) k
    (fun w => suffixAvg q k w.1)
    ((measurable_suffixAvg hq k).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    (fun w => fun j => w.2 (Fin.castAdd c j))
    (measurable_pi_lambda _ (fun j => (measurable_pi_apply _).comp measurable_snd))
  have hM : MeasurableSet {z : ((Fin (2 * k - 1) → X × Bool) × (Fin (k + c) → X × Bool)) × (X × Bool) |
      sel k (suffixAvg q k z.1.1) (fun j => z.1.2 (Fin.castAdd c j)) z.2.1 ≠ z.2.2} := by
    exact (MeasurableSet.of_discrete (s := {q : Bool × Bool | q.1 ≠ q.2})).preimage
      ((hG.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd))
  have := (measurable_measure_prodMk_left (ν := P) hM).ennreal_toReal
  exact this

theorem main_bound (H : Set (X → Bool)) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞)) (hmeas : ∀ h ∈ H, Measurable h)
    (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (hq : IsLOOScore H d q)
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (hmin : AttainsMinRisk P H)
    (k n : ℕ) (hk : 1 ≤ k) (h3 : 3 * k ≤ n) (h6 : n ≤ 6 * k) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    sampleLaw P n
      {S | minRisk P H +
            2 * 10 ^ 8 *
              (Real.sqrt (minRisk P H * ((d : ℝ) + Real.log (48 / δ)) / (n : ℝ)) +
                ((d : ℝ) + Real.log (48 / δ)) / (n : ℝ)) <
          risk P (Aeff q k n h3 S)} ≤
      ENNReal.ofReal δ := by
  have hℓ : 0 < Real.log (48 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkn : (n : ℝ) ≤ 6 * k := by exact_mod_cast h6
  have hLs0 : 0 ≤ minRisk P H := Real.sInf_nonneg (by rintro _ ⟨h, _, rfl⟩; exact measureReal_nonneg)
  obtain ⟨hIcc, hT3⟩ := OptimalAgnosticPAC.Learner.theorem_3 H d hd hVC hmeas q hq P hmin k hk
  obtain ⟨c, rfl⟩ : ∃ c, n = (2 * k - 1) + (k + c) := ⟨n - 3 * k + 1, by omega⟩
  let T3set : Set (Fin (2 * k - 1) → X × Bool) :=
    {w | minRisk P H + 17000 * (Real.sqrt (minRisk P H * ((d : ℝ) + Real.log (48 / δ)) / (k : ℝ)) +
      ((d : ℝ) + Real.log (48 / δ)) / (k : ℝ)) < scoreRisk P (suffixAvg q k w)}
  have hT3b : Measure.pi (fun _ : Fin (2 * k - 1) => P) T3set ≤ ENNReal.ofReal (δ / 16) := by
    have := hT3 (δ / 16) (by positivity) (by linarith)
    have e48 : 3 / (δ / 16) = 48 / δ := by field_simp; norm_num
    rw [e48] at this
    exact this
  let V : Set ((Fin (2 * k - 1) → X × Bool) × (Fin (k + c) → X × Bool)) :=
    {w | scoreRisk P (suffixAvg q k w.1) +
        223000 * (Real.sqrt (scoreRisk P (suffixAvg q k w.1) * Real.log (48 / δ) / (k : ℝ)) +
          Real.log (48 / δ) / (k : ℝ)) <
      risk P (sel k (suffixAvg q k w.1) (fun j => w.2 (Fin.castAdd c j)))}
  have hV : MeasurableSet V := by
    have hLt := measurable_scoreRisk_suffix hq P k
    have hf : Measurable (fun w : (Fin (2 * k - 1) → X × Bool) × (Fin (k + c) → X × Bool) =>
        scoreRisk P (suffixAvg q k w.1) +
        223000 * (Real.sqrt (scoreRisk P (suffixAvg q k w.1) * Real.log (48 / δ) / (k : ℝ)) +
          Real.log (48 / δ) / (k : ℝ))) := by
      have h1 : Measurable (fun w : (Fin (2 * k - 1) → X × Bool) × (Fin (k + c) → X × Bool) =>
          scoreRisk P (suffixAvg q k w.1)) := hLt.comp measurable_fst
      exact h1.add (measurable_const.mul ((h1.mul_const _ |>.div_const _).sqrt.add_const _))
    exact measurableSet_lt hf (measurable_risk_sel hq P k c)
  have hslice : ∀ w : Fin (2 * k - 1) → X × Bool,
      Measure.pi (fun _ : Fin k => P)
        {Sv | scoreRisk P (suffixAvg q k w) +
          223000 * (Real.sqrt (scoreRisk P (suffixAvg q k w) * Real.log (48 / δ) / (k : ℝ)) +
            Real.log (48 / δ) / (k : ℝ)) < risk P (sel k (suffixAvg q k w) Sv)} ≤
        ENNReal.ofReal (δ / 4) := by
    intro w
    have hp : Measurable (suffixAvg q k w) :=
      (measurable_suffixAvg hq k).comp (measurable_const.prodMk measurable_id)
    have hp1 := hIcc w
    have hmr := minRisk_le_scoreRisk P _ hp hp1
    have hm0 : 0 ≤ minRisk P (thresholdClass (suffixAvg q k w)) :=
      Real.sInf_nonneg (by rintro _ ⟨h, _, rfl⟩; exact measureReal_nonneg)
    have hlem := OptimalAgnosticPAC.Learner.lemma_3_3 P (suffixAvg q k w) hp hp1 k hk
      (sel k (suffixAvg q k w)) (sel_isERM _ hp1) (δ / 4) (by positivity) (by linarith)
    have e12 : 12 / (δ / 4) = 48 / δ := by field_simp; norm_num
    rw [e12] at hlem
    refine le_trans (measure_mono ?_) hlem
    intro Sv hSv
    simp only [Set.mem_setOf_eq] at hSv ⊢
    refine lt_of_le_of_lt ?_ hSv
    have h1 : Real.sqrt (minRisk P (thresholdClass (suffixAvg q k w)) * Real.log (48 / δ) / (k : ℝ)) ≤
        Real.sqrt (scoreRisk P (suffixAvg q k w) * Real.log (48 / δ) / (k : ℝ)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmr hℓ.le) hkR.le)
    linarith
  have hsub : {S : Fin ((2 * k - 1) + (k + c)) → X × Bool |
      minRisk P H +
            2 * 10 ^ 8 *
              (Real.sqrt (minRisk P H * ((d : ℝ) + Real.log (48 / δ)) / (((2 * k - 1) + (k + c) : ℕ) : ℝ)) +
                ((d : ℝ) + Real.log (48 / δ)) / (((2 * k - 1) + (k + c) : ℕ) : ℝ)) <
          risk P (Aeff q k ((2 * k - 1) + (k + c)) h3 S)} ⊆
      ((fun (S : Fin ((2 * k - 1) + (k + c)) → X × Bool) (i : Fin (2 * k - 1)) => S (Fin.castAdd (k + c) i)) ⁻¹' T3set) ∪
      ((fun (S : Fin ((2 * k - 1) + (k + c)) → X × Bool) =>
        ((fun i : Fin (2 * k - 1) => S (Fin.castAdd (k + c) i)),
          (fun j : Fin (k + c) => S (Fin.natAdd (2 * k - 1) j)))) ⁻¹' V) := by
    intro S hS
    by_contra hcon
    simp only [Set.mem_union, not_or, Set.mem_preimage] at hcon
    obtain ⟨h1, h2⟩ := hcon
    simp only [T3set, Set.mem_setOf_eq] at h1
    simp only [V, Set.mem_setOf_eq] at h2
    have h1' := not_lt.mp h1
    have h2' := not_lt.mp h2
    have hLt0 : 0 ≤ scoreRisk P (suffixAvg q k (fun i => S (Fin.castAdd (k + c) i))) :=
      integral_nonneg (fun z => by unfold loss; positivity)
    have hch := real_chain (minRisk P H) (scoreRisk P (suffixAvg q k (fun i => S (Fin.castAdd (k + c) i))))
      ((d : ℝ) + Real.log (48 / δ)) (Real.log (48 / δ)) k (((2 * k - 1) + (k + c) : ℕ) : ℝ) hLs0 hℓ
      (by have : (0:ℝ) ≤ d := Nat.cast_nonneg d; linarith) hkR hnR hkn hLt0 h1'
    exact absurd hS (not_lt.mpr (le_trans h2' hch))
  have hA2 : Measure.pi (fun _ : Fin ((2 * k - 1) + (k + c)) => P)
      ((fun (S : Fin ((2 * k - 1) + (k + c)) → X × Bool) =>
        ((fun i : Fin (2 * k - 1) => S (Fin.castAdd (k + c) i)),
          (fun j : Fin (k + c) => S (Fin.natAdd (2 * k - 1) j)))) ⁻¹' V) ≤ ENNReal.ofReal (δ / 4) := by
    rw [fubini_split P _ _ V hV]
    calc _ ≤ ∫⁻ _w, ENNReal.ofReal (δ / 4) ∂(Measure.pi (fun _ : Fin (2 * k - 1) => P)) := by
          refine lintegral_mono (fun w => ?_)
          exact le_trans (fst_le P k c _) (hslice w)
      _ = ENNReal.ofReal (δ / 4) := by simp
  have hA1 : Measure.pi (fun _ : Fin ((2 * k - 1) + (k + c)) => P)
      ((fun (S : Fin ((2 * k - 1) + (k + c)) → X × Bool) (i : Fin (2 * k - 1)) => S (Fin.castAdd (k + c) i)) ⁻¹' T3set)
      ≤ ENNReal.ofReal (δ / 16) := le_trans (fst_le P _ _ _) hT3b
  unfold sampleLaw
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ / 16) + ENNReal.ofReal (δ / 4) := add_le_add hA1 hA2
    _ = ENNReal.ofReal (δ / 16 + δ / 4) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (by linarith)

end OptimalAgnosticPAC.Dev.T1

namespace OptimalAgnosticPAC.Learner
open MeasureTheory
open scoped Classical

theorem chk_theorem_1 {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞))
    (hmeas : ∀ h ∈ H, Measurable h) (htrace : TraceMeasurable H) :
    ∃ A : (n : ℕ) → (Fin n → X × Bool) → X → Bool,
      (∀ n : ℕ, Measurable (fun z : (Fin n → X × Bool) × X => A n z.1 z.2)) ∧
      ∀ (P : Measure (X × Bool)) [IsProbabilityMeasure P], AttainsMinRisk P H →
        ∀ n : ℕ, 1 ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 →
          sampleLaw P n
            {S | minRisk P H +
                  2 * 10 ^ 8 *
                    (Real.sqrt (minRisk P H * ((d : ℝ) + Real.log (48 / δ)) / (n : ℝ)) +
                      ((d : ℝ) + Real.log (48 / δ)) / (n : ℝ)) <
                risk P (A n S)} ≤
            ENNReal.ofReal δ := by
  by_cases hH : H.Nonempty
  · obtain ⟨q, hq⟩ := eq_13_symmetrized_loo H hH d hd hVC hmeas htrace
    refine ⟨Dev.T1.Alearn q, fun n => Dev.T1.measurable_Alearn hq n, ?_⟩
    intro P _ hmin n hn δ hδ0 hδ1
    by_cases h6 : 6 ≤ n
    · have := Dev.T1.main_bound H d hd hVC hmeas q hq P hmin (n / 3) n (by omega) (by omega)
        (by omega) δ hδ0 hδ1
      have e : ∀ S : Fin n → X × Bool, Dev.T1.Alearn q n S = Dev.T1.Aeff q (n / 3) n (by omega) S := by
        intro S; funext x; simp only [Dev.T1.Alearn, dif_pos h6]
      simp_rw [e]
      exact this
    · have hℓ : 0 < Real.log (48 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
      have hLs0 : 0 ≤ minRisk P H :=
        Real.sInf_nonneg (by rintro _ ⟨h, _, rfl⟩; exact measureReal_nonneg)
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hn5 : (n : ℝ) ≤ 5 := by exact_mod_cast (show n ≤ 5 by omega)
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hempty : {S : Fin n → X × Bool | minRisk P H +
                  2 * 10 ^ 8 *
                    (Real.sqrt (minRisk P H * ((d : ℝ) + Real.log (48 / δ)) / (n : ℝ)) +
                      ((d : ℝ) + Real.log (48 / δ)) / (n : ℝ)) <
                risk P (Dev.T1.Alearn q n S)} = ∅ := by
        refine Set.eq_empty_of_forall_notMem (fun S hS => ?_)
        have hS' : minRisk P H +
                  2 * 10 ^ 8 *
                    (Real.sqrt (minRisk P H * ((d : ℝ) + Real.log (48 / δ)) / (n : ℝ)) +
                      ((d : ℝ) + Real.log (48 / δ)) / (n : ℝ)) <
                risk P (Dev.T1.Alearn q n S) := hS
        have hr : risk P (Dev.T1.Alearn q n S) ≤ 1 := by
          unfold risk; exact measureReal_le_one
        have hD : (1 : ℝ) / 5 ≤ ((d : ℝ) + Real.log (48 / δ)) / n := by
          rw [div_le_div_iff₀ (by norm_num) hnR]; nlinarith
        have := Real.sqrt_nonneg (minRisk P H * ((d : ℝ) + Real.log (48 / δ)) / (n : ℝ))
        linarith
      unfold sampleLaw
      rw [hempty, measure_empty]
      exact zero_le
  · refine ⟨fun _ _ _ => false, fun n => measurable_const, ?_⟩
    intro P _ hmin
    exfalso
    obtain ⟨h, hh, _⟩ := hmin
    exact hH ⟨h, hh⟩

end OptimalAgnosticPAC.Learner
end

theorem solution : type_of% @OptimalAgnosticPAC.Learner.chk_theorem_1 := @OptimalAgnosticPAC.Learner.chk_theorem_1

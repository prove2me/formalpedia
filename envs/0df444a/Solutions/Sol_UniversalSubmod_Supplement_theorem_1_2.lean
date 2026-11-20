-- Prove2me | solution 1 for UniversalSubmod.Supplement.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:58:00.615484+00:00
-- url     : https://prove2.me/submissions/a1b79430-cf0b-455e-a254-cf9ee9bc3596

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_UniversalSubmod_threshSet
import Definitions.Def_UniversalSubmod_CorrMatrix
import Definitions.Def_UniversalSubmod_semidefExt
import Definitions.Def_Cohen2019_Robust_Phi
import Theorems.Thm_UniversalSubmod_theorem_2_3
import Theorems.Thm_UniversalSubmod_concavity_segment
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Theorems.Thm_UniversalSubmod_lemma_2_1
import Theorems.Thm_UniversalSubmod_lemma_2_6
import Theorems.Thm_UniversalSubmod_lattice_count

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Thm12A

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared

/-- Harris (FKG) correlation property of a measure on a preordered space. -/
def Harris {α : Type*} [MeasurableSpace α] [Preorder α] (μ : Measure α) : Prop :=
  ∀ g h : α → ℝ, Measurable g → Measurable h → Monotone g → Monotone h →
    (∃ C, ∀ a, |g a| ≤ C) → (∃ C, ∀ a, |h a| ≤ C) →
    (∫ a, g a ∂μ) * (∫ a, h a ∂μ) ≤ ∫ a, g a * h a ∂μ

lemma int_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) (C : ℝ) (h : ∀ a, |g a| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (ae_of_all _ (fun a => by simpa [Real.norm_eq_abs] using h a))

lemma harris_real (ν : Measure ℝ) [IsProbabilityMeasure ν] : Harris ν := by
  intro g h hg hh gm hm ⟨Cg, hCg⟩ ⟨Ch, hCh⟩
  have hgi : Integrable g ν := int_bdd ν hg Cg hCg
  have hhi : Integrable h ν := int_bdd ν hh Ch hCh
  have hgh : Measurable (fun a => g a * h a) := hg.mul hh
  have hghi : Integrable (fun a => g a * h a) ν :=
    int_bdd ν hgh (Cg * Ch) (fun a => by
      rw [abs_mul]
      exact mul_le_mul (hCg a) (hCh a) (abs_nonneg _) ((abs_nonneg _).trans (hCg a)))
  -- the symmetrised integral
  have hpos : 0 ≤ ∫ p : ℝ × ℝ, (g p.1 - g p.2) * (h p.1 - h p.2) ∂(ν.prod ν) := by
    refine integral_nonneg (fun p => ?_)
    rcases le_total p.1 p.2 with hle | hle
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (gm hle)) (sub_nonpos.2 (hm hle))
    · exact mul_nonneg (sub_nonneg.2 (gm hle)) (sub_nonneg.2 (hm hle))
  have e1 : ∫ p : ℝ × ℝ, g p.1 * h p.1 ∂(ν.prod ν) = ∫ a, g a * h a ∂ν := by
    have := integral_prod (μ := ν) (ν := ν) (fun p : ℝ × ℝ => g p.1 * h p.1)
      ((hghi.comp_fst ν))
    simp only [integral_const, probReal_univ, one_smul] at this
    exact this
  have e2 : ∫ p : ℝ × ℝ, g p.2 * h p.2 ∂(ν.prod ν) = ∫ a, g a * h a ∂ν := by
    have := integral_prod (μ := ν) (ν := ν) (fun p : ℝ × ℝ => g p.2 * h p.2)
      ((hghi.comp_snd ν))
    simp only [integral_const, probReal_univ, one_smul] at this
    exact this
  have e3 : ∫ p : ℝ × ℝ, g p.1 * h p.2 ∂(ν.prod ν) = (∫ a, g a ∂ν) * ∫ a, h a ∂ν :=
    integral_prod_mul g h
  have e4 : ∫ p : ℝ × ℝ, g p.2 * h p.1 ∂(ν.prod ν) = (∫ a, g a ∂ν) * ∫ a, h a ∂ν := by
    have := integral_prod_mul (μ := ν) (ν := ν) h g
    rw [mul_comm]
    have h2 : ∫ p : ℝ × ℝ, h p.1 * g p.2 ∂(ν.prod ν) = ∫ p : ℝ × ℝ, g p.2 * h p.1 ∂(ν.prod ν) :=
      integral_congr_ae (ae_of_all _ (fun p => mul_comm _ _))
    rw [← h2]; exact this
  have i1 : Integrable (fun p : ℝ × ℝ => g p.1 * h p.1) (ν.prod ν) := hghi.comp_fst ν
  have i2 : Integrable (fun p : ℝ × ℝ => g p.2 * h p.2) (ν.prod ν) := hghi.comp_snd ν
  have i3 : Integrable (fun p : ℝ × ℝ => g p.1 * h p.2) (ν.prod ν) := hgi.mul_prod hhi
  have i4 : Integrable (fun p : ℝ × ℝ => g p.2 * h p.1) (ν.prod ν) := by
    have := hhi.mul_prod hgi
    exact this.congr (ae_of_all _ (fun p => by simp [mul_comm]))
  have expand : (fun p : ℝ × ℝ => (g p.1 - g p.2) * (h p.1 - h p.2)) =
      fun p => ((g p.1 * h p.1 + g p.2 * h p.2) - g p.1 * h p.2) - g p.2 * h p.1 := by
    funext p; ring
  have j1 : Integrable (fun p : ℝ × ℝ => g p.1 * h p.1 + g p.2 * h p.2) (ν.prod ν) := i1.add i2
  have j2 : Integrable (fun p : ℝ × ℝ => (g p.1 * h p.1 + g p.2 * h p.2) - g p.1 * h p.2)
    (ν.prod ν) := j1.sub i3
  rw [expand, integral_sub j2 i4, integral_sub j1 i3, integral_add i1 i2, e1, e2, e3, e4] at hpos
  nlinarith

lemma harris_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Preorder α] [Preorder β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Harris μ) (hν : Harris ν) : Harris (μ.prod ν) := by
  intro g h hg hh gm hm ⟨Cg, hCg⟩ ⟨Ch, hCh⟩
  have hgi : Integrable g (μ.prod ν) := int_bdd _ hg Cg hCg
  have hhi : Integrable h (μ.prod ν) := int_bdd _ hh Ch hCh
  have hgh : Measurable (fun a => g a * h a) := hg.mul hh
  have hghi : Integrable (fun a => g a * h a) (μ.prod ν) :=
    int_bdd _ hgh (Cg * Ch) (fun a => by
      rw [abs_mul]
      exact mul_le_mul (hCg a) (hCh a) (abs_nonneg _) ((abs_nonneg _).trans (hCg a)))
  -- sectionwise averages
  set G : α → ℝ := fun a => ∫ b, g (a, b) ∂ν with hG
  set H : α → ℝ := fun a => ∫ b, h (a, b) ∂ν with hH
  have hGm : Measurable G := (hg.stronglyMeasurable.integral_prod_right').measurable
  have hHm : Measurable H := (hh.stronglyMeasurable.integral_prod_right').measurable
  have hGmono : Monotone G := by
    intro a a' haa
    refine integral_mono (int_bdd ν (hg.comp measurable_prodMk_left) Cg (fun b => hCg _))
      (int_bdd ν (hg.comp measurable_prodMk_left) Cg (fun b => hCg _)) (fun b => ?_)
    exact gm (Prod.mk_le_mk.2 ⟨haa, le_refl b⟩)
  have hHmono : Monotone H := by
    intro a a' haa
    refine integral_mono (int_bdd ν (hh.comp measurable_prodMk_left) Ch (fun b => hCh _))
      (int_bdd ν (hh.comp measurable_prodMk_left) Ch (fun b => hCh _)) (fun b => ?_)
    exact hm (Prod.mk_le_mk.2 ⟨haa, le_refl b⟩)
  have hGb' : ∀ a, |G a| ≤ Cg := fun a => by
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun b => g (a, b)) (C := Cg)
      (ae_of_all _ (fun b => by simpa [Real.norm_eq_abs] using hCg (a, b)))
    simpa [Real.norm_eq_abs] using this
  have hHb' : ∀ a, |H a| ≤ Ch := fun a => by
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun b => h (a, b)) (C := Ch)
      (ae_of_all _ (fun b => by simpa [Real.norm_eq_abs] using hCh (a, b)))
    simpa [Real.norm_eq_abs] using this
  have hGb : ∃ C, ∀ a, |G a| ≤ C := ⟨Cg, hGb'⟩
  have hHb : ∃ C, ∀ a, |H a| ≤ C := ⟨Ch, hHb'⟩
  have step1 : ∀ a, G a * H a ≤ ∫ b, g (a, b) * h (a, b) ∂ν := by
    intro a
    exact hν (fun b => g (a, b)) (fun b => h (a, b)) (hg.comp measurable_prodMk_left)
      (hh.comp measurable_prodMk_left)
      (fun b b' hbb => gm (Prod.mk_le_mk.2 ⟨le_refl a, hbb⟩))
      (fun b b' hbb => hm (Prod.mk_le_mk.2 ⟨le_refl a, hbb⟩))
      ⟨Cg, fun b => hCg _⟩ ⟨Ch, fun b => hCh _⟩
  have step2 := hμ G H hGm hHm hGmono hHmono hGb hHb
  have hint : ∫ a, g a ∂(μ.prod ν) = ∫ a, G a ∂μ := integral_prod _ hgi
  have hint' : ∫ a, h a ∂(μ.prod ν) = ∫ a, H a ∂μ := integral_prod _ hhi
  have hint'' : ∫ a, g a * h a ∂(μ.prod ν) = ∫ a, (∫ b, g (a, b) * h (a, b) ∂ν) ∂μ :=
    integral_prod _ hghi
  rw [hint, hint', hint'']
  refine step2.trans (integral_mono ?_ ?_ step1)
  · exact int_bdd μ (hGm.mul hHm) (Cg * Ch) (fun a => by
      rw [abs_mul]
      exact mul_le_mul (hGb' a) (hHb' a) (abs_nonneg _) ((abs_nonneg _).trans (hGb' a)))
  · exact (hghi.integral_prod_left)


lemma harris_transfer {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Preorder α]
    [Preorder β] (μ : Measure α) (ν : Measure β) (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (hmono' : Monotone e.symm) (hν : Harris ν) : Harris μ := by
  intro g h hg hh gm hm ⟨Cg, hCg⟩ ⟨Ch, hCh⟩
  have key := hν (fun b => g (e.symm b)) (fun b => h (e.symm b)) (hg.comp e.symm.measurable)
    (hh.comp e.symm.measurable) (gm.comp hmono') (hm.comp hmono')
    ⟨Cg, fun b => hCg _⟩ ⟨Ch, fun b => hCh _⟩
  have i1 := he.integral_comp' (fun b => g (e.symm b))
  have i2 := he.integral_comp' (fun b => h (e.symm b))
  have i3 := he.integral_comp' (fun b => g (e.symm b) * h (e.symm b))
  simp only [MeasurableEquiv.symm_apply_apply] at i1 i2 i3
  rw [i1, i2, i3]
  exact key

lemma harris_unique {α : Type*} [MeasurableSpace α] [Preorder α] [Unique α]
    (μ : Measure α) [IsProbabilityMeasure μ] : Harris μ := by
  intro g h _ _ _ _ _ _
  have hs : ∀ F : α → ℝ, ∫ a, F a ∂μ = F default := by
    intro F
    have : F = fun _ => F default := by funext a; rw [Subsingleton.elim a default]
    rw [this]; simp
  rw [hs, hs, hs]

lemma harris_pi {α : Type*} [MeasurableSpace α] [Preorder α] (m : ℕ) (μ : Fin m → Measure α)
    [∀ j, IsProbabilityMeasure (μ j)] (hμ : ∀ j, Harris (μ j)) : Harris (Measure.pi μ) := by
  induction m with
  | zero =>
    haveI : Unique (Fin 0 → α) := Pi.uniqueOfIsEmpty _
    exact harris_unique _
  | succ m ih =>
    refine harris_transfer (Measure.pi μ)
      ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j)))
      (MeasurableEquiv.piFinSuccAbove (fun _ => α) 0)
      (measurePreserving_piFinSuccAbove μ 0) ?_
      (harris_prod _ _ (hμ 0) (ih (fun j => μ (Fin.succAbove 0 j)) (fun j => hμ _)))
    · intro x y hxy i
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply]
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hxy.1
      · simpa using hxy.2 j


lemma harris_pi_fintype {α : Type*} [MeasurableSpace α] [Preorder α] {ι : Type*} [Fintype ι]
    (μ : ι → Measure α) [∀ j, IsProbabilityMeasure (μ j)] (hμ : ∀ j, Harris (μ j)) :
    Harris (Measure.pi μ) := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set ν : Fin (Fintype.card ι) → Measure α := fun j => μ (e.symm j) with hν
  haveI : ∀ j, IsProbabilityMeasure (ν j) := fun j => by simp only [hν]; infer_instance
  have h1 : Harris (Measure.pi ν) := harris_pi _ ν (fun j => hμ _)
  refine harris_transfer (Measure.pi μ) (Measure.pi ν)
    (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl α)) ?_ ?_ h1
  · exact measurePreserving_arrowCongr' μ ν e (MeasurableEquiv.refl α)
      (fun i => by simp only [hν, Equiv.symm_apply_apply]; exact MeasurePreserving.id _)
  · intro x y hxy i
    exact hxy (e i)

section abstract43

open Classical

/-- measurability of `ω ↦ f (T.filter (ω ∈ A i))` -/
lemma meas_filter {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (f : Finset ι → ℝ) (T : Finset ι) :
    Measurable (fun ω => f (T.filter (fun i => ω ∈ A i))) := by
  have h : (fun ω => f (T.filter (fun i => ω ∈ A i))) =
      fun ω => ∑ S ∈ T.powerset, if T.filter (fun i => ω ∈ A i) = S then f S else 0 := by
    funext ω
    rw [Finset.sum_eq_single (T.filter (fun i => ω ∈ A i))]
    · simp
    · intro S _ hS; simp [Ne.symm hS]
    · intro hnot; exact absurd (Finset.mem_powerset.2 (Finset.filter_subset _ _)) hnot
  rw [h]
  refine Finset.measurable_sum _ (fun S _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  by_cases hS : S ⊆ T
  · have : {ω | T.filter (fun i => ω ∈ A i) = S} = ⋂ i ∈ T, (if i ∈ S then A i else (A i)ᶜ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff, Finset.mem_filter]
      constructor
      · intro h i hi
        have := h i
        by_cases hiS : i ∈ S
        · simp only [hiS, if_true]; exact (this.2 hiS).2
        · simp only [hiS, if_false, Set.mem_compl_iff]
          intro hA; exact hiS (this.1 ⟨hi, hA⟩)
      · intro h i
        by_cases hiT : i ∈ T
        · have := h i hiT
          by_cases hiS : i ∈ S
          · simp only [hiS, if_true] at this; simp [hiS, hiT, this]
          · simp only [hiS, if_false, Set.mem_compl_iff] at this; simp [hiS, hiT, this]
        · have : i ∉ S := fun h' => hiT (hS h')
          simp [hiT, this]
    show MeasurableSet {ω | T.filter (fun i => ω ∈ A i) = S}
    rw [this]
    refine Finset.measurableSet_biInter _ (fun i _ => ?_)
    split_ifs
    · exact hA i
    · exact (hA i).compl
  · have : {ω | T.filter (fun i => ω ∈ A i) = S} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hS (h ▸ Finset.filter_subset _ _)
    show MeasurableSet {ω | T.filter (fun i => ω ∈ A i) = S}
    rw [this]; exact MeasurableSet.empty


/-- The multilinear sum over the subsets of `T`. -/
def Gsum {ι : Type*} [DecidableEq ι] (x : ι → ℝ) (f : Finset ι → ℝ) (T : Finset ι) : ℝ :=
  ∑ S ∈ T.powerset, f S * ((∏ i ∈ S, x i) * ∏ i ∈ T \ S, (1 - x i))

lemma Gsum_insert {ι : Type*} [DecidableEq ι] {a : ι} {T : Finset ι} (ha : a ∉ T) (x : ι → ℝ)
    (f : Finset ι → ℝ) :
    Gsum x f (insert a T) = (1 - x a) * Gsum x f T + x a * Gsum x (fun S => f (insert a S)) T := by
  unfold Gsum
  rw [Finset.sum_powerset_insert ha, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun S hS => ?_)
    have hSa : a ∉ S := fun h => ha (Finset.mem_powerset.1 hS h)
    have : insert a T \ S = insert a (T \ S) := by
      ext i; simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h2⟩
      · rintro (h1 | ⟨h1, h2⟩)
        · exact ⟨Or.inl h1, h1 ▸ hSa⟩
        · exact ⟨Or.inr h1, h2⟩
    rw [this, Finset.prod_insert (by simp [ha])]
    ring
  · refine Finset.sum_congr rfl (fun S hS => ?_)
    have hSa : a ∉ S := fun h => ha (Finset.mem_powerset.1 hS h)
    have : insert a T \ insert a S = T \ S := by
      ext i; simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd (Or.inl h1) h2
        · exact ⟨h1, fun h => h2 (Or.inr h)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨Or.inr h1, ?_⟩
        rintro (h | h)
        · exact ha (h ▸ h1)
        · exact h2 h
    rw [this, Finset.prod_insert hSa]
    ring

lemma bdd_filter {Ω : Type*} {ι : Type*} (A : ι → Set Ω) (f : Finset ι → ℝ) (T : Finset ι)
    (ω : Ω) : |f (T.filter (fun i => ω ∈ A i))| ≤ ∑ S ∈ T.powerset, |f S| :=
  Finset.single_le_sum (f := fun S => |f S|) (fun _ _ => abs_nonneg _)
    (Finset.mem_powerset.2 (Finset.filter_subset _ _))

theorem abstract43 {Ω : Type*} [MeasurableSpace Ω] [Preorder Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hH : Harris P) {ι : Type*} [DecidableEq ι] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i))
    (hmono : ∀ i, ∀ ω ω', ω ≤ ω' → ω ∈ A i → ω' ∈ A i) (T : Finset ι) :
    ∀ f : Finset ι → ℝ, (∀ S U, f (S ∪ U) + f (S ∩ U) ≤ f S + f U) →
      ∫ ω, f (T.filter (fun i => ω ∈ A i)) ∂P ≤ Gsum (fun i => P.real (A i)) f T := by
  induction T using Finset.induction_on with
  | empty =>
    intro f _
    simp [Gsum]
  | insert a T ha ih =>
    intro f hf
    set X : Ω → Finset ι := fun ω => T.filter (fun i => ω ∈ A i) with hX
    set f1 : Finset ι → ℝ := fun S => f (insert a S) with hf1
    have hf1sub : ∀ S U, f1 (S ∪ U) + f1 (S ∩ U) ≤ f1 S + f1 U := by
      intro S U
      simp only [hf1]
      rw [Finset.insert_union_distrib, Finset.insert_inter_distrib]
      exact hf _ _
    have hmeasf : Measurable (fun ω => f (X ω)) := meas_filter A hA f T
    have hmeasf1 : Measurable (fun ω => f1 (X ω)) := meas_filter A hA f1 T
    set B : ℝ := ∑ S ∈ T.powerset, |f S| with hB
    set B1 : ℝ := ∑ S ∈ T.powerset, |f1 S| with hB1
    have hintf : Integrable (fun ω => f (X ω)) P := int_bdd P hmeasf B (fun ω => bdd_filter A f T ω)
    have hintf1 : Integrable (fun ω => f1 (X ω)) P :=
      int_bdd P hmeasf1 B1 (fun ω => bdd_filter A f1 T ω)
    set g : Ω → ℝ := (A a).indicator (fun _ => (1 : ℝ)) with hg
    set d : Ω → ℝ := fun ω => f1 (X ω) - f (X ω) with hd
    have hgm : Measurable g := measurable_const.indicator (hA a)
    have hdm : Measurable d := hmeasf1.sub hmeasf
    have hpt : ∀ ω, f ((insert a T).filter (fun i => ω ∈ A i)) = f (X ω) + g ω * d ω := by
      intro ω
      rw [Finset.filter_insert]
      by_cases h : ω ∈ A a
      · simp [hg, hd, hX, hf1, h]
      · simp [hg, hd, hX, h]
    have hgmono : Monotone g := by
      intro ω ω' hle
      simp only [hg, Set.indicator_apply]
      by_cases h : ω ∈ A a
      · simp [h, hmono a ω ω' hle h]
      · by_cases h' : ω' ∈ A a <;> simp [h, h']
    have hdanti : Monotone (fun ω => - d ω) := by
      intro ω ω' hle
      have hsub : X ω ⊆ X ω' := by
        intro i hi
        simp only [hX, Finset.mem_filter] at hi ⊢
        exact ⟨hi.1, hmono i ω ω' hle hi.2⟩
      have haX : a ∉ X ω' := fun h => ha (Finset.mem_filter.1 h).1
      have := hf (insert a (X ω)) (X ω')
      have e1 : insert a (X ω) ∪ X ω' = insert a (X ω') := by
        ext i; simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr (hsub h)
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
      have e2 : insert a (X ω) ∩ X ω' = X ω := by
        ext i; simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨h | h, h2⟩
          · exact absurd (h ▸ h2) haX
          · exact h
        · intro h; exact ⟨Or.inr h, hsub h⟩
      rw [e1, e2] at this
      simp only [hd, hf1]
      linarith
    have hgb : ∃ C, ∀ ω, |g ω| ≤ C := ⟨1, fun ω => by
      simp only [hg, Set.indicator_apply]; split_ifs <;> simp⟩
    have hdb : ∃ C, ∀ ω, |-d ω| ≤ C := ⟨B1 + B, fun ω => by
      rw [abs_neg]
      calc |d ω| ≤ |f1 (X ω)| + |f (X ω)| := abs_sub _ _
        _ ≤ B1 + B := add_le_add (bdd_filter A f1 T ω) (bdd_filter A f T ω)⟩
    have hHarris := hH g (fun ω => - d ω) hgm hdm.neg hgmono hdanti hgb hdb
    have hintg : ∫ ω, g ω ∂P = P.real (A a) := by
      simp only [hg]
      exact integral_indicator_one (hA a)
    have hintd : Integrable d P := hintf1.sub hintf
    have hintgd : Integrable (fun ω => g ω * d ω) P := by
      refine int_bdd P (hgm.mul hdm) (B1 + B) (fun ω => ?_)
      rw [abs_mul]
      have : |g ω| ≤ 1 := by simp only [hg, Set.indicator_apply]; split_ifs <;> simp
      calc |g ω| * |d ω| ≤ 1 * |d ω| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = |d ω| := one_mul _
        _ ≤ |f1 (X ω)| + |f (X ω)| := abs_sub _ _
        _ ≤ B1 + B := add_le_add (bdd_filter A f1 T ω) (bdd_filter A f T ω)
    have hgd : ∫ ω, g ω * d ω ∂P ≤ P.real (A a) * ∫ ω, d ω ∂P := by
      have h1 : ∫ ω, g ω * (- d ω) ∂P = - ∫ ω, g ω * d ω ∂P := by
        rw [← integral_neg]; congr 1; funext ω; ring
      rw [h1, integral_neg, hintg] at hHarris
      linarith
    have hdi : ∫ ω, d ω ∂P = ∫ ω, f1 (X ω) ∂P - ∫ ω, f (X ω) ∂P := integral_sub hintf1 hintf
    have hmain : ∫ ω, f ((insert a T).filter (fun i => ω ∈ A i)) ∂P
        = ∫ ω, f (X ω) ∂P + ∫ ω, g ω * d ω ∂P := by
      simp_rw [hpt]
      exact integral_add hintf hintgd
    have hx0 : 0 ≤ P.real (A a) := measureReal_nonneg
    have hx1 : P.real (A a) ≤ 1 := measureReal_le_one
    have ih0 := ih f hf
    have ih1 := ih f1 hf1sub
    rw [Gsum_insert ha, hmain]
    simp only [hf1] at ih1
    calc ∫ ω, f (X ω) ∂P + ∫ ω, g ω * d ω ∂P
        ≤ ∫ ω, f (X ω) ∂P + P.real (A a) * (∫ ω, f1 (X ω) ∂P - ∫ ω, f (X ω) ∂P) := by
          rw [hdi] at hgd; linarith
      _ = (1 - P.real (A a)) * ∫ ω, f (X ω) ∂P + P.real (A a) * ∫ ω, f1 (X ω) ∂P := by ring
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left ih0 (sub_nonneg.2 hx1)
          have h2 := mul_le_mul_of_nonneg_left ih1 hx0
          simp only [hX, hf1] at *
          linarith

end abstract43


lemma Gsum_univ {n : ℕ} (x : Fin n → ℝ) (f : Finset (Fin n) → ℝ) :
    Gsum x f Finset.univ = F f x := by
  classical
  unfold Gsum F
  rw [Finset.powerset_univ]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  congr 1
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext i; simp
  · refine Finset.prod_congr ?_ (fun _ _ => rfl)
    ext i; simp

end UniversalSubmod.Dev.Thm12A

namespace UniversalSubmod

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared

open Classical in
/-- **Lemma 4.3** (Christofides–Vaggelatou via FKG; Adamczyk, Ueltzen, Vondrák, *Optimal universal
sets for submodular functions*, manuscript of November 3, 2026, Lemma 4.3, p.14). Let
`U₁, …, U_m` be independent random variables and `ψ : ℝ^m → {0,1}^n` measurable and monotone.
For `X := ψ(U₁, …, U_m)` and `x_i := P[X_i = 1]`, every submodular `f : {0,1}^n → ℝ` with
multilinear extension `F` satisfies `E[f(X)] ≤ F(x)`.

**Formalization Note.** The `U_j` are real random variables indexed by a finite type `ι` (so `m`
is `Fintype.card ι`), independent in Mathlib's `iIndepFun`, and measurable. The monotone map `ψ`
is given by its coordinate up-sets: `A i ⊆ ι → ℝ` is measurable and upward closed for the
coordinatewise order, and `X_i = 1` iff `(U_j)_j ∈ A i`; this is exactly a monotone measurable
`ψ : ℝ^ι → {0,1}^n`. The set `X ⊆ [n]` is `{i | (U_j)_j ∈ A i}` as a `Finset (Fin n)`, `f` is the
published `Submodular` function on `Finset (Fin n)` (no sign condition), and `F` is the published
multilinear extension `NonmonotoneSubmod.Shared.F`. `x_i` is `P.real {ω | (U_j ω)_j ∈ A i}`. -/
theorem inl_lemma_4_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] {n : ℕ} (U : ι → Ω → ℝ) (hU : ∀ j, Measurable (U j))
    (hind : iIndepFun U P)
    (A : Fin n → Set (ι → ℝ)) (hA : ∀ i, MeasurableSet (A i))
    (hmono : ∀ i, ∀ w w', w ≤ w' → w ∈ A i → w' ∈ A i)
    (f : Finset (Fin n) → ℝ) (hf : Submodular f) :
    ∫ ω, f (Finset.univ.filter (fun i => (fun j => U j ω) ∈ A i)) ∂P
      ≤ F f (fun i => P.real {ω | (fun j => U j ω) ∈ A i}) := by
  set W : Ω → (ι → ℝ) := fun ω j => U j ω with hW
  have hWm : Measurable W := measurable_pi_lambda _ hU
  have hmap : P.map W = Measure.pi (fun j => P.map (U j)) :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun j => (hU j).aemeasurable)).1 hind
  haveI : ∀ j, IsProbabilityMeasure (P.map (U j)) := fun j =>
    Measure.isProbabilityMeasure_map (hU j).aemeasurable
  haveI : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hWm.aemeasurable
  have hH : Dev.Thm12A.Harris (P.map W) := by
    rw [hmap]
    exact Dev.Thm12A.harris_pi_fintype _ (fun j => Dev.Thm12A.harris_real _)
  have hf' : ∀ S V : Finset (Fin n), f (S ∪ V) + f (S ∩ V) ≤ f S + f V := by
    intro S V; convert hf S V
  have key := Dev.Thm12A.abstract43 (P.map W) hH A hA hmono Finset.univ f hf'
  rw [Dev.Thm12A.Gsum_univ] at key
  have hmeas : Measurable (fun w : ι → ℝ => f (Finset.univ.filter (fun i => w ∈ A i))) :=
    Dev.Thm12A.meas_filter A hA f Finset.univ
  have e1 : ∫ w, f (Finset.univ.filter (fun i => w ∈ A i)) ∂(P.map W)
      = ∫ ω, f (Finset.univ.filter (fun i => (fun j => U j ω) ∈ A i)) ∂P :=
    integral_map hWm.aemeasurable hmeas.aestronglyMeasurable
  have e2 : ∀ i, (P.map W).real (A i) = P.real {ω | (fun j => U j ω) ∈ A i} := by
    intro i
    simp only [Measure.real]
    rw [Measure.map_apply hWm (hA i)]
    rfl
  rw [e1] at key
  simpa only [e2] using key

end UniversalSubmod
end

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Thm12C

open Finset

/-- indicator of a boolean -/
noncomputable def ind (b : Bool) : ℝ := if b then 1 else 0

lemma ind_nonneg (b : Bool) : 0 ≤ ind b := by cases b <;> simp [ind]
lemma ind_sq (b : Bool) : ind b * ind b = ind b := by cases b <;> simp [ind]

/-- weight of a Bernoulli(p) configuration -/
noncomputable def wt (k : ℕ) (p : ℝ) (z : Fin k → Bool) : ℝ := ∏ l, if z l then p else 1 - p

lemma wt_nonneg (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : Fin k → Bool) : 0 ≤ wt k p z := by
  unfold wt
  refine Finset.prod_nonneg (fun l _ => ?_)
  split_ifs
  · exact hp0
  · linarith

lemma sum_prod_ind (k : ℕ) (φ : Fin k → Bool → ℝ) :
    ∑ z : Fin k → Bool, ∏ l, φ l (z l) = ∏ l, (φ l true + φ l false) := by
  have := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset Bool)) (fun l b => φ l b)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  simp

lemma wt_sum (k : ℕ) (p : ℝ) : ∑ z : Fin k → Bool, wt k p z = 1 := by
  unfold wt
  rw [sum_prod_ind k (fun _ b => if b then p else 1 - p)]
  simp

lemma mgf (k : ℕ) (p : ℝ) (c : Fin k → ℝ) (t : ℝ) :
    ∑ z : Fin k → Bool, wt k p z * Real.exp (t * ∑ l, c l * ind (z l)) =
      ∏ l, (1 - p + p * Real.exp (t * c l)) := by
  have h1 : ∀ z : Fin k → Bool, wt k p z * Real.exp (t * ∑ l, c l * ind (z l)) =
      ∏ l, ((if z l then p else 1 - p) * Real.exp (t * (c l * ind (z l)))) := by
    intro z
    unfold wt
    rw [Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [sum_prod_ind k (fun l b => (if b then p else 1 - p) * Real.exp (t * (c l * ind b)))]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  simp [ind]
  ring

lemma chernoff (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (c : Fin k → ℝ) (a t : ℝ) (ht : 0 ≤ t) :
    ∑ z : Fin k → Bool, wt k p z * (if a ≤ ∑ l, c l * ind (z l) then 1 else 0) ≤
      Real.exp (-(t * a)) * ∏ l, (1 - p + p * Real.exp (t * c l)) := by
  rw [← mgf, Finset.mul_sum]
  refine Finset.sum_le_sum (fun z _ => ?_)
  have hw := wt_nonneg k p hp0 hp1 z
  by_cases h : a ≤ ∑ l, c l * ind (z l)
  · rw [if_pos h, mul_one]
    have : Real.exp (-(t * a)) * Real.exp (t * ∑ l, c l * ind (z l)) ≥ 1 := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    nlinarith
  · rw [if_neg h, mul_zero]
    positivity

lemma prod_bound (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (d : Fin k → ℝ) :
    ∏ l, (1 - p + p * Real.exp (d l)) ≤ Real.exp (p * ∑ l, (Real.exp (d l) - 1)) := by
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun l _ => ?_) (fun l _ => ?_)
  · have := Real.exp_pos (d l)
    nlinarith
  · have := Real.add_one_le_exp (p * (Real.exp (d l) - 1))
    linarith

lemma e_bounds : 2.718 < Real.exp 1 ∧ Real.exp 1 < 2.7183 ∧ Real.exp (-1) < 0.368 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  refine ⟨by linarith, by linarith, ?_⟩
  have h3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-1)
  nlinarith

lemma size_low (k : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑ z : Fin k → Bool, wt k p z * (if ∑ l, ind (z l) < p * k / 2 then 1 else 0) ≤
      Real.exp (-(p ^ 2 * k / 8)) := by
  obtain ⟨e1, e2, e3⟩ := e_bounds
  have hch := chernoff k p hp0.le hp1 (fun _ => -1) (-(p * k / 2)) 1 zero_le_one
  have hle : ∑ z : Fin k → Bool, wt k p z * (if ∑ l, ind (z l) < p * k / 2 then 1 else 0) ≤
      ∑ z : Fin k → Bool, wt k p z * (if -(p * k / 2) ≤ ∑ l, (fun _ : Fin k => (-1 : ℝ)) l * ind (z l) then 1 else 0) := by
    refine Finset.sum_le_sum (fun z _ => ?_)
    have hw := wt_nonneg k p hp0.le hp1 z
    refine mul_le_mul_of_nonneg_left ?_ hw
    by_cases h : ∑ l, ind (z l) < p * k / 2
    · rw [if_pos h, if_pos]
      simp only [neg_mul, one_mul, Finset.sum_neg_distrib]
      linarith
    · rw [if_neg h]; split_ifs <;> simp
  refine hle.trans (hch.trans ?_)
  have hpb := prod_bound k p hp0.le hp1 (fun _ => 1 * (-1))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hpb
  refine le_trans (mul_le_mul_of_nonneg_left hpb (Real.exp_pos _).le) ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have : p * (k * (Real.exp (1 * -1) - 1)) + -(1 * -(p * k / 2)) ≤ -(p ^ 2 * k / 8) := by
    have h1 : Real.exp (1 * -1) < 0.368 := by simpa using e3
    have hpk : p ^ 2 * k ≤ p * k := by nlinarith [mul_nonneg hp0.le hk]
    nlinarith [mul_nonneg hp0.le hk, mul_nonneg (mul_nonneg hp0.le hk) (sub_nonneg.2 h1.le)]
  linarith

lemma size_high (k : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑ z : Fin k → Bool, wt k p z * (if 2 * p * k < ∑ l, ind (z l) then 1 else 0) ≤
      Real.exp (-(p ^ 2 * k / 8)) := by
  obtain ⟨e1, e2, e3⟩ := e_bounds
  have hch := chernoff k p hp0.le hp1 (fun _ => 1) (2 * p * k) 1 zero_le_one
  have hle : ∑ z : Fin k → Bool, wt k p z * (if 2 * p * k < ∑ l, ind (z l) then 1 else 0) ≤
      ∑ z : Fin k → Bool, wt k p z * (if 2 * p * k ≤ ∑ l, (fun _ : Fin k => (1 : ℝ)) l * ind (z l) then 1 else 0) := by
    refine Finset.sum_le_sum (fun z _ => ?_)
    have hw := wt_nonneg k p hp0.le hp1 z
    refine mul_le_mul_of_nonneg_left ?_ hw
    by_cases h : 2 * p * k < ∑ l, ind (z l)
    · rw [if_pos h, if_pos]
      simp only [one_mul]
      linarith
    · rw [if_neg h]; split_ifs <;> simp
  refine hle.trans (hch.trans ?_)
  have hpb := prod_bound k p hp0.le hp1 (fun _ => 1 * 1)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hpb
  refine le_trans (mul_le_mul_of_nonneg_left hpb (Real.exp_pos _).le) ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have : -(1 * (2 * p * k)) + p * (k * (Real.exp (1 * 1) - 1)) ≤ -(p ^ 2 * k / 8) := by
    have h1 : Real.exp (1 * 1) < 2.7183 := by simpa using e2
    have hpk : p ^ 2 * k ≤ p * k := by nlinarith [mul_nonneg hp0.le hk]
    nlinarith [mul_nonneg hp0.le hk, mul_nonneg (mul_nonneg hp0.le hk) (sub_nonneg.2 h1.le)]
  linarith

lemma inter_bound (k : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (x : Fin k → Bool)
    (hx : ∑ l, ind (x l) ≤ 2 * p * k) :
    ∑ z : Fin k → Bool, wt k p z * (if 4 * p ^ 2 * k < ∑ l, ind (x l) * ind (z l) then 1 else 0) ≤
      Real.exp (-(p ^ 2 * k / 8)) := by
  obtain ⟨e1, e2, e3⟩ := e_bounds
  have hch := chernoff k p hp0.le hp1 (fun l => ind (x l)) (4 * p ^ 2 * k) 1 zero_le_one
  have hle : ∑ z : Fin k → Bool, wt k p z *
      (if 4 * p ^ 2 * k < ∑ l, ind (x l) * ind (z l) then 1 else 0) ≤
      ∑ z : Fin k → Bool, wt k p z *
        (if 4 * p ^ 2 * k ≤ ∑ l, (fun l => ind (x l)) l * ind (z l) then 1 else 0) := by
    refine Finset.sum_le_sum (fun z _ => ?_)
    have hw := wt_nonneg k p hp0.le hp1 z
    refine mul_le_mul_of_nonneg_left ?_ hw
    by_cases h : 4 * p ^ 2 * k < ∑ l, ind (x l) * ind (z l)
    · rw [if_pos h, if_pos h.le]
    · rw [if_neg h]; split_ifs <;> simp
  refine hle.trans (hch.trans ?_)
  have hpb := prod_bound k p hp0.le hp1 (fun l => 1 * ind (x l))
  have hsum : ∑ l, (Real.exp (1 * ind (x l)) - 1) = (Real.exp 1 - 1) * ∑ l, ind (x l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    cases x l <;> simp [ind]
  rw [hsum] at hpb
  refine le_trans (mul_le_mul_of_nonneg_left hpb (Real.exp_pos _).le) ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h2 : p * ((Real.exp 1 - 1) * ∑ l, ind (x l)) ≤ p * ((Real.exp 1 - 1) * (2 * p * k)) := by
    have : 0 ≤ Real.exp 1 - 1 := by linarith
    gcongr
  have : -(1 * (4 * p ^ 2 * k)) + p * ((Real.exp 1 - 1) * (2 * p * k)) ≤ -(p ^ 2 * k / 8) := by
    have hpk : 0 ≤ p ^ 2 * k := by positivity
    nlinarith [mul_nonneg hpk (sub_nonneg.2 e2.le)]
  linarith


lemma exp_small (n k : ℕ) (η : ℝ) (hn : 2 ≤ n) (hη : 0 < η) (hη1 : η < 1)
    (hk : 2000 * Real.log n ≤ η ^ 2 * k) :
    Real.exp (-((η / 8) ^ 2 * k / 8)) ≤ 1 / (n : ℝ) ^ 3 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 3 * Real.log n ≤ (η / 8) ^ 2 * k / 8 := by
    have : (η / 8) ^ 2 * k / 8 = η ^ 2 * k / 512 := by ring
    rw [this]
    have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    nlinarith
  calc Real.exp (-((η / 8) ^ 2 * k / 8)) ≤ Real.exp (-(3 * Real.log n)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = 1 / (n : ℝ) ^ 3 := by
        rw [Real.exp_neg, show 3 * Real.log n = ((3 : ℕ) : ℝ) * Real.log n by norm_num,
          Real.exp_nat_mul, Real.exp_log (by linarith)]
        simp

lemma exists_seq (n k : ℕ) (η : ℝ) (hn : 2 ≤ n) (hη : 0 < η) (hη1 : η < 1)
    (hk : 2000 * Real.log n ≤ η ^ 2 * k) :
    ∀ m, m ≤ n → ∃ x : ℕ → (Fin k → Bool),
      (∀ i < m, (η / 8) * k / 2 ≤ ∑ l, ind (x i l) ∧ ∑ l, ind (x i l) ≤ 2 * (η / 8) * k) ∧
      ∀ i j, i < j → j < m → ∑ l, ind (x i l) * ind (x j l) ≤ 4 * (η / 8) ^ 2 * k := by
  set p : ℝ := η / 8 with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := by rw [hp]; linarith
  have hB := exp_small n k η hn hη hη1 hk
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨fun _ _ => true, fun i hi => absurd hi (by omega), fun i j _ h => absurd h (by omega)⟩
  | succ m ih =>
    intro hm
    obtain ⟨x, hx1, hx2⟩ := ih (by omega)
    -- badness function
    let β : (Fin k → Bool) → ℝ := fun z =>
      (if ∑ l, ind (z l) < p * k / 2 then 1 else 0) + (if 2 * p * k < ∑ l, ind (z l) then 1 else 0)
      + ∑ i ∈ Finset.range m, (if 4 * p ^ 2 * k < ∑ l, ind (x i l) * ind (z l) then 1 else 0)
    have hsum : ∑ z : Fin k → Bool, wt k p z * β z ≤ (m + 2) * (1 / (n : ℝ) ^ 3) := by
      have e1 : ∑ z : Fin k → Bool, wt k p z * β z =
          (∑ z : Fin k → Bool, wt k p z * (if ∑ l, ind (z l) < p * k / 2 then 1 else 0))
          + (∑ z : Fin k → Bool, wt k p z * (if 2 * p * k < ∑ l, ind (z l) then 1 else 0))
          + ∑ i ∈ Finset.range m, ∑ z : Fin k → Bool, wt k p z *
              (if 4 * p ^ 2 * k < ∑ l, ind (x i l) * ind (z l) then 1 else 0) := by
        simp only [β, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        rw [Finset.sum_comm]
      rw [e1]
      have a1 := size_low k p hp0 hp1
      have a2 := size_high k p hp0 hp1
      have a3 : ∀ i ∈ Finset.range m, ∑ z : Fin k → Bool, wt k p z *
          (if 4 * p ^ 2 * k < ∑ l, ind (x i l) * ind (z l) then 1 else 0) ≤ 1 / (n : ℝ) ^ 3 := by
        intro i hi
        exact (inter_bound k p hp0 hp1 (x i) (hx1 i (Finset.mem_range.1 hi)).2).trans hB
      have a4 := Finset.sum_le_sum a3
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at a4
      nlinarith
    have hlt : (m + 2 : ℝ) * (1 / (n : ℝ) ^ 3) < 1 := by
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hm' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hm
      have hpos : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
      rw [mul_one_div, div_lt_one hpos]
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    have hex : ∃ z : Fin k → Bool, β z < 1 := by
      by_contra hcon
      push Not at hcon
      have : 1 ≤ ∑ z : Fin k → Bool, wt k p z * β z := by
        calc (1 : ℝ) = ∑ z : Fin k → Bool, wt k p z := (wt_sum k p).symm
          _ = ∑ z : Fin k → Bool, wt k p z * 1 := by simp
          _ ≤ _ := Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hcon z)
              (wt_nonneg k p hp0.le hp1 z))
      linarith
    obtain ⟨z, hz⟩ := hex
    -- all indicator terms vanish
    have t1 : ¬ (∑ l, ind (z l) < p * k / 2) := by
      intro h
      have h2 : 0 ≤ (if 2 * p * k < ∑ l, ind (z l) then (1 : ℝ) else 0) := by split_ifs <;> simp
      have h3 : 0 ≤ ∑ i ∈ Finset.range m, (if 4 * p ^ 2 * k < ∑ l, ind (x i l) * ind (z l) then (1 : ℝ) else 0) :=
        Finset.sum_nonneg (fun i _ => by split_ifs <;> simp)
      simp only [β, if_pos h] at hz
      linarith
    have t2 : ¬ (2 * p * k < ∑ l, ind (z l)) := by
      intro h
      have h2 : 0 ≤ (if ∑ l, ind (z l) < p * k / 2 then (1 : ℝ) else 0) := by split_ifs <;> simp
      have h3 : 0 ≤ ∑ i ∈ Finset.range m, (if 4 * p ^ 2 * k < ∑ l, ind (x i l) * ind (z l) then (1 : ℝ) else 0) :=
        Finset.sum_nonneg (fun i _ => by split_ifs <;> simp)
      simp only [β, if_pos h] at hz
      linarith
    have t3 : ∀ i < m, ¬ (4 * p ^ 2 * k < ∑ l, ind (x i l) * ind (z l)) := by
      intro i hi h
      have h2 : 0 ≤ (if ∑ l, ind (z l) < p * k / 2 then (1 : ℝ) else 0) := by split_ifs <;> simp
      have h2' : 0 ≤ (if 2 * p * k < ∑ l, ind (z l) then (1 : ℝ) else 0) := by split_ifs <;> simp
      have h3 : (1 : ℝ) ≤ ∑ i ∈ Finset.range m, (if 4 * p ^ 2 * k < ∑ l, ind (x i l) * ind (z l) then (1 : ℝ) else 0) := by
        calc (1 : ℝ) = (if 4 * p ^ 2 * k < ∑ l, ind (x i l) * ind (z l) then (1 : ℝ) else 0) := by
              rw [if_pos h]
          _ ≤ _ := Finset.single_le_sum (f := fun i => (if 4 * p ^ 2 * k < ∑ l, ind (x i l) * ind (z l) then (1 : ℝ) else 0))
              (fun i _ => by split_ifs <;> simp) (Finset.mem_range.2 hi)
      simp only [β] at hz
      linarith
    refine ⟨Function.update x m z, ?_, ?_⟩
    · intro i hi
      by_cases him : i = m
      · subst him
        simp only [Function.update_self]
        exact ⟨by linarith [not_lt.1 t1], by linarith [not_lt.1 t2]⟩
      · rw [Function.update_of_ne him]
        exact hx1 i (by omega)
    · intro i j hij hj
      by_cases hjm : j = m
      · subst hjm
        rw [Function.update_of_ne (by omega), Function.update_self]
        exact not_lt.1 (t3 i hij)
      · rw [Function.update_of_ne (by omega), Function.update_of_ne hjm]
        exact hx2 i j hij (by omega)

end UniversalSubmod.Dev.Thm12C

namespace UniversalSubmod

open scoped RealInnerProductSpace

/-- **Lemma 4.2** (nonnegative near-orthogonal unit vectors; Adamczyk, Ueltzen, Vondrák, *Optimal
universal sets for submodular functions*, manuscript of November 3, 2026, Lemma 4.2, p.12; proof
p.12). For every integer `n ≥ 2`, `ε ∈ (0,1)` and positive integer `k ≥ c ε⁻² ln n` there exist
vectors `v₁, …, vₙ ∈ ℝ^k` with nonnegative entries such that `‖vᵢ‖ = 1` and `0 ≤ ⟨vᵢ,vⱼ⟩ ≤ ε`
for `i ≠ j`.

**Formalization Note.** `ℝ^k` is `EuclideanSpace ℝ (Fin k)`; the vectors are indexed by `Fin n`;
nonnegative entries is `0 ≤ v i l`; the bound `⟨vᵢ,vⱼ⟩ ≥ 0` follows from it and is not restated.
The printed constant is `c = 100`; this statement uses `c = 2000` (any absolute constant serves
the application in Theorem 1.2, and the counting proof here is not tuned). The parameter is named
`η`. -/
theorem inl_lemma_4_2 (n k : ℕ) (hn : 2 ≤ n) (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hk : 2000 * Real.log n ≤ η ^ 2 * k) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin k),
      (∀ i, ‖v i‖ = 1) ∧ (∀ i l, 0 ≤ v i l) ∧ ∀ i j, i ≠ j → ⟪v i, v j⟫ ≤ η := by
  obtain ⟨x, hx1, hx2⟩ := Dev.Thm12C.exists_seq n k η hn hη hη1 hk n le_rfl
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hkpos : (0 : ℝ) < k := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg η]
  set p : ℝ := η / 8 with hp
  have hp0 : 0 < p := by positivity
  set s : Fin n → ℝ := fun i => ∑ l, Dev.Thm12C.ind (x i l) with hs
  have hs_lo : ∀ i : Fin n, p * k / 2 ≤ s i := fun i => (hx1 i i.2).1
  have hspos : ∀ i : Fin n, 0 < s i := fun i => lt_of_lt_of_le (by positivity) (hs_lo i)
  refine ⟨fun i => WithLp.toLp 2 (fun l => Dev.Thm12C.ind (x i l) / Real.sqrt (s i)), ?_, ?_, ?_⟩
  · intro i
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp only [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (hspos i).le]
    have : ∀ l, Dev.Thm12C.ind (x i l) ^ 2 = Dev.Thm12C.ind (x i l) := fun l => by
      rw [sq]; exact Dev.Thm12C.ind_sq _
    simp only [this, ← Finset.sum_div]
    exact div_self (hspos i).ne'
  · intro i l
    show 0 ≤ Dev.Thm12C.ind (x i l) / Real.sqrt (s i)
    exact div_nonneg (Dev.Thm12C.ind_nonneg _) (Real.sqrt_nonneg _)
  · intro i j hij
    have hinner : ⟪(WithLp.toLp 2 (fun l => Dev.Thm12C.ind (x i l) / Real.sqrt (s i)) :
        EuclideanSpace ℝ (Fin k)), WithLp.toLp 2 (fun l => Dev.Thm12C.ind (x j l) / Real.sqrt (s j))⟫
        = (∑ l, Dev.Thm12C.ind (x i l) * Dev.Thm12C.ind (x j l)) /
          (Real.sqrt (s i) * Real.sqrt (s j)) := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      have h1 := (Real.sqrt_pos.2 (hspos i)).ne'
      have h2 := (Real.sqrt_pos.2 (hspos j)).ne'
      field_simp
    rw [hinner]
    have hden : p * k / 2 ≤ Real.sqrt (s i) * Real.sqrt (s j) := by
      rw [← Real.sqrt_mul (hspos i).le]
      apply Real.le_sqrt_of_sq_le
      have h1 := hs_lo i
      have h2 := hs_lo j
      have : (p * k / 2) ^ 2 ≤ s i * s j := by
        have a0 : 0 ≤ p * k / 2 := by positivity
        calc (p * k / 2) ^ 2 = (p * k / 2) * (p * k / 2) := sq _
          _ ≤ s i * s j := mul_le_mul h1 h2 a0 (hspos i).le
      exact this
    have hnum : ∑ l, Dev.Thm12C.ind (x i l) * Dev.Thm12C.ind (x j l) ≤ 4 * p ^ 2 * k := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact hx2 i j h j.2
      · have := hx2 j i h i.2
        simpa [mul_comm] using this
    have hnn : 0 ≤ ∑ l, Dev.Thm12C.ind (x i l) * Dev.Thm12C.ind (x j l) :=
      Finset.sum_nonneg (fun l _ => mul_nonneg (Dev.Thm12C.ind_nonneg _) (Dev.Thm12C.ind_nonneg _))
    have hdpos : 0 < p * k / 2 := by positivity
    calc (∑ l, Dev.Thm12C.ind (x i l) * Dev.Thm12C.ind (x j l)) /
          (Real.sqrt (s i) * Real.sqrt (s j))
        ≤ (4 * p ^ 2 * k) / (p * k / 2) := by
          apply div_le_div₀ (by positivity) hnum hdpos hden
      _ = η := by rw [hp]; field_simp; ring

end UniversalSubmod
end

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Cor41

open MeasureTheory ProbabilityTheory Cohen2019.Robust NonmonotoneSubmod.Shared
open scoped RealInnerProductSpace

lemma meas_comp {α : Type*} [MeasurableSpace α] {n : ℕ} (φ : α → Finset (Fin n))
    (hφ : ∀ i, MeasurableSet {a | i ∈ φ a}) (f : Finset (Fin n) → ℝ) :
    Measurable (fun a => f (φ a)) := by
  classical
  have h : (fun a => f (φ a)) = fun a => ∑ S : Finset (Fin n), if φ a = S then f S else 0 := by
    funext a
    rw [Finset.sum_eq_single (φ a)]
    · simp
    · intro S _ hS; simp [Ne.symm hS]
    · simp
  rw [h]
  refine Finset.measurable_sum _ (fun S _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {a | φ a = S} = ⋂ i, {a | i ∈ φ a ↔ i ∈ S} := by
    ext a; simp [Finset.ext_iff]
  rw [this]
  refine MeasurableSet.iInter (fun i => ?_)
  by_cases hi : i ∈ S
  · simpa [hi] using hφ i
  · have e : {a | i ∈ φ a ↔ i ∈ S} = {a | i ∈ φ a}ᶜ := by ext a; simp [hi]
    rw [e]; exact (hφ i).compl

lemma integrable_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) (C : ℝ) (h : ∀ a, |g a| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (ae_of_all _ (fun a => by simpa [Real.norm_eq_abs] using h a))

lemma gauss_Iic (u : ℝ) : (gaussianReal 0 1).real (Set.Iic u) = Phi u := by
  unfold Phi; rw [cdf_eq_real]

lemma phi_nonneg (u : ℝ) : 0 ≤ Phi u := by unfold Phi; exact cdf_nonneg _ _
lemma phi_le_one (u : ℝ) : Phi u ≤ 1 := by unfold Phi; exact cdf_le_one _ _

lemma gauss_singleton (x : ℝ) : gaussianReal 0 1 {x} = 0 :=
  gaussianReal_absolutelyContinuous 0 one_ne_zero (by simp)

lemma gauss_Iio_ae (u : ℝ) : Set.Iio u =ᵐ[gaussianReal 0 1] Set.Iic u :=
  Iio_ae_eq_Iic' (gauss_singleton u)

lemma gauss_Ioc (a b : ℝ) (hab : a ≤ b) :
    (gaussianReal 0 1).real (Set.Ioc a b) = Phi b - Phi a := by
  have : Set.Iic b \ Set.Iic a = Set.Ioc a b := by
    ext x; simp [Set.mem_Ioc, and_comm]
  rw [← this, measureReal_sdiff (Set.Iic_subset_Iic.2 hab) measurableSet_Iic,
    gauss_Iic, gauss_Iic]

lemma phi_strictMono : StrictMono Phi := by
  intro a b hab
  have h1 : 0 < (gaussianReal 0 1).real (Set.Ioc a b) := by
    have h2 : (gaussianReal 0 1) (Set.Ioc a b) ≠ 0 := by
      intro h
      have := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) one_ne_zero h
      simp at this
      linarith
    exact ENNReal.toReal_pos h2 (measure_ne_top _ _)
  rw [gauss_Ioc a b hab.le] at h1
  linarith

lemma phi_le_iff (a b : ℝ) : Phi a ≤ Phi b ↔ a ≤ b := phi_strictMono.le_iff_le

lemma gauss_Iio (u : ℝ) : (gaussianReal 0 1).real (Set.Iio u) = Phi u := by
  rw [← gauss_Iic]; exact measureReal_congr (gauss_Iio_ae u)

lemma gauss_Ici (u : ℝ) : (gaussianReal 0 1).real (Set.Ici u) = 1 - Phi u := by
  rw [← gauss_Iio, ← Set.compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ]

lemma phi_zero : Phi 0 = 1 / 2 := by
  have h2 : gaussianReal 0 1 (Set.Iic 0) = gaussianReal 0 1 (Set.Ici 0) := by
    have := gaussianReal_map_neg (μ := 0) (v := 1)
    rw [neg_zero] at this
    conv_lhs => rw [← this]
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1; ext x; simp
  have h : (gaussianReal 0 1).real (Set.Iic 0) = (gaussianReal 0 1).real (Set.Ici 0) := by
    simp [Measure.real, h2]
  rw [gauss_Iic, gauss_Ici] at h
  linarith

lemma phi_sq_bound (u : ℝ) : (Phi u - 1 / 2) ^ 2 ≤ u ^ 2 / (2 * Real.pi) := by
  have hc : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hdens : ∀ x : ℝ, ‖gaussianPDFReal 0 1 x‖ ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    intro x
    have hh : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) hh
  have key : ∀ a b : ℝ, a ≤ b → Phi b - Phi a ≤ (b - a) * (Real.sqrt (2 * Real.pi))⁻¹ := by
    intro a b hab
    rw [← gauss_Ioc a b hab, Measure.real, gaussianReal_apply_eq_integral 0 one_ne_zero _,
      ENNReal.toReal_ofReal]
    · have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc a b)
        (f := gaussianPDFReal 0 1) (C := (Real.sqrt (2 * Real.pi))⁻¹)
        (by simp) (fun x _ => hdens x)
      rw [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hab] at this
      linarith [le_abs_self (∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x)]
    · exact setIntegral_nonneg measurableSet_Ioc (fun x _ => gaussianPDFReal_nonneg _ _ _)
  have hb : |Phi u - 1 / 2| ≤ |u| * (Real.sqrt (2 * Real.pi))⁻¹ := by
    rcases le_total 0 u with h | h
    · have k := key 0 u h
      have m := phi_strictMono.monotone h
      rw [phi_zero] at k m
      rw [abs_of_nonneg (by linarith), abs_of_nonneg h]
      linarith
    · have k := key u 0 h
      have m := phi_strictMono.monotone h
      rw [phi_zero] at k m
      rw [abs_of_nonpos (by linarith), abs_of_nonpos h]
      linarith
  calc (Phi u - 1/2)^2 = |Phi u - 1/2|^2 := (sq_abs _).symm
    _ ≤ (|u| * (Real.sqrt (2 * Real.pi))⁻¹)^2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = u^2 / (2 * Real.pi) := by
      rw [mul_pow, sq_abs, inv_pow, Real.sq_sqrt (by positivity)]; ring


lemma pi_integral_filter {n : ℕ} (f : Finset (Fin n) → ℝ) (u : ℝ) :
    ∫ y : Fin n → ℝ, f (Finset.univ.filter (fun i => u ≤ y i))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = F f (fun _ => 1 - Phi u) := by
  classical
  let φ : Finset (Fin n) → (Fin n → ℝ) → ℝ := fun S y =>
    ∏ i : Fin n, (if i ∈ S then (Set.Ici u).indicator (fun _ => (1:ℝ)) (y i)
      else (Set.Iio u).indicator (fun _ => (1:ℝ)) (y i))
  have key : ∀ y : Fin n → ℝ, f (Finset.univ.filter (fun i => u ≤ y i)) =
      ∑ S : Finset (Fin n), f S * φ S y := by
    intro y
    rw [Finset.sum_eq_single (Finset.univ.filter (fun i => u ≤ y i))]
    · have : φ (Finset.univ.filter (fun i => u ≤ y i)) y = 1 :=
        Finset.prod_eq_one (fun i _ => by by_cases h : u ≤ y i <;> simp [h])
      rw [this, mul_one]
    · intro S _ hS
      have : φ S y = 0 := by
        obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ Finset.univ.filter (fun i => u ≤ y i)) := by
          by_contra h; push Not at h; exact hS (Finset.ext h)
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        by_cases h1 : i ∈ S <;> by_cases h2 : u ≤ y i <;> simp_all
      rw [this, mul_zero]
    · simp
  have hmeas : ∀ S, Measurable (φ S) := by
    intro S
    refine Finset.measurable_prod _ (fun i _ => ?_)
    by_cases h : i ∈ S
    · simp only [h, if_true]
      exact (measurable_const.indicator measurableSet_Ici).comp (measurable_pi_apply i)
    · simp only [h, if_false]
      exact (measurable_const.indicator measurableSet_Iio).comp (measurable_pi_apply i)
  have hbound : ∀ S y, |φ S y| ≤ 1 := by
    intro S y
    simp only [φ, Finset.abs_prod]
    refine Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => ?_)
    split_ifs <;> simp [Set.indicator_apply] <;> split_ifs <;> simp
  simp_rw [key]
  rw [integral_finsetSum]
  · unfold F
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [integral_const_mul]
    congr 1
    have := integral_fintype_prod_eq_prod (μ := fun _ : Fin n => gaussianReal 0 1)
      (fun (i : Fin n) (x : ℝ) => if i ∈ S then (Set.Ici u).indicator (fun _ => (1:ℝ)) x
        else (Set.Iio u).indicator (fun _ => (1:ℝ)) x)
    refine this.trans (Finset.prod_congr rfl (fun i _ => ?_))
    by_cases h : i ∈ S
    · simp only [h, if_true]
      rw [integral_indicator_const _ measurableSet_Ici, gauss_Ici]; simp
    · simp only [h, if_false]
      rw [integral_indicator_const _ measurableSet_Iio, gauss_Iio]; simp
  · intro S _
    exact (integrable_bdd _ (hmeas S) 1 (hbound S)).const_mul _


def Sc {n : ℕ} (a b : ℝ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (if i = j then a^2 else 0) + b^2

lemma Sc_quad {n : ℕ} (a b : ℝ) (x : Fin n → ℝ) :
    dotProduct x (Matrix.mulVec (Sc a b) x) = a^2 * ∑ i, x i ^ 2 + b^2 * (∑ i, x i)^2 := by
  simp only [Sc, dotProduct, Matrix.mulVec, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    mul_add, Finset.mul_sum, Finset.sum_mul, ite_mul, zero_mul, mul_ite, mul_zero]
  simp [sq, Finset.sum_ite_eq, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum, Finset.sum_mul]

lemma Sc_psd {n : ℕ} (a b : ℝ) : (Sc (n := n) a b).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · ext i j; simp [Sc, Matrix.conjTranspose_apply, eq_comm]
  · simpa [Sc_quad] using by positivity

lemma law_gram {m n : ℕ} (w : Fin n → EuclideanSpace ℝ (Fin m)) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).map
      (fun z => (WithLp.toLp 2 (fun i => ⟪w i, z⟫) : EuclideanSpace ℝ (Fin n)))
      = multivariateGaussian 0 (Matrix.gram ℝ w) := by
  have hS := Matrix.posSemidef_gram ℝ w
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_multivariateGaussian hS, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have h1 : ∀ z : EuclideanSpace ℝ (Fin m),
      ⟪(WithLp.toLp 2 (fun i => ⟪w i, z⟫) : EuclideanSpace ℝ (Fin n)), t⟫ = ⟪z, ∑ i, t i • w i⟫ := by
    intro z
    rw [PiLp.inner_apply, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [WithLp.ofLp_toLp]
    rw [inner_smul_right, real_inner_comm z (w i)]
    simp [mul_comm]
  simp_rw [h1]
  rw [← charFun_apply, charFun_stdGaussian]
  have h2 := Matrix.star_dotProduct_gram_mulVec (𝕜 := ℝ) w t.ofLp t.ofLp
  simp only [star_trivial, real_inner_self_eq_norm_sq] at h2
  rw [h2, inner_zero_right]
  push_cast
  congr 1
  ring

lemma law_corr {n : ℕ} (a b : ℝ) :
    ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)).map
      (fun p : ℝ × (Fin n → ℝ) =>
        (WithLp.toLp 2 (fun i => a * p.2 i + b * p.1) : EuclideanSpace ℝ (Fin n)))
      = multivariateGaussian 0 (Sc a b) := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_multivariateGaussian (Sc_psd a b), charFun_apply,
    integral_map (by fun_prop) (by fun_prop)]
  have h1 : ∀ p : ℝ × (Fin n → ℝ),
      Complex.exp (↑⟪(WithLp.toLp 2 (fun i => a * p.2 i + b * p.1) : EuclideanSpace ℝ (Fin n)), t⟫ * Complex.I)
      = Complex.exp (↑(b * (∑ i, t i) * p.1) * Complex.I) *
        ∏ i, Complex.exp (↑(a * t i * p.2 i) * Complex.I) := by
    intro p
    rw [← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← add_mul, ← Complex.ofReal_add]
    congr 2
    simp only [PiLp.inner_apply, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [add_comm]
    congr 1 <;> refine Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [h1]
  rw [integral_prod_mul (fun y0 : ℝ => Complex.exp (↑(b * (∑ i, t i) * y0) * Complex.I))
    (fun y : Fin n → ℝ => ∏ i, Complex.exp (↑(a * t i * y i) * Complex.I))]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin n => gaussianReal 0 1)
    (fun (i : Fin n) (x : ℝ) => Complex.exp (↑(a * t i * x) * Complex.I))]
  have e1 : ∀ (c : ℝ), ∫ y : ℝ, Complex.exp (↑(c * y) * Complex.I) ∂(gaussianReal 0 1)
      = Complex.exp (-(c ^ 2 : ℝ) / 2) := by
    intro c
    have := charFun_gaussianReal (μ := 0) (v := 1) c
    rw [charFun_apply_real] at this
    simp only [Complex.ofReal_mul] at this ⊢
    rw [this]
    simp
    ring_nf
  simp_rw [e1]
  rw [← Complex.exp_sum, ← Complex.exp_add, inner_zero_right, Sc_quad]
  congr 1
  push_cast
  simp only [zero_mul, zero_sub, mul_pow, neg_div, Finset.sum_neg_distrib, ← Finset.sum_div,
    ← Finset.mul_sum]
  ring

lemma f_bdd {n : ℕ} (f : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : |f S| ≤ ∑ T, |f T| :=
  Finset.single_le_sum (f := fun T => |f T|) (fun T _ => abs_nonneg _) (Finset.mem_univ S)

lemma phi_meas : Measurable Phi := phi_strictMono.monotone.measurable

lemma semidefExt_Sc {n : ℕ} (f : Finset (Fin n) → ℝ) (a b : ℝ) (ha : 0 < a) (t : ℝ) :
    semidefExt f (fun _ => 1 - Phi t) (Sc a b)
      = ∫ y0 : ℝ, F f (fun _ => 1 - Phi ((t - b * y0) / a)) ∂(gaussianReal 0 1) := by
  unfold semidefExt
  rw [← law_corr a b]
  have hg : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (WithLp.toLp 2 (fun i => a * p.2 i + b * p.1) : EuclideanSpace ℝ (Fin n))) := by fun_prop
  have hm : Measurable (fun g : EuclideanSpace ℝ (Fin n) =>
      f (Finset.univ.filter (fun i => 1 - (1 - Phi t) ≤ Phi (g i)))) := by
    refine meas_comp (fun g : EuclideanSpace ℝ (Fin n) =>
      Finset.univ.filter (fun i => 1 - (1 - Phi t) ≤ Phi (g i))) (fun i => ?_) f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact measurableSet_le measurable_const (phi_meas.comp (by fun_prop))
  rw [integral_map hg.aemeasurable hm.aestronglyMeasurable]
  have e : ∀ p : ℝ × (Fin n → ℝ),
      f (Finset.univ.filter (fun i => 1 - (1 - Phi t) ≤ Phi
        ((WithLp.toLp 2 (fun i => a * p.2 i + b * p.1) : EuclideanSpace ℝ (Fin n)) i)))
      = f (Finset.univ.filter (fun i => (t - b * p.1) / a ≤ p.2 i)) := by
    intro p
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_sub_cancel, phi_le_iff,
      WithLp.ofLp_toLp, div_le_iff₀ ha]
    constructor <;> intro h <;> nlinarith
  simp_rw [e]
  have hm2 : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      f (Finset.univ.filter (fun i => (t - b * p.1) / a ≤ p.2 i))) := by
    refine meas_comp (fun p : ℝ × (Fin n → ℝ) =>
      Finset.univ.filter (fun i => (t - b * p.1) / a ≤ p.2 i)) (fun i => ?_) f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact measurableSet_le (by fun_prop) (by fun_prop)
  rw [integral_prod _ (integrable_bdd _ hm2 _ (fun p => f_bdd f _))]
  simp_rw [pi_integral_filter]


lemma gauss_int_id : Integrable (fun y : ℝ => y) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl

lemma gauss_int_sq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 1) := by
  have := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  simpa using this

lemma gauss_mean : ∫ y : ℝ, y ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal

lemma gauss_second : ∫ y : ℝ, y ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (memLp_id_gaussianReal (μ := 0) (v := 1) 2).aemeasurable] at h
  simpa [integral_id_gaussianReal] using h

lemma F_bdd {n : ℕ} (f : Finset (Fin n) → ℝ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |F f (fun _ => p)| ≤ ∑ T, |f T| := by
  unfold F
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun S _ => ?_))
  rw [abs_mul]
  have : |∏ i : Fin n, (if i ∈ S then p else 1 - p)| ≤ 1 := by
    rw [Finset.abs_prod]
    refine Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => ?_)
    split_ifs
    · rw [abs_of_nonneg hp0]; exact hp1
    · rw [abs_of_nonneg (by linarith)]; linarith
  calc |f S| * |∏ i : Fin n, (if i ∈ S then p else 1 - p)| ≤ |f S| * 1 :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |f S| := mul_one _

lemma F_meas {n : ℕ} (f : Finset (Fin n) → ℝ) {α : Type*} [MeasurableSpace α] (q : α → ℝ)
    (hq : Measurable q) : Measurable (fun y => F f (fun _ => q y)) := by
  unfold F
  refine Finset.measurable_sum _ (fun S _ => ?_)
  refine Measurable.const_mul (Finset.measurable_prod _ (fun i _ => ?_)) _
  split_ifs
  · exact hq
  · exact measurable_const.sub hq

lemma semidefExt_gram {n k : ℕ} (f : Finset (Fin n) → ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (t : ℝ) :
    semidefExt f (fun _ => 1 - Phi t) (Matrix.gram ℝ v)
      = ∫ z, f (threshSet v z t) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  unfold semidefExt
  rw [← law_gram v]
  have hg : Measurable (fun z : EuclideanSpace ℝ (Fin k) =>
      (WithLp.toLp 2 (fun i => ⟪v i, z⟫) : EuclideanSpace ℝ (Fin n))) := by fun_prop
  have hm : Measurable (fun g : EuclideanSpace ℝ (Fin n) =>
      f (Finset.univ.filter (fun i => 1 - (1 - Phi t) ≤ Phi (g i)))) := by
    refine meas_comp (fun g : EuclideanSpace ℝ (Fin n) =>
      Finset.univ.filter (fun i => 1 - (1 - Phi t) ≤ Phi (g i))) (fun i => ?_) f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact measurableSet_le measurable_const (phi_meas.comp (by fun_prop))
  rw [integral_map hg.aemeasurable hm.aestronglyMeasurable]
  congr 1
  funext z
  congr 1
  ext i
  simp [threshSet, phi_le_iff]


lemma F_ind {n : ℕ} (f : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    F f (fun i => if i ∈ S then (1 : ℝ) else 0) = f S := by
  unfold F
  rw [Finset.sum_eq_single S]
  · have : ∏ i : Fin n, (if i ∈ S then (if i ∈ S then (1 : ℝ) else 0)
        else 1 - (if i ∈ S then (1 : ℝ) else 0)) = 1 := by
      refine Finset.prod_eq_one (fun i _ => ?_)
      by_cases h : i ∈ S <;> simp [h]
    rw [this, mul_one]
  · intro T _ hT
    have : ∏ i : Fin n, (if i ∈ T then (if i ∈ S then (1 : ℝ) else 0)
        else 1 - (if i ∈ S then (1 : ℝ) else 0)) = 0 := by
      have : ∃ i, ¬ (i ∈ T ↔ i ∈ S) := by
        by_contra hc
        push Not at hc
        exact hT (Finset.ext hc)
      obtain ⟨i, hi⟩ := this
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      by_cases h1 : i ∈ T <;> by_cases h2 : i ∈ S <;> simp_all
    rw [this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ S) h

lemma F_half {n : ℕ} (f : Finset (Fin n) → ℝ) :
    F f (fun _ => 1 / 2) = (∑ S, f S) / 2 ^ n := by
  unfold F
  have : ∀ S : Finset (Fin n), ∏ i : Fin n, (if i ∈ S then (1 / 2 : ℝ) else 1 - 1 / 2)
      = 1 / 2 ^ n := by
    intro S
    have : ∀ i : Fin n, (if i ∈ S then (1 / 2 : ℝ) else 1 - 1 / 2) = 1 / 2 := by
      intro i; split_ifs <;> norm_num
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [one_div, one_div, inv_pow]
  simp only [this]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  ring

lemma F_lower {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - 2 * |q - 1 / 2|) * F f (fun _ => 1 / 2) ≤ F f (fun _ => q) := by
  set g : ℝ → ℝ := fun t => F f (fun _ => t) with hg
  have hc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g := by
    have := (concavity_segment f hf0 hf).2 (0 : Fin n → ℝ) (1 : Fin n → ℝ)
      (fun i => by simp) (fun i => by simp) (fun i => by simp)
    convert this using 2
    rename_i t
    simp only [hg]
    congr 1
    ext i
    simp
  have h0 : g 0 = f ∅ := by
    have := F_ind f ∅
    simpa [hg] using this
  have h1 : g 1 = f Finset.univ := by
    have := F_ind f Finset.univ
    simpa [hg] using this
  have hg0 : 0 ≤ g 0 := by rw [h0]; exact hf0 _
  have hg1 : 0 ≤ g 1 := by rw [h1]; exact hf0 _
  have hhalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h00 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  show (1 - 2 * |q - 1 / 2|) * g (1 / 2) ≤ g q
  rcases le_total q (1 / 2) with h | h
  · rw [abs_of_nonpos (by linarith)]
    have := hc.2 h00 hhalf (show 0 ≤ 1 - 2 * q by linarith) (show 0 ≤ 2 * q by linarith)
      (by ring)
    simp only [smul_eq_mul] at this
    have e : (1 - 2 * q) * 0 + 2 * q * (1 / 2) = q := by ring
    rw [e] at this
    nlinarith [mul_nonneg (show 0 ≤ 1 - 2 * q by linarith) hg0]
  · rw [abs_of_nonneg (by linarith)]
    have := hc.2 hhalf h11 (show 0 ≤ 2 * (1 - q) by linarith) (show 0 ≤ 2 * q - 1 by linarith)
      (by ring)
    simp only [smul_eq_mul] at this
    have e : 2 * (1 - q) * (1 / 2) + (2 * q - 1) * 1 = q := by ring
    rw [e] at this
    nlinarith [mul_nonneg (show 0 ≤ 2 * q - 1 by linarith) hg1]

lemma gauss_u2 (a b t : ℝ) (ha : 0 < a) :
    ∫ y : ℝ, ((t - b * y) / a) ^ 2 ∂(gaussianReal 0 1) = (t ^ 2 + b ^ 2) / a ^ 2 := by
  have e : (fun y : ℝ => ((t - b * y) / a) ^ 2) =
      fun y => (t ^ 2 / a ^ 2) - (2 * t * b / a ^ 2) * y + (b ^ 2 / a ^ 2) * y ^ 2 := by
    funext y; field_simp; ring
  rw [e, integral_add, integral_sub, integral_const, integral_const_mul, integral_const_mul,
    gauss_mean, gauss_second]
  · simp; field_simp
  · exact integrable_const _
  · exact gauss_int_id.const_mul _
  · exact (integrable_const _).sub (gauss_int_id.const_mul _)
  · exact gauss_int_sq.const_mul _

lemma abs_le_amgm (d c : ℝ) (hc : 0 < c) : 2 * |d| ≤ d ^ 2 / c + c := by
  rw [← sub_nonneg]
  have : d ^ 2 / c + c - 2 * |d| = (|d| - c) ^ 2 / c := by
    field_simp
    nlinarith [sq_abs d]
  rw [this]; positivity

lemma pointwise {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (a b t c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (∑ S, f S) / 2 ^ n * (1 - c - (t ^ 2 + b ^ 2) / (a ^ 2 * (2 * Real.pi) * c))
      ≤ semidefExt f (fun _ => 1 - Phi t) (Sc a b) := by
  rw [semidefExt_Sc f a b ha t]
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hAvg : 0 ≤ (∑ S, f S) / 2 ^ n := by
    have := Finset.sum_nonneg (fun S (_ : S ∈ Finset.univ) => hf0 S)
    positivity
  have h1 : ∀ y : ℝ, (∑ S, f S) / 2 ^ n * (1 - c - ((t - b * y) / a) ^ 2 / ((2 * Real.pi) * c))
      ≤ F f (fun _ => 1 - Phi ((t - b * y) / a)) := by
    intro y
    set u := (t - b * y) / a with hu
    have hq0 : 0 ≤ 1 - Phi u := by linarith [phi_le_one u]
    have hq1 : 1 - Phi u ≤ 1 := by linarith [phi_nonneg u]
    have h2 := F_lower f hf0 hf (1 - Phi u) hq0 hq1
    rw [F_half] at h2
    have h3 := phi_sq_bound u
    have h4 := abs_le_amgm (Phi u - 1 / 2) c hc
    have h5 : |1 - Phi u - 1 / 2| = |Phi u - 1 / 2| := by
      rw [← abs_neg]; congr 1; ring
    rw [h5] at h2
    refine le_trans ?_ h2
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hAvg
    have h6 : (Phi u - 1 / 2) ^ 2 / c ≤ u ^ 2 / (2 * Real.pi) / c :=
      div_le_div_of_nonneg_right h3 hc.le
    have h7 : u ^ 2 / (2 * Real.pi) / c = u ^ 2 / ((2 * Real.pi) * c) := by
      rw [div_div]
    linarith
  have hint1 : Integrable (fun y : ℝ => (∑ S, f S) / 2 ^ n *
      (1 - c - ((t - b * y) / a) ^ 2 / ((2 * Real.pi) * c))) (gaussianReal 0 1) := by
    refine Integrable.const_mul (Integrable.sub (integrable_const _) (Integrable.div_const ?_ _)) _
    have hm : MemLp (fun y : ℝ => (t - b * y) / a) 2 (gaussianReal 0 1) := by
      have h0 : MemLp (fun y : ℝ => t - b * y) 2 (gaussianReal 0 1) :=
        MemLp.sub (memLp_const t) (MemLp.const_mul (memLp_id_gaussianReal' (μ := 0) (v := 1) 2
          (by simp)) b)
      have h1 := h0.const_mul a⁻¹
      convert h1 using 2
      simp [div_eq_inv_mul]
    simpa using hm.integrable_sq
  have hq : Measurable (fun y : ℝ => 1 - Phi ((t - b * y) / a)) :=
    measurable_const.sub (phi_meas.comp (by fun_prop))
  have hint2 : Integrable (fun y : ℝ => F f (fun _ => 1 - Phi ((t - b * y) / a)))
      (gaussianReal 0 1) :=
    integrable_bdd _ (F_meas f _ hq) (∑ T, |f T|) (fun y =>
      F_bdd f _ (by linarith [phi_le_one ((t - b * y) / a)])
        (by linarith [phi_nonneg ((t - b * y) / a)]))
  have hval : ∫ y : ℝ, (∑ S, f S) / 2 ^ n *
      (1 - c - ((t - b * y) / a) ^ 2 / ((2 * Real.pi) * c)) ∂(gaussianReal 0 1)
      = (∑ S, f S) / 2 ^ n * (1 - c - (t ^ 2 + b ^ 2) / (a ^ 2 * (2 * Real.pi) * c)) := by
    rw [integral_const_mul]
    congr 1
    have hi : Integrable (fun y : ℝ => ((t - b * y) / a) ^ 2 / ((2 * Real.pi) * c))
        (gaussianReal 0 1) := by
      have hm : MemLp (fun y : ℝ => (t - b * y) / a) 2 (gaussianReal 0 1) := by
        have h0 : MemLp (fun y : ℝ => t - b * y) 2 (gaussianReal 0 1) :=
          MemLp.sub (memLp_const t) (MemLp.const_mul (memLp_id_gaussianReal' (μ := 0) (v := 1) 2
            (by simp)) b)
        have h1 := h0.const_mul a⁻¹
        convert h1 using 2
        simp [div_eq_inv_mul]
      exact (by simpa using hm.integrable_sq : Integrable (fun y : ℝ => ((t - b * y) / a) ^ 2)
        (gaussianReal 0 1)).div_const _
    rw [integral_sub (integrable_const _) hi, integral_const, integral_div, gauss_u2 a b t ha]
    simp only [probReal_univ, one_smul]
    field_simp
  rw [← hval]
  exact integral_mono hint1 hint2 h1

end UniversalSubmod.Dev.Cor41

namespace UniversalSubmod

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared
open scoped RealInnerProductSpace

/-- **Corollary 4.1** (Gaussian rounding compared with the uniform expectation; Adamczyk,
Ueltzen, Vondrák, *Optimal universal sets for submodular functions*, manuscript of November 3,
2026, Corollary 4.1, p.11; proof pp.10-11). Under the assumptions of Theorem 2.4,
`E[f(R_Z(T))] ≥ (1 − 2√ε) E_{S⊆[n]}[f(S)]`.

**Formalization Note.** The hypotheses are those of the published Theorem 2.4 (`‖vᵢ‖ = 1`,
`⟨vᵢ,vⱼ⟩ ≤ ε`, `0 < ε < 1/2`, `Z` with law `stdGaussian`, `T` independent, mean `0`, variance
at most `ε`, `f ≥ 0` submodular); `E_{S⊆[n]}[f(S)]` is `2^{-n} ∑_S f(S)`. -/
theorem inl_corollary_4_1 (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ = 1)
    (hvv : ∀ i j, i ≠ j → ⟪v i, v j⟫ ≤ ε)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → EuclideanSpace ℝ (Fin k)) (hZ : Measurable Z)
    (hZlaw : P.map Z = stdGaussian (EuclideanSpace ℝ (Fin k)))
    (T : Ω → ℝ) (hT : Measurable T) (hind : IndepFun Z T P) (hT2 : MemLp T 2 P)
    (hT0 : ∫ ω, T ω ∂P = 0) (hTvar : variance T P ≤ ε)
    (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) :
    (1 - 2 * Real.sqrt ε) * ((∑ S, f S) / 2 ^ n) ≤ ∫ ω, f (threshSet v (Z ω) (T ω)) ∂P := by
  classical
  have hε : 0 < 1 - ε := by linarith
  have ha : 0 < Real.sqrt (1 - ε) := Real.sqrt_pos.2 hε
  have ha2 : Real.sqrt (1 - ε) ^ 2 = 1 - ε := Real.sq_sqrt hε.le
  have hb2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε0.le
  have hS' : CorrMatrix (Dev.Cor41.Sc (n := n) (Real.sqrt (1 - ε)) (Real.sqrt ε)) :=
    ⟨Dev.Cor41.Sc_psd _ _, fun i => by simp [Dev.Cor41.Sc, ha2, hb2]⟩
  have hS : CorrMatrix (Matrix.gram ℝ v) :=
    ⟨Matrix.posSemidef_gram ℝ v, fun i => by
      simp [Matrix.gram, real_inner_self_eq_norm_sq, hv i]⟩
  have hle : ∀ i j, i ≠ j →
      Matrix.gram ℝ v i j ≤ Dev.Cor41.Sc (Real.sqrt (1 - ε)) (Real.sqrt ε) i j := by
    intro i j hij
    simp only [Matrix.gram, Dev.Cor41.Sc, Matrix.of_apply, hij, if_false, zero_add, hb2]
    exact hvv i j hij
  have hc : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε0
  have hpt : ∀ t : ℝ, (∑ S, f S) / 2 ^ n * (1 - Real.sqrt ε -
        (t ^ 2 + ε) / ((1 - ε) * (2 * Real.pi) * Real.sqrt ε))
      ≤ ∫ z, f (threshSet v z t) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    intro t
    have hx : ∀ i : Fin n, (fun _ : Fin n => 1 - Cohen2019.Robust.Phi t) i ∈ Set.Icc (0 : ℝ) 1 :=
      fun i => ⟨by linarith [Dev.Cor41.phi_le_one t], by linarith [Dev.Cor41.phi_nonneg t]⟩
    have h23 := theorem_2_3 f hf0 hf _ _ hS hS' hle _ hx
    have h1 := Dev.Cor41.pointwise f hf0 hf (Real.sqrt (1 - ε)) (Real.sqrt ε) t (Real.sqrt ε) ha hc
    rw [Dev.Cor41.semidefExt_gram] at h23
    rw [ha2, hb2] at h1
    exact h1.trans h23
  have hH : Measurable (fun p : EuclideanSpace ℝ (Fin k) × ℝ => f (threshSet v p.1 p.2)) := by
    refine Dev.Cor41.meas_comp (fun p : EuclideanSpace ℝ (Fin k) × ℝ => threshSet v p.1 p.2) (fun i => ?_) f
    simp only [threshSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact measurableSet_le measurable_snd (by fun_prop)
  have hmap : P.map (fun ω => (Z ω, T ω))
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).prod (P.map T) := by
    rw [← hZlaw]; exact hind.map_prod_eq_prod_map_map hZ.aemeasurable hT.aemeasurable
  haveI : IsProbabilityMeasure (P.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  have hI : ∫ ω, f (threshSet v (Z ω) (T ω)) ∂P
      = ∫ p, f (threshSet v p.1 p.2)
          ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (P.map T)) := by
    rw [← hmap, integral_map (hZ.prodMk hT).aemeasurable hH.aestronglyMeasurable]
  have hint : Integrable (fun p : EuclideanSpace ℝ (Fin k) × ℝ => f (threshSet v p.1 p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (P.map T)) :=
    Dev.Cor41.integrable_bdd _ hH _ (fun p => Dev.Cor41.f_bdd f _)
  rw [hI, integral_prod_symm _ hint]
  have hint_t2 : Integrable (fun t : ℝ => t ^ 2) (P.map T) := by
    rw [integrable_map_measure (by fun_prop) hT.aemeasurable]
    exact hT2.integrable_sq
  have hET : ∫ t : ℝ, t ^ 2 ∂(P.map T) = variance T P := by
    rw [integral_map hT.aemeasurable (by fun_prop), variance_eq_sub hT2]
    simp [hT0]
  have hD : 0 < (1 - ε) * (2 * Real.pi) * Real.sqrt ε := by positivity
  have hAvg : 0 ≤ (∑ S, f S) / 2 ^ n := by
    have := Finset.sum_nonneg (fun S (_ : S ∈ Finset.univ) => hf0 S)
    positivity
  have hi3 : Integrable (fun t : ℝ => (t ^ 2 + ε) / ((1 - ε) * (2 * Real.pi) * Real.sqrt ε))
      (P.map T) := (hint_t2.add (integrable_const ε)).div_const _
  have hcint : Integrable (fun t : ℝ => (∑ S, f S) / 2 ^ n * (1 - Real.sqrt ε -
        (t ^ 2 + ε) / ((1 - ε) * (2 * Real.pi) * Real.sqrt ε))) (P.map T) :=
    ((integrable_const _).sub hi3).const_mul _
  have hcval : ∫ t : ℝ, (∑ S, f S) / 2 ^ n * (1 - Real.sqrt ε -
        (t ^ 2 + ε) / ((1 - ε) * (2 * Real.pi) * Real.sqrt ε)) ∂(P.map T)
      = (∑ S, f S) / 2 ^ n * (1 - Real.sqrt ε -
        (variance T P + ε) / ((1 - ε) * (2 * Real.pi) * Real.sqrt ε)) := by
    have hi4 : ∫ t : ℝ, (t ^ 2 + ε) ∂(P.map T) = variance T P + ε := by
      rw [integral_add hint_t2 (integrable_const ε), hET]; simp
    rw [integral_const_mul, integral_sub (integrable_const _) hi3,
      integral_div _ (fun t : ℝ => t ^ 2 + ε), hi4]
    simp
  calc (1 - 2 * Real.sqrt ε) * ((∑ S, f S) / 2 ^ n)
      ≤ (∑ S, f S) / 2 ^ n * (1 - Real.sqrt ε -
        (variance T P + ε) / ((1 - ε) * (2 * Real.pi) * Real.sqrt ε)) := by
        have hπ := Real.pi_gt_three
        have hsq : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε0.le
        have : (variance T P + ε) / ((1 - ε) * (2 * Real.pi) * Real.sqrt ε) ≤ Real.sqrt ε := by
          rw [div_le_iff₀ hD]
          have h2 : 2 ≤ (1 - ε) * (2 * Real.pi) := by nlinarith
          have : 2 * ε ≤ ε * ((1 - ε) * (2 * Real.pi)) := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]
        nlinarith [mul_le_mul_of_nonneg_left this hAvg]
    _ = _ := hcval.symm
    _ ≤ _ := integral_mono hcint hint.integral_prod_right hpt

end UniversalSubmod
end

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Aux12

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared

lemma meas_comp {α : Type*} [MeasurableSpace α] {n : ℕ} (φ : α → Finset (Fin n))
    (hφ : ∀ i, MeasurableSet {a | i ∈ φ a}) (f : Finset (Fin n) → ℝ) :
    Measurable (fun a => f (φ a)) := by
  classical
  have h : (fun a => f (φ a)) = fun a => ∑ S : Finset (Fin n), if φ a = S then f S else 0 := by
    funext a
    rw [Finset.sum_eq_single (φ a)]
    · simp
    · intro S _ hS; simp [Ne.symm hS]
    · simp
  rw [h]
  refine Finset.measurable_sum _ (fun S _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {a | φ a = S} = ⋂ i, {a | i ∈ φ a ↔ i ∈ S} := by
    ext a; simp [Finset.ext_iff]
  rw [this]
  refine MeasurableSet.iInter (fun i => ?_)
  by_cases hi : i ∈ S
  · simpa [hi] using hφ i
  · have e : {a | i ∈ φ a ↔ i ∈ S} = {a | i ∈ φ a}ᶜ := by ext a; simp [hi]
    rw [e]; exact (hφ i).compl

lemma integrable_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) (C : ℝ) (h : ∀ a, |g a| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (ae_of_all _ (fun a => by simpa [Real.norm_eq_abs] using h a))

lemma f_bdd {n : ℕ} (f : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : |f S| ≤ ∑ T, |f T| :=
  Finset.single_le_sum (f := fun T => |f T|) (fun T _ => abs_nonneg _) (Finset.mem_univ S)

lemma F_half {n : ℕ} (f : Finset (Fin n) → ℝ) :
    F f (fun _ => 1 / 2) = (∑ S, f S) / 2 ^ n := by
  unfold F
  have : ∀ S : Finset (Fin n), ∏ i : Fin n, (if i ∈ S then (1 / 2 : ℝ) else 1 - 1 / 2)
      = 1 / 2 ^ n := by
    intro S
    have : ∀ i : Fin n, (if i ∈ S then (1 / 2 : ℝ) else 1 - 1 / 2) = 1 / 2 := by
      intro i; split_ifs <;> norm_num
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [one_div, one_div, inv_pow]
  simp only [this]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  ring

lemma gauss_int_sq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 1) := by
  have := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  simpa using this

lemma gauss_second : ∫ y : ℝ, y ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (memLp_id_gaussianReal (μ := 0) (v := 1) 2).aemeasurable] at h
  simpa [integral_id_gaussianReal] using h


end UniversalSubmod.Dev.Aux12

namespace UniversalSubmod.Dev.Thm12D

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared
open scoped RealInnerProductSpace
open UniversalSubmod.Dev

noncomputable abbrev gam : Measure ℝ := gaussianReal 0 1
noncomputable abbrev u01 : Measure ℝ := volume.restrict (Set.Ico (0:ℝ) 1)
noncomputable abbrev kap (η : ℝ) : Measure ℝ := gaussianReal 0 η.toNNReal

lemma u01_prob : IsProbabilityMeasure u01 := ⟨by simp⟩

/-- randomized rounding of `z` to the grid `η ℤ`, driven by `u ∈ [0,1)` -/
noncomputable def rnd (η z u : ℝ) : ℝ := η * ⌊z / η + u⌋

noncomputable def eu {k : ℕ} (x : Fin k → ℝ) : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 x

/-- the sampling measure on `(z_j, u_j)_{j<k} × τ` -/
noncomputable def PP (k : ℕ) (η : ℝ) : Measure ((Fin k → ℝ × ℝ) × ℝ) :=
  (Measure.pi (fun _ : Fin k => gam.prod u01)).prod (kap η)

noncomputable def Zv {k : ℕ} (ω : (Fin k → ℝ × ℝ) × ℝ) : EuclideanSpace ℝ (Fin k) :=
  eu (fun j => (ω.1 j).1)

noncomputable def Yv {k : ℕ} (η : ℝ) (ω : (Fin k → ℝ × ℝ) × ℝ) : EuclideanSpace ℝ (Fin k) :=
  eu (fun j => rnd η (ω.1 j).1 (ω.1 j).2)

lemma floor_decomp (a u : ℝ) (hu : u ∈ Set.Ico (0:ℝ) 1) :
    (⌊a + u⌋ : ℝ) = ⌊a⌋ + (Set.Ici (1 - Int.fract a)).indicator (fun _ => (1:ℝ)) u := by
  have h1 : a + u = (⌊a⌋ : ℝ) + (Int.fract a + u) := by
    have := Int.floor_add_fract a
    linarith
  have h2 : ⌊a + u⌋ = ⌊a⌋ + ⌊Int.fract a + u⌋ := by
    rw [h1]; exact Int.floor_intCast_add _ _
  have hf0 := Int.fract_nonneg a
  have hf1 := Int.fract_lt_one a
  rw [h2]
  push_cast
  by_cases h : 1 - Int.fract a ≤ u
  · have : ⌊Int.fract a + u⌋ = 1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith [hu.1, hu.2]
    simp [Set.indicator_of_mem (Set.mem_Ici.2 h), this]
  · have : ⌊Int.fract a + u⌋ = 0 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith [hu.1, hu.2, not_le.1 h]
    simp [Set.indicator_of_notMem (show u ∉ Set.Ici (1 - Int.fract a) from h), this]

lemma floor_mean (a : ℝ) : ∫ u, (⌊a + u⌋ : ℝ) ∂u01 = a := by
  have h : ∫ u, (⌊a + u⌋ : ℝ) ∂u01 = ∫ u in Set.Ico (0:ℝ) 1,
      ((⌊a⌋ : ℝ) + (Set.Ici (1 - Int.fract a)).indicator (fun _ => (1:ℝ)) u) := by
    refine setIntegral_congr_fun measurableSet_Ico (fun u hu => ?_)
    exact floor_decomp a u hu
  rw [h]
  have hf0 := Int.fract_nonneg a
  have hf1 := Int.fract_lt_one a
  rw [integral_add (integrable_const _) ?_, integral_const]
  · rw [integral_indicator measurableSet_Ici]
    simp only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply MeasurableSet.univ]
    simp only [Set.univ_inter]
    have e1 : Set.Ici (1 - Int.fract a) ∩ Set.Ico (0:ℝ) 1 = Set.Ico (1 - Int.fract a) 1 := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ico]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩
    rw [Measure.restrict_apply measurableSet_Ici, e1, Real.volume_Ico, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal (by linarith)]
    have := Int.floor_add_fract a
    ring_nf
    linarith
  · exact (integrable_const (1:ℝ)).indicator measurableSet_Ici


lemma PP_prob (k : ℕ) (η : ℝ) : IsProbabilityMeasure (PP k η) := by
  haveI := u01_prob
  unfold PP
  infer_instance

lemma meas_eu_coord (k : ℕ) : Measurable (fun w : Fin k → ℝ × ℝ => eu (fun j => (w j).1)) := by
  unfold eu; fun_prop

lemma Zv_eq (k : ℕ) : (Zv : (Fin k → ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin k)) =
    (fun w : Fin k → ℝ × ℝ => eu (fun j => (w j).1)) ∘ Prod.fst := rfl

lemma Zv_meas (k : ℕ) : Measurable (Zv : (Fin k → ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin k)) := by
  rw [Zv_eq]; exact (meas_eu_coord k).comp measurable_fst

lemma Zv_law (k : ℕ) (η : ℝ) :
    (PP k η).map Zv = stdGaussian (EuclideanSpace ℝ (Fin k)) := by
  haveI := u01_prob
  rw [Zv_eq, ← Measure.map_map (meas_eu_coord k) measurable_fst]
  have h1 : (PP k η).map Prod.fst = Measure.pi (fun _ : Fin k => gam.prod u01) := by
    unfold PP; rw [Measure.map_fst_prod]; simp
  rw [h1]
  have h2 : (Measure.pi (fun _ : Fin k => gam.prod u01)).map
      (fun w : Fin k → ℝ × ℝ => (fun j => (w j).1)) = Measure.pi (fun _ : Fin k => gam) := by
    have := Measure.pi_map_pi (μ := fun _ : Fin k => gam.prod u01) (f := fun _ => Prod.fst)
      (fun _ => measurable_fst.aemeasurable)
    simpa [Measure.map_fst_prod] using this
  have h3 : (fun w : Fin k → ℝ × ℝ => eu (fun j => (w j).1)) =
      (fun x : Fin k → ℝ => eu x) ∘ (fun w : Fin k → ℝ × ℝ => (fun j => (w j).1)) := rfl
  rw [h3, ← Measure.map_map (by unfold eu; fun_prop) (by fun_prop), h2]
  exact map_pi_eq_stdGaussian

lemma tau_law (k : ℕ) (η : ℝ) : (PP k η).map (fun ω => ω.2) = kap η := by
  haveI := u01_prob
  unfold PP
  rw [Measure.map_snd_prod]; simp

lemma Zv_tau_indep (k : ℕ) (η : ℝ) :
    IndepFun (Zv : (Fin k → ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin k)) (fun ω => ω.2) (PP k η) := by
  haveI := u01_prob
  unfold PP
  exact indepFun_prod (X := fun w : Fin k → ℝ × ℝ => eu (fun j => (w j).1))
    (Y := fun t : ℝ => t) (meas_eu_coord k) measurable_id

lemma tau_memLp (k : ℕ) (η : ℝ) : MemLp (fun ω : (Fin k → ℝ × ℝ) × ℝ => ω.2) 2 (PP k η) := by
  have h : MemLp (id : ℝ → ℝ) 2 ((PP k η).map (fun ω => ω.2)) := by
    rw [tau_law]; exact memLp_id_gaussianReal 2
  have := (memLp_map_measure_iff (by exact measurable_id.aestronglyMeasurable)
    measurable_snd.aemeasurable).1 h
  exact this

lemma tau_mean (k : ℕ) (η : ℝ) : ∫ ω : (Fin k → ℝ × ℝ) × ℝ, ω.2 ∂(PP k η) = 0 := by
  have := integral_map (μ := PP k η) (φ := fun ω : (Fin k → ℝ × ℝ) × ℝ => ω.2)
    (f := fun x : ℝ => x) measurable_snd.aemeasurable measurable_id.aestronglyMeasurable
  rw [tau_law] at this
  rw [← this]
  exact integral_id_gaussianReal

lemma tau_var (k : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    variance (fun ω : (Fin k → ℝ × ℝ) × ℝ => ω.2) (PP k η) = η := by
  have h := variance_map (μ := PP k η) (X := fun x : ℝ => x)
    (Y := fun ω : (Fin k → ℝ × ℝ) × ℝ => ω.2) (by rw [tau_law]; exact measurable_id.aemeasurable)
    measurable_snd.aemeasurable
  rw [tau_law] at h
  have h2 : variance (fun x : ℝ => x) (kap η) = η.toNNReal := variance_id_gaussianReal
  rw [h2] at h
  rw [show (fun ω : (Fin k → ℝ × ℝ) × ℝ => ω.2) = (fun x : ℝ => x) ∘ (fun ω => ω.2) from rfl,
    ← h, Real.coe_toNNReal _ hη]

theorem cor41_PP (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1 / 2)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ = 1)
    (hvv : ∀ i j, i ≠ j → ⟪v i, v j⟫ ≤ η)
    (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) :
    (1 - 2 * Real.sqrt η) * ((∑ S, f S) / 2 ^ n) ≤
      ∫ ω, f (threshSet v (Zv ω) ω.2) ∂(PP k η) := by
  haveI := PP_prob k η
  exact inl_corollary_4_1 n k hn hk η hη0 hη1 v hv hvv (PP k η) Zv (Zv_meas k) (Zv_law k η)
    (fun ω => ω.2) measurable_snd (Zv_tau_indep k η) (tau_memLp k η) (tau_mean k η)
    (le_of_eq (tau_var k η hη0.le)) f hf0 hf

lemma pdf_eq (η : ℝ) (hη : 0 < η) (x : ℝ) :
    gaussianPDFReal 0 η.toNNReal x = (Real.sqrt (2 * Real.pi * η))⁻¹ * Real.exp (-(x ^ 2) / (2 * η)) := by
  rw [gaussianPDFReal_def]
  simp [Real.coe_toNNReal _ hη.le]

lemma pdf_contDiff (η : ℝ) (hη : 0 < η) : ContDiff ℝ 1 (gaussianPDFReal 0 η.toNNReal) := by
  have : gaussianPDFReal 0 η.toNNReal = fun x => (Real.sqrt (2 * Real.pi * η))⁻¹ * Real.exp (-(x ^ 2) / (2 * η)) :=
    funext (pdf_eq η hη)
  rw [this]
  fun_prop

lemma pdf_deriv (η : ℝ) (hη : 0 < η) (t : ℝ) :
    deriv (gaussianPDFReal 0 η.toNNReal) t =
      (Real.sqrt (2 * Real.pi * η))⁻¹ * Real.exp (-(t ^ 2) / (2 * η)) * (-(t / η)) := by
  have : gaussianPDFReal 0 η.toNNReal = fun x => (Real.sqrt (2 * Real.pi * η))⁻¹ * Real.exp (-(x ^ 2) / (2 * η)) :=
    funext (pdf_eq η hη)
  rw [this]
  have h0 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / (2 * η)) (-(2 * t) / (2 * η)) t :=
    (h0.neg).div_const (2 * η)
  have e : -(2 * t) / (2 * η) = -(t / η) := by field_simp
  rw [e] at h1
  have h := h1
  have h2 := (h.exp).const_mul (Real.sqrt (2 * Real.pi * η))⁻¹
  rw [h2.deriv]
  ring

lemma pdf_deriv_bound (η : ℝ) (hη : 0 < η) (t : ℝ) :
    |deriv (gaussianPDFReal 0 η.toNNReal) t| ≤ 1 / η := by
  rw [pdf_deriv η hη t]
  have hs : 0 < Real.sqrt (2 * Real.pi * η) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (2 * Real.pi * η) ^ 2 = 2 * Real.pi * η := Real.sq_sqrt (by positivity)
  have hη' : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hηsq : Real.sqrt η ^ 2 = η := Real.sq_sqrt hη.le
  -- |t| exp(-t^2/(2η)) ≤ sqrt η
  have key : |t| * Real.exp (-(t ^ 2) / (2 * η)) ≤ Real.sqrt η := by
    have h1 : |t| / Real.sqrt η ≤ Real.exp (t ^ 2 / (2 * η)) := by
      have := Real.add_one_le_exp (t ^ 2 / (2 * η))
      have h3 : |t| / Real.sqrt η ≤ t ^ 2 / (2 * η) + 1 := by
        have hs2 : (|t| / Real.sqrt η) ^ 2 = t ^ 2 / η := by
          rw [div_pow, sq_abs, hηsq]
        have : t ^ 2 / (2 * η) = (|t| / Real.sqrt η) ^ 2 / 2 := by rw [hs2]; field_simp
        rw [this]
        nlinarith [sq_nonneg (|t| / Real.sqrt η - 1)]
      linarith
    have h2 : Real.exp (-(t ^ 2) / (2 * η)) = (Real.exp (t ^ 2 / (2 * η)))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [h2]
    have hep := Real.exp_pos (t ^ 2 / (2 * η))
    rw [div_le_iff₀ hη'] at h1
    calc |t| * (Real.exp (t ^ 2 / (2 * η)))⁻¹ ≤ (Real.exp (t ^ 2 / (2 * η)) * Real.sqrt η) * (Real.exp (t ^ 2 / (2 * η)))⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = Real.sqrt η := by field_simp
  rw [abs_mul, abs_mul, abs_neg, abs_div, abs_of_pos hη, abs_of_pos (Real.exp_pos _), abs_of_pos (inv_pos.2 hs)]
  have hc : (Real.sqrt (2 * Real.pi * η))⁻¹ * Real.sqrt η ≤ 1 := by
    rw [inv_mul_le_iff₀ hs, mul_one]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three, hη])
  calc (Real.sqrt (2 * Real.pi * η))⁻¹ * Real.exp (-(t ^ 2) / (2 * η)) * (|t| / η)
      = (Real.sqrt (2 * Real.pi * η))⁻¹ * (|t| * Real.exp (-(t ^ 2) / (2 * η))) / η := by ring
    _ ≤ (Real.sqrt (2 * Real.pi * η))⁻¹ * Real.sqrt η / η := by
        gcongr
    _ ≤ 1 / η := by
        gcongr

lemma meas_rnd (η : ℝ) : Measurable (fun p : ℝ × ℝ => rnd η p.1 p.2) := by
  unfold rnd
  have h1 : Measurable (fun p : ℝ × ℝ => p.1 / η + p.2) := by fun_prop
  have h2 : Measurable (fun p : ℝ × ℝ => ⌊p.1 / η + p.2⌋) := (Int.measurable_floor (R := ℝ)).comp h1
  have h3 : Measurable (fun p : ℝ × ℝ => ((⌊p.1 / η + p.2⌋ : ℤ) : ℝ)) :=
    (measurable_from_top (f := fun m : ℤ => (m : ℝ))).comp h2
  exact measurable_const.mul h3

lemma rnd_bound (η z u : ℝ) (hη : 0 < η) (hu : u ∈ Set.Ico (0:ℝ) 1) : |rnd η z u - z| ≤ η := by
  have hz : η * (z / η) = z := by field_simp
  have h1 := Int.floor_le (z / η + u)
  have h2 := Int.lt_floor_add_one (z / η + u)
  have e : rnd η z u - z = η * ((⌊z / η + u⌋ : ℝ) - z / η) := by
    unfold rnd; rw [mul_sub, hz]
  rw [e, abs_mul, abs_of_pos hη]
  have : |(⌊z / η + u⌋ : ℝ) - z / η| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
  nlinarith

lemma iIndepFun_fst {Ω1 Ω2 : Type*} [MeasurableSpace Ω1] [MeasurableSpace Ω2] {k : ℕ}
    (μ : Measure Ω1) (ν : Measure Ω2) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Fin k → Ω1 → ℝ) (hf : ∀ j, Measurable (f j)) (h : iIndepFun f μ) :
    iIndepFun (fun j (ω : Ω1 × Ω2) => f j ω.1) (μ.prod ν) := by
  have hm : ∀ {β : Type} [MeasurableSpace β] (g : Ω1 → β), Measurable g →
      (μ.prod ν).map (fun ω => g ω.1) = μ.map g := by
    intro β _ g hg
    have := Measure.map_map (μ := μ.prod ν) hg measurable_fst
    simp only [Function.comp_def] at this
    rw [← this, Measure.map_fst_prod]; simp
  have hf' : ∀ j, AEMeasurable (fun ω : Ω1 × Ω2 => f j ω.1) (μ.prod ν) :=
    fun j => ((hf j).comp measurable_fst).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hf']
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun j => (hf j).aemeasurable)] at h
  have h2 : (μ.prod ν).map (fun ω j => f j ω.1) = μ.map (fun ω j => f j ω) :=
    hm (fun ω j => f j ω) (measurable_pi_lambda _ hf)
  rw [h2, h]
  congr 1
  funext j
  exact (hm (f j) (hf j)).symm

lemma meas_rnd1 (η z : ℝ) : Measurable (fun u : ℝ => rnd η z u) := by
  unfold rnd
  have h1 : Measurable (fun u : ℝ => z / η + u) := by fun_prop
  have h2 : Measurable (fun u : ℝ => ⌊z / η + u⌋) := (Int.measurable_floor (R := ℝ)).comp h1
  have h3 : Measurable (fun u : ℝ => ((⌊z / η + u⌋ : ℤ) : ℝ)) :=
    (measurable_from_top (f := fun m : ℤ => (m : ℝ))).comp h2
  exact measurable_const.mul h3

noncomputable abbrev Pz (k : ℕ) (η : ℝ) : Measure ((Fin k → ℝ) × ℝ) :=
  (Measure.pi (fun _ : Fin k => u01)).prod (kap η)

lemma Pz_prob (k : ℕ) (η : ℝ) : IsProbabilityMeasure (Pz k η) := by
  haveI := u01_prob
  unfold Pz; infer_instance

lemma Pz_map_coord (k : ℕ) (η : ℝ) (j : Fin k) : (Pz k η).map (fun q => q.1 j) = u01 := by
  haveI := u01_prob
  have h1 : (Pz k η).map Prod.fst = Measure.pi (fun _ : Fin k => u01) := by
    unfold Pz; rw [Measure.map_fst_prod]; simp
  have := Measure.map_map (μ := Pz k η) (measurable_pi_apply j) measurable_fst
  simp only [Function.comp_def] at this
  rw [← this, h1]
  exact (measurePreserving_eval (fun _ : Fin k => u01) j).map_eq

lemma Pz_ae_mem (k : ℕ) (η : ℝ) : ∀ᵐ q ∂(Pz k η), ∀ j, q.1 j ∈ Set.Ico (0:ℝ) 1 := by
  rw [ae_all_iff]
  intro j
  have h : ∀ᵐ x ∂u01, x ∈ Set.Ico (0:ℝ) 1 := ae_restrict_mem measurableSet_Ico
  rw [← Pz_map_coord k η j] at h
  exact (ae_map_iff (measurable_pi_apply j |>.comp measurable_fst).aemeasurable
    measurableSet_Ico).1 h

lemma meas_Yz (k : ℕ) (η : ℝ) (z : Fin k → ℝ) :
    Measurable (fun q : (Fin k → ℝ) × ℝ => eu (fun j => rnd η (z j) (q.1 j))) := by
  unfold eu
  have : Measurable (fun q : (Fin k → ℝ) × ℝ => (fun j => rnd η (z j) (q.1 j))) :=
    measurable_pi_lambda _ (fun j => (meas_rnd1 η (z j)).comp
      ((measurable_pi_apply j).comp measurable_fst))
  have h2 : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) := by fun_prop
  exact h2.comp this

lemma lower_fixed_z {n k : ℕ} (η : ℝ) (hη : 0 < η) (f : Finset (Fin n) → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ = 1) (z : Fin k → ℝ) :
    ∫ q, f (threshSet v (eu z) q.2) ∂(Pz k η) - OPT f * η ≤
      ∫ q, f (threshSet v (eu (fun j => rnd η (z j) (q.1 j))) q.2) ∂(Pz k η) := by
  haveI := Pz_prob k η
  haveI := u01_prob
  have hηn : η.toNNReal ≠ 0 := by
    intro h; rw [Real.toNNReal_eq_zero] at h; linarith
  have hY : Measurable (fun q : (Fin k → ℝ) × ℝ => eu (fun j => rnd η (z j) (q.1 j))) :=
    meas_Yz k η z
  have hYind : iIndepFun (fun j (q : (Fin k → ℝ) × ℝ) => (eu (fun j => rnd η (z j) (q.1 j))) j)
      (Pz k η) := by
    have h0 : iIndepFun (fun j (u : Fin k → ℝ) => rnd η (z j) (u j)) (Measure.pi (fun _ : Fin k => u01)) :=
      iIndepFun_pi (μ := fun _ : Fin k => u01) (X := fun j => fun x => rnd η (z j) x)
        (fun j => (meas_rnd1 η (z j)).aemeasurable)
    exact iIndepFun_fst (Measure.pi (fun _ : Fin k => u01)) (kap η)
      (fun j (u : Fin k → ℝ) => rnd η (z j) (u j))
      (fun j => (meas_rnd1 η (z j)).comp (measurable_pi_apply j)) h0
  have hae := Pz_ae_mem k η
  have hbd : ∀ j, ∀ᵐ q ∂(Pz k η), |rnd η (z j) (q.1 j) - z j| ≤ η := by
    intro j
    filter_upwards [hae] with q hq
    exact rnd_bound η (z j) (q.1 j) hη (hq j)
  have hcoord : ∀ j, Measurable (fun q : (Fin k → ℝ) × ℝ => rnd η (z j) (q.1 j)) := fun j =>
    (meas_rnd1 η (z j)).comp ((measurable_pi_apply j).comp measurable_fst)
  have hY2 : ∀ j, MemLp (fun q : (Fin k → ℝ) × ℝ => (eu (fun j => rnd η (z j) (q.1 j))) j) 2
      (Pz k η) := by
    intro j
    refine MemLp.of_bound (hcoord j).aestronglyMeasurable (|z j| + η) ?_
    filter_upwards [hbd j] with q hq
    show ‖rnd η (z j) (q.1 j)‖ ≤ |z j| + η
    rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (rnd η (z j) (q.1 j)) (z j)
    linarith
  have hYmean : ∀ j, ∫ q, (eu (fun j => rnd η (z j) (q.1 j))) j ∂(Pz k η) = z j := by
    intro j
    show ∫ q, rnd η (z j) (q.1 j) ∂(Pz k η) = z j
    have h1 := integral_map (μ := Pz k η) (φ := fun q : (Fin k → ℝ) × ℝ => q.1 j)
      (f := fun x : ℝ => rnd η (z j) x)
      ((measurable_pi_apply j).comp measurable_fst).aemeasurable
      (by rw [Pz_map_coord]; exact (meas_rnd1 η (z j)).aestronglyMeasurable)
    rw [Pz_map_coord] at h1
    rw [← h1]
    unfold rnd
    rw [integral_const_mul, floor_mean]
    field_simp
  have hYvar : ∀ j, ∫ q, ((eu (fun j => rnd η (z j) (q.1 j))) j - z j) ^ 2 ∂(Pz k η) ≤ η ^ 2 := by
    intro j
    have hm : Measurable (fun q : (Fin k → ℝ) × ℝ => (rnd η (z j) (q.1 j) - z j) ^ 2) :=
      ((hcoord j).sub measurable_const).pow_const 2
    have hint : Integrable (fun q : (Fin k → ℝ) × ℝ => (rnd η (z j) (q.1 j) - z j) ^ 2) (Pz k η) := by
      refine Integrable.of_bound hm.aestronglyMeasurable (η ^ 2) ?_
      filter_upwards [hbd j] with q hq
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_nonneg (rnd η (z j) (q.1 j) - z j), sq_abs (rnd η (z j) (q.1 j) - z j)]
    calc ∫ q, ((eu (fun j => rnd η (z j) (q.1 j))) j - z j) ^ 2 ∂(Pz k η)
        = ∫ q, (rnd η (z j) (q.1 j) - z j) ^ 2 ∂(Pz k η) := rfl
      _ ≤ ∫ q, η ^ 2 ∂(Pz k η) := by
          refine integral_mono_ae hint (integrable_const _) ?_
          filter_upwards [hbd j] with q hq
          nlinarith [abs_nonneg (rnd η (z j) (q.1 j) - z j), sq_abs (rnd η (z j) (q.1 j) - z j)]
      _ = η ^ 2 := by simp
  have hind : IndepFun (fun q : (Fin k → ℝ) × ℝ => eu (fun j => rnd η (z j) (q.1 j)))
      (fun q => q.2) (Pz k η) := by
    unfold Pz
    exact indepFun_prod (X := fun u : Fin k → ℝ => eu (fun j => rnd η (z j) (u j)))
      (Y := fun t : ℝ => t) (by
        have : Measurable (fun u : Fin k → ℝ => (fun j => rnd η (z j) (u j))) :=
          measurable_pi_lambda _ (fun j => (meas_rnd1 η (z j)).comp (measurable_pi_apply j))
        have h2 : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) := by fun_prop
        unfold eu; exact h2.comp this) measurable_id
  have hlaw : (Pz k η).map (fun q => q.2) = volume.withDensity
      (fun t => ENNReal.ofReal (gaussianPDFReal 0 η.toNNReal t)) := by
    have h1 : (Pz k η).map (fun q => q.2) = kap η := by
      unfold Pz; rw [Measure.map_snd_prod]; simp
    rw [h1]
    show gaussianReal 0 η.toNNReal = _
    rw [gaussianReal_of_var_ne_zero 0 hηn]
    rfl
  have h26 := lemma_2_6 f hf0 hf v hv (eu z) (η ^ 2) (sq_nonneg η) (Pz k η)
    (fun q => eu (fun j => rnd η (z j) (q.1 j))) hY hYind hY2 hYmean hYvar
    (fun q => q.2) measurable_snd hind (gaussianPDFReal 0 η.toNNReal) (pdf_contDiff η hη)
    (fun t => gaussianPDFReal_nonneg _ _ _) hlaw (1 / η) (pdf_deriv_bound η hη)
  have e : OPT f * (1 / η) * η ^ 2 = OPT f * η := by field_simp
  rw [e] at h26
  exact h26

/-- rearrangement `((z_j,u_j)_j, t) ↦ (z, (u, t))` -/
noncomputable def T0 (k : ℕ) :
    ((Fin k → ℝ × ℝ) × ℝ) ≃ᵐ (Fin k → ℝ) × ((Fin k → ℝ) × ℝ) :=
  ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin k)).prodCongr
    (MeasurableEquiv.refl ℝ)).trans MeasurableEquiv.prodAssoc

lemma T0_mp (k : ℕ) (η : ℝ) :
    MeasurePreserving (T0 k) (PP k η)
      ((Measure.pi fun _ : Fin k => gam).prod (Pz k η)) := by
  haveI := u01_prob
  have h1 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin k) (fun _ => gam) (fun _ => u01)
  have h2 : MeasurePreserving
      (Prod.map (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin k)) (MeasurableEquiv.refl ℝ))
      (PP k η)
      (((Measure.pi fun _ : Fin k => gam).prod (Measure.pi fun _ : Fin k => u01)).prod (kap η)) :=
    h1.prod (MeasurePreserving.id (kap η))
  have h3 := measurePreserving_prodAssoc (Measure.pi fun _ : Fin k => gam)
    (Measure.pi fun _ : Fin k => u01) (kap η)
  exact h3.comp h2

lemma meas_G {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin k)) (f : Finset (Fin n) → ℝ)
    {α : Type*} [MeasurableSpace α] (X : α → EuclideanSpace ℝ (Fin k)) (hX : Measurable X)
    (t : α → ℝ) (ht : Measurable t) :
    Measurable (fun a => f (threshSet v (X a) (t a))) := by
  refine Aux12.meas_comp (fun a => threshSet v (X a) (t a)) (fun i => ?_) f
  simp only [threshSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact measurableSet_le ht (by fun_prop)

theorem lower_coupling {n k : ℕ} (η : ℝ) (hη : 0 < η) (f : Finset (Fin n) → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ = 1) :
    ∫ ω, f (threshSet v (Zv ω) ω.2) ∂(PP k η) - OPT f * η ≤
      ∫ ω, f (threshSet v (Yv η ω) ω.2) ∂(PP k η) := by
  haveI := PP_prob k η
  haveI := Pz_prob k η
  set G1 : (Fin k → ℝ) × ((Fin k → ℝ) × ℝ) → ℝ := fun x => f (threshSet v (eu x.1) x.2.2) with hG1
  set G2 : (Fin k → ℝ) × ((Fin k → ℝ) × ℝ) → ℝ :=
    fun x => f (threshSet v (eu (fun j => rnd η (x.1 j) (x.2.1 j))) x.2.2) with hG2
  have h2 : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) := by fun_prop
  have hsnd : Measurable (fun x : (Fin k → ℝ) × ((Fin k → ℝ) × ℝ) => x.2.2) :=
    measurable_snd.comp measurable_snd
  have hm1 : Measurable G1 := by
    refine meas_G (α := (Fin k → ℝ) × ((Fin k → ℝ) × ℝ)) v f (fun x => eu x.1) ?_
      (fun x => x.2.2) hsnd
    exact h2.comp measurable_fst
  have hm2 : Measurable G2 := by
    refine meas_G (α := (Fin k → ℝ) × ((Fin k → ℝ) × ℝ)) v f
      (fun x => eu (fun j => rnd η (x.1 j) (x.2.1 j))) ?_ (fun x => x.2.2) hsnd
    refine h2.comp (measurable_pi_lambda _ (fun j => ?_))
    have hpair : Measurable (fun x : (Fin k → ℝ) × ((Fin k → ℝ) × ℝ) =>
        ((x.1 j, x.2.1 j) : ℝ × ℝ)) :=
      ((measurable_pi_apply j).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))
    have := (meas_rnd η).comp hpair
    exact this
  have hi1 : Integrable G1 ((Measure.pi fun _ : Fin k => gam).prod (Pz k η)) :=
    Aux12.integrable_bdd _ hm1 _ (fun x => Aux12.f_bdd f _)
  have hi2 : Integrable G2 ((Measure.pi fun _ : Fin k => gam).prod (Pz k η)) :=
    Aux12.integrable_bdd _ hm2 _ (fun x => Aux12.f_bdd f _)
  have e1 : ∫ ω, f (threshSet v (Zv ω) ω.2) ∂(PP k η) =
      ∫ x, G1 x ∂((Measure.pi fun _ : Fin k => gam).prod (Pz k η)) :=
    (T0_mp k η).integral_comp' G1
  have e2 : ∫ ω, f (threshSet v (Yv η ω) ω.2) ∂(PP k η) =
      ∫ x, G2 x ∂((Measure.pi fun _ : Fin k => gam).prod (Pz k η)) :=
    (T0_mp k η).integral_comp' G2
  rw [e1, e2, integral_prod _ hi1, integral_prod _ hi2]
  have hz : ∀ z : Fin k → ℝ, ∫ q, G1 (z, q) ∂(Pz k η) - OPT f * η ≤ ∫ q, G2 (z, q) ∂(Pz k η) :=
    fun z => lower_fixed_z η hη f hf0 hf v hv z
  have hint1 := hi1.integral_prod_left
  have hint2 := hi2.integral_prod_left
  have hint3 : Integrable (fun z : Fin k → ℝ => ∫ q, G1 (z, q) ∂(Pz k η) - OPT f * η)
      (Measure.pi fun _ : Fin k => gam) := hint1.sub (integrable_const _)
  have := integral_mono hint3 hint2 hz
  have hsub : ∫ z : Fin k → ℝ, (∫ q, G1 (z, q) ∂(Pz k η) - OPT f * η) ∂(Measure.pi fun _ : Fin k => gam)
      = (∫ z : Fin k → ℝ, ∫ q, G1 (z, q) ∂(Pz k η) ∂(Measure.pi fun _ : Fin k => gam)) - OPT f * η := by
    rw [integral_sub hint1 (integrable_const _)]
    simp
  linarith


end UniversalSubmod.Dev.Thm12D

namespace UniversalSubmod.Dev.Thm12D

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared
open scoped RealInnerProductSpace

lemma u01_map_one_sub : u01.map (fun u : ℝ => 1 - u) = u01 := by
  have h1 : MeasurePreserving (fun u : ℝ => 1 - u) volume volume := Measure.measurePreserving_sub_left volume 1
  have e1 : u01 = volume.restrict (Set.Ioo (0:ℝ) 1) := by
    exact (Measure.restrict_congr_set Ioo_ae_eq_Ico).symm
  have e2 : (fun u : ℝ => 1 - u) ⁻¹' Set.Ioo (0:ℝ) 1 = Set.Ioo (0:ℝ) 1 := by
    ext x; simp only [Set.mem_preimage, Set.mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have := (h1.restrict_preimage (measurableSet_Ioo (a := (0:ℝ)) (b := 1))).map_eq
  rw [e2] at this
  rw [e1]; exact this

lemma gam_map_neg : gam.map (fun x : ℝ => -x) = gam := by
  have := gaussianReal_map_neg (μ := 0) (v := 1)
  simpa using this

lemma kap_map_neg (η : ℝ) : (kap η).map (fun x : ℝ => -x) = kap η := by
  have := gaussianReal_map_neg (μ := 0) (v := η.toNNReal)
  simpa using this

/-- the reflection `(z, u, τ) ↦ (-z, 1-u, -τ)` -/
def sig1 (k : ℕ) (w : Fin k → ℝ × ℝ) : Fin k → ℝ × ℝ := fun j => (-(w j).1, 1 - (w j).2)

def sig (k : ℕ) (ω : (Fin k → ℝ × ℝ) × ℝ) : (Fin k → ℝ × ℝ) × ℝ := (sig1 k ω.1, -ω.2)

lemma sig_mp (k : ℕ) (η : ℝ) : MeasurePreserving (sig k) (PP k η) (PP k η) := by
  haveI := u01_prob
  have hg : MeasurePreserving (fun p : ℝ × ℝ => ((-p.1, 1 - p.2) : ℝ × ℝ)) (gam.prod u01)
      (gam.prod u01) := by
    have h1 : MeasurePreserving (fun z : ℝ => -z) gam gam := ⟨measurable_neg, gam_map_neg⟩
    have h2 : MeasurePreserving (fun u : ℝ => 1 - u) u01 u01 :=
      ⟨measurable_const.sub measurable_id, u01_map_one_sub⟩
    exact h1.prod h2
  have hσ1 : MeasurePreserving (sig1 k) (Measure.pi fun _ : Fin k => gam.prod u01)
      (Measure.pi fun _ : Fin k => gam.prod u01) :=
    measurePreserving_pi (fun _ : Fin k => gam.prod u01) (fun _ : Fin k => gam.prod u01)
      (fun _ => hg)
  have hn : MeasurePreserving (fun x : ℝ => -x) (kap η) (kap η) := ⟨measurable_neg, kap_map_neg η⟩
  exact hσ1.prod hn

lemma PP_coord_map (k : ℕ) (η : ℝ) (j : Fin k) :
    (PP k η).map (fun ω => ω.1 j) = gam.prod u01 := by
  haveI := u01_prob
  have h1 : (PP k η).map Prod.fst = Measure.pi (fun _ : Fin k => gam.prod u01) := by
    unfold PP; rw [Measure.map_fst_prod]; simp
  have := Measure.map_map (μ := PP k η) (measurable_pi_apply j) measurable_fst
  simp only [Function.comp_def] at this
  rw [← this, h1]
  exact (measurePreserving_eval (fun _ : Fin k => gam.prod u01) j).map_eq

lemma ae_no_int (k : ℕ) (η : ℝ) :
    ∀ᵐ ω ∂(PP k η), ∀ (j : Fin k) (m : ℤ), (ω.1 j).1 / η + (ω.1 j).2 ≠ m := by
  haveI := u01_prob
  rw [ae_all_iff]; intro j
  rw [ae_all_iff]; intro m
  have hE : MeasurableSet {p : ℝ × ℝ | p.1 / η + p.2 = (m : ℝ)} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have h0 : (gam.prod u01) {p : ℝ × ℝ | p.1 / η + p.2 = (m : ℝ)} = 0 := by
    rw [Measure.measure_prod_null hE]
    refine Filter.Eventually.of_forall (fun z => ?_)
    have : Prod.mk z ⁻¹' {p : ℝ × ℝ | p.1 / η + p.2 = (m : ℝ)} = {(m : ℝ) - z / η} := by
      ext u; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    simp only [this, Pi.zero_apply]
    exact measure_singleton _
  have h1 : (PP k η) {ω | (ω.1 j).1 / η + (ω.1 j).2 = (m : ℝ)} = 0 := by
    have := Measure.map_apply (μ := PP k η) (f := fun ω => ω.1 j)
      ((measurable_pi_apply j).comp measurable_fst) hE
    rw [PP_coord_map] at this
    rw [h0] at this
    exact this.symm
  have : ∀ᵐ ω ∂(PP k η), ω ∉ {ω : (Fin k → ℝ × ℝ) × ℝ | (ω.1 j).1 / η + (ω.1 j).2 = (m : ℝ)} :=
    measure_eq_zero_iff_ae_notMem.1 h1
  filter_upwards [this] with ω hω
  simpa using hω

lemma ae_no_tie (k : ℕ) (η : ℝ) (hη : 0 < η) (g : (Fin k → ℝ × ℝ) → ℝ) (hg : Measurable g) :
    ∀ᵐ ω ∂(PP k η), g ω.1 ≠ ω.2 := by
  haveI := u01_prob
  have hηn : η.toNNReal ≠ 0 := by
    intro h; rw [Real.toNNReal_eq_zero] at h; linarith
  have hE : MeasurableSet {ω : (Fin k → ℝ × ℝ) × ℝ | g ω.1 = ω.2} :=
    measurableSet_eq_fun (hg.comp measurable_fst) measurable_snd
  have h0 : (PP k η) {ω : (Fin k → ℝ × ℝ) × ℝ | g ω.1 = ω.2} = 0 := by
    unfold PP
    rw [Measure.measure_prod_null hE]
    refine Filter.Eventually.of_forall (fun w => ?_)
    have : Prod.mk w ⁻¹' {ω : (Fin k → ℝ × ℝ) × ℝ | g ω.1 = ω.2} = {g w} := by
      ext t; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact eq_comm
    simp only [this, Pi.zero_apply]
    exact gaussianReal_absolutelyContinuous 0 hηn (by simp)
  have := measure_eq_zero_iff_ae_notMem.1 h0
  filter_upwards [this] with ω hω
  simpa using hω

lemma floor_one_sub (x : ℝ) (hx : ∀ m : ℤ, x ≠ m) : ⌊1 - x⌋ = -⌊x⌋ := by
  rw [Int.floor_eq_iff]
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne h1 (fun h => hx ⌊x⌋ h.symm)
  push_cast
  constructor <;> linarith

lemma rnd_neg (η z u : ℝ) (h : ∀ m : ℤ, z / η + u ≠ m) : rnd η (-z) (1 - u) = - rnd η z u := by
  unfold rnd
  have : -z / η + (1 - u) = 1 - (z / η + u) := by ring
  rw [this, floor_one_sub _ h]
  push_cast; ring

lemma Yv_sig (k : ℕ) (η : ℝ) (ω : (Fin k → ℝ × ℝ) × ℝ)
    (h : ∀ (j : Fin k) (m : ℤ), (ω.1 j).1 / η + (ω.1 j).2 ≠ m) :
    Yv η (sig k ω) = - Yv η ω := by
  ext j
  show rnd η (-(ω.1 j).1) (1 - (ω.1 j).2) = -(rnd η (ω.1 j).1 (ω.1 j).2)
  exact rnd_neg η _ _ (h j)

lemma thresh_sig {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin k)) (η : ℝ)
    (ω : (Fin k → ℝ × ℝ) × ℝ)
    (hint : ∀ (j : Fin k) (m : ℤ), (ω.1 j).1 / η + (ω.1 j).2 ≠ m)
    (htie : ∀ i, ⟪v i, Yv η ω⟫ ≠ ω.2) :
    threshSet v (Yv η (sig k ω)) (sig k ω).2 = (threshSet v (Yv η ω) ω.2)ᶜ := by
  ext i
  simp only [threshSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  rw [Yv_sig k η ω hint, inner_neg_right]
  show -ω.2 ≤ -⟪v i, Yv η ω⟫ ↔ ¬ ω.2 ≤ ⟪v i, Yv η ω⟫
  have := htie i
  constructor
  · intro h1 h2
    exact this (le_antisymm (by linarith) h2)
  · intro h1
    have := lt_of_not_ge h1
    linarith

lemma meas_inner_Yv {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin k)) (η : ℝ) (i : Fin n) :
    Measurable (fun w : Fin k → ℝ × ℝ => ⟪v i, eu (fun j => rnd η (w j).1 (w j).2)⟫) := by
  have h : Measurable (fun w : Fin k → ℝ × ℝ => (fun j => rnd η (w j).1 (w j).2)) :=
    measurable_pi_lambda _ (fun j => (meas_rnd η).comp (measurable_pi_apply j))
  have h2 : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) := by fun_prop
  have h3 : Measurable (fun w : Fin k → ℝ × ℝ => eu (fun j => rnd η (w j).1 (w j).2)) := by
    unfold eu; exact h2.comp h
  exact (continuous_const.inner continuous_id).measurable.comp h3

lemma ae_thresh_sig {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin k)) (η : ℝ) (hη : 0 < η) :
    ∀ᵐ ω ∂(PP k η), threshSet v (Yv η (sig k ω)) (sig k ω).2 = (threshSet v (Yv η ω) ω.2)ᶜ := by
  have h1 := ae_no_int k η
  have h2 : ∀ᵐ ω ∂(PP k η), ∀ i, ⟪v i, Yv η ω⟫ ≠ ω.2 := by
    rw [ae_all_iff]
    intro i
    exact ae_no_tie k η hη _ (meas_inner_Yv v η i)
  filter_upwards [h1, h2] with ω hω1 hω2
  exact thresh_sig v η ω hω1 hω2

lemma Yv_meas (k : ℕ) (η : ℝ) :
    Measurable (Yv η : (Fin k → ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin k)) := by
  have h : Measurable (fun ω : (Fin k → ℝ × ℝ) × ℝ => (fun j => rnd η (ω.1 j).1 (ω.1 j).2)) :=
    measurable_pi_lambda _ (fun j => (meas_rnd η).comp
      (((measurable_pi_apply j).comp measurable_fst)))
  have h2 : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) := by fun_prop
  exact h2.comp h

lemma sig_meas (k : ℕ) : Measurable (sig k : (Fin k → ℝ × ℝ) × ℝ → (Fin k → ℝ × ℝ) × ℝ) := by
  unfold sig sig1
  refine Measurable.prodMk ?_ (measurable_snd.neg)
  refine measurable_pi_lambda _ (fun j => ?_)
  exact (((measurable_pi_apply j).comp measurable_fst).fst.neg).prodMk
    (measurable_const.sub (((measurable_pi_apply j).comp measurable_fst).snd))

lemma int_sig (k : ℕ) (η : ℝ) (F : (Fin k → ℝ × ℝ) × ℝ → ℝ) (hF : Measurable F) :
    ∫ ω, F (sig k ω) ∂(PP k η) = ∫ ω, F ω ∂(PP k η) := by
  have := integral_map (μ := PP k η) (φ := sig k) (f := F) (sig_meas k).aemeasurable
    hF.aestronglyMeasurable
  rw [(sig_mp k η).map_eq] at this
  exact this.symm

lemma marginal_half {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin k)) (η : ℝ) (hη : 0 < η)
    (i : Fin n) :
    (PP k η).real {ω | i ∈ threshSet v (Yv η ω) ω.2} = 1 / 2 := by
  haveI := PP_prob k η
  set B : Set ((Fin k → ℝ × ℝ) × ℝ) := {ω | i ∈ threshSet v (Yv η ω) ω.2} with hB
  have hBm : MeasurableSet B := by
    have : B = {ω | ω.2 ≤ ⟪v i, Yv η ω⟫} := by
      ext ω; simp [hB, threshSet]
    rw [this]
    exact measurableSet_le measurable_snd
      ((continuous_const.inner continuous_id).measurable.comp (Yv_meas k η))
  have h1 : (PP k η) (sig k ⁻¹' B) = (PP k η) B :=
    (sig_mp k η).measure_preimage hBm.nullMeasurableSet
  have h2 : sig k ⁻¹' B =ᵐ[PP k η] Bᶜ := by
    refine Filter.eventuallyEq_set.2 ?_
    filter_upwards [ae_thresh_sig v η hη] with ω hω
    show i ∈ threshSet v (Yv η (sig k ω)) (sig k ω).2 ↔ ω ∈ Bᶜ
    rw [hω]
    simp [hB]
  have h3 : (PP k η) B = (PP k η) Bᶜ := by rw [← h1]; exact measure_congr h2
  have h4 : (PP k η).real B = (PP k η).real Bᶜ := by simp only [Measure.real, h3]
  rw [measureReal_compl hBm, probReal_univ] at h4
  linarith

lemma submod_compl {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : Submodular f) (A : Finset (Fin n)) :
    f ∅ + f Finset.univ ≤ f A + f Aᶜ := by
  have := hf A Aᶜ
  rwa [Finset.union_compl, Finset.inter_compl, add_comm] at this

theorem tail_sym {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin k)) (η : ℝ) (hη : 0 < η)
    (f : Finset (Fin n) → ℝ) (hf : Submodular f)
    (T : Set ((Fin k → ℝ × ℝ) × ℝ)) (hT : MeasurableSet T)
    (hTσ : sig k ⁻¹' T =ᵐ[PP k η] T) :
    (PP k η).real T * ((f ∅ + f Finset.univ) / 2) ≤
      ∫ ω, T.indicator (fun ω => f (threshSet v (Yv η ω) ω.2)) ω ∂(PP k η) := by
  haveI := PP_prob k η
  set H : (Fin k → ℝ × ℝ) × ℝ → ℝ := fun ω => f (threshSet v (Yv η ω) ω.2) with hH
  set H' : (Fin k → ℝ × ℝ) × ℝ → ℝ := fun ω => f ((threshSet v (Yv η ω) ω.2)ᶜ) with hH'
  have hHm : Measurable H := meas_G v f (Yv η) (Yv_meas k η) (fun ω => ω.2) measurable_snd
  have hH'm : Measurable H' := by
    refine Aux12.meas_comp (fun ω => (threshSet v (Yv η ω) ω.2)ᶜ) (fun i => ?_) f
    have : {ω : (Fin k → ℝ × ℝ) × ℝ | i ∈ (threshSet v (Yv η ω) ω.2)ᶜ}
        = {ω | i ∈ threshSet v (Yv η ω) ω.2}ᶜ := by ext ω; simp
    rw [this]
    refine MeasurableSet.compl ?_
    have : {ω : (Fin k → ℝ × ℝ) × ℝ | i ∈ threshSet v (Yv η ω) ω.2}
        = {ω | ω.2 ≤ ⟪v i, Yv η ω⟫} := by ext ω; simp [threshSet]
    rw [this]
    exact measurableSet_le measurable_snd
      ((continuous_const.inner continuous_id).measurable.comp (Yv_meas k η))
  set B : ℝ := ∑ S, |f S| with hB
  have hHi : Integrable H (PP k η) := Aux12.integrable_bdd _ hHm B (fun ω => Aux12.f_bdd f _)
  have hH'i : Integrable H' (PP k η) := Aux12.integrable_bdd _ hH'm B (fun ω => Aux12.f_bdd f _)
  have hFi : Integrable (T.indicator H) (PP k η) := hHi.indicator hT
  have hF'i : Integrable (T.indicator H') (PP k η) := hH'i.indicator hT
  -- reflection
  have hFm : Measurable (T.indicator H) := hHm.indicator hT
  have e1 : ∫ ω, T.indicator H (sig k ω) ∂(PP k η) = ∫ ω, T.indicator H ω ∂(PP k η) :=
    int_sig k η _ hFm
  have e2 : ∫ ω, T.indicator H (sig k ω) ∂(PP k η) = ∫ ω, T.indicator H' ω ∂(PP k η) := by
    refine integral_congr_ae ?_
    have h1 := Filter.eventuallyEq_set.1 hTσ
    filter_upwards [h1, ae_thresh_sig v η hη] with ω hω1 hω2
    by_cases hT' : ω ∈ T
    · have : sig k ω ∈ T := hω1.2 hT'
      rw [Set.indicator_of_mem this, Set.indicator_of_mem hT']
      show f (threshSet v (Yv η (sig k ω)) (sig k ω).2) = f ((threshSet v (Yv η ω) ω.2)ᶜ)
      rw [hω2]
    · have : sig k ω ∉ T := fun h => hT' (hω1.1 h)
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hT']
  have hineq : ∫ ω, T.indicator (fun _ => f ∅ + f Finset.univ) ω ∂(PP k η) ≤
      ∫ ω, T.indicator H ω + T.indicator H' ω ∂(PP k η) := by
    refine integral_mono ((integrable_const _).indicator hT) (hFi.add hF'i) (fun ω => ?_)
    by_cases h : ω ∈ T
    · simp only [Set.indicator_of_mem h]
      exact submod_compl f hf _
    · simp [Set.indicator_of_notMem h]
  rw [integral_add hFi hF'i, ← e2, e1] at hineq
  have e3 : ∫ ω, T.indicator (fun _ => f ∅ + f Finset.univ) ω ∂(PP k η)
      = (PP k η).real T * (f ∅ + f Finset.univ) := by
    rw [integral_indicator hT]
    simp [Measure.real, mul_comm]
  rw [e3] at hineq
  linarith

/-- the `k+1` independent real variables: `Y_1, …, Y_k` and `-τ` -/
noncomputable def UU (k : ℕ) (η : ℝ) : Option (Fin k) → (Fin k → ℝ × ℝ) × ℝ → ℝ
  | none => fun ω => -ω.2
  | some j => fun ω => rnd η (ω.1 j).1 (ω.1 j).2

lemma UU_meas (k : ℕ) (η : ℝ) (i : Option (Fin k)) : Measurable (UU k η i) := by
  cases i with
  | none => exact measurable_snd.neg
  | some j => exact (meas_rnd η).comp ((measurable_pi_apply j).comp measurable_fst)

lemma UU_indep (k : ℕ) (η : ℝ) : iIndepFun (UU k η) (PP k η) := by
  haveI := u01_prob
  haveI := PP_prob k η
  set ν : Measure ℝ := (gam.prod u01).map (fun p : ℝ × ℝ => rnd η p.1 p.2) with hν
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (meas_rnd η).aemeasurable
  set μ : Option (Fin k) → Measure ℝ := fun i => Option.elim i (kap η) (fun _ => ν) with hμ
  haveI hμprob : ∀ i, IsProbabilityMeasure (μ i) := by
    intro i; cases i with
    | none => exact (by infer_instance : IsProbabilityMeasure (kap η))
    | some j => exact this
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (UU_meas k η i).aemeasurable)]
  -- the marginals
  have hm : ∀ i, (PP k η).map (UU k η i) = μ i := by
    intro i
    cases i with
    | none =>
      have h1 := Measure.map_map (μ := PP k η) (measurable_neg (G := ℝ)) measurable_snd
      have h2 : (PP k η).map (fun ω => ω.2) = kap η := tau_law k η
      show (PP k η).map (fun ω => -ω.2) = kap η
      have : (fun ω : (Fin k → ℝ × ℝ) × ℝ => -ω.2) = (fun x : ℝ => -x) ∘ (fun ω => ω.2) := rfl
      rw [this, ← Measure.map_map measurable_neg measurable_snd, h2, kap_map_neg]
    | some j =>
      show (PP k η).map (fun ω => rnd η (ω.1 j).1 (ω.1 j).2) = ν
      have : (fun ω : (Fin k → ℝ × ℝ) × ℝ => rnd η (ω.1 j).1 (ω.1 j).2) =
          (fun p : ℝ × ℝ => rnd η p.1 p.2) ∘ (fun ω => ω.1 j) := rfl
      rw [this, ← Measure.map_map (meas_rnd η) ((measurable_pi_apply j).comp measurable_fst),
        PP_coord_map]
  simp_rw [hm]
  rw [← Measure.pi_map_piOptionEquivProd μ]
  -- the joint law
  have h1 : (Measure.pi fun _ : Fin k => gam.prod u01).map
      (fun w : Fin k → ℝ × ℝ => (fun j => rnd η (w j).1 (w j).2)) = Measure.pi (fun _ : Fin k => ν) := by
    have := Measure.pi_map_pi (μ := fun _ : Fin k => gam.prod u01)
      (f := fun _ => fun p : ℝ × ℝ => rnd η p.1 p.2) (fun _ => (meas_rnd η).aemeasurable)
    exact this
  have h2 : (PP k η).map (fun ω : (Fin k → ℝ × ℝ) × ℝ =>
      ((fun j => rnd η (ω.1 j).1 (ω.1 j).2, -ω.2) : (Fin k → ℝ) × ℝ)) =
      (Measure.pi (fun _ : Fin k => ν)).prod (kap η) := by
    have hG : Measurable (fun w : Fin k → ℝ × ℝ => (fun j => rnd η (w j).1 (w j).2)) :=
      measurable_pi_lambda _ (fun j => (meas_rnd η).comp (measurable_pi_apply j))
    have := Measure.map_prod_map (Measure.pi fun _ : Fin k => gam.prod u01) (kap η) hG
      (measurable_neg (G := ℝ))
    rw [h1, kap_map_neg] at this
    unfold PP
    rw [this]
    rfl
  have h3 : (fun ω : (Fin k → ℝ × ℝ) × ℝ => (fun i => UU k η i ω)) =
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin k) => ℝ)).symm ∘
        (fun ω : (Fin k → ℝ × ℝ) × ℝ =>
          ((fun j => rnd η (ω.1 j).1 (ω.1 j).2, -ω.2) : (Fin k → ℝ) × ℝ)) := by
    funext ω i
    cases i <;> rfl
  have hmeas : Measurable (fun ω : (Fin k → ℝ × ℝ) × ℝ =>
      ((fun j => rnd η (ω.1 j).1 (ω.1 j).2, -ω.2) : (Fin k → ℝ) × ℝ)) := by
    refine Measurable.prodMk ?_ measurable_snd.neg
    exact measurable_pi_lambda _ (fun j => (meas_rnd η).comp ((measurable_pi_apply j).comp measurable_fst))
  rw [h3, ← Measure.map_map (MeasurableEquiv.measurable _) hmeas, h2]
  have : (Measure.pi fun i => μ (some i)) = Measure.pi (fun _ : Fin k => ν) := rfl
  rw [this]
  rfl

theorem upper_PP {n k : ℕ} (η : ℝ) (hη : 0 < η)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hvpos : ∀ i l, 0 ≤ v i l)
    (f : Finset (Fin n) → ℝ) (hf : Submodular f) :
    ∫ ω, f (threshSet v (Yv η ω) ω.2) ∂(PP k η) ≤ (∑ S, f S) / 2 ^ n := by
  haveI := PP_prob k η
  classical
  set A : Fin n → Set (Option (Fin k) → ℝ) := fun i =>
    {w | 0 ≤ ⟪v i, eu (fun j => w (some j))⟫ + w none} with hA
  have hAm : ∀ i, MeasurableSet (A i) := by
    intro i
    have h1 : Measurable (fun w : Option (Fin k) → ℝ => eu (fun j => w (some j))) := by
      have h2 : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) := by fun_prop
      exact h2.comp (measurable_pi_lambda _ (fun j => measurable_pi_apply (some j)))
    have h3 : Measurable (fun w : Option (Fin k) → ℝ => ⟪v i, eu (fun j => w (some j))⟫) :=
      (continuous_const.inner continuous_id).measurable.comp h1
    exact measurableSet_le measurable_const (h3.add (measurable_pi_apply none))
  have hAmono : ∀ i, ∀ w w' : Option (Fin k) → ℝ, w ≤ w' → w ∈ A i → w' ∈ A i := by
    intro i w w' hw hwA
    simp only [hA, Set.mem_setOf_eq] at hwA ⊢
    have h1 : ⟪v i, eu (fun j => w (some j))⟫ ≤ ⟪v i, eu (fun j => w' (some j))⟫ := by
      simp only [eu, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      refine Finset.sum_le_sum (fun l _ => ?_)
      have := hvpos i l
      have h2 := hw (some l)
      show w (some l) * v i l ≤ w' (some l) * v i l
      exact mul_le_mul_of_nonneg_right h2 this
    have := hw none
    linarith
  have key := inl_lemma_4_3 (PP k η) (UU k η) (UU_meas k η) (UU_indep k η) A hAm hAmono f hf
  have hiff : ∀ ω i, ((fun j => UU k η j ω) ∈ A i) ↔ i ∈ threshSet v (Yv η ω) ω.2 := by
    intro ω i
    simp only [hA, Set.mem_setOf_eq, threshSet, Finset.mem_filter, Finset.mem_univ, true_and]
    show 0 ≤ ⟪v i, eu (fun j => rnd η (ω.1 j).1 (ω.1 j).2)⟫ + -ω.2 ↔
      ω.2 ≤ ⟪v i, eu (fun j => rnd η (ω.1 j).1 (ω.1 j).2)⟫
    constructor <;> intro h <;> linarith
  have e1 : ∀ ω, Finset.univ.filter (fun i => (fun j => UU k η j ω) ∈ A i) =
      threshSet v (Yv η ω) ω.2 := by
    intro ω; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hiff ω i
  have e2 : ∀ i, (PP k η).real {ω | (fun j => UU k η j ω) ∈ A i} = 1 / 2 := by
    intro i
    rw [← marginal_half v η hη i]
    congr 1
    ext ω; exact hiff ω i
  simp only [e1, e2] at key
  rw [Aux12.F_half] at key
  exact key

lemma Z_sq_int (k : ℕ) (η : ℝ) (j : Fin k) :
    ∫ ω : (Fin k → ℝ × ℝ) × ℝ, ((ω.1 j).1) ^ 2 ∂(PP k η) = 1 := by
  haveI := u01_prob
  have h1 : (gam.prod u01).map Prod.fst = gam := by rw [Measure.map_fst_prod]; simp
  have := integral_map (μ := PP k η) (φ := fun ω => ω.1 j) (f := fun p : ℝ × ℝ => p.1 ^ 2)
    ((measurable_pi_apply j).comp measurable_fst).aemeasurable
    (by rw [PP_coord_map]; exact (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 ^ 2).aestronglyMeasurable)
  rw [PP_coord_map] at this
  rw [← this]
  have := integral_map (μ := gam.prod u01) (φ := Prod.fst) (f := fun x : ℝ => x ^ 2)
    measurable_fst.aemeasurable (by rw [h1]; exact (by fun_prop : Measurable fun x : ℝ => x ^ 2).aestronglyMeasurable)
  rw [h1] at this
  rw [← this]
  exact Aux12.gauss_second

lemma Z_sq_integrable (k : ℕ) (η : ℝ) (j : Fin k) :
    Integrable (fun ω : (Fin k → ℝ × ℝ) × ℝ => ((ω.1 j).1) ^ 2) (PP k η) := by
  haveI := u01_prob
  have h1 : (gam.prod u01).map Prod.fst = gam := by rw [Measure.map_fst_prod]; simp
  have h2 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (gam.prod u01) := by
    have : Integrable (fun x : ℝ => x ^ 2) ((gam.prod u01).map Prod.fst) := by
      rw [h1]; exact Aux12.gauss_int_sq
    have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 ^ 2) ((gam.prod u01)) :=
      (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 ^ 2).aestronglyMeasurable
    have hm' : AEStronglyMeasurable (fun x : ℝ => x ^ 2) ((gam.prod u01).map Prod.fst) := by
      rw [h1]; exact (by fun_prop : Measurable fun x : ℝ => x ^ 2).aestronglyMeasurable
    exact (integrable_map_measure hm' measurable_fst.aemeasurable).1 this
  have h3 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) ((PP k η).map (fun ω => ω.1 j)) := by
    rw [PP_coord_map]; exact h2
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 ^ 2) ((PP k η).map (fun ω => ω.1 j)) := by
    rw [PP_coord_map]; exact (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 ^ 2).aestronglyMeasurable
  exact (integrable_map_measure hm
    ((measurable_pi_apply j).comp measurable_fst).aemeasurable).1 h3

lemma PP_ae_mem (k : ℕ) (η : ℝ) : ∀ᵐ ω ∂(PP k η), ∀ j, (ω.1 j).2 ∈ Set.Ico (0:ℝ) 1 := by
  haveI := u01_prob
  rw [ae_all_iff]
  intro j
  have h1 : (gam.prod u01).map Prod.snd = u01 := by rw [Measure.map_snd_prod]; simp
  have h : ∀ᵐ x ∂u01, x ∈ Set.Ico (0:ℝ) 1 := ae_restrict_mem measurableSet_Ico
  rw [← h1] at h
  have h2 := (ae_map_iff measurable_snd.aemeasurable measurableSet_Ico).1 h
  rw [← PP_coord_map k η j] at h2
  exact (ae_map_iff ((measurable_pi_apply j).comp measurable_fst).aemeasurable
    (measurableSet_Ico.preimage measurable_snd)).1 h2

theorem tail_prob (k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1 / 2) :
    (PP k η).real {ω | 3 * k / η ≤ ‖Yv η ω‖ ^ 2} ≤ η := by
  haveI := PP_prob k η
  have hnorm : ∀ ω : (Fin k → ℝ × ℝ) × ℝ, ‖Yv η ω‖ ^ 2 = ∑ j, (rnd η (ω.1 j).1 (ω.1 j).2) ^ 2 := by
    intro ω
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  have hmeasj : ∀ j : Fin k, Measurable (fun ω : (Fin k → ℝ × ℝ) × ℝ => rnd η (ω.1 j).1 (ω.1 j).2) :=
    fun j => (meas_rnd η).comp ((measurable_pi_apply j).comp measurable_fst)
  have hf2m : Measurable (fun ω : (Fin k → ℝ × ℝ) × ℝ => ‖Yv η ω‖ ^ 2) := by
    simp_rw [hnorm]
    exact Finset.measurable_sum _ (fun j _ => (hmeasj j).pow_const 2)
  -- pointwise domination
  have hdom : ∀ᵐ ω ∂(PP k η), ‖Yv η ω‖ ^ 2 ≤ ∑ j : Fin k, (2 * ((ω.1 j).1) ^ 2 + 2 * η ^ 2) := by
    filter_upwards [PP_ae_mem k η] with ω hω
    rw [hnorm]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have h := rnd_bound η (ω.1 j).1 (ω.1 j).2 hη (hω j)
    have h2 : (rnd η (ω.1 j).1 (ω.1 j).2 - (ω.1 j).1) ^ 2 ≤ η ^ 2 := by
      nlinarith [abs_nonneg (rnd η (ω.1 j).1 (ω.1 j).2 - (ω.1 j).1),
        sq_abs (rnd η (ω.1 j).1 (ω.1 j).2 - (ω.1 j).1)]
    nlinarith [sq_nonneg (rnd η (ω.1 j).1 (ω.1 j).2 - 2 * (ω.1 j).1)]
  have hg_int : Integrable (fun ω : (Fin k → ℝ × ℝ) × ℝ =>
      ∑ j : Fin k, (2 * ((ω.1 j).1) ^ 2 + 2 * η ^ 2)) (PP k η) := by
    refine integrable_finset_sum _ (fun j _ => ?_)
    exact ((Z_sq_integrable k η j).const_mul 2).add (integrable_const _)
  have hf2_int : Integrable (fun ω : (Fin k → ℝ × ℝ) × ℝ => ‖Yv η ω‖ ^ 2) (PP k η) := by
    refine hg_int.mono' hf2m.aestronglyMeasurable ?_
    filter_upwards [hdom] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hω
  have hint : ∫ ω, ‖Yv η ω‖ ^ 2 ∂(PP k η) ≤ 3 * k := by
    calc ∫ ω, ‖Yv η ω‖ ^ 2 ∂(PP k η)
        ≤ ∫ ω, ∑ j : Fin k, (2 * ((ω.1 j).1) ^ 2 + 2 * η ^ 2) ∂(PP k η) :=
          integral_mono_ae hf2_int hg_int hdom
      _ = ∑ j : Fin k, ∫ ω, (2 * ((ω.1 j).1) ^ 2 + 2 * η ^ 2) ∂(PP k η) :=
          integral_finset_sum _ (fun j _ => ((Z_sq_integrable k η j).const_mul 2).add
            (integrable_const _))
      _ = ∑ j : Fin k, (2 + 2 * η ^ 2) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [integral_add ((Z_sq_integrable k η j).const_mul 2) (integrable_const _),
            integral_const_mul, Z_sq_int]
          simp
      _ ≤ 3 * k := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have : 2 + 2 * η ^ 2 ≤ 3 := by nlinarith
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
          nlinarith
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := PP k η)
    (f := fun ω => ‖Yv η ω‖ ^ 2) (Filter.Eventually.of_forall (fun ω => sq_nonneg _)) hf2_int
    (3 * k / η)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : 0 < 3 * (k : ℝ) / η := by positivity
  have : 3 * (k : ℝ) / η * (PP k η).real {ω | 3 * k / η ≤ ‖Yv η ω‖ ^ 2} ≤ 3 * k :=
    hmk.trans hint
  rw [div_mul_eq_mul_div, div_le_iff₀ hη] at this
  nlinarith


end UniversalSubmod.Dev.Thm12D

namespace UniversalSubmod.Dev.Thm12D3

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared
open scoped RealInnerProductSpace
open UniversalSubmod.Dev.Thm12D

/-- the at most `n+1` sets `{i | t ≤ c i}` -/
noncomputable def chainSets {n : ℕ} (c : Fin n → ℝ) : Finset (Finset (Fin n)) :=
  insert ∅ ((Finset.univ.image c).image (fun s => Finset.univ.filter (fun i => s ≤ c i)))

lemma chainSets_card {n : ℕ} (c : Fin n → ℝ) : (chainSets c).card ≤ n + 1 := by
  unfold chainSets
  refine (Finset.card_insert_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := Finset.univ.image c)
    (f := fun s => Finset.univ.filter (fun i => s ≤ c i))
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := c)
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  omega

lemma mem_chainSets {n : ℕ} (c : Fin n → ℝ) (t : ℝ) :
    Finset.univ.filter (fun i => t ≤ c i) ∈ chainSets c := by
  classical
  by_cases h : (Finset.univ.filter (fun i => t ≤ c i)).Nonempty
  · obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun i => t ≤ c i)) c h
    unfold chainSets
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨c i0, Finset.mem_image_of_mem c (Finset.mem_univ _), ?_⟩)
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      have := (Finset.mem_filter.1 hi0).2
      linarith
    · intro hi
      exact hmin i (by simpa using hi)
  · unfold chainSets
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h]
    exact Finset.mem_insert_self _ _

lemma meas_val {α : Type*} [MeasurableSpace α] {n : ℕ} (R : α → Finset (Fin n))
    (hR : ∀ i, MeasurableSet {a | i ∈ R a}) (S : Finset (Fin n)) :
    MeasurableSet {a | R a = S} := by
  classical
  have := Aux12.meas_comp R hR (fun S' => if S' = S then (1 : ℝ) else 0)
  have h : {a | R a = S} = (fun a => if R a = S then (1 : ℝ) else 0) ⁻¹' {1} := by
    ext a; by_cases h : R a = S <;> simp [h]
  rw [h]
  exact this (measurableSet_singleton _)

lemma sum_val {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P] {n : ℕ}
    (R : α → Finset (Fin n)) (hR : ∀ i, MeasurableSet {a | i ∈ R a})
    (A : Set α) (hA : MeasurableSet A) (g : Finset (Fin n) → ℝ) :
    ∑ S, g S * P.real {a | a ∈ A ∧ R a = S} = ∫ a, A.indicator (fun a => g (R a)) a ∂P := by
  classical
  have hset : ∀ S, MeasurableSet {a | a ∈ A ∧ R a = S} := fun S =>
    hA.inter (meas_val R hR S)
  have hpt : ∀ a, A.indicator (fun a => g (R a)) a =
      ∑ S, g S * ({a | a ∈ A ∧ R a = S}.indicator (fun _ => (1 : ℝ)) a) := by
    intro a
    rw [Finset.sum_eq_single (R a)]
    · by_cases ha : a ∈ A
      · have h2 : a ∈ {a_1 | a_1 ∈ A ∧ R a_1 = R a} := ⟨ha, rfl⟩
        rw [Set.indicator_of_mem ha, Set.indicator_of_mem h2, mul_one]
      · have h2 : a ∉ {a_1 | a_1 ∈ A ∧ R a_1 = R a} := fun h => ha h.1
        rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem h2, mul_zero]
    · intro S _ hS
      have : a ∉ {a | a ∈ A ∧ R a = S} := fun h => hS h.2.symm
      simp [Set.indicator_of_notMem this]
    · simp
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [integral_const_mul, integral_indicator (hset S), setIntegral_const]
    simp [Measure.real]
  · intro S _
    exact ((integrable_const (1 : ℝ)).indicator (hset S)).const_mul _

lemma R_mem {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin k)) (η : ℝ) (hη0 : 0 < η) (ρ : ℝ)
    (hρ : ρ ^ 2 = 3 * k / η ^ 3) (ω : (Fin k → ℝ × ℝ) × ℝ)
    (hω : ¬ 3 * k / η < ‖Yv η ω‖ ^ 2) :
    ∃ y : Fin k → ℤ, ∑ i, ((y i : ℤ) : ℝ) ^ 2 ≤ ρ ^ 2 ∧
      threshSet v (Yv η ω) ω.2 ∈ chainSets (fun i => ⟪v i, eu (fun j => η * ((y j : ℤ) : ℝ))⟫) := by
  refine ⟨fun j => ⌊(ω.1 j).1 / η + (ω.1 j).2⌋, ?_, ?_⟩
  · have h1 : ‖Yv η ω‖ ^ 2 = η ^ 2 * ∑ j, ((⌊(ω.1 j).1 / η + (ω.1 j).2⌋ : ℤ) : ℝ) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      show (η * ((⌊(ω.1 j).1 / η + (ω.1 j).2⌋ : ℤ) : ℝ)) ^ 2 = _
      ring
    have h2 : ‖Yv η ω‖ ^ 2 ≤ 3 * k / η := not_lt.1 hω
    rw [h1] at h2
    rw [hρ]
    have h3 : η ^ 2 * ∑ j, ((⌊(ω.1 j).1 / η + (ω.1 j).2⌋ : ℤ) : ℝ) ^ 2 ≤ 3 * k / η := h2
    have hη2 : 0 < η ^ 2 := by positivity
    rw [le_div_iff₀ (by positivity)]
    have : (η ^ 2 * ∑ j, ((⌊(ω.1 j).1 / η + (ω.1 j).2⌋ : ℤ) : ℝ) ^ 2) * η ≤ 3 * k / η * η := by
      gcongr
    rw [div_mul_cancel₀ _ hη0.ne'] at this
    nlinarith
  · have : Yv η ω = eu (fun j => η * ((⌊(ω.1 j).1 / η + (ω.1 j).2⌋ : ℤ) : ℝ)) := rfl
    rw [this]
    show Finset.univ.filter (fun i => ω.2 ≤ ⟪v i, eu (fun j => η * ((⌊(ω.1 j).1 / η + (ω.1 j).2⌋ : ℤ) : ℝ))⟫) ∈ _
    exact mem_chainSets _ ω.2

theorem construct {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1 / 2)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ = 1) (hvnn : ∀ i l, 0 ≤ v i l)
    (hvv : ∀ i j, i ≠ j → ⟪v i, v j⟫ ≤ η) :
    ∃ w : Finset (Fin n) → ℝ, (∀ S, 0 ≤ w S) ∧ ∑ S, w S = 1 ∧
      ((Finset.univ.filter (fun S => 0 < w S)).card : ℝ) ≤
        ((n : ℝ) + 3) * (2 * Real.sqrt (3 * k / η ^ 3) *
          Real.sqrt (2 * Real.pi * Real.exp 1 / k)) ^ k ∧
      ∀ f : Finset (Fin n) → ℝ, (∀ S, 0 ≤ f S) → Submodular f →
        (∑ S, w S * f S ≤ (∑ S, f S) / 2 ^ n) ∧
        (1 - 2 * Real.sqrt η - 8 * η) * ((∑ S, f S) / 2 ^ n) ≤ ∑ S, w S * f S := by
  classical
  haveI := PP_prob k η
  set R : (Fin k → ℝ × ℝ) × ℝ → Finset (Fin n) := fun ω => threshSet v (Yv η ω) ω.2 with hR
  have hRm : ∀ i, MeasurableSet {ω | i ∈ R ω} := by
    intro i
    have : {ω : (Fin k → ℝ × ℝ) × ℝ | i ∈ R ω} = {ω | ω.2 ≤ ⟪v i, Yv η ω⟫} := by
      ext ω; simp [hR, threshSet]
    rw [this]
    exact measurableSet_le measurable_snd
      ((continuous_const.inner continuous_id).measurable.comp (Yv_meas k η))
  set T : Set ((Fin k → ℝ × ℝ) × ℝ) := {ω | 3 * k / η < ‖Yv η ω‖ ^ 2} with hT
  have hTm : MeasurableSet T :=
    measurableSet_lt measurable_const ((Yv_meas k η).norm.pow_const 2)
  set q : ℝ := (PP k η).real T with hq
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hqη : q ≤ η := by
    refine le_trans (measureReal_mono (fun ω hω => (le_of_lt hω : 3 * (k : ℝ) / η ≤ ‖Yv η ω‖ ^ 2))
      (measure_ne_top _ _)) (tail_prob k hk η hη0 hη1.le)
  set w : Finset (Fin n) → ℝ := fun S =>
    (PP k η).real {ω | ω ∈ Tᶜ ∧ R ω = S} + (if S = ∅ then q / 2 else 0)
      + (if S = Finset.univ then q / 2 else 0) with hw
  -- the identity for sums
  have hsumw : ∀ g : Finset (Fin n) → ℝ, ∑ S, w S * g S =
      ∫ ω, Tᶜ.indicator (fun ω => g (R ω)) ω ∂(PP k η) + q / 2 * (g ∅ + g Finset.univ) := by
    intro g
    have h1 := sum_val (PP k η) R hRm Tᶜ hTm.compl g
    have e1 : ∑ S, w S * g S = (∑ S, g S * (PP k η).real {ω | ω ∈ Tᶜ ∧ R ω = S})
        + q / 2 * g ∅ + q / 2 * g Finset.univ := by
      simp only [hw, add_mul, Finset.sum_add_distrib]
      congr 1
      · congr 1
        · refine Finset.sum_congr rfl (fun S _ => ?_); ring
        · simp [ite_mul, Finset.sum_ite_eq']
      · simp [ite_mul, Finset.sum_ite_eq']
    rw [e1, h1]; ring
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro S
    simp only [hw]
    have := measureReal_nonneg (μ := PP k η) (s := {ω | ω ∈ Tᶜ ∧ R ω = S})
    have h1 : 0 ≤ (if S = ∅ then q / 2 else 0) := by split_ifs <;> linarith
    have h2 : 0 ≤ (if S = Finset.univ then q / 2 else 0) := by split_ifs <;> linarith
    linarith
  · have := hsumw (fun _ => 1)
    simp only [mul_one] at this
    rw [this]
    have h1 : ∫ ω, Tᶜ.indicator (fun _ => (1 : ℝ)) ω ∂(PP k η) = 1 - q := by
      rw [integral_indicator hTm.compl, setIntegral_const, smul_eq_mul, mul_one,
        measureReal_compl hTm, probReal_univ]
    rw [h1]; ring
  · -- support
    set ρ : ℝ := Real.sqrt (3 * k / η ^ 3) with hρ
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hη3 : η ^ 3 < 1 := by
      have : η ^ 3 ≤ η := by nlinarith [sq_nonneg η, mul_pos hη0 hη0]
      linarith
    have hρsq : ρ ^ 2 = 3 * k / η ^ 3 := Real.sq_sqrt (by positivity)
    have hρ0 : Real.sqrt k / 2 ≤ ρ := by
      rw [hρ]
      apply Real.le_sqrt_of_sq_le
      have h1 : (Real.sqrt k / 2) ^ 2 = k / 4 := by
        rw [div_pow, Real.sq_sqrt hk0.le]; norm_num
      rw [h1, le_div_iff₀ (by positivity)]
      nlinarith [pow_pos hη0 3]
    obtain ⟨hfin, hc1, hc2, hc3⟩ := lattice_count k hk ρ hρ0
    set Bfin := hfin.toFinset with hBfin
    have hBcard : (Bfin.card : ℝ) ≤
        (2 * ρ * Real.sqrt (2 * Real.pi * Real.exp 1 / k)) ^ k := by
      have h1 := Set.ncard_eq_toFinset_card _ hfin
      rw [← hBfin] at h1
      rw [← h1]
      calc _ ≤ _ := hc1
        _ ≤ _ := mul_le_mul_of_nonneg_left hc2 (by positivity)
        _ = _ := hc3
    set Fset : Finset (Finset (Fin n)) := Bfin.biUnion (fun y =>
      chainSets (fun i => ⟪v i, eu (fun j => η * ((y j : ℤ) : ℝ))⟫)) ∪ {∅, Finset.univ} with hF
    have hFcard : Fset.card ≤ (n + 1) * Bfin.card + 2 := by
      refine (Finset.card_union_le _ _).trans ?_
      have h1 : (Bfin.biUnion (fun y =>
          chainSets (fun i => ⟪v i, eu (fun j => η * ((y j : ℤ) : ℝ))⟫))).card ≤
          (n + 1) * Bfin.card := by
        refine Finset.card_biUnion_le.trans ?_
        calc ∑ y ∈ Bfin, (chainSets (fun i => ⟪v i, eu (fun j => η * ((y j : ℤ) : ℝ))⟫)).card
            ≤ ∑ y ∈ Bfin, (n + 1) := Finset.sum_le_sum (fun y _ => chainSets_card _)
          _ = Bfin.card * (n + 1) := by simp
          _ = (n + 1) * Bfin.card := mul_comm _ _
      have h2 : ({∅, Finset.univ} : Finset (Finset (Fin n))).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      omega
    have hB1 : 1 ≤ Bfin.card := by
      rw [Nat.one_le_iff_ne_zero]
      intro h
      rw [Finset.card_eq_zero] at h
      have : (fun _ : Fin k => (0 : ℤ)) ∈ Bfin := by
        rw [hBfin, Set.Finite.mem_toFinset]
        show ∑ i, (((fun _ : Fin k => (0 : ℤ)) i : ℤ) : ℝ) ^ 2 ≤ ρ ^ 2
        simp [sq_nonneg ρ]
      rw [h] at this
      simp at this
    have hsupp : Finset.univ.filter (fun S => 0 < w S) ⊆ Fset := by
      intro S hS
      rw [Finset.mem_filter] at hS
      by_contra hnot
      have hne : S ≠ ∅ := fun h => hnot (by
        rw [hF]; exact Finset.mem_union_right _ (by simp [h]))
      have hnu : S ≠ Finset.univ := fun h => hnot (by
        rw [hF]; exact Finset.mem_union_right _ (by simp [h]))
      have hempty : {ω : (Fin k → ℝ × ℝ) × ℝ | ω ∈ Tᶜ ∧ R ω = S} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hωT hRS
        obtain ⟨y, hy, hmem⟩ := R_mem v η hη0 ρ hρsq ω hωT
        apply hnot
        rw [hF]
        refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨y, ?_, ?_⟩)
        · rw [hBfin, Set.Finite.mem_toFinset]; exact hy
        · rw [← hRS]; exact hmem
      have : w S = 0 := by
        simp only [hw, hempty, measureReal_empty, hne, hnu, if_false, add_zero]
      linarith [hS.2]
    have hcard : (Finset.univ.filter (fun S => 0 < w S)).card ≤ (n + 3) * Bfin.card := by
      refine (Finset.card_le_card hsupp).trans (hFcard.trans ?_)
      nlinarith
    calc ((Finset.univ.filter (fun S => 0 < w S)).card : ℝ) ≤ ((n + 3) * Bfin.card : ℕ) := by
          exact_mod_cast hcard
      _ = ((n : ℝ) + 3) * Bfin.card := by push_cast; ring
      _ ≤ ((n : ℝ) + 3) * (2 * ρ * Real.sqrt (2 * Real.pi * Real.exp 1 / k)) ^ k :=
          mul_le_mul_of_nonneg_left hBcard (by positivity)
  · intro f hf0 hf
    set avg : ℝ := (∑ S, f S) / 2 ^ n with havg
    set M : ℝ := OPT f with hM
    have hM0 : 0 ≤ M := (hf0 ∅).trans (Finset.le_sup' f (Finset.mem_univ ∅))
    have hfM : ∀ S, f S ≤ M := fun S => Finset.le_sup' f (Finset.mem_univ S)
    have hMle : M ≤ 4 * avg := by
      have := lemma_2_1 f hf0 hf (1 / 2) (by norm_num) (by norm_num)
      rw [Aux12.F_half] at this
      rw [hM]; linarith
    set H : (Fin k → ℝ × ℝ) × ℝ → ℝ := fun ω => f (R ω) with hH
    have hHm : Measurable H := meas_G v f (Yv η) (Yv_meas k η) (fun ω => ω.2) measurable_snd
    set B : ℝ := ∑ S, |f S| with hB
    have hHi : Integrable H (PP k η) := Aux12.integrable_bdd _ hHm B (fun ω => Aux12.f_bdd f _)
    have hsplit : ∫ ω, H ω ∂(PP k η) = ∫ ω, T.indicator H ω ∂(PP k η)
        + ∫ ω, Tᶜ.indicator H ω ∂(PP k η) := by
      rw [← integral_add (hHi.indicator hTm) (hHi.indicator hTm.compl)]
      congr 1; funext ω
      have := congrFun (Set.indicator_self_add_compl T H) ω
      simpa using this.symm
    have hTσ : sig k ⁻¹' T =ᵐ[PP k η] T := by
      refine Filter.eventuallyEq_set.2 ?_
      filter_upwards [ae_no_int k η] with ω hω
      show (3 * (k : ℝ) / η < ‖Yv η (sig k ω)‖ ^ 2) ↔ (3 * (k : ℝ) / η < ‖Yv η ω‖ ^ 2)
      rw [Yv_sig k η ω hω, norm_neg]
    have hsym := tail_sym v η hη0 f hf T hTm hTσ
    have hup := upper_PP η hη0 v hvnn f hf
    have hlow := lower_coupling η hη0 f hf0 hf v hv
    have hcor := cor41_PP n k hn hk η hη0 hη1 v hv hvv f hf0 hf
    have hS := hsumw f
    -- the tail integral is at most `M q`
    have hT_le : ∫ ω, T.indicator H ω ∂(PP k η) ≤ M * q := by
      have : ∫ ω, T.indicator H ω ∂(PP k η) ≤ ∫ ω, T.indicator (fun _ => M) ω ∂(PP k η) := by
        refine integral_mono (hHi.indicator hTm) ((integrable_const _).indicator hTm) (fun ω => ?_)
        by_cases h : ω ∈ T
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; exact hfM _
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      refine this.trans (le_of_eq ?_)
      rw [integral_indicator hTm, setIntegral_const, smul_eq_mul, hq]
      ring
    constructor
    · rw [hS]
      have hsym' : q / 2 * (f ∅ + f Finset.univ) ≤ ∫ ω, T.indicator H ω ∂(PP k η) := by
        have := hsym
        simp only [hq]
        linarith
      have : ∫ ω, H ω ∂(PP k η) ≤ avg := hup
      linarith
    · rw [hS]
      have hnn : 0 ≤ q / 2 * (f ∅ + f Finset.univ) := by
        have := hf0 ∅; have := hf0 Finset.univ; positivity
      have hZ : (1 - 2 * Real.sqrt η) * avg ≤ ∫ ω, f (threshSet v (Zv ω) ω.2) ∂(PP k η) := hcor
      have hY : ∫ ω, f (threshSet v (Zv ω) ω.2) ∂(PP k η) - M * η ≤ ∫ ω, H ω ∂(PP k η) := hlow
      have hMq : M * q ≤ M * η := mul_le_mul_of_nonneg_left hqη hM0
      have hMη : M * η ≤ 4 * avg * η := mul_le_mul_of_nonneg_right hMle hη0.le
      nlinarith


end UniversalSubmod.Dev.Thm12D3

namespace UniversalSubmod.Dev.Thm12E

lemma ln405 : Real.log 405 ≤ 7 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have h2 : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by gcongr; linarith
  have h3 : Real.exp 1 ^ 7 = Real.exp 7 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h3] at h2
  norm_num at h2
  linarith

/-- the final polynomial-exponent estimate -/
lemma support_arith (n : ℕ) (hn : 2 ≤ n) (ε₀ : ℝ) (h0 : 0 < ε₀) (h1 : ε₀ ≤ 1 / 4) (k : ℕ)
    (hk : (k : ℝ) ≤ 2000 * Real.log n / (((ε₀ / 3) ^ 2) ^ 2) + 1) (X : ℝ) (hX0 : 0 ≤ X)
    (hX : X ≤ 405 / ε₀ ^ 3) :
    ((n : ℝ) + 3) * X ^ k ≤
      (n : ℝ) ^ (1200000 * (1 / ε₀ ^ 4) * (1 + Real.log (1 / ε₀))) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set L : ℝ := Real.log n with hL
  have hL0 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hn'
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hLhalf : 1 / 2 < L := lt_of_lt_of_le hlog2 hL0
  set a : ℝ := 1 / ε₀ ^ 4 with ha
  set b : ℝ := Real.log (1 / ε₀) with hb
  have ha1 : 256 ≤ a := by
    rw [ha, le_div_iff₀ (by positivity)]
    have : ε₀ ^ 4 ≤ (1 / 4) ^ 4 := by gcongr
    nlinarith
  have hb0 : 0 ≤ b := by
    rw [hb]; apply Real.log_nonneg
    rw [le_div_iff₀ h0]; linarith
  -- k bound
  have hk2 : (k : ℝ) ≤ 162002 * a * L := by
    have e : 2000 * L / (((ε₀ / 3) ^ 2) ^ 2) = 162000 * a * L := by
      rw [ha]; field_simp; ring
    rw [e] at hk
    nlinarith
  -- X ≤ ... in log form
  have hXpos : 0 < 405 / ε₀ ^ 3 := by positivity
  have hXk : X ^ k ≤ (405 / ε₀ ^ 3) ^ k := pow_le_pow_left₀ hX0 hX k
  have hlogX : Real.log (405 / ε₀ ^ 3) ≤ 7 * (1 + b) := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_pow]
    have : Real.log ε₀ = - b := by
      rw [hb, one_div, Real.log_inv]; ring
    rw [this]
    have := ln405
    push_cast
    nlinarith
  have hexpk : (405 / ε₀ ^ 3) ^ k = Real.exp (k * Real.log (405 / ε₀ ^ 3)) := by
    rw [Real.exp_nat_mul, Real.exp_log hXpos]
  have hn3 : (n : ℝ) + 3 ≤ (n : ℝ) ^ 3 := by nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hexpn : (n : ℝ) ^ 3 = Real.exp (3 * L) := by
    rw [hL, show (3 : ℝ) * Real.log n = ((3 : ℕ) : ℝ) * Real.log n by norm_num, Real.exp_nat_mul,
      Real.exp_log hnpos]
  have hXk' : X ^ k ≤ Real.exp (k * (7 * (1 + b))) := by
    refine hXk.trans ?_
    rw [hexpk]
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_left hlogX (Nat.cast_nonneg _)
  have hrp : (n : ℝ) ^ (1200000 * a * (1 + b)) = Real.exp (L * (1200000 * a * (1 + b))) := by
    rw [Real.rpow_def_of_pos hnpos]
  rw [hrp]
  calc ((n : ℝ) + 3) * X ^ k ≤ Real.exp (3 * L) * Real.exp (k * (7 * (1 + b))) := by
        have := mul_le_mul hn3 hXk' (by positivity) (by positivity)
        rwa [hexpn] at this
    _ = Real.exp (3 * L + k * (7 * (1 + b))) := (Real.exp_add _ _).symm
    _ ≤ _ := by
        apply Real.exp_le_exp.2
        have h1b : 0 ≤ 1 + b := by linarith
        have hab : 1 ≤ a * (1 + b) := by nlinarith
        have hk3 : (k : ℝ) * (7 * (1 + b)) ≤ 162002 * a * L * (7 * (1 + b)) :=
          mul_le_mul_of_nonneg_right hk2 (by positivity)
        have hL1 : 3 * L ≤ 3 * a * (1 + b) * L := by nlinarith
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ a) h1b) (by linarith : (0:ℝ) ≤ L)]


lemma X_bound (k : ℕ) (hk : 1 ≤ k) (ε₀ : ℝ) (h0 : 0 < ε₀) :
    2 * Real.sqrt (3 * k / ((ε₀ / 3) ^ 2) ^ 3) * Real.sqrt (2 * Real.pi * Real.exp 1 / k)
      ≤ 405 / ε₀ ^ 3 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set η : ℝ := (ε₀ / 3) ^ 2 with hη
  have hη0 : 0 < η := by positivity
  have hX0 : 0 ≤ 2 * Real.sqrt (3 * k / η ^ 3) * Real.sqrt (2 * Real.pi * Real.exp 1 / k) := by
    positivity
  have hsq : (2 * Real.sqrt (3 * k / η ^ 3) * Real.sqrt (2 * Real.pi * Real.exp 1 / k)) ^ 2
      = 24 * Real.pi * Real.exp 1 / η ^ 3 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
    ring
  rw [← pow_le_pow_iff_left₀ hX0 (by positivity) (two_ne_zero), hsq]
  have hpi : Real.pi < 3.15 := by linarith [Real.pi_lt_d2]
  have he : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have hpe : Real.pi * Real.exp 1 ≤ 9.375 := by
    nlinarith [Real.pi_pos, Real.exp_pos 1]
  have e1 : η ^ 3 = ε₀ ^ 6 / 729 := by rw [hη]; ring
  rw [e1, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have h6 : 0 < ε₀ ^ 6 := by positivity
  have : 24 * Real.pi * Real.exp 1 * 729 ≤ 405 ^ 2 := by nlinarith
  have h7 : ε₀ ^ 6 * 405 ^ 2 = (405 : ℝ) ^ 2 * ε₀ ^ 6 := by ring
  nlinarith [mul_le_mul_of_nonneg_right this h6.le]

end UniversalSubmod.Dev.Thm12E

namespace UniversalSubmod.Supplement

open NonmonotoneSubmod.Shared

theorem chk_theorem_1_2 :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ n : ℕ, 2 ≤ n →
      ∃ w : Finset (Fin n) → ℝ,
        (∀ S, 0 ≤ w S) ∧ (∑ S, w S) = 1 ∧
        ((Finset.univ.filter (fun S => 0 < w S)).card : ℝ) ≤
          (n : ℝ) ^ (C * (1 / ε ^ 4) * (1 + Real.log (1 / ε))) ∧
        ∀ f : Finset (Fin n) → ℝ, (∀ S, 0 ≤ f S) → Submodular f →
          (∑ S, w S * f S) ≤ (∑ S, f S) / 2 ^ n ∧
          (1 - ε) * ((∑ S, f S) / 2 ^ n) ≤ ∑ S, w S * f S := by
  refine ⟨1000000000, ?_⟩
  intro ε hε0 hε1 n hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  set ε₀ : ℝ := min ε (1 / 4) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε0 (by norm_num)
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  have hε₀4 : ε₀ ≤ 1 / 4 := min_le_right _ _
  set η : ℝ := (ε₀ / 3) ^ 2 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η < 1 / 2 := by
    rw [hη]; nlinarith
  have hsqrt : Real.sqrt η = ε₀ / 3 := by
    rw [hη]; exact Real.sqrt_sq (by positivity)
  set k : ℕ := ⌈2000 * Real.log n / η ^ 2⌉₊ with hk
  have hkge : 2000 * Real.log n / η ^ 2 ≤ (k : ℝ) := Nat.le_ceil _
  have hk1 : 1 ≤ k := by
    rw [hk]; exact Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 (by positivity)))
  have hkle : (k : ℝ) ≤ 2000 * Real.log n / η ^ 2 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hkeq : 2000 * Real.log n ≤ η ^ 2 * k := by
    have : 2000 * Real.log n / η ^ 2 * η ^ 2 ≤ k * η ^ 2 := mul_le_mul_of_nonneg_right hkge (by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at this
    linarith
  obtain ⟨v, hv, hvnn, hvv⟩ := inl_lemma_4_2 n k hn η hη0 (by linarith) hkeq
  obtain ⟨w, hw0, hw1, hcard, hf⟩ :=
    Dev.Thm12D3.construct (by omega) hk1 η hη0 hη1 v hv hvnn hvv
  refine ⟨w, hw0, hw1, ?_, ?_⟩
  · refine hcard.trans ?_
    have hX := Dev.Thm12E.X_bound k hk1 ε₀ hε₀0
    have hX0 : 0 ≤ 2 * Real.sqrt (3 * k / η ^ 3) * Real.sqrt (2 * Real.pi * Real.exp 1 / k) := by
      positivity
    have hk' : (k : ℝ) ≤ 2000 * Real.log n / (((ε₀ / 3) ^ 2) ^ 2) + 1 := hkle
    have key := Dev.Thm12E.support_arith n hn ε₀ hε₀0 hε₀4 k hk' _ hX0 hX
    refine key.trans ?_
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    -- compare the exponents
    have hb1 : 0 ≤ Real.log (1 / ε₀) := by
      apply Real.log_nonneg; rw [le_div_iff₀ hε₀0]; linarith
    have hb2 : 0 ≤ Real.log (1 / ε) := by
      apply Real.log_nonneg; rw [le_div_iff₀ hε0]; linarith
    by_cases hcase : ε ≤ 1 / 4
    · have : ε₀ = ε := min_eq_left hcase
      rw [this]
      have h1 : 0 ≤ 1 / ε ^ 4 * (1 + Real.log (1 / ε)) := by positivity
      nlinarith
    · push_neg at hcase
      have : ε₀ = 1 / 4 := min_eq_right hcase.le
      have hlog4 : Real.log (1 / ε₀) ≤ 2 := by
        rw [this, one_div_one_div]
        have := Real.log_two_lt_d9
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        linarith
      have h4 : 1 / ε₀ ^ 4 = 256 := by rw [this]; norm_num
      rw [h4]
      have h5 : 1 ≤ 1 / ε ^ 4 := by
        rw [le_div_iff₀ (by positivity)]
        have : ε ^ 4 ≤ 1 := pow_le_one₀ hε0.le hε1.le
        linarith
      have h6 : 1 ≤ 1 + Real.log (1 / ε) := by linarith
      have h7 : 1 ≤ 1 / ε ^ 4 * (1 + Real.log (1 / ε)) := by nlinarith
      nlinarith
  · intro f hf0 hsub
    obtain ⟨hup, hlow⟩ := hf f hf0 hsub
    refine ⟨hup, ?_⟩
    have havg : 0 ≤ (∑ S, f S) / 2 ^ n := by
      have := Finset.sum_nonneg (fun S (_ : S ∈ Finset.univ) => hf0 S)
      positivity
    have : 1 - ε ≤ 1 - 2 * Real.sqrt η - 8 * η := by
      rw [hsqrt, hη]
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_right this havg) hlow

end UniversalSubmod.Supplement
end

theorem solution : type_of% @UniversalSubmod.Supplement.chk_theorem_1_2 := @UniversalSubmod.Supplement.chk_theorem_1_2

-- Prove2me | solution 1 for SPPRevenue.SingleUnit.eq_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T08:56:17.561638+00:00
-- url     : https://prove2.me/submissions/02fee3e4-5148-4522-a6b3-a6d45b2e299d

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

section

open MeasureTheory Set
open scoped ENNReal

namespace SPPAux
open SPPRevenue.SingleUnit

variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
  (t : Fin n → (Fin n → ℝ) → ℝ)

lemma sStarI_antitone (i : Fin n) : Antitone (sStarI μ t i) := fun a b hab =>
  measure_mono fun _ hv => ⟨hv.1, le_trans hab hv.2⟩

lemma sStar_antitone : Antitone (sStar μ t) := by
  intro a b hab
  exact Finset.sum_le_sum fun i _ => sStarI_antitone μ t i hab

lemma opt_eq (hm : ∀ i, Measurable (t i)) (hnn : ∀ i v, 0 ≤ t i v) :
    optRev μ t = ∫⁻ τ in Ioi 0, sStar μ t τ := by
  unfold optRev sStar
  have hmeasA : ∀ i, MeasurableSet {v : Fin n → ℝ | t i v ≤ v i} := fun i =>
    measurableSet_le (hm i) (measurable_pi_apply i)
  rw [lintegral_finsetSum _ (fun i _ =>
    Measurable.ite (hmeasA i) (hm i).ennreal_ofReal measurable_const)]
  rw [lintegral_finsetSum' _ (fun i _ => (sStarI_antitone μ t i).measurable.aemeasurable)]
  refine Finset.sum_congr rfl fun i _ => ?_
  set g : (Fin n → ℝ) → ℝ := fun v => if t i v ≤ v i then t i v else 0 with hg
  have hfun : (fun v => if t i v ≤ v i then ENNReal.ofReal (t i v) else 0) =
      fun v => ENNReal.ofReal (g v) := by
    funext v; simp only [hg]; split_ifs <;> simp
  have hgm : Measurable g := Measurable.ite (hmeasA i) (hm i) measurable_const
  have hg0 : ∀ v, 0 ≤ g v := fun v => by simp only [hg]; split_ifs; exacts [hnn i v, le_rfl]
  rw [hfun, lintegral_eq_lintegral_meas_le _ (ae_of_all _ hg0) hgm.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
  have hτ0 : 0 < τ := hτ
  unfold sStarI
  congr 1
  ext v
  simp only [hg, mem_setOf_eq]
  split_ifs with h
  · exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
  · exact ⟨fun h' => absurd h' (not_le.2 hτ0), fun h' => absurd h'.1 h⟩

lemma measA (ht : IsThresholdMech μ t) (τ : ℝ) (i : Fin n) :
    MeasurableSet {v : Fin n → ℝ | t i v ≤ v i ∧ τ ≤ t i v} :=
  (measurableSet_le (ht.measurable i) (measurable_pi_apply i)).inter
    (measurableSet_le measurable_const (ht.measurable i))

lemma sStar_eq_union (ht : IsThresholdMech μ t) (τ : ℝ) :
    sStar μ t τ = Measure.pi μ (⋃ i ∈ (Finset.univ : Finset (Fin n)),
      {v : Fin n → ℝ | t i v ≤ v i ∧ τ ≤ t i v}) := by
  unfold sStar sStarI
  rw [measure_biUnion_finset₀]
  · intro i _ j _ hij
    refine measure_mono_null ?_ (ae_iff.1 ht.single_unit)
    intro v hv
    simp only [mem_setOf_eq, not_forall]
    exact ⟨i, j, hv.1.1, hv.2.1, hij⟩
  · exact fun i _ => (measA μ t ht τ i).nullMeasurableSet

lemma sStar_le_one (ht : IsThresholdMech μ t) (τ : ℝ) : sStar μ t τ ≤ 1 := by
  rw [sStar_eq_union μ t ht]; exact prob_le_one

lemma up_bound (ht : IsThresholdMech μ t) (τ : ℝ) :
    ENNReal.ofReal τ * sStar μ t τ ≤ sppRev μ (fun _ => τ) := by
  rw [sStar_eq_union μ t ht]
  set U := ⋃ i ∈ (Finset.univ : Finset (Fin n)), {v : Fin n → ℝ | t i v ≤ v i ∧ τ ≤ t i v}
  have hU : MeasurableSet U := Finset.measurableSet_biUnion _ fun i _ => measA μ t ht τ i
  rw [← lintegral_indicator_const hU]
  unfold sppRev
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ U
  · rw [indicator_of_mem hv]
    simp only [U, mem_iUnion, Finset.mem_univ, exists_true_left, mem_setOf_eq] at hv
    obtain ⟨i, h1, h2⟩ := hv
    unfold sppRevAt
    exact Finset.le_sup (f := fun i => ENNReal.ofReal ((fun _ => τ) i))
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, le_trans h2 h1⟩)
  · rw [indicator_of_notMem hv]; exact zero_le

lemma mp_le (ht : IsThresholdMech μ t) (X : ℝ≥0∞)
    (h : ∀ p : Fin n → ℝ, (∀ i, 0 ≤ p i) → sppRev μ p ≤ X) : mpRev μ t ≤ X := by
  unfold mpRev resampleLaw
  refine (lintegral_prod_le _).trans ?_
  calc ∫⁻ W, ∫⁻ v, sppRevAt (fun i => t i ((W, v).1 i)) (W, v).2 ∂(Measure.pi μ)
        ∂(Measure.pi fun _ : Fin n => Measure.pi μ)
      ≤ ∫⁻ _W, X ∂(Measure.pi fun _ : Fin n => Measure.pi μ) :=
        lintegral_mono fun W => h (fun i => t i (W i)) fun i => ht.nonneg i _
    _ = X := by rw [lintegral_const, measure_univ, mul_one]

end SPPAux

namespace SPPAux
open SPPRevenue.SingleUnit

variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
  (t : Fin n → (Fin n → ℝ) → ℝ)

instance resampleLaw_prob : IsProbabilityMeasure (resampleLaw μ) := by
  unfold resampleLaw; infer_instance

lemma sppRevAt_ne_top (p v : Fin n → ℝ) : sppRevAt p v ≠ ⊤ := by
  unfold sppRevAt
  exact ((Finset.sup_lt_iff (a := (⊤ : ℝ≥0∞)) bot_lt_top).2
    fun i _ => ENNReal.ofReal_lt_top).ne

lemma mp_ge (ht : IsThresholdMech μ t) :
    ∫⁻ τ in Ioi 0, mSell μ t τ ≤ mpRev μ t := by
  set E : Set (((Fin n → Fin n → ℝ) × (Fin n → ℝ)) × ℝ) :=
    {z | ∃ i, t i (z.1.1 i) ≤ z.1.2 i ∧ z.2 ≤ t i (z.1.1 i)} with hEdef
  have hE : MeasurableSet E := by
    have : E = ⋃ i, ({z : ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) × ℝ | t i (z.1.1 i) ≤ z.1.2 i} ∩
        {z | z.2 ≤ t i (z.1.1 i)}) := by
      ext z; simp [hEdef]
    rw [this]
    refine MeasurableSet.iUnion fun i => ?_
    have m1 : Measurable fun z : ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) × ℝ => t i (z.1.1 i) :=
      (ht.measurable i).comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))
    have m2 : Measurable fun z : ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) × ℝ => z.1.2 i :=
      (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
    exact (measurableSet_le m1 m2).inter (measurableSet_le measurable_snd m1)
  have hmS : ∀ τ, mSell μ t τ = ∫⁻ x, E.indicator 1 (x, τ) ∂(resampleLaw μ) := by
    intro τ
    have hs : MeasurableSet {x : (Fin n → Fin n → ℝ) × (Fin n → ℝ) | (x, τ) ∈ E} :=
      measurable_prodMk_right hE
    have := lintegral_indicator_one (μ := resampleLaw μ) hs
    unfold mSell
    exact this.symm
  simp_rw [hmS]
  rw [lintegral_lintegral_swap]
  · unfold mpRev
    refine lintegral_mono fun x => ?_
    set F := sppRevAt (fun i => t i (x.1 i)) x.2 with hF
    have hFtop : F ≠ ⊤ := sppRevAt_ne_top _ _
    have hle : ∀ τ, E.indicator 1 (x, τ) ≤ (Iic F.toReal).indicator (1 : ℝ → ℝ≥0∞) τ := by
      intro τ
      by_cases hxτ : (x, τ) ∈ E
      · rw [indicator_of_mem hxτ]
        obtain ⟨i, h1, h2⟩ := hxτ
        have hi : ENNReal.ofReal (t i (x.1 i)) ≤ F := by
          rw [hF]; unfold sppRevAt
          exact Finset.le_sup (f := fun j => ENNReal.ofReal ((fun j => t j (x.1 j)) j))
            (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩)
        have : τ ≤ F.toReal := le_trans h2 ((ENNReal.ofReal_le_iff_le_toReal hFtop).1 hi)
        rw [indicator_of_mem (show τ ∈ Iic F.toReal from this)]
        simp
      · rw [indicator_of_notMem hxτ]; exact zero_le
    calc ∫⁻ τ in Ioi 0, E.indicator 1 (x, τ)
        ≤ ∫⁻ τ in Ioi 0, (Iic F.toReal).indicator 1 τ := lintegral_mono hle
      _ = volume (Iic F.toReal ∩ Ioi 0) := by
        rw [lintegral_indicator_one measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
      _ ≤ volume (Ioc 0 F.toReal) := by
        apply measure_mono; intro y hy; exact ⟨hy.2, hy.1⟩
      _ = F := by rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_toReal hFtop]
  · exact ((measurable_one.indicator hE).comp measurable_swap).aemeasurable

end SPPAux

namespace SPPAux
open SPPRevenue.SingleUnit

variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
  (t : Fin n → (Fin n → ℝ) → ℝ)

lemma mp_update (i : Fin n) :
    MeasurePreserving (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) where
  measurable := measurable_update'
  map_eq := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
    have hpre : (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (Set.pi univ s) =
        (Set.pi univ (Function.update s i univ)) ×ˢ (s i) := by
      ext ⟨w, a⟩
      simp only [mem_preimage, mem_univ_pi, mem_prod]
      constructor
      · intro h
        refine ⟨fun j => ?_, ?_⟩
        · by_cases hj : j = i
          · subst hj; simp
          · have := h j; rw [Function.update_of_ne hj] at this
            rw [Function.update_of_ne hj]; exact this
        · have := h i; rwa [Function.update_self] at this
      · rintro ⟨h1, h2⟩ j
        by_cases hj : j = i
        · subst hj; rw [Function.update_self]; exact h2
        · rw [Function.update_of_ne hj]; have := h1 j; rwa [Function.update_of_ne hj] at this
    rw [hpre, Measure.prod_prod, Measure.pi_pi]
    rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (fun j => μ j (s j))]
    rw [Function.update_self, measure_univ, one_mul, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    have : j ≠ i := by simpa using hj
    rw [Function.update_of_ne this]

lemma prod_set_eq (ht : IsThresholdMech μ t) (τ : ℝ) (i : Fin n) :
    ((Measure.pi μ).prod (μ i)) {p : (Fin n → ℝ) × ℝ | t i p.1 ≤ p.2 ∧ τ ≤ t i p.1} =
      sStarI μ t i τ := by
  have hpre : (fun p : (Fin n → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹'
      {v : Fin n → ℝ | t i v ≤ v i ∧ τ ≤ t i v} =
      {p : (Fin n → ℝ) × ℝ | t i p.1 ≤ p.2 ∧ τ ≤ t i p.1} := by
    ext ⟨w, a⟩
    have h : t i (Function.update w i a) = t i w :=
      ht.indep_own i _ _ fun j hj => Function.update_of_ne hj _ _
    simp only [mem_preimage, mem_setOf_eq, h, Function.update_self]
  rw [← hpre, (mp_update μ i).measure_preimage (measA μ t ht τ i).nullMeasurableSet]
  rfl

lemma one_sub_le_exp (s : ℝ≥0∞) (hs : s ≤ 1) :
    1 - s ≤ ENNReal.ofReal (Real.exp (-s.toReal)) := by
  have hfin : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hs
  have : 1 - s = ENNReal.ofReal (1 - s.toReal) := by
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_toReal hfin]
  rw [this]
  apply ENNReal.ofReal_le_ofReal
  have := Real.add_one_le_exp (-s.toReal)
  linarith

lemma mSell_ge (ht : IsThresholdMech μ t) (τ : ℝ) :
    ENNReal.ofReal (1 - Real.exp (-(sStar μ t τ).toReal)) ≤ mSell μ t τ := by
  set A : Fin n → Set ((Fin n → ℝ) × ℝ) :=
    fun i => {p : (Fin n → ℝ) × ℝ | t i p.1 ≤ p.2 ∧ τ ≤ t i p.1} with hAdef
  have hA : ∀ i, MeasurableSet (A i) := fun i =>
    (measurableSet_le ((ht.measurable i).comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_const ((ht.measurable i).comp measurable_fst))
  set X : Set ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) :=
    {x | ∃ i, t i (x.1 i) ≤ x.2 i ∧ τ ≤ t i (x.1 i)} with hXdef
  have hX : MeasurableSet X := by
    have : X = ⋃ i, ({x : (Fin n → Fin n → ℝ) × (Fin n → ℝ) | t i (x.1 i) ≤ x.2 i} ∩
        {x | τ ≤ t i (x.1 i)}) := by
      ext z; simp [hXdef]
    rw [this]
    refine MeasurableSet.iUnion fun i => ?_
    have m1 : Measurable fun z : (Fin n → Fin n → ℝ) × (Fin n → ℝ) => t i (z.1 i) :=
      (ht.measurable i).comp ((measurable_pi_apply i).comp measurable_fst)
    have m2 : Measurable fun z : (Fin n → Fin n → ℝ) × (Fin n → ℝ) => z.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    exact (measurableSet_le m1 m2).inter (measurableSet_le measurable_const m1)
  -- measure of the complement
  have hmp := measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ) ℝ (Fin n)
    (fun _ => Measure.pi μ) μ
  have hcompl : resampleLaw μ Xᶜ = ∏ i, ((Measure.pi μ).prod (μ i)) (A i)ᶜ := by
    unfold resampleLaw
    rw [← hmp.measure_preimage hX.compl.nullMeasurableSet]
    have : (MeasurableEquiv.arrowProdEquivProdArrow (Fin n → ℝ) ℝ (Fin n)) ⁻¹' Xᶜ =
        Set.pi univ (fun i => (A i)ᶜ) := by
      ext f
      simp [hXdef, hAdef, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
    rw [this, Measure.pi_pi]
  have hprod : ∏ i, ((Measure.pi μ).prod (μ i)) (A i)ᶜ =
      ∏ i, (1 - sStarI μ t i τ) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [prob_compl_eq_one_sub (hA i), hAdef, prod_set_eq μ t ht τ i]
  have hsI1 : ∀ i, sStarI μ t i τ ≤ 1 := fun i => prob_le_one
  have hfinI : ∀ i, sStarI μ t i τ ≠ ⊤ := fun i => ne_top_of_le_ne_top ENNReal.one_ne_top (hsI1 i)
  have hbound : ∏ i, (1 - sStarI μ t i τ) ≤ ENNReal.ofReal (Real.exp (-(sStar μ t τ).toReal)) := by
    unfold sStar
    rw [ENNReal.toReal_sum fun i _ => hfinI i, ← Finset.sum_neg_distrib, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
    exact Finset.prod_le_prod' fun i _ => one_sub_le_exp _ (hsI1 i)
  have hm : mSell μ t τ = 1 - resampleLaw μ Xᶜ := by
    rw [prob_compl_eq_one_sub hX, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
    rfl
  rw [hm, hcompl, hprod, ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left hbound 1

end SPPAux

namespace SPPAux
open SPPRevenue.SingleUnit

variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
  (t : Fin n → (Fin n → ℝ) → ℝ)

lemma mp_le_int (ht : IsThresholdMech μ t) :
    mpRev μ t ≤ ∫⁻ τ in Ioi 0, mSell μ t τ := by
  set E : Set (((Fin n → Fin n → ℝ) × (Fin n → ℝ)) × ℝ) :=
    {z | ∃ i, t i (z.1.1 i) ≤ z.1.2 i ∧ z.2 ≤ t i (z.1.1 i)} with hEdef
  have hE : MeasurableSet E := by
    have : E = ⋃ i, ({z : ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) × ℝ | t i (z.1.1 i) ≤ z.1.2 i} ∩
        {z | z.2 ≤ t i (z.1.1 i)}) := by
      ext z; simp [hEdef]
    rw [this]
    refine MeasurableSet.iUnion fun i => ?_
    have m1 : Measurable fun z : ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) × ℝ => t i (z.1.1 i) :=
      (ht.measurable i).comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))
    have m2 : Measurable fun z : ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) × ℝ => z.1.2 i :=
      (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
    exact (measurableSet_le m1 m2).inter (measurableSet_le measurable_snd m1)
  have hmS : ∀ τ, mSell μ t τ = ∫⁻ x, E.indicator 1 (x, τ) ∂(resampleLaw μ) := by
    intro τ
    have hs : MeasurableSet {x : (Fin n → Fin n → ℝ) × (Fin n → ℝ) | (x, τ) ∈ E} :=
      measurable_prodMk_right hE
    have := lintegral_indicator_one (μ := resampleLaw μ) hs
    unfold mSell
    exact this.symm
  simp_rw [hmS]
  rw [lintegral_lintegral_swap]
  · unfold mpRev
    refine lintegral_mono fun x => ?_
    unfold sppRevAt
    set s := Finset.univ.filter (fun i => (fun i => t i (x.1 i)) i ≤ x.2 i) with hs
    by_cases hne : s.Nonempty
    · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup s hne
        (fun i => ENNReal.ofReal ((fun i => t i (x.1 i)) i))
      rw [hjeq]
      have hjmem := (Finset.mem_filter.1 hj).2
      have hle : ∀ τ, (Iic (t j (x.1 j))).indicator (1 : ℝ → ℝ≥0∞) τ ≤ E.indicator 1 (x, τ) := by
        intro τ
        by_cases hτ : τ ≤ t j (x.1 j)
        · rw [indicator_of_mem (show τ ∈ Iic (t j (x.1 j)) from hτ),
            indicator_of_mem (show (x, τ) ∈ E from ⟨j, hjmem, hτ⟩)]
          simp
        · rw [indicator_of_notMem (show τ ∉ Iic (t j (x.1 j)) from hτ)]; exact zero_le
      calc ENNReal.ofReal (t j (x.1 j)) = volume (Ioc 0 (t j (x.1 j))) := by
            rw [Real.volume_Ioc, sub_zero]
        _ = volume (Iic (t j (x.1 j)) ∩ Ioi 0) := by
            congr 1; ext y; simp [and_comm]
        _ = ∫⁻ τ in Ioi 0, (Iic (t j (x.1 j))).indicator 1 τ := by
            rw [lintegral_indicator_one measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
        _ ≤ ∫⁻ τ in Ioi 0, E.indicator 1 (x, τ) := lintegral_mono hle
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sup_empty]; exact zero_le
  · exact ((measurable_one.indicator hE).comp measurable_swap).aemeasurable

end SPPAux

end
open MeasureTheory Set
open scoped ENNReal
open SPPRevenue.SingleUnit

theorem solution {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (t : Fin n → (Fin n → ℝ) → ℝ) (ht : IsThresholdMech μ t) :
    mpRev μ t = ∫⁻ τ in Set.Ioi 0, mSell μ t τ ∧
      ∀ τ : ℝ, ENNReal.ofReal (1 - Real.exp (-(sStar μ t τ).toReal)) ≤ mSell μ t τ :=
  ⟨le_antisymm (SPPAux.mp_le_int μ t ht) (SPPAux.mp_ge μ t ht), SPPAux.mSell_ge μ t ht⟩

-- Prove2me | solution 1 for PermLimits.Existence.densities_determine_measure
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:01:06.12607+00:00
-- url     : https://prove2.me/submissions/b990be3b-7ba5-4798-9191-d3f4a810e39f

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_LimitMeasure
open PermLimits.Shared

namespace PermLimits.Existence

open unitInterval MeasureTheory Set Filter Topology

lemma aux_dm_quantile_le_iff {Z : I → I → ℝ} {x : I} (hx : IsCDF (Z x)) (u y : I) :
    quantile Z x u ≤ y ↔ (u : ℝ) ≤ Z x y := by
  constructor
  · intro h
    have h1 : (1 : I) ∈ {y : I | (u : ℝ) ≤ Z x y} := by
      show (u : ℝ) ≤ Z x 1
      rw [hx.2.2.2]; exact u.2.2
    have key : (u : ℝ) ≤ Z x (quantile Z x u) := by
      by_cases hs : quantile Z x u = 1
      · rw [hs]; exact h1
      · have hs1 : quantile Z x u < 1 := lt_of_le_of_ne unitInterval.le_one' hs
        have ht : ∀ t : I, quantile Z x u < t → (u : ℝ) ≤ Z x t := by
          intro t hst
          obtain ⟨b, hbS, hbt⟩ := (sInf_lt_iff).1 hst
          exact le_trans hbS (hx.1 hbt.le)
        have hc : ContinuousWithinAt (Z x) (Ioi (quantile Z x u)) (quantile Z x u) :=
          (hx.2.1 _).mono Ioi_subset_Ici_self
        have : (𝓝[>] (quantile Z x u)).NeBot := nhdsGT_neBot_of_exists_gt ⟨1, hs1⟩
        exact ge_of_tendsto hc (eventually_nhdsWithin_of_forall ht)
    exact key.trans (hx.1 h)
  · intro h
    exact sInf_le h

lemma aux_dm_aemeas_slice {Z : I → I → ℝ} (hZ : IsLimitPerm Z) (y : I) :
    AEMeasurable (fun x => Z x y) volume := by
  have hne : ∀ y : I, (y : ℝ) ≠ 0 → AEMeasurable (fun x => Z x y) volume := by
    intro y hy
    have : Integrable (fun x => Z x y) volume := by
      by_contra hni
      exact hy ((hZ.2.2.2 y).symm.trans (integral_undef hni))
    exact this.aemeasurable
  by_cases hy : (y : ℝ) = 0
  · have hy0 : y = 0 := Subtype.ext hy
    subst hy0
    let yn : ℕ → I := fun n => ⟨1 / ((n : ℝ) + 1), by
      constructor
      · positivity
      · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        rw [div_le_one (by positivity)]; linarith⟩
    have htend : Tendsto yn atTop (𝓝 0) := by
      rw [tendsto_subtype_rng]
      exact (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
    apply aemeasurable_of_tendsto_metrizable_ae' (f := fun n x => Z x (yn n))
    · intro n
      exact hne _ (by simp only [yn]; positivity)
    · filter_upwards with x
      have hc := (hZ.2.2.1 x).2.1 0
      have hcu : Ici (0 : I) = univ := by
        ext t; simp
      rw [ContinuousWithinAt, hcu, nhdsWithin_univ] at hc
      exact hc.comp htend
  · exact hne y hy

lemma aux_dm_aemeas_map {Z : I → I → ℝ} (hZ : IsLimitPerm Z) :
    AEMeasurable (fun p : I × I => (p.1, quantile Z p.1 p.2)) volume := by
  have hq : NullMeasurable (fun p : I × I => quantile Z p.1 p.2) volume := by
    have : @Measurable (NullMeasurableSpace (I × I) volume) I _ _
        (fun p : I × I => quantile Z p.1 p.2) := by
      apply measurable_of_Iic
      intro y
      have hset : (fun p : I × I => quantile Z p.1 p.2) ⁻¹' Iic y =
          {p : I × I | (p.2 : ℝ) ≤ Z p.1 y} := by
        ext p
        simp only [mem_preimage, mem_Iic, mem_setOf_eq]
        exact aux_dm_quantile_le_iff (hZ.2.2.1 p.1) p.2 y
      show NullMeasurableSet ((fun p : I × I => quantile Z p.1 p.2) ⁻¹' Iic y) volume
      rw [hset]
      apply nullMeasurableSet_le
      · exact (measurable_subtype_coe.comp measurable_snd).aemeasurable
      · rw [Measure.volume_eq_prod]
        exact (aux_dm_aemeas_slice hZ y).comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_fst
    exact this
  exact measurable_fst.aemeasurable.prodMk hq.aemeasurable

lemma aux_dm_prob {Z : I → I → ℝ} (hZ : IsLimitPerm Z) : IsProbabilityMeasure (limitMeasure Z) :=
  Measure.isProbabilityMeasure_map (aux_dm_aemeas_map hZ)

lemma aux_dm_fst {Z : I → I → ℝ} (hZ : IsLimitPerm Z) :
    (limitMeasure Z).map Prod.fst = volume := by
  unfold limitMeasure
  rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (aux_dm_aemeas_map hZ)]
  have : (Prod.fst ∘ fun p : I × I => (p.1, quantile Z p.1 p.2)) = Prod.fst := rfl
  rw [this, Measure.volume_eq_prod, Measure.map_fst_prod, measure_univ, one_smul]

lemma aux_dm_snd_Iic {Z : I → I → ℝ} (hZ : IsLimitPerm Z) (y : I) :
    volume {p : I × I | (p.2 : ℝ) ≤ Z p.1 y} = ENNReal.ofReal y := by
  have hB := aux_dm_aemeas_slice hZ y
  set h' := hB.mk _ with hh'
  have hh'm : Measurable h' := hB.measurable_mk
  have hae : (fun x => Z x y) =ᵐ[volume] h' := hB.ae_eq_mk
  have hS : {p : I × I | (p.2 : ℝ) ≤ Z p.1 y} =ᵐ[volume] {p : I × I | (p.2 : ℝ) ≤ h' p.1} := by
    rw [Measure.volume_eq_prod]
    have := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure I))
      (ν := (volume : Measure I))).ae_eq_comp hae
    filter_upwards [this] with p hp
    simp only [Function.comp] at hp
    show ((p.2 : ℝ) ≤ Z p.1 y) = ((p.2 : ℝ) ≤ h' p.1)
    rw [hp]
  have hint : Integrable (fun x => Z x y) volume :=
    (integrable_const (1 : ℝ)).mono' hB.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_le]
      have := hZ.2.1 x y
      constructor <;> linarith [this.1, this.2])
  rw [measure_congr hS, Measure.volume_eq_prod,
    Measure.prod_apply (measurableSet_le (f := fun p : I × I => (p.2 : ℝ))
      (g := fun p : I × I => h' p.1) (by fun_prop) (hh'm.comp measurable_fst))]
  rw [← hZ.2.2.2 y, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (hZ.2.1 x y).1)]
  apply lintegral_congr_ae
  filter_upwards [hae] with x hx
  have hc := hZ.2.1 x y
  have : Prod.mk x ⁻¹' {p : I × I | (p.2 : ℝ) ≤ h' p.1} = Iic ⟨Z x y, hc⟩ := by
    ext u
    simp only [mem_preimage, mem_setOf_eq, mem_Iic]
    rw [← hx]
    exact Iff.rfl
  rw [this, volume_Iic]

lemma aux_dm_snd {Z : I → I → ℝ} (hZ : IsLimitPerm Z) :
    (limitMeasure Z).map Prod.snd = volume := by
  have := aux_dm_prob hZ
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply measurable_snd measurableSet_Iic, limitMeasure,
    Measure.map_apply_of_aemeasurable (aux_dm_aemeas_map hZ) (measurable_snd measurableSet_Iic),
    volume_Iic, ← aux_dm_snd_Iic hZ y]
  congr 1
  ext p
  simp only [mem_preimage, mem_Iic, mem_setOf_eq]
  exact aux_dm_quantile_le_iff (hZ.2.2.1 p.1) p.2 y

lemma aux_dm_fst_lt {Z : I → I → ℝ} (hZ : IsLimitPerm Z) (t : I) :
    limitMeasure Z {a | a.1 < t} = ENNReal.ofReal t := by
  have := congrArg (fun m => m (Iio t)) (aux_dm_fst hZ)
  rw [Measure.map_apply measurable_fst measurableSet_Iio, volume_Iio] at this
  exact this

lemma aux_dm_snd_lt {Z : I → I → ℝ} (hZ : IsLimitPerm Z) (t : I) :
    limitMeasure Z {a | a.2 < t} = ENNReal.ofReal t := by
  have := congrArg (fun m => m (Iio t)) (aux_dm_snd hZ)
  rw [Measure.map_apply measurable_snd measurableSet_Iio, volume_Iio] at this
  exact this

lemma aux_dm_fst_eq {Z : I → I → ℝ} (hZ : IsLimitPerm Z) (t : I) :
    limitMeasure Z {a | a.1 = t} = 0 := by
  have := congrArg (fun m => m {t}) (aux_dm_fst hZ)
  rw [Measure.map_apply measurable_fst (measurableSet_singleton t), measure_singleton] at this
  exact this

lemma aux_dm_snd_eq {Z : I → I → ℝ} (hZ : IsLimitPerm Z) (t : I) :
    limitMeasure Z {a | a.2 = t} = 0 := by
  have := congrArg (fun m => m {t}) (aux_dm_snd hZ)
  rw [Measure.map_apply measurable_snd (measurableSet_singleton t), measure_singleton] at this
  exact this

/-- The cell of tuples sorted by `ρ` in the first coordinate with pattern `τ`. -/
def aux_dm_cell {k : ℕ} (τ ρ : Equiv.Perm (Fin k)) : Set (Fin k → I × I) :=
  {p | (∀ i j, i < j → (p (ρ i)).1 < (p (ρ j)).1) ∧
    ∀ i j, ((p (ρ i)).2 < (p (ρ j)).2 ↔ τ i < τ j)}

lemma aux_dm_pattern_eq {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    patternEvent τ = ⋃ ρ, aux_dm_cell τ ρ := by
  ext p; simp [patternEvent, aux_dm_cell]

lemma aux_dm_cell_meas {k : ℕ} (τ ρ : Equiv.Perm (Fin k)) : MeasurableSet (aux_dm_cell τ ρ) := by
  have h1 : ∀ a b : Fin k, MeasurableSet {p : Fin k → I × I | (p a).1 < (p b).1} := fun a b =>
    measurableSet_lt (measurable_fst.comp (measurable_pi_apply a))
      (measurable_fst.comp (measurable_pi_apply b))
  have h2 : ∀ a b : Fin k, MeasurableSet {p : Fin k → I × I | (p a).2 < (p b).2} := fun a b =>
    measurableSet_lt (measurable_snd.comp (measurable_pi_apply a))
      (measurable_snd.comp (measurable_pi_apply b))
  simp only [aux_dm_cell, setOf_and, setOf_forall]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    exact MeasurableSet.iInter fun _ => h1 _ _
  · refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : τ i < τ j
    · simp only [hij, iff_true]; exact h2 _ _
    · simp only [hij, iff_false]; exact (h2 _ _).compl

lemma aux_dm_perm_eq_one {k : ℕ} (π : Equiv.Perm (Fin k)) (h : StrictMono π) : π = 1 := by
  have := Subsingleton.elim (StrictMono.orderIsoOfSurjective π h π.surjective) (OrderIso.refl _)
  refine Equiv.ext fun i => ?_
  have := congrArg (fun f => f i) this
  simpa using this

lemma aux_dm_cell_unique {k : ℕ} {τ ρ τ' ρ' : Equiv.Perm (Fin k)} {p : Fin k → I × I}
    (h : p ∈ aux_dm_cell τ ρ) (h' : p ∈ aux_dm_cell τ' ρ') : ρ = ρ' ∧ τ = τ' := by
  have hs : StrictMono (fun i => (p (ρ i)).1) := fun i j hij => h.1 i j hij
  have hs' : StrictMono (fun i => (p (ρ' i)).1) := fun i j hij => h'.1 i j hij
  have hπ : StrictMono (ρ.trans ρ'.symm) := by
    intro i j hij
    have := hs hij
    apply hs'.lt_iff_lt.mp
    simpa using this
  have e1 := aux_dm_perm_eq_one _ hπ
  have hρ : ρ = ρ' := by
    refine Equiv.ext fun i => ?_
    have := congrArg (fun f : Equiv.Perm (Fin k) => f i) e1
    simp only [Equiv.trans_apply, Equiv.Perm.coe_one, id_eq] at this
    exact ρ'.symm_apply_eq.mp this
  subst hρ
  refine ⟨rfl, ?_⟩
  have hπ2 : StrictMono (τ.symm.trans τ') := by
    intro a b hab
    simp only [Equiv.trans_apply]
    rw [← h'.2, h.2]
    simpa using hab
  have e2 := aux_dm_perm_eq_one _ hπ2
  refine Equiv.ext fun a => ?_
  have := congrArg (fun f : Equiv.Perm (Fin k) => f (τ a)) e2
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.coe_one, id_eq] at this
  exact this.symm

lemma aux_dm_cover {k : ℕ} (p : Fin k → I × I) (h1 : Function.Injective fun m => (p m).1)
    (h2 : Function.Injective fun m => (p m).2) : ∃ τ ρ, p ∈ aux_dm_cell τ ρ := by
  set f := fun m => (p m).1 with hf
  set ρ := Tuple.sort f
  have hρ : StrictMono (f ∘ ρ) :=
    (Tuple.monotone_sort f).strictMono_of_injective (h1.comp ρ.injective)
  set g := fun i => (p (ρ i)).2 with hg
  set sg := Tuple.sort g
  have hsg : StrictMono (g ∘ sg) :=
    (Tuple.monotone_sort g).strictMono_of_injective ((h2.comp ρ.injective).comp sg.injective)
  refine ⟨sg.symm, ρ, fun i j hij => hρ hij, fun i j => ?_⟩
  have e1 : g i = (g ∘ sg) (sg.symm i) := by simp
  have e2 : g j = (g ∘ sg) (sg.symm j) := by simp
  show g i < g j ↔ _
  rw [e1, e2]
  exact hsg.lt_iff_lt

lemma aux_dm_cell_lt1 {k : ℕ} {τ ρ : Equiv.Perm (Fin k)} {p : Fin k → I × I}
    (hp : p ∈ aux_dm_cell τ ρ) (a b : Fin k) : (p a).1 < (p b).1 ↔ ρ.symm a < ρ.symm b := by
  have hs : StrictMono (fun i => (p (ρ i)).1) := fun i j hij => hp.1 i j hij
  have := hs.lt_iff_lt (a := ρ.symm a) (b := ρ.symm b)
  simpa using this

lemma aux_dm_cell_lt2 {k : ℕ} {τ ρ : Equiv.Perm (Fin k)} {p : Fin k → I × I}
    (hp : p ∈ aux_dm_cell τ ρ) (a b : Fin k) :
    (p a).2 < (p b).2 ↔ τ (ρ.symm a) < τ (ρ.symm b) := by
  have := hp.2 (ρ.symm a) (ρ.symm b)
  simpa using this

lemma aux_dm_tie1 {n : ℕ} (μ : Measure (I × I)) [IsProbabilityMeasure μ] (g : I × I → I)
    (hg : Measurable g) (h : ∀ t, μ {a | g a = t} = 0) (i j : Fin (n + 1)) (hij : i ≠ j) :
    (Measure.pi fun _ : Fin (n + 1) => μ) {p | g (p i) = g (p j)} = 0 := by
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hij.symm
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  have hpre : {p : Fin (n + 1) → I × I | g (p i) = g (p (i.succAbove j'))} =
      (MeasurableEquiv.piFinSuccAbove (fun _ => I × I) i) ⁻¹'
        {x : (I × I) × (Fin n → I × I) | g x.1 = g (x.2 j')} := by
    ext p
    simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth]
  rw [hpre, hmp.measure_preimage_equiv]
  rw [Measure.prod_apply_symm]
  · simp [h]
  · exact measurableSet_eq_fun (hg.comp measurable_fst)
      (hg.comp ((measurable_pi_apply j').comp measurable_snd))

lemma aux_dm_tie_null {n : ℕ} (μ : Measure (I × I)) [IsProbabilityMeasure μ]
    (h1 : ∀ t : I, μ {a | a.1 = t} = 0) (h2 : ∀ t : I, μ {a | a.2 = t} = 0) :
    (Measure.pi fun _ : Fin (n + 1) => μ)
      (⋃ x : Equiv.Perm (Fin (n + 1)) × Equiv.Perm (Fin (n + 1)), aux_dm_cell x.1 x.2)ᶜ = 0 := by
  apply measure_mono_null (t := ⋃ i : Fin (n + 1), ⋃ j : Fin (n + 1), ⋃ (_ : i ≠ j),
    ({p : Fin (n + 1) → I × I | (p i).1 = (p j).1} ∪ {p | (p i).2 = (p j).2}))
  · intro p hp
    simp only [mem_compl_iff, mem_iUnion, not_exists] at hp
    by_cases hi1 : Function.Injective fun m => (p m).1
    · by_cases hi2 : Function.Injective fun m => (p m).2
      · obtain ⟨τ, ρ, hc⟩ := aux_dm_cover p hi1 hi2
        exact absurd hc (hp (τ, ρ))
      · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 hi2
        simp only [mem_iUnion, mem_union, mem_setOf_eq]
        exact ⟨a, b, hne, Or.inr hab⟩
    · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 hi1
      simp only [mem_iUnion, mem_union, mem_setOf_eq]
      exact ⟨a, b, hne, Or.inl hab⟩
  · refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
    exact measure_union_null (aux_dm_tie1 μ Prod.fst measurable_fst h1 i j hij)
      (aux_dm_tie1 μ Prod.snd measurable_snd h2 i j hij)

lemma aux_dm_cell_perm {k : ℕ} (μ : Measure (I × I)) [IsProbabilityMeasure μ]
    (τ ρ : Equiv.Perm (Fin k)) :
    (Measure.pi fun _ : Fin k => μ) (aux_dm_cell τ ρ) =
      (Measure.pi fun _ : Fin k => μ) (aux_dm_cell τ 1) := by
  have hmp : MeasurePreserving (fun p : Fin k → I × I => p ∘ ρ)
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
    have := measurePreserving_arrowCongr' (fun _ : Fin k => μ) (fun _ : Fin k => μ) ρ.symm
      (MeasurableEquiv.refl (I × I)) (fun _ => MeasurePreserving.id μ)
    convert this using 1
    funext p
    rfl
  have : aux_dm_cell τ ρ = (fun p : Fin k → I × I => p ∘ ρ) ⁻¹' aux_dm_cell τ 1 := by
    ext p; simp [aux_dm_cell]
  rw [this, hmp.measure_preimage (aux_dm_cell_meas τ 1).nullMeasurableSet]

lemma aux_dm_cell_eq {k : ℕ} (μ ν : Measure (I × I)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (h : ∀ τ : Equiv.Perm (Fin k), (Measure.pi fun _ : Fin k => μ).real (patternEvent τ) =
      (Measure.pi fun _ : Fin k => ν).real (patternEvent τ)) (τ ρ : Equiv.Perm (Fin k)) :
    (Measure.pi fun _ : Fin k => μ) (aux_dm_cell τ ρ) =
      (Measure.pi fun _ : Fin k => ν) (aux_dm_cell τ ρ) := by
  have key : ∀ (m : Measure (I × I)) [IsProbabilityMeasure m],
      (Measure.pi fun _ : Fin k => m) (patternEvent τ) =
        (Fintype.card (Equiv.Perm (Fin k)) : ENNReal) *
          (Measure.pi fun _ : Fin k => m) (aux_dm_cell τ 1) := by
    intro m _
    rw [aux_dm_pattern_eq, measure_iUnion (fun a b hab => ?_) (fun ρ => aux_dm_cell_meas τ ρ),
      tsum_fintype]
    · simp_rw [aux_dm_cell_perm m τ]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    · rw [Function.onFun, Set.disjoint_left]
      intro p hpa hpb
      exact hab (aux_dm_cell_unique hpa hpb).1
  have hμν : (Measure.pi fun _ : Fin k => μ) (patternEvent τ) =
      (Measure.pi fun _ : Fin k => ν) (patternEvent τ) := by
    have := h τ
    rwa [Measure.real, Measure.real,
      ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)] at this
  rw [aux_dm_cell_perm μ, aux_dm_cell_perm ν]
  rw [key μ, key ν] at hμν
  exact (ENNReal.mul_right_inj (by simp) (by simp)).1 hμν

lemma aux_dm_event_eq {n : ℕ} (μ ν : Measure (I × I)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hμ1 : ∀ t : I, μ {a | a.1 = t} = 0) (hμ2 : ∀ t : I, μ {a | a.2 = t} = 0)
    (hν1 : ∀ t : I, ν {a | a.1 = t} = 0) (hν2 : ∀ t : I, ν {a | a.2 = t} = 0)
    (h : ∀ τ : Equiv.Perm (Fin (n + 1)),
      (Measure.pi fun _ : Fin (n + 1) => μ).real (patternEvent τ) =
        (Measure.pi fun _ : Fin (n + 1) => ν).real (patternEvent τ))
    (E : Set (Fin (n + 1) → I × I)) (hE : MeasurableSet E)
    (hc : ∀ τ ρ, ∀ p ∈ aux_dm_cell τ ρ, ∀ q ∈ aux_dm_cell τ ρ, p ∈ E → q ∈ E) :
    (Measure.pi fun _ : Fin (n + 1) => μ) E = (Measure.pi fun _ : Fin (n + 1) => ν) E := by
  have key : ∀ (m : Measure (I × I)) [IsProbabilityMeasure m], (∀ t : I, m {a | a.1 = t} = 0) →
      (∀ t : I, m {a | a.2 = t} = 0) →
      (Measure.pi fun _ : Fin (n + 1) => m) E =
        ∑ x : Equiv.Perm (Fin (n + 1)) × Equiv.Perm (Fin (n + 1)),
          (Measure.pi fun _ : Fin (n + 1) => m) (E ∩ aux_dm_cell x.1 x.2) := by
    intro m _ h1 h2
    have hnull := aux_dm_tie_null (n := n) m h1 h2
    rw [← measure_inter_conull hnull, Set.inter_iUnion,
      measure_iUnion (fun a b hab => ?_) (fun x => hE.inter (aux_dm_cell_meas _ _)), tsum_fintype]
    rw [Function.onFun, Set.disjoint_left]
    intro p hpa hpb
    obtain ⟨e1, e2⟩ := aux_dm_cell_unique hpa.2 hpb.2
    exact hab (Prod.ext e2 e1)
  rw [key μ hμ1 hμ2, key ν hν1 hν2]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : (E ∩ aux_dm_cell x.1 x.2).Nonempty
  · obtain ⟨p, hpE, hpc⟩ := hx
    have : E ∩ aux_dm_cell x.1 x.2 = aux_dm_cell x.1 x.2 :=
      Set.inter_eq_right.2 fun q hq => hc _ _ p hpc q hq hpE
    rw [this]
    exact aux_dm_cell_eq μ ν h x.1 x.2
  · rw [Set.not_nonempty_iff_eq_empty.1 hx]
    simp

/-- The half-plane selected by a Boolean flag. -/
def aux_dm_S (b : Bool) (a : I × I) : Set (I × I) :=
  if b then {q | q.1 < a.1} else {q | q.2 < a.2}

/-- The event used to compute a mixed moment. -/
def aux_dm_E {n : ℕ} (c : Fin n → Bool) : Set (Fin (n + 1) → I × I) :=
  {p | ∀ i : Fin n, p i.succ ∈ aux_dm_S (c i) (p 0)}

lemma aux_dm_E_meas {n : ℕ} (c : Fin n → Bool) : MeasurableSet (aux_dm_E c) := by
  simp only [aux_dm_E, setOf_forall]
  refine MeasurableSet.iInter fun i => ?_
  cases c i
  · simp only [aux_dm_S, Bool.false_eq_true, if_false, mem_setOf_eq]
    exact measurableSet_lt (measurable_snd.comp (measurable_pi_apply _))
      (measurable_snd.comp (measurable_pi_apply _))
  · simp only [aux_dm_S, if_true, mem_setOf_eq]
    exact measurableSet_lt (measurable_fst.comp (measurable_pi_apply _))
      (measurable_fst.comp (measurable_pi_apply _))

lemma aux_dm_E_cell {n : ℕ} (c : Fin n → Bool) (τ ρ : Equiv.Perm (Fin (n + 1))) :
    ∀ p ∈ aux_dm_cell τ ρ, ∀ q ∈ aux_dm_cell τ ρ, p ∈ aux_dm_E c → q ∈ aux_dm_E c := by
  intro p hp q hq hpE i
  have := hpE i
  cases hci : c i
  · rw [hci] at this
    simp only [aux_dm_S, Bool.false_eq_true, if_false, mem_setOf_eq] at this ⊢
    rw [aux_dm_cell_lt2 hq]; rw [aux_dm_cell_lt2 hp] at this; exact this
  · rw [hci] at this
    simp only [aux_dm_S, if_true, mem_setOf_eq] at this ⊢
    rw [aux_dm_cell_lt1 hq]; rw [aux_dm_cell_lt1 hp] at this; exact this

lemma aux_dm_moment {n : ℕ} (μ : Measure (I × I)) [IsProbabilityMeasure μ]
    (h1 : ∀ t : I, μ {a | a.1 < t} = ENNReal.ofReal t)
    (h2 : ∀ t : I, μ {a | a.2 < t} = ENNReal.ofReal t) (c : Fin n → Bool) :
    (Measure.pi fun _ : Fin (n + 1) => μ) (aux_dm_E c) =
      ∫⁻ a, ∏ i, (if c i then ENNReal.ofReal a.1 else ENNReal.ofReal a.2) ∂μ := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
  set E' : Set ((I × I) × (Fin n → I × I)) := {x | ∀ i, x.2 i ∈ aux_dm_S (c i) x.1} with hE'def
  have hpre : aux_dm_E c = (MeasurableEquiv.piFinSuccAbove (fun _ => I × I) 0) ⁻¹' E' := by
    ext p
    simp [aux_dm_E, E', MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
  have hE' : MeasurableSet E' := by
    simp only [E', setOf_forall]
    refine MeasurableSet.iInter fun i => ?_
    cases c i
    · simp only [aux_dm_S, Bool.false_eq_true, if_false, mem_setOf_eq]
      exact measurableSet_lt (measurable_snd.comp ((measurable_pi_apply _).comp measurable_snd))
        (measurable_snd.comp measurable_fst)
    · simp only [aux_dm_S, if_true, mem_setOf_eq]
      exact measurableSet_lt (measurable_fst.comp ((measurable_pi_apply _).comp measurable_snd))
        (measurable_fst.comp measurable_fst)
  rw [hpre, hmp.measure_preimage_equiv, Measure.prod_apply hE']
  refine lintegral_congr fun a => ?_
  have : Prod.mk a ⁻¹' E' = Set.pi univ (fun i => aux_dm_S (c i) a) := by
    ext q; simp [E']
  rw [this, Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases c i
  · simp [aux_dm_S, h2]
  · simp [aux_dm_S, h1]

lemma aux_dm_prod_ite (a b : ℕ) (x y : ENNReal) :
    ∏ i : Fin (a + b), (if decide ((i : ℕ) < a) then x else y) = x ^ a * y ^ b := by
  rw [Fin.prod_univ_add]
  simp

lemma aux_dm_moments {Z Z' : I → I → ℝ} (hZ : IsLimitPerm Z) (hZ' : IsLimitPerm Z')
    (h : ∀ (k : ℕ) (τ : Equiv.Perm (Fin k)), limitDensity τ Z = limitDensity τ Z') (a b : ℕ) :
    ∫ p, (p.1 : ℝ) ^ a * (p.2 : ℝ) ^ b ∂(limitMeasure Z) =
      ∫ p, (p.1 : ℝ) ^ a * (p.2 : ℝ) ^ b ∂(limitMeasure Z') := by
  have := aux_dm_prob hZ
  have := aux_dm_prob hZ'
  let c : Fin (a + b) → Bool := fun i => decide ((i : ℕ) < a)
  have hE := aux_dm_event_eq (limitMeasure Z) (limitMeasure Z') (aux_dm_fst_eq hZ)
    (aux_dm_snd_eq hZ) (aux_dm_fst_eq hZ') (aux_dm_snd_eq hZ') (fun τ => h _ τ) (aux_dm_E c)
    (aux_dm_E_meas c) (aux_dm_E_cell c)
  rw [aux_dm_moment _ (aux_dm_fst_lt hZ) (aux_dm_snd_lt hZ) c,
    aux_dm_moment _ (aux_dm_fst_lt hZ') (aux_dm_snd_lt hZ') c] at hE
  have hprod : ∀ p : I × I, ∏ i, (if c i then ENNReal.ofReal p.1 else ENNReal.ofReal p.2) =
      ENNReal.ofReal ((p.1 : ℝ) ^ a * (p.2 : ℝ) ^ b) := by
    intro p
    rw [aux_dm_prod_ite, ENNReal.ofReal_mul (pow_nonneg p.1.2.1 _), ENNReal.ofReal_pow p.1.2.1,
      ENNReal.ofReal_pow p.2.2.1]
  simp_rw [hprod] at hE
  have hm : Measurable fun p : I × I => (p.1 : ℝ) ^ a * (p.2 : ℝ) ^ b := by fun_prop
  have hnn : ∀ p : I × I, 0 ≤ (p.1 : ℝ) ^ a * (p.2 : ℝ) ^ b := fun p =>
    mul_nonneg (pow_nonneg p.1.2.1 _) (pow_nonneg p.2.2.1 _)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hm.aestronglyMeasurable, hE]

lemma aux_dm_ext (μ ν : Measure (I × I)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a b : ℕ, ∫ p, (p.1 : ℝ) ^ a * (p.2 : ℝ) ^ b ∂μ =
      ∫ p, (p.1 : ℝ) ^ a * (p.2 : ℝ) ^ b ∂ν) : μ = ν := by
  let fx : BoundedContinuousFunction (I × I) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun p => (p.1 : ℝ), by fun_prop⟩
  let fy : BoundedContinuousFunction (I × I) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun p => (p.2 : ℝ), by fun_prop⟩
  let A : StarSubalgebra ℝ (BoundedContinuousFunction (I × I) ℝ) :=
    { Algebra.adjoin ℝ {fx, fy} with
      star_mem' := fun {f} hf => by
        have : star f = f := by ext x; simp
        rw [this]; exact hf }
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish (A := A)
  · intro p q hpq
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
      refine ⟨fun r => (r.2 : ℝ), ⟨BoundedContinuousFunction.toContinuousMapStarₐ ℝ fy, ?_, rfl⟩,
        ?_⟩
      · exact StarSubalgebra.mem_map.2 ⟨fy, Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl), rfl⟩
      · intro h; exact h2 (Subtype.ext h)
    · refine ⟨fun r => (r.1 : ℝ), ⟨BoundedContinuousFunction.toContinuousMapStarₐ ℝ fx, ?_, rfl⟩,
        ?_⟩
      · exact StarSubalgebra.mem_map.2 ⟨fx, Algebra.subset_adjoin (Set.mem_insert _ _), rfl⟩
      · intro h; exact h1 (Subtype.ext h)
  · intro g hg
    have hg' : g ∈ Submodule.span ℝ
        (Submonoid.closure ({fx, fy} : Set (BoundedContinuousFunction (I × I) ℝ)) : Set (BoundedContinuousFunction (I × I) ℝ)) := by
      rw [← Algebra.adjoin_eq_span]; exact hg
    clear hg
    induction hg' using Submodule.span_induction with
    | mem g hgc =>
      obtain ⟨m, k, rfl⟩ := (Submonoid.mem_closure_pair fx fy g).1 hgc
      have : ((fx ^ m * fy ^ k : BoundedContinuousFunction (I × I) ℝ) : I × I → ℝ) =
          fun p => (p.1 : ℝ) ^ m * (p.2 : ℝ) ^ k := by
        ext p; simp [fx, fy]
      rw [this]; exact h m k
    | zero => simp
    | add f g _ _ hf hg =>
      simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
      rw [integral_add (f.integrable μ) (g.integrable μ),
        integral_add (f.integrable ν) (g.integrable ν), hf, hg]
    | smul r f _ hf =>
      simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul]
      rw [integral_const_mul, integral_const_mul, hf]

end PermLimits.Existence

open PermLimits.Existence
open unitInterval

theorem solution (Z Z' : I → I → ℝ) (hZ : IsLimitPerm Z) (hZ' : IsLimitPerm Z')
    (h : ∀ (k : ℕ) (τ : Equiv.Perm (Fin k)), limitDensity τ Z = limitDensity τ Z') :
    limitMeasure Z = limitMeasure Z' := by
  have := aux_dm_prob hZ
  have := aux_dm_prob hZ'
  exact aux_dm_ext _ _ (aux_dm_moments hZ hZ' h)

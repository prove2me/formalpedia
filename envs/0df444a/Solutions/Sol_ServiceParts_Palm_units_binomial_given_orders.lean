-- Prove2me | solution 1 for ServiceParts.Palm.units_binomial_given_orders
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T21:09:46.901007+00:00
-- url     : https://prove2.me/submissions/522f4e7a-c364-4cb7-a43b-f25020c2d209

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem
import Theorems.Thm_ServiceParts_Palm_arrival_times_order_statistics

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ServiceParts.Palm
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}



lemma palm_diag_null (n : ℕ) :
    volume {s : Fin n → ℝ | ∃ i j, i ≠ j ∧ s i = s j} = 0 := by
  have : {s : Fin n → ℝ | ∃ i j, i ≠ j ∧ s i = s j} ⊆
      ⋃ p : Fin n × Fin n, ⋃ _ : p.1 ≠ p.2,
        ((LinearMap.ker ((LinearMap.proj p.1 : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj p.2) :
          Submodule ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    rintro s ⟨i, j, hij, h⟩
    simp only [Set.mem_iUnion]
    refine ⟨(i, j), hij, ?_⟩
    simp [LinearMap.mem_ker, h]
  refine measure_mono_null this ?_
  refine (measure_iUnion_null fun p => ?_)
  refine measure_iUnion_null fun hp => ?_
  apply Measure.addHaar_submodule
  intro htop
  have hmem : (Pi.single p.1 (1:ℝ) : Fin n → ℝ) ∈ LinearMap.ker ((LinearMap.proj p.1 : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj p.2) := by
    rw [htop]; exact Submodule.mem_top
  simp [LinearMap.mem_ker, Pi.single_apply, hp] at hmem


def palmSimplex (n : ℕ) (t : ℝ) : Set (Fin n → ℝ) :=
  {s | StrictMono s ∧ ∀ i, 0 < s i ∧ s i < t}

def palmCube (n : ℕ) (t : ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Ioo (0 : ℝ) t)

lemma palmSimplex_meas (n : ℕ) (t : ℝ) : MeasurableSet (palmSimplex n t) := by
  have h1 : MeasurableSet {s : Fin n → ℝ | StrictMono s} := by
    have : {s : Fin n → ℝ | StrictMono s} = ⋂ i, ⋂ j, {s : Fin n → ℝ | i < j → s i < s j} := by
      ext s; simp [StrictMono]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases h : i < j
    · simpa [h] using measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
    · simp [h]
  have h2 : MeasurableSet {s : Fin n → ℝ | ∀ i, 0 < s i ∧ s i < t} := by
    have : {s : Fin n → ℝ | ∀ i, 0 < s i ∧ s i < t} = ⋂ i, {s | 0 < s i} ∩ {s | s i < t} := by
      ext s; simp
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    exact (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const)
  exact h1.inter h2

lemma palmCube_meas (n : ℕ) (t : ℝ) : MeasurableSet (palmCube n t) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

lemma palm_cube_simplex (n : ℕ) (t : ℝ) (F : (Fin n → ℝ) → ℝ≥0∞)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ), F (s ∘ σ) = F s) :
    ∫⁻ s in palmCube n t, F s = (Nat.factorial n : ℝ≥0∞) * ∫⁻ s in palmSimplex n t, F s := by
  classical
  let Φ : Equiv.Perm (Fin n) → (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) := fun σ =>
    MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl ℝ)
  have hΦ : ∀ σ s, Φ σ s = s ∘ σ := fun σ s => rfl
  have hmp : ∀ σ, MeasurePreserving (Φ σ) volume volume := fun σ =>
    volume_preserving_arrowCongr' σ.symm (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)
  let C : Equiv.Perm (Fin n) → Set (Fin n → ℝ) := fun σ => Φ σ ⁻¹' palmSimplex n t
  have hCmeas : ∀ σ, MeasurableSet (C σ) := fun σ => (Φ σ).measurable (palmSimplex_meas n t)
  have hCsub : ∀ σ, C σ ⊆ palmCube n t := by
    intro σ s hs i _
    have := hs.2 (σ.symm i)
    simpa [hΦ] using this
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro σ τ hστ
    rw [Function.onFun, Set.disjoint_left]
    intro s hσ hτ
    have h1 : StrictMono (s ∘ σ) := hσ.1
    have h2 : StrictMono (s ∘ τ) := hτ.1
    have hr : Set.range (s ∘ σ) = Set.range (s ∘ τ) := by
      rw [Set.range_comp, Set.range_comp, Equiv.range_eq_univ, Equiv.range_eq_univ]
    have heq := (StrictMono.range_inj h1 h2).1 hr
    have hs : Function.Injective s := by
      have := h1.injective.comp σ.symm.injective
      simpa [Function.comp_def] using this
    apply hστ
    ext j
    exact congrArg Fin.val (hs (congrFun heq j))
  have hnull : volume (palmCube n t \ ⋃ σ, C σ) = 0 := by
    refine measure_mono_null ?_ (palm_diag_null n)
    intro s ⟨hs, hns⟩
    by_contra hcon
    apply hns
    have hinj : Function.Injective s := by
      intro i j hij
      by_contra hne
      exact hcon ⟨i, j, hne, hij⟩
    let σ := Tuple.sort s
    refine Set.mem_iUnion.2 ⟨σ, ?_, ?_⟩
    · exact (Tuple.monotone_sort s).strictMono_of_injective (hinj.comp σ.injective)
    · intro i
      exact hs (σ i) (Set.mem_univ _)
  have hae : palmCube n t =ᵐ[volume] ⋃ σ, C σ := by
    rw [ae_eq_set]
    refine ⟨hnull, ?_⟩
    rw [Set.sdiff_eq_empty.2 (Set.iUnion_subset hCsub)]
    simp
  rw [setLIntegral_congr hae, lintegral_iUnion hCmeas hdisj, tsum_fintype]
  have hterm : ∀ σ, ∫⁻ s in C σ, F s = ∫⁻ s in palmSimplex n t, F s := by
    intro σ
    rw [← (hmp σ).setLIntegral_comp_preimage_emb (Φ σ).measurableEmbedding F (palmSimplex n t)]
    refine setLIntegral_congr_fun ((hCmeas σ)) ?_
    intro s _
    show F s = F (Φ σ s)
    rw [hΦ, hsym]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]




noncomputable def palmF (S : ResupplySystem Ω P) (t : ℝ) (n x : ℕ) (s : Fin n → ℝ) : ℝ≥0∞ :=
  P {ω | (Finset.univ.filter (fun i : Fin n => t < s i + S.resupply i ω)).card = x}

noncomputable def palmQ (S : ResupplySystem Ω P) (t c : ℝ) : ℝ≥0∞ :=
  P {ω | t < c + S.resupply 0 ω}

noncomputable def palmR (S : ResupplySystem Ω P) (t c : ℝ) : ℝ≥0∞ :=
  P {ω | c + S.resupply 0 ω ≤ t}

lemma palm_resupply_prob (S : ResupplySystem Ω P) (i : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    P (S.resupply i ⁻¹' B) = P (S.resupply 0 ⁻¹' B) := by
  rw [← Measure.map_apply (S.resupply_measurable i) hB, S.resupply_law i,
    ← Measure.map_apply (S.resupply_measurable 0) hB, S.resupply_law 0]

lemma palm_indep_resupply (S : ResupplySystem Ω P) (n : ℕ) :
    iIndepFun (fun i : Fin n => S.resupply (i : ℕ)) P := by
  have h := S.indep.precomp (g := fun i : Fin n => (Sum.inr (i : ℕ) : ℕ ⊕ ℕ))
    (fun a b hab => by simpa [Fin.ext_iff] using hab)
  exact h

lemma palmF_eq [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (t : ℝ) (n x : ℕ)
    (s : Fin n → ℝ) :
    palmF S t n x s = ∑ J ∈ Finset.powersetCard x (Finset.univ : Finset (Fin n)),
      ∏ i, (if i ∈ J then palmQ S t (s i) else palmR S t (s i)) := by
  classical
  let B : Finset (Fin n) → Fin n → Set ℝ := fun J i =>
    if i ∈ J then Set.Ioi (t - s i) else Set.Iic (t - s i)
  have hBm : ∀ J i, MeasurableSet (B J i) := by
    intro J i; by_cases h : i ∈ J <;> simp [B, h]
  let E : Finset (Fin n) → Set Ω := fun J => ⋂ i : Fin n, S.resupply (i : ℕ) ⁻¹' B J i
  have hEm : ∀ J, MeasurableSet (E J) := fun J =>
    MeasurableSet.iInter fun i => S.resupply_measurable _ (hBm J i)
  have hset : {ω | (Finset.univ.filter (fun i : Fin n => t < s i + S.resupply i ω)).card = x} =
      ⋃ J ∈ Finset.powersetCard x (Finset.univ : Finset (Fin n)), E J := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard, E, B, Set.mem_iInter,
      Set.mem_preimage]
    constructor
    · intro h
      refine ⟨Finset.univ.filter (fun i : Fin n => t < s i + S.resupply i ω),
        ⟨Finset.subset_univ _, h⟩, fun i => ?_⟩
      by_cases hi : t < s i + S.resupply i ω
      · simp [hi]; linarith
      · simp [hi]; linarith
    · rintro ⟨J, ⟨_, hJ⟩, hω⟩
      have : Finset.univ.filter (fun i : Fin n => t < s i + S.resupply i ω) = J := by
        ext i
        have := hω i
        by_cases hi : i ∈ J
        · simp only [hi, if_true, Set.mem_Ioi] at this
          simp [hi]; linarith
        · simp only [hi, if_false, Set.mem_Iic] at this
          simp [hi]; linarith
      rw [this, hJ]
  have hdisj : (↑(Finset.powersetCard x (Finset.univ : Finset (Fin n))) : Set (Finset (Fin n))).PairwiseDisjoint E := by
    intro J _ J' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    apply hne
    ext i
    simp only [E, B, Set.mem_iInter, Set.mem_preimage] at h1 h2
    have a := h1 i
    have b := h2 i
    by_cases hi : i ∈ J <;> by_cases hj : i ∈ J' <;> simp [hi, hj] at a b ⊢
    · linarith
    · linarith
  unfold palmF
  rw [hset, measure_biUnion_finset hdisj (fun J _ => hEm J)]
  refine Finset.sum_congr rfl fun J _ => ?_
  have hind := (palm_indep_resupply S n).meas_iInter
    (s := fun i : Fin n => S.resupply (i : ℕ) ⁻¹' B J i)
    (fun i : Fin n => ⟨B J i, hBm J i, rfl⟩)
  simp only [E]
  rw [hind]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [palm_resupply_prob S i (hBm J i)]
  by_cases hi : i ∈ J
  · simp only [B, hi, if_true, palmQ]
    congr 1; ext ω; simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
  · simp only [B, hi, if_false, palmR]
    congr 1; ext ω; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]; constructor <;> intro h <;> linarith


lemma palmCdf_mono [IsProbabilityMeasure P] (S : ResupplySystem Ω P) : Monotone S.resupplyCdf := by
  intro u v huv
  unfold ResupplySystem.resupplyCdf
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  intro ω hω
  exact le_trans hω huv

lemma palmCdf_nonneg [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (u : ℝ) :
    0 ≤ S.resupplyCdf u := ENNReal.toReal_nonneg

lemma palmCdf_le_one [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (u : ℝ) :
    S.resupplyCdf u ≤ 1 := by
  unfold ResupplySystem.resupplyCdf
  have : P {ω | S.resupply 0 ω ≤ u} ≤ 1 := prob_le_one
  simpa using ENNReal.toReal_mono (by simp) this

lemma palmR_eq [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (t c : ℝ) :
    palmR S t c = ENNReal.ofReal (S.resupplyCdf (t - c)) := by
  unfold palmR ResupplySystem.resupplyCdf
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  congr 1; ext ω
  simp only [Set.mem_setOf_eq]
  constructor <;> intro h <;> linarith

lemma palmQ_eq [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (t c : ℝ) :
    palmQ S t c = ENNReal.ofReal (1 - S.resupplyCdf (t - c)) := by
  have h1 : palmQ S t c = 1 - palmR S t c := by
    unfold palmQ palmR
    have hm : MeasurableSet {ω | c + S.resupply 0 ω ≤ t} :=
      measurableSet_le (measurable_const.add (S.resupply_measurable 0)) measurable_const
    rw [← prob_compl_eq_one_sub hm]
    congr 1; ext ω
    simp
  rw [h1, palmR_eq, ENNReal.ofReal_sub _ (palmCdf_nonneg S _), ENNReal.ofReal_one]

lemma palmF_eq_real [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (t : ℝ) (n x : ℕ)
    (s : Fin n → ℝ) :
    palmF S t n x s = ENNReal.ofReal (∑ J ∈ Finset.powersetCard x (Finset.univ : Finset (Fin n)),
      ∏ i, (if i ∈ J then 1 - S.resupplyCdf (t - s i) else S.resupplyCdf (t - s i))) := by
  rw [palmF_eq, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun J _ => ?_
    rw [ENNReal.ofReal_prod_of_nonneg]
    · refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i ∈ J
      · simp [hi, palmQ_eq]
      · simp [hi, palmR_eq]
    · intro i _
      by_cases hi : i ∈ J
      · simp [hi]; exact palmCdf_le_one S _
      · simp [hi]; exact palmCdf_nonneg S _
  · intro J _
    refine Finset.prod_nonneg fun i _ => ?_
    by_cases hi : i ∈ J
    · simp [hi]; exact palmCdf_le_one S _
    · simp [hi]; exact palmCdf_nonneg S _

lemma palmF_symm [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (t : ℝ) (n x : ℕ)
    (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) :
    palmF S t n x (s ∘ σ) = palmF S t n x s := by
  classical
  rw [palmF_eq_real, palmF_eq_real]
  congr 1
  refine Finset.sum_nbij (fun J => J.map σ.toEmbedding) ?_ ?_ ?_ ?_
  · intro J hJ
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hJ ⊢
    simpa using hJ
  · intro J _ J' _ h
    exact Finset.map_injective σ.toEmbedding h
  · intro J hJ
    refine ⟨J.map σ.symm.toEmbedding, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hJ ⊢
      simpa using hJ
    · ext j
      simp
  · intro J _
    refine Fintype.prod_equiv σ _ _ (fun i => ?_)
    simp


lemma palmCdf_meas [IsProbabilityMeasure P] (S : ResupplySystem Ω P) :
    Measurable S.resupplyCdf := (palmCdf_mono S).measurable

lemma palmF_meas [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (t : ℝ) (n x : ℕ) :
    Measurable (palmF S t n x) := by
  have : palmF S t n x = fun s => ENNReal.ofReal
      (∑ J ∈ Finset.powersetCard x (Finset.univ : Finset (Fin n)),
      ∏ i, (if i ∈ J then 1 - S.resupplyCdf (t - s i) else S.resupplyCdf (t - s i))) :=
    funext (palmF_eq_real S t n x)
  rw [this]
  refine ENNReal.measurable_ofReal.comp ?_
  refine Finset.measurable_sum _ fun J _ => Finset.measurable_prod _ fun i _ => ?_
  by_cases hi : i ∈ J
  · simp only [hi, if_true]
    exact measurable_const.sub ((palmCdf_meas S).comp (measurable_const.sub (measurable_pi_apply i)))
  · simp only [hi, if_false]
    exact (palmCdf_meas S).comp (measurable_const.sub (measurable_pi_apply i))

lemma palmCube_restrict (n : ℕ) (t : ℝ) :
    (volume : Measure (Fin n → ℝ)).restrict (palmCube n t) =
      Measure.pi (fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) t)) := by
  show (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict _ = _
  exact Measure.restrict_pi_pi _ _

lemma palm_pi_integrable {n : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ] (f : Fin n → ℝ → ℝ)
    (hm : ∀ i, Measurable (f i)) (h01 : ∀ i c, 0 ≤ f i c ∧ f i c ≤ 1) :
    Integrable (fun s : Fin n → ℝ => ∏ i, f i (s i)) (Measure.pi fun _ => μ) := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact (Finset.measurable_prod _ fun i _ => (hm i).comp (measurable_pi_apply i)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ => (h01 i _).1)]
    exact Finset.prod_le_one (fun i _ => (h01 i _).1) (fun i _ => (h01 i _).2)

lemma palm_int_G [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) :
    ∫ c in Set.Ioo (0 : ℝ) t, S.resupplyCdf (t - c) = ∫ u in (0 : ℝ)..t, S.resupplyCdf u := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
    intervalIntegral.integral_comp_sub_left (fun u => S.resupplyCdf u) t]
  simp

lemma palm_int_Q [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) :
    ∫ c in Set.Ioo (0 : ℝ) t, (1 - S.resupplyCdf (t - c)) =
      ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u) := by
  have hint : IntervalIntegrable S.resupplyCdf volume 0 t := (palmCdf_mono S).intervalIntegrable
  have hint' : IntervalIntegrable (fun c => S.resupplyCdf (t - c)) volume 0 t := by
    have := hint.comp_sub_left t
    simpa using this.symm
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
    intervalIntegral.integral_sub intervalIntegrable_const hint',
    intervalIntegral.integral_sub intervalIntegrable_const hint,
    intervalIntegral.integral_comp_sub_left (fun u => S.resupplyCdf u) t]
  simp


lemma palm_prod_ite (n x : ℕ) (a b : ℝ) (J : Finset (Fin n)) (hJ : J.card = x) :
    ∏ i, (if i ∈ J then a else b) = a ^ x * b ^ (n - x) := by
  classical
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp [Finset.prod_const, hJ]
  have : (Finset.univ.filter (fun i => i ∉ J)).card = n - x := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _)]; simp [hJ]
  simp [this]

lemma palm_cube_integral [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t)
    (n x : ℕ) :
    ∫⁻ s in palmCube n t, palmF S t n x s =
      ENNReal.ofReal (t ^ n * ((Nat.choose n x : ℝ) *
        ((1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ x *
        (1 - (1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ (n - x))) := by
  classical
  set I := ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u) with hI
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) t)
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simp [μ, Real.volume_Ioo]
  let h : Finset (Fin n) → Fin n → ℝ → ℝ := fun J i c =>
    if i ∈ J then 1 - S.resupplyCdf (t - c) else S.resupplyCdf (t - c)
  have hm : ∀ J i, Measurable (h J i) := by
    intro J i
    by_cases hi : i ∈ J
    · simp only [h, hi, if_true]
      exact measurable_const.sub ((palmCdf_meas S).comp (measurable_const.sub measurable_id))
    · simp only [h, hi, if_false]
      exact (palmCdf_meas S).comp (measurable_const.sub measurable_id)
  have h01 : ∀ J i c, 0 ≤ h J i c ∧ h J i c ≤ 1 := by
    intro J i c
    by_cases hi : i ∈ J
    · simp only [h, hi, if_true]
      constructor
      · linarith [palmCdf_le_one S (t - c)]
      · linarith [palmCdf_nonneg S (t - c)]
    · simp only [h, hi, if_false]
      exact ⟨palmCdf_nonneg S _, palmCdf_le_one S _⟩
  have hJint : ∀ J, Integrable (fun s : Fin n → ℝ => ∏ i, h J i (s i))
      (Measure.pi fun _ : Fin n => μ) := fun J => palm_pi_integrable μ (h J) (hm J) (h01 J)
  have hsumint : Integrable (fun s : Fin n → ℝ => ∑ J ∈ Finset.powersetCard x (Finset.univ : Finset (Fin n)), ∏ i, h J i (s i))
      (Measure.pi fun _ : Fin n => μ) := integrable_finset_sum _ fun J _ => hJint J
  have hnn : 0 ≤ᵐ[Measure.pi fun _ : Fin n => μ] (fun s : Fin n → ℝ => ∑ J ∈ Finset.powersetCard x (Finset.univ : Finset (Fin n)), ∏ i, h J i (s i)) :=
    Filter.Eventually.of_forall fun s => Finset.sum_nonneg fun J _ => Finset.prod_nonneg fun i _ => (h01 J i _).1
  have step1 : ∫⁻ s in palmCube n t, palmF S t n x s =
      ∫⁻ s, ENNReal.ofReal (∑ J ∈ Finset.powersetCard x (Finset.univ : Finset (Fin n)), ∏ i, h J i (s i))
        ∂(Measure.pi fun _ : Fin n => μ) := by
    rw [palmCube_restrict]
    refine lintegral_congr fun s => ?_
    exact palmF_eq_real S t n x s
  rw [step1, ← ofReal_integral_eq_lintegral_ofReal hsumint hnn]
  congr 1
  have hQ : ∀ J i, ∫ c, h J i c ∂μ = if i ∈ J then I else t - I := by
    intro J i
    have hG : ∫ c in Set.Ioo (0 : ℝ) t, S.resupplyCdf (t - c) = t - I := by
      rw [palm_int_G S ht, hI, intervalIntegral.integral_sub intervalIntegrable_const
        (palmCdf_mono S).intervalIntegrable]
      simp
    by_cases hi : i ∈ J
    · simp only [h, hi, if_true]
      exact palm_int_Q S ht
    · simp only [h, hi, if_false]
      exact hG
  rw [integral_finset_sum _ (fun J _ => hJint J)]
  have hprod : ∀ J ∈ Finset.powersetCard x (Finset.univ : Finset (Fin n)),
      ∫ s, ∏ i, h J i (s i) ∂(Measure.pi fun _ : Fin n => μ) = I ^ x * (t - I) ^ (n - x) := by
    intro J hJ
    rw [integral_fintype_prod_eq_prod (fun i c => h J i c)]
    simp_rw [hQ]
    rw [palm_prod_ite n x I (t - I) J (Finset.mem_powersetCard.1 hJ).2]
  rw [Finset.sum_congr rfl hprod, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  by_cases hxn : x ≤ n
  · have e1 : t ^ n = t ^ x * t ^ (n - x) := by rw [← pow_add]; congr 1; omega
    have e2 : t ^ x * (1 / t * I) ^ x = I ^ x := by
      rw [← mul_pow]; congr 1; field_simp
    have e3 : t ^ (n - x) * (1 - 1 / t * I) ^ (n - x) = (t - I) ^ (n - x) := by
      rw [← mul_pow]; congr 1; field_simp
    calc (Nat.choose n x : ℝ) * (I ^ x * (t - I) ^ (n - x))
        = (Nat.choose n x : ℝ) * ((t ^ x * (1 / t * I) ^ x) * (t ^ (n - x) * (1 - 1 / t * I) ^ (n - x))) := by
          rw [e2, e3]
      _ = _ := by rw [e1]; ring
  · have : Nat.choose n x = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [this]


def palmM (S : ResupplySystem Ω P) (t : ℝ) (n : ℕ) : Set Ω :=
  {ω | (∀ i : Fin n, S.arrival i ω ≤ t) ∧ t < S.arrival n ω}

lemma palm_down_eq (A : Set ℕ) (hfin : A.Finite) (hdown : ∀ k ∈ A, ∀ j ≤ k, j ∈ A) :
    A = Set.Iio A.ncard := by
  classical
  by_cases hA : A = ∅
  · subst hA; simp
  · have hne : hfin.toFinset.Nonempty := by
      rw [Set.Finite.toFinset_nonempty]; exact Set.nonempty_iff_ne_empty.2 hA
    set k := hfin.toFinset.max' hne with hkdef
    have hk : k ∈ A := by
      have := hfin.toFinset.max'_mem hne
      simpa [hkdef] using this
    have hAeq : A = Set.Iio (k + 1) := by
      ext j
      constructor
      · intro hj
        have : j ≤ k := hfin.toFinset.le_max' j (by simpa using hj)
        simp only [Set.mem_Iio]; omega
      · intro hj
        exact hdown k hk j (by simp only [Set.mem_Iio] at hj; omega)
    have hn : A.ncard = k + 1 := by
      rw [hAeq]
      have : Set.Iio (k + 1) = ((Finset.range (k + 1) : Finset ℕ) : Set ℕ) := by
        ext j; simp
      rw [this, Set.ncard_coe_finset, Finset.card_range]
    rw [hn]; exact hAeq

lemma palm_ident (S : ResupplySystem Ω P) (t : ℝ) (n : ℕ) (ω : Ω)
    (hg : ∀ k, 0 ≤ S.gap k ω) (hb : ∃ j, t < S.gap j ω) :
    (S.orderCount t ω = n ↔ ω ∈ palmM S t n) ∧
    (ω ∈ palmM S t n → S.unitsInResupply t ω =
      (Finset.univ.filter (fun i : Fin n => t < S.arrival i ω + S.resupply i ω)).card) := by
  classical
  have hmono : ∀ {a b : ℕ}, a ≤ b → S.arrival a ω ≤ S.arrival b ω := by
    intro a b hab
    unfold ResupplySystem.arrival
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => hg j)
  have hgap : ∀ {j k : ℕ}, j ≤ k → S.gap j ω ≤ S.arrival k ω := by
    intro j k hjk
    unfold ResupplySystem.arrival
    exact Finset.single_le_sum (f := fun i => S.gap i ω) (fun i _ => hg i)
      (Finset.mem_range.2 (by omega))
  obtain ⟨j, hj⟩ := hb
  set A : Set ℕ := {k | S.arrival k ω ≤ t} with hAdef
  have hfin : A.Finite := by
    refine (Set.finite_Iio j).subset ?_
    intro k hk
    simp only [Set.mem_Iio]
    by_contra hkj
    have := hgap (not_lt.1 hkj)
    have hk' : S.arrival k ω ≤ t := hk
    linarith
  have hdown : ∀ k ∈ A, ∀ j ≤ k, j ∈ A := by
    intro k hk i hik
    exact le_trans (hmono hik) hk
  have hcount : S.orderCount t ω = A.ncard := rfl
  have hAM : ω ∈ palmM S t n → A = Set.Iio n := by
    rintro ⟨h1, h2⟩
    ext k
    simp only [hAdef, Set.mem_setOf_eq, Set.mem_Iio]
    constructor
    · intro hk
      by_contra hkn
      have := hmono (not_lt.1 hkn)
      linarith
    · intro hk
      exact h1 ⟨k, hk⟩
  have hncard : (Set.Iio n).ncard = n := by
    have : Set.Iio n = ((Finset.range n : Finset ℕ) : Set ℕ) := by ext j; simp
    rw [this, Set.ncard_coe_finset, Finset.card_range]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · have hAe := palm_down_eq A hfin hdown
    rw [← hcount, h] at hAe
    refine ⟨fun i => ?_, ?_⟩
    · have : (i : ℕ) ∈ A := by rw [hAe]; exact i.2
      exact this
    · have : n ∉ A := by rw [hAe]; simp
      simpa [hAdef] using this
  · rw [hcount, hAM h, hncard]
  · have hA := hAM h
    have hset : {k | S.arrival k ω ≤ t ∧ t < S.arrival k ω + S.resupply k ω} =
        (((Finset.univ.filter (fun i : Fin n => t < S.arrival i ω + S.resupply i ω)).map
          Fin.valEmbedding : Finset ℕ) : Set ℕ) := by
      ext k
      have hkA : k ∈ A ↔ k < n := by rw [hA]; simp
      simp only [hAdef, Set.mem_setOf_eq] at hkA
      simp only [Set.mem_setOf_eq, Finset.coe_map, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_image, Fin.valEmbedding_apply]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨k, hkA.1 h1⟩, h2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨hkA.2 i.2, hi⟩
    unfold ResupplySystem.unitsInResupply
    rw [hset, Set.ncard_coe_finset, Finset.card_map]


lemma palm_gap_nonneg_ae (S : ResupplySystem Ω P) :
    ∀ᵐ ω ∂P, ∀ k, 0 ≤ S.gap k ω := by
  refine ae_all_iff.2 fun k => ?_
  have h0 : P {ω | S.gap k ω < 0} = 0 := by
    have : {ω | S.gap k ω < 0} = S.gap k ⁻¹' Set.Iio 0 := rfl
    rw [this, ← Measure.map_apply (S.gap_measurable k) measurableSet_Iio, S.gap_law k]
    unfold expMeasure gammaMeasure
    rw [withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
  simpa using hω

lemma palm_gap_prob (S : ResupplySystem Ω P) (k : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    P (S.gap k ⁻¹' B) = P (S.gap 0 ⁻¹' B) := by
  rw [← Measure.map_apply (S.gap_measurable k) hB, S.gap_law k,
    ← Measure.map_apply (S.gap_measurable 0) hB, S.gap_law 0]

lemma palm_bad_null [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (t : ℝ) :
    P {ω | ∀ j, S.gap j ω ≤ t} = 0 := by
  set ρ : ℝ≥0∞ := P (S.gap 0 ⁻¹' Set.Iic t) with hρ
  have hρlt : ρ < 1 := by
    have hr := S.rate_pos
    haveI : IsProbabilityMeasure (expMeasure S.rate) := isProbabilityMeasure_expMeasure hr
    have h1 : ρ = expMeasure S.rate (Set.Iic t) := by
      rw [hρ, ← Measure.map_apply (S.gap_measurable 0) measurableSet_Iic, S.gap_law 0]
    have h2 : (expMeasure S.rate (Set.Iic t)).toReal = cdf (expMeasure S.rate) t := by
      rw [cdf_eq_real]; rfl
    have h3 : cdf (expMeasure S.rate) t < 1 := by
      rw [cdf_expMeasure_eq hr]
      split_ifs with h
      · have : 0 < Real.exp (-(S.rate * t)) := Real.exp_pos _
        linarith
      · norm_num
    rw [h1]
    refine lt_of_le_of_ne prob_le_one ?_
    intro hone
    rw [hone] at h2
    simp at h2
    linarith
  have hind : iIndepFun (fun k : ℕ => S.gap k) P := by
    have h := S.indep.precomp (g := fun k : ℕ => (Sum.inl k : ℕ ⊕ ℕ)) (fun a b hab => by simpa using hab)
    exact h
  have hle : ∀ m : ℕ, P {ω | ∀ j, S.gap j ω ≤ t} ≤ ρ ^ m := by
    intro m
    have hsub : {ω | ∀ j, S.gap j ω ≤ t} ⊆ ⋂ i ∈ Finset.range m, S.gap i ⁻¹' Set.Iic t := by
      intro ω hω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
      exact fun i _ => hω i
    refine (measure_mono hsub).trans ?_
    rw [hind.measure_inter_preimage_eq_mul (Finset.range m) (sets := fun _ => Set.Iic t)
      (fun i _ => measurableSet_Iic)]
    rw [Finset.prod_congr rfl (fun i _ => palm_gap_prob S i measurableSet_Iic)]
    simp [hρ]
  have hlim : Filter.Tendsto (fun m : ℕ => ρ ^ m) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρlt
  exact le_antisymm (ge_of_tendsto' hlim hle) bot_le


noncomputable def palmAvec (S : ResupplySystem Ω P) (n : ℕ) (ω : Ω) : Fin (n + 1) → ℝ :=
  fun k => S.arrival k ω

def palmLvec (S : ResupplySystem Ω P) (n : ℕ) (ω : Ω) : Fin n → ℝ :=
  fun i => S.resupply i ω

noncomputable def palmTvec (S : ResupplySystem Ω P) (n : ℕ) (ω : Ω) : Fin n → ℝ :=
  fun i => S.arrival i ω

lemma palm_arrival_meas (S : ResupplySystem Ω P) (k : ℕ) : Measurable (S.arrival k) := by
  unfold ResupplySystem.arrival
  exact Finset.measurable_sum _ fun j _ => S.gap_measurable j

lemma palm_Avec_meas (S : ResupplySystem Ω P) (n : ℕ) : Measurable (palmAvec S n) :=
  measurable_pi_lambda _ fun k => palm_arrival_meas S k

lemma palm_Lvec_meas (S : ResupplySystem Ω P) (n : ℕ) : Measurable (palmLvec S n) :=
  measurable_pi_lambda _ fun i => S.resupply_measurable i

lemma palm_Tvec_meas (S : ResupplySystem Ω P) (n : ℕ) : Measurable (palmTvec S n) :=
  measurable_pi_lambda _ fun i => palm_arrival_meas S i

lemma palm_indep_AL (S : ResupplySystem Ω P) (n : ℕ) :
    IndepFun (palmAvec S n) (palmLvec S n) P := by
  classical
  let f : ℕ ⊕ ℕ → Ω → ℝ := Sum.elim S.gap S.resupply
  have hfm : ∀ i, Measurable (f i) := by
    intro i; rcases i with i | i
    · exact S.gap_measurable i
    · exact S.resupply_measurable i
  let S1 : Finset (ℕ ⊕ ℕ) := (Finset.range (n + 1)).image Sum.inl
  let T1 : Finset (ℕ ⊕ ℕ) := (Finset.range n).image Sum.inr
  have hdisj : Disjoint S1 T1 := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [S1, T1, Finset.mem_image] at ha hb
    obtain ⟨_, _, rfl⟩ := ha
    obtain ⟨_, _, h⟩ := hb
    cases h
  have hind := S.indep.indepFun_finset S1 T1 hdisj hfm
  let ext1 : (S1 → ℝ) → (ℕ ⊕ ℕ → ℝ) := fun g i => if h : i ∈ S1 then g ⟨i, h⟩ else 0
  let ext2 : (T1 → ℝ) → (ℕ ⊕ ℕ → ℝ) := fun g i => if h : i ∈ T1 then g ⟨i, h⟩ else 0
  have hext1 : ∀ i, Measurable (fun g : S1 → ℝ => ext1 g i) := by
    intro i
    by_cases h : i ∈ S1
    · simp only [ext1, h, dif_pos]; exact measurable_pi_apply _
    · simp only [ext1, h, dif_neg, not_false_eq_true]; exact measurable_const
  have hext2 : ∀ i, Measurable (fun g : T1 → ℝ => ext2 g i) := by
    intro i
    by_cases h : i ∈ T1
    · simp only [ext2, h, dif_pos]; exact measurable_pi_apply _
    · simp only [ext2, h, dif_neg, not_false_eq_true]; exact measurable_const
  let φ : (S1 → ℝ) → (Fin (n + 1) → ℝ) := fun g k => ∑ j ∈ Finset.range ((k : ℕ) + 1), ext1 g (Sum.inl j)
  let ψ : (T1 → ℝ) → (Fin n → ℝ) := fun g i => ext2 g (Sum.inr i)
  have hφ : Measurable φ :=
    measurable_pi_lambda _ fun k => Finset.measurable_sum _ fun j _ => hext1 _
  have hψ : Measurable ψ := measurable_pi_lambda _ fun i => hext2 _
  have h2 := hind.comp hφ hψ
  convert h2 using 1
  · funext ω k
    simp only [palmAvec, ResupplySystem.arrival, Function.comp_apply, φ, ext1]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n + 1 := by
      have := Finset.mem_range.1 hj
      have := k.2
      omega
    have : (Sum.inl j : ℕ ⊕ ℕ) ∈ S1 := by simp [S1]; omega
    simp [this, f]
  · funext ω i
    simp only [palmLvec, Function.comp_apply, ψ, ext2]
    have : (Sum.inr (i : ℕ) : ℕ ⊕ ℕ) ∈ T1 := by simp [T1, i.2]
    simp [this, f]

lemma palm_disint {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [IsProbabilityMeasure P]
    (A : Ω → α) (L : Ω → β) (hA : Measurable A) (hL : Measurable L) (hind : IndepFun A L P)
    {C : Set (α × β)} (hC : MeasurableSet C) :
    P {ω | (A ω, L ω) ∈ C} = ∫⁻ ω, (P.map L) (Prod.mk (A ω) ⁻¹' C) ∂P := by
  have h1 : P {ω | (A ω, L ω) ∈ C} = (P.map (fun ω => (A ω, L ω))) C :=
    (Measure.map_apply (hA.prodMk hL) hC).symm
  rw [h1, (indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hL.aemeasurable).1 hind,
    Measure.prod_apply hC, lintegral_map (measurable_measure_prodMk_left hC) hA]


lemma palm_good_ae [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (t : ℝ) :
    ∀ᵐ ω ∂P, (∀ k, 0 ≤ S.gap k ω) ∧ ∃ j, t < S.gap j ω := by
  have h1 := palm_gap_nonneg_ae S
  have h2 := measure_eq_zero_iff_ae_notMem.1 (palm_bad_null S t)
  filter_upwards [h1, h2] with ω hω1 hω2
  refine ⟨hω1, ?_⟩
  by_contra hcon
  apply hω2
  intro j
  by_contra hj
  exact hcon ⟨j, not_le.1 hj⟩

lemma palmM_meas (S : ResupplySystem Ω P) (t : ℝ) (n : ℕ) : MeasurableSet (palmM S t n) := by
  have : palmM S t n = (⋂ i : Fin n, {ω | S.arrival i ω ≤ t}) ∩ {ω | t < S.arrival n ω} := by
    ext ω; simp [palmM]
  rw [this]
  exact (MeasurableSet.iInter (fun i : Fin n =>
    (measurableSet_le (palm_arrival_meas S (i : ℕ)) measurable_const :
      MeasurableSet {ω | S.arrival (i : ℕ) ω ≤ t}))).inter
    (measurableSet_lt measurable_const (palm_arrival_meas S n))

lemma palm_orderCount_ae [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (t : ℝ) (n : ℕ) :
    {ω | S.orderCount t ω = n} =ᵐ[P] palmM S t n := by
  refine Filter.eventuallyEq_set.2 ?_
  filter_upwards [palm_good_ae S t] with ω hω
  exact (palm_ident S t n ω hω.1 hω.2).1

lemma palm_law_T [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (n : ℕ)
    (hOS : ∀ {A : Set (Fin n → ℝ)}, MeasurableSet A →
      P ({ω | S.orderCount t ω = n} ∩ {ω | (fun i : Fin n => S.arrival i ω) ∈ A}) =
        P {ω | S.orderCount t ω = n} *
          (ENNReal.ofReal ((Nat.factorial n : ℝ) / t ^ n) *
            volume (A ∩ {x : Fin n → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t}))) :
    (P.restrict (palmM S t n)).map (palmTvec S n) =
      (P {ω | S.orderCount t ω = n} * ENNReal.ofReal ((Nat.factorial n : ℝ) / t ^ n)) •
        (volume : Measure (Fin n → ℝ)).restrict (palmSimplex n t) := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (palm_Tvec_meas S n) hA,
    Measure.restrict_apply ((palm_Tvec_meas S n) hA), Measure.smul_apply, Measure.restrict_apply hA,
    smul_eq_mul]
  rw [Set.inter_comm (palmTvec S n ⁻¹' A)]
  have hae := (palm_orderCount_ae S t n).symm.inter
    (Filter.EventuallyEq.refl (ae P) (palmTvec S n ⁻¹' A))
  calc P (palmM S t n ∩ palmTvec S n ⁻¹' A)
      = P ({ω | S.orderCount t ω = n} ∩ palmTvec S n ⁻¹' A) := measure_congr hae
    _ = P {ω | S.orderCount t ω = n} *
          (ENNReal.ofReal ((Nat.factorial n : ℝ) / t ^ n) *
            volume (A ∩ {x : Fin n → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t})) := hOS hA
    _ = _ := by rw [mul_assoc]; rfl


def palmMprime (n : ℕ) (t : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {s | (∀ i : Fin n, s i.castSucc ≤ t) ∧ t < s (Fin.last n)}

def palmC (n x : ℕ) (t : ℝ) : Set ((Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
  {p | p.1 ∈ palmMprime n t ∧
    (Finset.univ.filter (fun i : Fin n => t < p.1 i.castSucc + p.2 i)).card = x}

lemma palm_cardset_meas (n x : ℕ) (t : ℝ) (c : Fin n → ℝ) :
    MeasurableSet {l : Fin n → ℝ | (Finset.univ.filter (fun i : Fin n => t < c i + l i)).card = x} := by
  have hm : Measurable (fun l : Fin n → ℝ =>
      (Finset.univ.filter (fun i : Fin n => t < c i + l i)).card) := by
    simp_rw [Finset.card_filter]
    refine Finset.measurable_sum _ fun i _ => ?_
    exact Measurable.ite (measurableSet_lt measurable_const (measurable_const.add (measurable_pi_apply i)))
      measurable_const measurable_const
  exact hm (measurableSet_singleton x)

lemma palmMprime_meas (n : ℕ) (t : ℝ) : MeasurableSet (palmMprime n t) := by
  have : palmMprime n t = (⋂ i : Fin n, {s : Fin (n + 1) → ℝ | s i.castSucc ≤ t}) ∩
      {s : Fin (n + 1) → ℝ | t < s (Fin.last n)} := by
    ext s; simp [palmMprime]
  rw [this]
  exact (MeasurableSet.iInter fun i : Fin n =>
    measurableSet_le (measurable_pi_apply _) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_pi_apply _))

lemma palmC_meas (n x : ℕ) (t : ℝ) : MeasurableSet (palmC n x t) := by
  have hm : Measurable (fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      (Finset.univ.filter (fun i : Fin n => t < p.1 i.castSucc + p.2 i)).card) := by
    simp_rw [Finset.card_filter]
    refine Finset.measurable_sum _ fun i _ => ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt measurable_const
      (((measurable_pi_apply i.castSucc).comp measurable_fst).add ((measurable_pi_apply i).comp measurable_snd))
  have : palmC n x t = (Prod.fst ⁻¹' palmMprime n t) ∩ (fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      (Finset.univ.filter (fun i : Fin n => t < p.1 i.castSucc + p.2 i)).card) ⁻¹' {x} := by
    ext p; simp [palmC]
  rw [this]
  exact (measurable_fst (palmMprime_meas n t)).inter (hm (measurableSet_singleton x))

open Classical in
lemma palm_fiber [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (t : ℝ) (n x : ℕ)
    (s : Fin (n + 1) → ℝ) :
    (P.map (palmLvec S n)) (Prod.mk s ⁻¹' palmC n x t) =
      if s ∈ palmMprime n t then palmF S t n x (fun i => s i.castSucc) else 0 := by
  by_cases h : s ∈ palmMprime n t
  · have : Prod.mk s ⁻¹' palmC n x t = {l : Fin n → ℝ |
        (Finset.univ.filter (fun i : Fin n => t < s i.castSucc + l i)).card = x} := by
      ext l; simp [palmC, h]
    rw [this, Measure.map_apply (palm_Lvec_meas S n) (palm_cardset_meas n x t _), if_pos h]
    rfl
  · have : Prod.mk s ⁻¹' palmC n x t = ∅ := by
      ext l; simp [palmC, h]
    rw [this, if_neg h]; simp

lemma palm_Avec_mem (S : ResupplySystem Ω P) (t : ℝ) (n : ℕ) (ω : Ω) :
    palmAvec S n ω ∈ palmMprime n t ↔ ω ∈ palmM S t n := by
  simp [palmAvec, palmMprime, palmM]

lemma palm_joint [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (n x : ℕ)
    (hOS : ∀ {A : Set (Fin n → ℝ)}, MeasurableSet A →
      P ({ω | S.orderCount t ω = n} ∩ {ω | (fun i : Fin n => S.arrival i ω) ∈ A}) =
        P {ω | S.orderCount t ω = n} *
          (ENNReal.ofReal ((Nat.factorial n : ℝ) / t ^ n) *
            volume (A ∩ {x : Fin n → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t}))) :
    P ({ω | S.unitsInResupply t ω = x} ∩ {ω | S.orderCount t ω = n}) =
      (P {ω | S.orderCount t ω = n} * ENNReal.ofReal ((Nat.factorial n : ℝ) / t ^ n)) *
        ∫⁻ s in palmSimplex n t, palmF S t n x s := by
  classical
  have hset : ({ω | S.unitsInResupply t ω = x} ∩ {ω | S.orderCount t ω = n} : Set Ω) =ᵐ[P]
      {ω | (palmAvec S n ω, palmLvec S n ω) ∈ palmC n x t} := by
    refine Filter.eventuallyEq_set.2 ?_
    filter_upwards [palm_good_ae S t] with ω hω
    obtain ⟨h1, h2⟩ := palm_ident S t n ω hω.1 hω.2
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, palmC, palm_Avec_mem]
    constructor
    · rintro ⟨hX, hN⟩
      have hM := h1.1 hN
      refine ⟨hM, ?_⟩
      rw [← hX, h2 hM]
      rfl
    · rintro ⟨hM, hc⟩
      refine ⟨?_, h1.2 hM⟩
      rw [h2 hM]
      exact hc
  rw [measure_congr hset, palm_disint (palmAvec S n) (palmLvec S n) (palm_Avec_meas S n)
    (palm_Lvec_meas S n) (palm_indep_AL S n) (palmC_meas n x t)]
  simp_rw [palm_fiber]
  have h3 : ∫⁻ ω, (if palmAvec S n ω ∈ palmMprime n t then
      palmF S t n x (fun i => palmAvec S n ω i.castSucc) else 0) ∂P =
      ∫⁻ ω in palmM S t n, palmF S t n x (palmTvec S n ω) ∂P := by
    rw [← lintegral_indicator (palmM_meas S t n)]
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ palmM S t n
    · rw [Set.indicator_of_mem hω, if_pos ((palm_Avec_mem S t n ω).2 hω)]
      rfl
    · rw [Set.indicator_of_notMem hω, if_neg (fun h => hω ((palm_Avec_mem S t n ω).1 h))]
  rw [h3, ← lintegral_map (palmF_meas S t n x) (palm_Tvec_meas S n), palm_law_T S n hOS,
    lintegral_smul_measure]
  rfl


lemma palm_p_bounds [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) :
    0 ≤ (1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u) ∧
      (1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u) ≤ 1 := by
  have hint : IntervalIntegrable S.resupplyCdf volume 0 t := (palmCdf_mono S).intervalIntegrable
  have h1 : 0 ≤ ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u) :=
    intervalIntegral.integral_nonneg ht.le (fun u _ => sub_nonneg.2 (palmCdf_le_one S u))
  have h2 : ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u) ≤ t := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint]
    have : 0 ≤ ∫ u in (0 : ℝ)..t, S.resupplyCdf u :=
      intervalIntegral.integral_nonneg ht.le (fun u _ => palmCdf_nonneg S u)
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one]
    linarith
  refine ⟨mul_nonneg (by positivity) h1, ?_⟩
  rw [one_div, inv_mul_le_iff₀ ht]
  linarith

theorem palm_binomial [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t)
    (n x : ℕ)
    (hOS : ∀ {A : Set (Fin n → ℝ)}, MeasurableSet A →
      P ({ω | S.orderCount t ω = n} ∩ {ω | (fun i : Fin n => S.arrival i ω) ∈ A}) =
        P {ω | S.orderCount t ω = n} *
          (ENNReal.ofReal ((Nat.factorial n : ℝ) / t ^ n) *
            volume (A ∩ {x : Fin n → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t}))) :
    (P ({ω | S.unitsInResupply t ω = x} ∩ {ω | S.orderCount t ω = n})).toReal =
      (P {ω | S.orderCount t ω = n}).toReal *
        ((Nat.choose n x : ℝ) * ((1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ x *
          (1 - (1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ (n - x)) := by
  obtain ⟨hp0, hp1⟩ := palm_p_bounds S ht
  set p := (1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u) with hp
  set B : ℝ := (Nat.choose n x : ℝ) * p ^ x * (1 - p) ^ (n - x) with hB
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (by linarith) _)
  have hcube := palm_cube_simplex n t (palmF S t n x) (palmF_symm S t n x)
  rw [palm_cube_integral S ht n x] at hcube
  have htn : 0 < t ^ n := pow_pos ht n
  have key : ENNReal.ofReal ((Nat.factorial n : ℝ) / t ^ n) * ∫⁻ s in palmSimplex n t, palmF S t n x s =
      ENNReal.ofReal B := by
    have e1 : ENNReal.ofReal ((Nat.factorial n : ℝ) / t ^ n) =
        ENNReal.ofReal (1 / t ^ n) * (Nat.factorial n : ℝ≥0∞) := by
      rw [div_eq_mul_inv, mul_comm, one_div, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    rw [e1, mul_assoc, ← hcube, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hB, hp]
    field_simp
  rw [palm_joint S n x hOS, mul_assoc, key, ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0]

end ServiceParts.Palm

open MeasureTheory ProbabilityTheory Filter Topology ServiceParts.Palm in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) (n x : ℕ) :
    (P ({ω | S.unitsInResupply t ω = x} ∩ {ω | S.orderCount t ω = n})).toReal =
      (P {ω | S.orderCount t ω = n}).toReal *
        ((Nat.choose n x : ℝ) * ((1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ x *
          (1 - (1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ (n - x)) := by
  exact ServiceParts.Palm.palm_binomial S ht n x
    (fun {A} hA => ServiceParts.Palm.arrival_times_order_statistics S ht n hA)

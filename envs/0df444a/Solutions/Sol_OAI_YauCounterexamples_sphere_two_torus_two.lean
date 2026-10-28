-- Prove2me | solution 1 for OAI.YauCounterexamples.sphere_two_torus_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:24:53.235039+00:00
-- url     : https://prove2.me/submissions/50cd33a0-e5ae-4504-b0f2-5768317951e2

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_exists_three_fixed_witnesses
import Theorems.Thm_OAI_YauCounterexamples_four_nodal_finite
import Theorems.Thm_OAI_YauCounterexamples_laplaceBeltrami_four_lift
import Theorems.Thm_OAI_YauCounterexamples_nodalMeasure_coordinates_lower_bound

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_ExtrusionEquiv
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace YauCounterexamples.SignTests

theorem swept_subset_box {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (s : Set (ι → ℝ)) (p : ι → ℝ) (hp : p ∈ s)
    (hs : ediam s ≠ (∞ : ℝ≥0∞)) :
    swept i d s ⊆ Icc (fun j => p j - Metric.diam s - if j = i then d else 0)
      (fun j => p j + Metric.diam s) := by
  rintro x ⟨z, hz, t, ht, rfl⟩
  have hdist : ∀ j, dist (z j) (p j) ≤ Metric.diam s :=
    (dist_pi_le_iff Metric.diam_nonneg).mp (Metric.dist_le_diam_of_mem' hs hz hp)
  constructor
  · intro j
    have hj := abs_le.mp (hdist j)
    by_cases hji : j = i
    · subst j
      simp only [Pi.sub_apply, Pi.single_eq_same, ↓reduceIte]
      linarith [ht.2]
    · simp only [Pi.sub_apply, Pi.single_eq_of_ne hji, ite_eq_right hji, sub_zero]
      linarith
  · intro j
    have hj := abs_le.mp (hdist j)
    by_cases hji : j = i
    · subst j
      simp only [Pi.sub_apply, Pi.single_eq_same]
      linarith [ht.1]
    · simp only [Pi.sub_apply, Pi.single_eq_of_ne hji, sub_zero]
      linarith

lemma prod_one_special {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommMonoid R] (i : ι) (a b : R) :
    (∏ j : ι, if j = i then a else b) = a * b ^ (Fintype.card ι - 1) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => if j = i then a else b)
    (Finset.mem_univ i)]
  simp only [↓reduceIte]
  congr 1
  calc
    (∏ j ∈ Finset.univ.erase i, if j = i then a else b) =
        ∏ _j ∈ Finset.univ.erase i, b := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
    _ = b ^ (Fintype.card ι - 1) := by simp

lemma swept_box_volume {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d r : ℝ) (p : ι → ℝ) :
    volume (Icc (fun j => p j - r - if j = i then d else 0) (fun j => p j + r)) =
      ENNReal.ofReal (2 * r + d) * (ENNReal.ofReal (2 * r)) ^ (Fintype.card ι - 1) := by
  rw [Real.volume_Icc_pi]
  have h (j : ι) : ENNReal.ofReal (p j + r - (p j - r - if j = i then d else 0)) =
      if j = i then ENNReal.ofReal (2 * r + d) else ENNReal.ofReal (2 * r) := by
    split_ifs <;> congr 1 <;> ring
  simp only [h]
  exact prod_one_special i _ _

theorem sweptVolume_le_of_ediam_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (hd : 0 < d) (s : Set (ι → ℝ))
    (hs : ediam s ≤ ENNReal.ofReal d) :
    sweptVolume i d s ≤
      (3 * ENNReal.ofReal d * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)) *
        ediam s ^ (Fintype.card ι - 1) := by
  obtain hse | ⟨p, hp⟩ := s.eq_empty_or_nonempty
  · subst s
    simp
  have hfin : ediam s ≠ (∞ : ℝ≥0∞) := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
  have hr : Metric.diam s ≤ d := ENNReal.toReal_le_of_le_ofReal hd.le hs
  have hr0 : 0 ≤ Metric.diam s := Metric.diam_nonneg
  have her : ENNReal.ofReal (Metric.diam s) = ediam s :=
    ENNReal.ofReal_toReal hfin
  change volume (swept i d s) ≤ _
  calc
    volume (swept i d s) ≤
        volume (Icc (fun j => p j - Metric.diam s - if j = i then d else 0)
          (fun j => p j + Metric.diam s)) :=
      measure_mono (swept_subset_box i d s p hp hfin)
    _ = ENNReal.ofReal (2 * Metric.diam s + d) *
        (ENNReal.ofReal (2 * Metric.diam s)) ^ (Fintype.card ι - 1) :=
      swept_box_volume i _ _ _
    _ ≤ ENNReal.ofReal (3 * d) *
        (ENNReal.ofReal (2 * Metric.diam s)) ^ (Fintype.card ι - 1) := by
      gcongr
      linarith
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), her, mul_pow]
      norm_num only [ENNReal.ofReal_ofNat]
      ring

theorem sweptVolume_le_hausdorff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (hd : 0 < d) (s : Set (ι → ℝ)) :
    volume (swept i d s) ≤
      (3 * ENNReal.ofReal d * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)) *
        Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ) s := by
  let c : ℝ≥0∞ := 3 * ENNReal.ofReal d * 2 ^ (Fintype.card ι - 1)
  have hc : c ≠ (∞ : ℝ≥0∞) := by
    dsimp [c]
    finiteness
  have hc0 : c ≠ 0 := by
    dsimp [c]
    positivity
  have h := OuterMeasure.le_mkMetric
    (fun r : ℝ≥0∞ => c * r ^ (Fintype.card ι - 1 : ℕ)) (sweptVolume i d)
    (ENNReal.ofReal d) (ENNReal.ofReal_pos.mpr hd)
    (sweptVolume_le_of_ediam_le i d hd)
  have heq : (fun r : ℝ≥0∞ => c * r ^ (Fintype.card ι - 1 : ℕ)) =
      c • (fun r : ℝ≥0∞ => r ^ ((Fintype.card ι - 1 : ℕ) : ℝ)) := by
    ext r
    simp [ENNReal.rpow_natCast]
  rw [heq, OuterMeasure.mkMetric_smul _ hc hc0] at h
  have hs := h s
  simpa only [smul_apply, smul_eq_mul, OuterMeasure.coe_mkMetric,
    Measure.hausdorffMeasure, sweptVolume, c, OuterMeasure.coe_mk] using hs

theorem oppositeSet_subset_swept {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (hd : 0 ≤ d) (D P : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    (hf : ContinuousOn f P)
    (hseg : ∀ x ∈ D, ∀ t ∈ Icc 0 d, x + Pi.single i t ∈ P) :
    oppositeSet D id (fun x => x + Pi.single i d) f ⊆
      swept i d (P ∩ {z | f z = 0}) := by
  rintro x ⟨hx, hsign⟩
  let g : ℝ → ℝ := fun t => f (x + Pi.single i t)
  have hcont : ContinuousOn g (Icc 0 d) := by
    apply hf.comp (continuous_const.add (continuous_single i)).continuousOn
    exact fun t ht => hseg x hx t ht
  have hg0 : g 0 = f x := by simp [g]
  have hgd : g d = f (x + Pi.single i d) := rfl
  have hz : (0 : ℝ) ∈ g '' Icc 0 d := by
    rcases mul_neg_iff.mp hsign with h | h
    · apply intermediate_value_Icc' hd hcont
      simpa only [hg0, hgd, mem_Icc, id_eq] using And.intro h.2.le h.1.le
    · apply intermediate_value_Icc hd hcont
      simpa only [hg0, hgd, mem_Icc, id_eq] using And.intro h.1.le h.2.le
  obtain ⟨t, ht, hzero⟩ := hz
  refine ⟨x + Pi.single i t, ⟨hseg x hx t ht, hzero⟩, t, ht, ?_⟩
  simp

theorem signMass_le_hausdorff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (d : ℝ) (hd : 0 < d) (D P : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    (hf : ContinuousOn f P)
    (hseg : ∀ x ∈ D, ∀ t ∈ Icc 0 d, x + Pi.single i t ∈ P) :
    signMass volume D id (fun x => x + Pi.single i d) f ≤
      (3 * ENNReal.ofReal d * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)) *
        Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ) (P ∩ {z | f z = 0}) :=
  (measure_mono (oppositeSet_subset_swept i d hd.le D P f hf hseg)).trans
    (sweptVolume_le_hausdorff i d hd _)

theorem signCertificate_le_hausdorff_on_union {ι J : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (P : J → Set (ι → ℝ)) (d : J → ℝ) (hd : ∀ p, 0 < d p)
    (hPi : ∀ p, IsOpen (P p)) (hPc : ∀ p, Convex ℝ (P p))
    (hPd : Pairwise fun p q => Disjoint (P p) (P q)) (f : (ι → ℝ) → ℝ)
    (hf : ContinuousOn f (⋃ p, P p)) :
    signCertificate P d f ≤
      ((Fintype.card ι : ℝ≥0∞) * (3 * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1))) *
        Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ) ((⋃ p, P p) ∩ {z | f z = 0}) := by
  let μ : Measure (ι → ℝ) := Measure.hausdorffMeasure (Fintype.card ι - 1 : ℕ)
  let c : ℝ≥0∞ := 3 * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)
  have hterm (p : J) (i : ι) : (ENNReal.ofReal (d p))⁻¹ *
      signMass volume {x | x ∈ P p ∧ x + Pi.single i (d p) ∈ P p}
        id (fun x => x + Pi.single i (d p)) f ≤ c * μ (P p ∩ {z | f z = 0}) := by
    have hseg : ∀ x ∈ {x | x ∈ P p ∧ x + Pi.single i (d p) ∈ P p},
        ∀ t ∈ Icc 0 (d p), x + Pi.single i t ∈ P p := by
      rintro x ⟨hx, hy⟩ t ht
      have hc := hPc p hx hy (show 0 ≤ 1 - t / d p by
        have := (div_le_one (hd p)).mpr ht.2
        linarith) (div_nonneg ht.1 (hd p).le) (by ring : 1 - t / d p + t / d p = 1)
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hji : j = i
      · subst j
        simp only [Pi.single_eq_same]
        field_simp [ne_of_gt (hd p)]
        ring
      · simp only [Pi.single_eq_of_ne hji]
        ring
    have h := signMass_le_hausdorff i (d p) (hd p) _ (P p) f (hf.mono (subset_iUnion P p)) hseg
    have hc0 : ENNReal.ofReal (d p) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (hd p))
    calc
      _ ≤ (ENNReal.ofReal (d p))⁻¹ *
          ((3 * ENNReal.ofReal (d p) * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1)) *
            μ (P p ∩ {z | f z = 0})) := mul_le_mul_right h _
      _ = _ := by
        unfold c
        rw [show 3 * ENNReal.ofReal (d p) * (2 : ℝ≥0∞) ^ (Fintype.card ι - 1) =
          ENNReal.ofReal (d p) * (3 * 2 ^ (Fintype.card ι - 1)) by ring,
          ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
  have hms (p : J) : MeasurableSet (P p ∩ {z | f z = 0}) := by
    obtain ⟨C, hC, heq⟩ := continuousOn_iff_isClosed.mp (hf.mono (subset_iUnion P p))
      {0} isClosed_singleton
    change MeasurableSet (P p ∩ f ⁻¹' {0})
    rw [inter_comm, heq]
    exact hC.measurableSet.inter (hPi p).measurableSet
  have hdis : Pairwise (fun p q => Disjoint (P p ∩ {z | f z = 0})
      (P q ∩ {z | f z = 0})) := by
    intro p q hpq
    exact (hPd hpq).mono inter_subset_left inter_subset_left
  have hsum : ∑ p, μ (P p ∩ {z | f z = 0}) ≤ μ ((⋃ p, P p) ∩ {z | f z = 0}) := by
    have heq : μ (⋃ p, P p ∩ {z | f z = 0}) = ∑ p, μ (P p ∩ {z | f z = 0}) := by
      simpa only [tsum_fintype] using measure_iUnion hdis hms
    rw [← heq]
    rw [iUnion_inter]

  calc
    signCertificate P d f ≤ ∑ p : J, ∑ _i : ι, c * μ (P p ∩ {z | f z = 0}) :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun i _ => hterm p i
    _ = ((Fintype.card ι : ℝ≥0∞) * c) * ∑ p : J, μ (P p ∩ {z | f z = 0}) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp_rw [← mul_assoc]
      rw [← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_right hsum _

end YauCounterexamples.SignTests
end

open Set Function MeasureTheory
open scoped ENNReal
namespace YauCounterexamples.SignTests
lemma extrusionEquiv_apply {n : ℕ} (x : Fin (n+1) → ℝ) :
    extrusionEquiv n x=(x 0, Fin.tail x) := by
  ext i <;> simp [extrusionEquiv,MeasurableEquiv.piFinSuccAbove,Fin.tail]
lemma extrudeSet_volume {n : ℕ} (P : Set (Fin n → ℝ)) :
    volume (extrudeSet P)=volume P := by
  rw [extrudeSet,(volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).measure_preimage_emb
    (extrusionEquiv n).measurableEmbedding]
  change (volume.prod volume) (Ioo (0:ℝ) 1 ×ˢ P)=volume P
  rw [Measure.prod_prod]
  simp
lemma tail_shift_succ {n : ℕ} (x : Fin (n+1) → ℝ) (i : Fin n) (d : ℝ) :
    Fin.tail (x+Pi.single i.succ d)=Fin.tail x+Pi.single i d := by
  ext j
  simp [Fin.tail,Pi.single_apply]
lemma head_shift_succ {n : ℕ} (x : Fin (n+1) → ℝ) (i : Fin n) (d : ℝ) :
    (x+Pi.single i.succ d : Fin (n+1) → ℝ) 0=x 0 := by simp
lemma tail_shift_zero {n : ℕ} (x : Fin (n+1) → ℝ) (d : ℝ) :
    Fin.tail (x+Pi.single 0 d)=Fin.tail x := by
  ext j
  simp [Fin.tail]
lemma signMass_extrude_succ {n : ℕ} (P : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (d : ℝ) :
    signMass volume {x | x∈extrudeSet P ∧ x+Pi.single i.succ d∈extrudeSet P}
      id (fun x => x+Pi.single i.succ d) (f ∘ Fin.tail) =
    signMass volume {x | x∈P ∧ x+Pi.single i d∈P}
      id (fun x => x+Pi.single i d) f := by
  unfold signMass
  have he : oppositeSet {x | x∈extrudeSet P ∧ x+Pi.single i.succ d∈extrudeSet P}
      id (fun x => x+Pi.single i.succ d) (f ∘ Fin.tail) =
      extrudeSet (oppositeSet {x | x∈P ∧ x+Pi.single i d∈P} id (fun x => x+Pi.single i d) f) := by
    ext x
    simp only [oppositeSet,extrudeSet,mem_preimage,extrusionEquiv_apply,
      mem_prod,mem_ofPred_eq,Function.comp_apply,id_eq,head_shift_succ,tail_shift_succ]
    tauto
  rw [he,extrudeSet_volume]
lemma signMass_extrude_zero {n : ℕ} (P : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (d : ℝ) :
    signMass volume {x | x∈extrudeSet P ∧ x+Pi.single 0 d∈extrudeSet P}
      id (fun x => x+Pi.single 0 d) (f ∘ Fin.tail)=0 := by
  unfold signMass
  have he : oppositeSet {x | x∈extrudeSet P ∧ x+Pi.single 0 d∈extrudeSet P}
      id (fun x => x+Pi.single 0 d) (f ∘ Fin.tail)=∅ := by
    ext x
    simp only [oppositeSet,mem_ofPred_eq,Function.comp_apply,id_eq,tail_shift_zero,mem_empty_iff_false,iff_false]
    intro hx
    nlinarith [sq_nonneg (f (Fin.tail x))]
  rw [he,measure_empty]
theorem signCertificate_extrude {n : ℕ} {J : Type*} [Fintype J]
    (P : J → Set (Fin n → ℝ)) (d : J → ℝ) (f : (Fin n → ℝ) → ℝ) :
    signCertificate (fun j => extrudeSet (P j)) d (f ∘ Fin.tail)=signCertificate P d f := by
  unfold signCertificate
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_succ,signMass_extrude_zero,mul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [signMass_extrude_succ]
end YauCounterexamples.SignTests
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_ProductMetric_FourWaveThreeSmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle Function Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma four_chart_target (p : FourManifold) : (chartAt FourModel p).target=univ := by
  change (chartAt (Euclidean 2) p.1).target ×ˢ
    ((chartAt (Euclidean 1) p.2.1).target ×ˢ (chartAt (Euclidean 1) p.2.2).target)=univ
  have hc (z : Circle) : (chartAt (Euclidean 1) z).target=univ := by
    change (stereographic' 1 (-z)).target=univ
    exact stereographic'_target (-z)
  rw [sphere_chart_target,hc,hc,univ_prod_univ,univ_prod_univ]
lemma four_chart_symm_three (p : FourManifold) (y : FourModel) :
    fourToThree ((chartAt FourModel p).symm y)=
      (chartAt ThreeModel (fourToThree p)).symm (fourProjThree y) := by rfl
lemma four_chart_symm_smooth (p : FourManifold) :
    ContMDiff 𝓘(ℝ,FourModel) 𝓘(ℝ,FourModel) ∞ (chartAt FourModel p).symm := by
  have h := contMDiffOn_chart_symm (I:=𝓘(ℝ,FourModel)) (n:=∞) (x:=p)
  rwa [four_chart_target,contMDiffOn_univ] at h
end


open Set Filter Manifold Bundle Function Matrix BoxIntegral MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise ENNReal NNReal
lemma fourProfileCenter_three : fourToThree fourProfileCenter=threeProfileCenter := rfl
lemma fourWave_proj (x : Fin 4 → ℝ) :
    fourProjThree (fourWaveEquiv x)=threeNormalEquiv (normalWaveEquiv (Fin.tail x)) := by
  change (fourSplitEquiv (fourSplitEquiv.symm _)).1 = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl
lemma fourWave_lift (u : ThreeManifold → ℝ) :
    ((u ∘ fourToThree) ∘ (chartAt FourModel fourProfileCenter).symm) ∘ fourWaveEquiv =
      ((u ∘ threeNormalInv) ∘ normalWaveEquiv) ∘ Fin.tail := by
  funext x
  simp only [Function.comp_apply,four_chart_symm_three,fourWave_proj,fourProfileCenter_three,threeNormalInv]
lemma extrudeSet_tailhead (P : Set (Fin 3 → ℝ)) :
    SignTests.extrudeSet P = fourTailHeadEquiv ⁻¹' (P ×ˢ Ioo 0 1) := by
  ext x
  simp only [SignTests.extrudeSet,mem_preimage,SignTests.extrusionEquiv_apply,mem_prod]
  tauto
lemma extrudeSet_open {P : Set (Fin 3 → ℝ)} (hP : IsOpen P) : IsOpen (SignTests.extrudeSet P) := by
  rw [extrudeSet_tailhead]
  exact (hP.prod isOpen_Ioo).preimage fourTailHeadEquiv.continuous
lemma extrudeSet_convex {P : Set (Fin 3 → ℝ)} (hP : Convex ℝ P) : Convex ℝ (SignTests.extrudeSet P) := by
  rw [extrudeSet_tailhead]
  exact (hP.prod (convex_Ioo (0:ℝ) 1)).linear_preimage fourTailHeadEquiv.toLinearMap
lemma extrudeSet_disjoint {P Q : Set (Fin 3 → ℝ)} (h : Disjoint P Q) :
    Disjoint (SignTests.extrudeSet P) (SignTests.extrudeSet Q) := by
  rw [extrudeSet_tailhead,extrudeSet_tailhead]
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp h hx.1 hy.1
lemma fourWaveCompact_isCompact (R : ℝ) : IsCompact (fourWaveCompact R) :=
  ((((isCompact_closedBall (0:NormalWaveSpace) (R/2)).image normalWaveEquiv.symm.continuous).prod isCompact_Icc).image
    fourTailHeadEquiv.symm.continuous).image fourWaveEquiv.continuous
lemma fourWaveCompact_mem {R : ℝ} (x : Fin 4 → ℝ)
    (hx : normalWaveEquiv (Fin.tail x)∈Metric.closedBall 0 (R/2)) (hx0 : x 0∈Ioo 0 1) :
    fourWaveEquiv x∈fourWaveCompact R := by
  refine ⟨x,⟨fourTailHeadEquiv x,?_,fourTailHeadEquiv.symm_apply_apply x⟩,rfl⟩
  exact ⟨⟨normalWaveEquiv (Fin.tail x),hx,normalWaveEquiv.symm_apply_apply _⟩,hx0.1.le,hx0.2.le⟩
lemma four_signCertificate_bound (g : SmoothMetric FourModel FourManifold) (R : ℝ) :
    ∃ D : ℝ≥0, 0<D ∧ ∀ u : ThreeManifold → ℝ, Continuous u →
      ∀ (I : Box (Fin 3)), normalWaveEquiv '' Box.Icc I⊆Metric.closedBall 0 (R/2) →
      ∀ (partition : TaggedPrepartition I) (d : {J : Box (Fin 3) // J∈partition.boxes} → ℝ),
      (∀ j, 0<d j) → SignTests.signCertificate (fun j => Box.Ioo j.val) d
        ((u ∘ threeNormalInv) ∘ normalWaveEquiv) ≤ (D:ℝ≥0∞)*nodalMeasure g 3 (u ∘ fourToThree) := by
  classical
  let K := fourWaveCompact R
  obtain ⟨C,hC,hCbound⟩ := nodalMeasure_coordinates_lower_bound g fourProfileCenter (fourWaveCompact_isCompact R)
    (by rw [four_chart_target]; exact subset_univ _)
  let L : ℝ≥0 := max ‖fourWaveEquiv.symm.toContinuousLinearMap‖₊ 1
  have hL : 0<L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlip : LipschitzWith L fourWaveEquiv.symm :=
    fourWaveEquiv.symm.toContinuousLinearMap.lipschitz.weaken (le_max_left _ _)
  refine ⟨96*L^3*C ^ 3,by positivity,?_⟩
  intro u hu I hI partition d hd
  let f := ((u ∘ fourToThree) ∘ (chartAt FourModel fourProfileCenter).symm) ∘ fourWaveEquiv
  have hf : Continuous f := ((hu.comp fourToThree_smooth.continuous).comp
    (four_chart_symm_smooth _).continuous).comp fourWaveEquiv.continuous
  let P := fun j : {J : Box (Fin 3) // J∈partition.boxes} => SignTests.extrudeSet (Box.Ioo j.val)
  let Z := (⋃ j, P j) ∩ {z | f z=0}
  have hsign : SignTests.signCertificate (fun j => Box.Ioo j.val) d
      ((u ∘ threeNormalInv) ∘ normalWaveEquiv) ≤ 96*Measure.hausdorffMeasure 3 Z := by
    have hh := SignTests.signCertificate_le_hausdorff_on_union P d hd
      (fun j => extrudeSet_open (isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)))
      (fun j => extrudeSet_convex (convex_pi (fun i _ => convex_Ioo _ _)))
      (fun j k hjk => extrudeSet_disjoint ((partition.toPrepartition.disjoint_coe_of_mem j.property k.property
        (fun hh => hjk (Subtype.ext hh))).mono j.val.Ioo_subset_coe k.val.Ioo_subset_coe))
      f hf.continuousOn
    have he : SignTests.signCertificate P d f = SignTests.signCertificate (fun j => Box.Ioo j.val) d
        ((u ∘ threeNormalInv) ∘ normalWaveEquiv) := by
      dsimp [P,f]
      rw [fourWave_lift,SignTests.signCertificate_extrude]
    rw [he] at hh
    norm_num [Z] at hh ⊢
    exact hh
  have hZsub : Z ⊆ fourWaveEquiv.symm '' (K ∩ {y | (u ∘ fourToThree) ((chartAt FourModel fourProfileCenter).symm y)=0}) := by
    rintro x ⟨hx,hfx⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    have hp : Fin.tail x∈Box.Ioo j.val ∧ x 0∈Ioo 0 1 := by
      change x ∈ SignTests.extrudeSet (Box.Ioo j.val) at hj
      rw [extrudeSet_tailhead] at hj
      exact hj
    refine ⟨fourWaveEquiv x,⟨fourWaveCompact_mem x ?_ hp.2,hfx⟩,fourWaveEquiv.symm_apply_apply x⟩
    apply hI
    exact ⟨Fin.tail x,Box.coe_subset_Icc (partition.toPrepartition.le_of_mem j.property (j.val.Ioo_subset_coe hp.1)),rfl⟩
  have hmeasure : Measure.hausdorffMeasure 3 Z ≤ (L:ℝ≥0∞)^3*(C:ℝ≥0∞)^3*nodalMeasure g 3 (u ∘ fourToThree) := by
    calc
      _ ≤ Measure.hausdorffMeasure 3 (fourWaveEquiv.symm ''
        (K ∩ {y | (u ∘ fourToThree) ((chartAt FourModel fourProfileCenter).symm y)=0})) := measure_mono hZsub
      _ ≤ (L:ℝ≥0∞)^(3:ℝ)*Measure.hausdorffMeasure 3
        (K ∩ {y | (u ∘ fourToThree) ((chartAt FourModel fourProfileCenter).symm y)=0}) :=
          hlip.hausdorffMeasure_image_le (by norm_num : (0:ℝ)≤3) _
      _ ≤ (L:ℝ≥0∞)^(3:ℝ)*((C:ℝ≥0∞)^(3:ℝ)*nodalMeasure g 3 (u ∘ fourToThree)) :=
          mul_le_mul' le_rfl (hCbound _ 3 (by norm_num))
      _ = _ := by rw [show (3:ℝ)=(3:ℕ) by norm_num,ENNReal.rpow_natCast,ENNReal.rpow_natCast,mul_assoc]
  apply hsign.trans
  calc
    _ ≤ 96*((L:ℝ≥0∞)^3*(C:ℝ≥0∞)^3*nodalMeasure g 3 (u ∘ fourToThree)) := mul_le_mul' le_rfl hmeasure
    _ = _ := by simp only [ENNReal.coe_mul,ENNReal.coe_pow,ENNReal.coe_ofNat]; ring

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_ProductMetric_SphereProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral MeasureTheory
open scoped Topology ContDiff Distributions ENNReal NNReal
namespace YauCounterexamples
lemma four_sign_nodal_real (g : SmoothMetric FourModel FourManifold) (R : ℝ) :
    ∃ D : ℝ, 0<D ∧ ∀ u : ThreeManifold → ℝ,
      ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u → ThreeRegular u →
      ∀ L : ℝ, 0≤L → ThreeSignAbove R u L → L < D*(nodalMeasure g 3 (u ∘ fourToThree)).toReal := by
  obtain ⟨D,hD,hbound⟩ := four_signCertificate_bound g R
  refine ⟨D,hD,?_⟩
  intro u hu hr L hL hs
  obtain ⟨I,hI,partition,hpart,d,hd,hscore⟩ := hs
  have hh := hscore.trans_le (hbound u hu.continuous I hI partition d hd)
  have hfin := four_nodal_finite g u hu hr
  have hhreal := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)).mpr hh
  simpa only [ENNReal.toReal_ofReal hL,ENNReal.toReal_mul,ENNReal.coe_toReal] using hhreal
lemma four_witnesses_unbounded (R : ℝ) (g : SmoothMetric ThreeModel ThreeManifold)
    (hw : ∀ n : ℕ, ThreeLargeWitness R g ((n:ℝ)+1) ((n:ℝ)+1)) :
    HasUnboundedNodalRatio (fourProductMetric g) 4 := by
  classical
  choose k hk e u heB heD hu hu0 hue hreg hscore using hw
  have hepos (n : ℕ) : 0<e n := lt_trans (by positivity) (heB n)
  have hfin (n : ℕ) : nodalMeasure (fourProductMetric g) 3 (u n ∘ fourToThree) ≠ (∞ : ℝ≥0∞) :=
    four_nodal_finite _ _ (hu n) (hreg n)
  obtain ⟨D,hD,hbound⟩ := four_sign_nodal_real (fourProductMetric g) R
  have hbase : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have heratio (n : ℕ) : ((n:ℝ)+1)/(2*D) ≤
      (nodalMeasure (fourProductMetric g) 3 (u n ∘ fourToThree)).toReal / Real.sqrt (e n) := by
    have hkpos : (0:ℝ)<k n := by exact_mod_cast (show 0<k n by have := hk n; omega)
    have hnp : (0:ℝ)≤(n:ℝ)+1 := by positivity
    have hscore' := hbound (u n) (hu n) (hreg n) (((n:ℝ)+1)*(k n:ℝ))
      (mul_nonneg hnp hkpos.le) (hscore n)
    have hsqrtpos := Real.sqrt_pos.mpr (hepos n)
    have hsq := Real.sq_sqrt (hepos n).le
    have hsqrt : Real.sqrt (e n) ≤ 2*(k n:ℝ) := by
      have := heD n
      nlinarith
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<2*D) hsqrtpos).mpr
    have hh := mul_le_mul_of_nonneg_left hsqrt hnp
    nlinarith
  refine ⟨fun n => u n ∘ fourToThree,e,?_,?_,?_⟩
  · intro n
    refine ⟨(hu n).comp fourToThree_smooth,?_,hepos n,?_,hfin n⟩
    · intro heq
      apply hu0 n
      funext q
      exact congrFun heq (q.1,(q.2,1))
    · intro p
      rw [laplaceBeltrami_four_lift g (u n) (hu n) p]
      exact hue n (fourToThree p)
  · exact tendsto_atTop_mono (fun n => (heB n).le) hbase
  · exact tendsto_atTop_mono heratio (hbase.atTop_div_const (by positivity : (0:ℝ)<2*D))

theorem sphere_two_torus_two_oai :
    ∃ g : SmoothMetric FourModel FourManifold,
      HasUnboundedNodalRatio g 4 := by
  obtain ⟨R,hR,g,hg⟩ := exists_three_fixed_witnesses
  exact ⟨fourProductMetric g,four_witnesses_unbounded R g hg⟩
end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.sphere_two_torus_two_oai := @OAI.YauCounterexamples.sphere_two_torus_two_oai

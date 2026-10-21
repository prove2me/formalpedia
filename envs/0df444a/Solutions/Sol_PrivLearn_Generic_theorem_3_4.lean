-- Prove2me | solution 1 for PrivLearn.Generic.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T13:56:02.185878+00:00
-- url     : https://prove2.me/submissions/36eb2193-2996-4965-bfa3-4f4ddd50b882

/-
SPDX-License-Identifier: Apache-2.0
Full native private agnostic learning theorem.
Mathematical source: S. P. Kasiviswanathan, H. K. Lee, K. Nissim,
S. Raskhodnikova, A. Smith, What Can We Learn Privately?,
arXiv:0803.0924v3, section 3.1, Theorem 3.4, printed pp. 11–12.
Fresh proof of actual normalized weighted-Dirac privacy and mixed product-law
accuracy. Official Mathlib sub-Gaussian bounds give finite-class concentration.
The universal witness C=18 repairs the printed constant6 arithmetic while
preserving the exact existential native statement and every hypothesis.
No accepted proof implementation is copied.
-/
import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivLearn_Generic_ExpMech

-- BEGIN Foundation
open MeasureTheory
open scoped ENNReal NNReal BigOperators
-- END Foundation

-- BEGIN Mechanism
open MeasureTheory PrivLearn.Generic
open scoped ENNReal BigOperators

namespace PrivateLearningProof

variable {X : Type*} {n : ℕ}

noncomputable def mass (H : Finset (X → Bool)) (ε : ℝ) (z : Fin n → X × Bool)
    (h : X → Bool) : ℝ := weight ε z h / ∑ a ∈ H, weight ε z a

lemma normalizer_pos (H : Finset (X → Bool)) (hH : H.Nonempty) (ε : ℝ)
    (z : Fin n → X × Bool) : 0 < ∑ a ∈ H, weight ε z a := by
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) hH

lemma mass_nonneg (H : Finset (X → Bool)) (ε : ℝ) (z : Fin n → X × Bool)
    (h : X → Bool) : 0 ≤ mass H ε z h := by
  unfold mass
  exact div_nonneg (Real.exp_nonneg _) (Finset.sum_nonneg fun _ _ => Real.exp_nonneg _)

lemma sum_mass (H : Finset (X → Bool)) (hH : H.Nonempty) (ε : ℝ)
    (z : Fin n → X × Bool) : ∑ h ∈ H, mass H ε z h = 1 := by
  simp only [mass, ← Finset.sum_div]
  exact div_self (normalizer_pos H hH ε z).ne'

open Classical in
lemma mechanism_apply (H : Finset (X → Bool)) (ε : ℝ) (z : Fin n → X × Bool)
    (S : Set (X → Bool)) (hS : MeasurableSet S) :
    expMech H ε z S = ∑ h ∈ H, if h ∈ S then ENNReal.ofReal (mass H ε z h) else 0 := by
  classical
  simp only [expMech, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hS, Set.indicator_apply, Pi.one_apply, smul_eq_mul, mass]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs <;> simp

lemma mechanism_univ (H : Finset (X → Bool)) (hH : H.Nonempty) (ε : ℝ)
    (z : Fin n → X × Bool) : expMech H ε z Set.univ = 1 := by
  rw [mechanism_apply _ _ _ _ MeasurableSet.univ]
  simp only [Set.mem_univ, ↓reduceIte]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun h _ => mass_nonneg H ε z h), sum_mass H hH]
  simp

lemma mechanism_le_one (H : Finset (X → Bool)) (hH : H.Nonempty) (ε : ℝ)
    (z : Fin n → X × Bool) (S : Set (X → Bool)) : expMech H ε z S ≤ 1 := by
  calc
    _ ≤ expMech H ε z Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := mechanism_univ H hH ε z

lemma score_eq_sum (z : Fin n → X × Bool) (h : X → Bool) :
    score z h = -(∑ i : Fin n, if h (z i).1 ≠ (z i).2 then (1 : ℝ) else 0) := by
  classical
  unfold score
  rw [← Finset.sum_boole]

lemma score_eq_neg_mul_errT (z : Fin n → X × Bool) (h : X → Bool) (hn : 0 < n) :
    score z h = -(n : ℝ) * errT z h := by
  unfold score errT
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn']

end PrivateLearningProof
-- END Mechanism

-- BEGIN Privacy
open MeasureTheory PrivLearn.Generic
open scoped ENNReal BigOperators

namespace PrivateLearningProof
variable {X : Type*} {n : ℕ}

lemma score_sensitivity (z z' : Fin n → X × Bool) (hz : Neighbors z z')
    (h : X → Bool) : score z h ≤ score z' h + 1 := by
  classical
  obtain ⟨i, _, hi⟩ := hz
  rw [score_eq_sum, score_eq_sum]
  have he : (∑ j ∈ Finset.univ.erase i, if h (z j).1 ≠ (z j).2 then (1:ℝ) else 0) =
      ∑ j ∈ Finset.univ.erase i, if h (z' j).1 ≠ (z' j).2 then (1:ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hi j (Finset.mem_erase.mp hj).1]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i), he]
  split_ifs <;> linarith

lemma neighbors_symm {D : Type*} (z z' : Fin n → D) (hz : Neighbors z z') :
    Neighbors z' z := by
  obtain ⟨i, hi, hj⟩ := hz
  exact ⟨i, hi.symm, fun j h => (hj j h).symm⟩

lemma weight_neighbor (ε : ℝ) (hε : 0 ≤ ε) (z z' : Fin n → X × Bool)
    (hz : Neighbors z z') (h : X → Bool) :
    weight ε z h ≤ Real.exp (ε/2) * weight ε z' h := by
  have hs := score_sensitivity z z' hz h
  unfold weight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma mass_neighbor (H : Finset (X → Bool)) (hH : H.Nonempty) (ε : ℝ) (hε : 0 ≤ ε)
    (z z' : Fin n → X × Bool) (hz : Neighbors z z') (h : X → Bool) :
    mass H ε z h ≤ Real.exp ε * mass H ε z' h := by
  have hp := normalizer_pos H hH ε z
  have hp' := normalizer_pos H hH ε z'
  have hw := weight_neighbor ε hε z z' hz h
  have hd : (∑ a ∈ H, weight ε z' a) ≤ Real.exp (ε/2) * ∑ a ∈ H, weight ε z a := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => weight_neighbor ε hε z' z (neighbors_symm z z' hz) a
  unfold mass
  rw [← mul_div_assoc, div_le_div_iff₀ hp hp']
  calc
    weight ε z h * ∑ a ∈ H, weight ε z' a ≤
      (Real.exp (ε/2) * weight ε z' h) * (Real.exp (ε/2) * ∑ a ∈ H, weight ε z a) :=
      mul_le_mul hw hd hp'.le (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ = (Real.exp ε * weight ε z' h) * ∑ a ∈ H, weight ε z a := by
      have he : Real.exp (ε/2) * Real.exp (ε/2) = Real.exp ε := by
        rw [← Real.exp_add]; congr 1; ring
      calc
        _ = (Real.exp (ε/2) * Real.exp (ε/2)) * weight ε z' h * ∑ a ∈ H, weight ε z a := by ring
        _ = _ := by rw [he]

lemma mechanism_private (H : Finset (X → Bool)) (hH : H.Nonempty) (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) : IsDP (fun z : Fin n → X × Bool => expMech H ε z) ε := by
  classical
  intro z z' hz S hS
  rw [mechanism_apply _ _ _ _ hS, mechanism_apply _ _ _ _ hS, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  split_ifs with hh
  · rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mass_neighbor H hH ε hε.le z z' hz h)
  · simp

end PrivateLearningProof
-- END Privacy

-- BEGIN Utility
open MeasureTheory PrivLearn.Generic
open scoped ENNReal BigOperators

namespace PrivateLearningProof
variable {X : Type*} {n : ℕ}

lemma mass_le_gap (H : Finset (X → Bool)) (hH : H.Nonempty) (ε : ℝ) (hε : 0 ≤ ε)
    (z : Fin n → X × Bool) (hn : 0 < n) (h a : X → Bool) (ha : a ∈ H)
    (δ : ℝ) (hgap : δ ≤ errT z h - errT z a) :
    mass H ε z h ≤ Real.exp (-ε * n * δ / 2) := by
  have _ := hH
  have hd : weight ε z a ≤ ∑ j ∈ H, weight ε z j :=
    Finset.single_le_sum (f := weight ε z) (fun _ _ => Real.exp_nonneg _) ha
  have ha' : 0 < weight ε z a := Real.exp_pos _
  calc
    mass H ε z h ≤ weight ε z h / weight ε z a :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) ha' hd
    _ = Real.exp (ε * (score z h - score z a) / 2) := by
      unfold weight
      rw [← Real.exp_sub]
      congr 1; ring
    _ ≤ Real.exp (-ε * n * δ / 2) := by
      apply Real.exp_le_exp.mpr
      rw [score_eq_neg_mul_errT z h hn, score_eq_neg_mul_errT z a hn]
      have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have := mul_le_mul_of_nonneg_left hgap (mul_nonneg hε hn')
      nlinarith

lemma good_data_utility [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X] (P : Measure (X × Bool))
    (H : Finset (X → Bool)) (hH : H.Nonempty) (ε α : ℝ) (hε : 0 < ε)
    (z : Fin n → X × Bool) (hn : 0 < n)
    (hgood : ∀ h ∈ H, |errT z h - err P h| < α/3) :
    expMech H ε z {h | OPT P H hH + α < err P h} ≤
      ENNReal.ofReal ((H.card : ℝ) * Real.exp (-ε * n * α / 6)) := by
  classical
  obtain ⟨a, ha, hopt⟩ := Finset.exists_mem_eq_inf' hH (err P)
  have hS : MeasurableSet {h | OPT P H hH + α < err P h} := by measurability
  rw [mechanism_apply _ _ _ _ hS]
  calc
    _ ≤ ∑ _h ∈ H, ENNReal.ofReal (Real.exp (-ε * n * α / 6)) := by
      apply Finset.sum_le_sum
      intro h hh
      split_ifs with hf
      · apply ENNReal.ofReal_le_ofReal
        have hg := abs_lt.mp (hgood h hh)
        have ag := abs_lt.mp (hgood a ha)
        have ho : OPT P H hH = err P a := hopt
        have hgap : α/3 ≤ errT z h - errT z a := by
          change OPT P H hH + α < err P h at hf
          linarith
        have hm := mass_le_gap H hH ε hε.le z hn h a ha (α/3) hgap
        convert hm using 2; ring
      · positivity
    _ = ENNReal.ofReal ((H.card : ℝ) * Real.exp (-ε * n * α / 6)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.exp_nonneg _)]
      simp

lemma accuracy_of_uniform_bound [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (H : Finset (X → Bool)) (hH : H.Nonempty) (ε α : ℝ) (hε : 0 < ε)
    (n : ℕ) (hn : 0 < n) (B : ℝ≥0∞)
    (hB : (Measure.pi fun _ : Fin n => P)
      {z | ∃ h ∈ H, α/3 ≤ |errT z h - err P h|} ≤ B) :
    (∫⁻ z, expMech H ε z {h | OPT P H hH + α < err P h}
      ∂(Measure.pi fun _ : Fin n => P)) ≤
      B + ENNReal.ofReal ((H.card : ℝ) * Real.exp (-ε * n * α / 6)) := by
  classical
  let bad : Set (Fin n → X × Bool) := {z | ∃ h ∈ H, α/3 ≤ |errT z h - err P h|}
  let c := ENNReal.ofReal ((H.card : ℝ) * Real.exp (-ε * n * α / 6))
  have hb : MeasurableSet bad := MeasurableSet.of_discrete
  have hp : ∀ z, expMech H ε z {h | OPT P H hH + α < err P h} ≤ bad.indicator (fun _ => 1) z + c := by
    intro z
    by_cases hz : z ∈ bad
    · simp only [Set.indicator_of_mem hz]
      exact (mechanism_le_one H hH ε z _).trans (le_add_right le_rfl)
    · simp only [Set.indicator_of_notMem hz, zero_add]
      apply good_data_utility P H hH ε α hε z hn
      intro h hh
      exact lt_of_not_ge fun he => hz ⟨h, hh, he⟩
  calc
    _ ≤ ∫⁻ z, bad.indicator (fun _ => (1 : ℝ≥0∞)) z + c ∂(Measure.pi fun _ : Fin n => P) :=
      lintegral_mono hp
    _ = (Measure.pi fun _ : Fin n => P) bad + c := by
      rw [lintegral_add_left (measurable_const.indicator hb)]
      simp [lintegral_indicator hb]
    _ ≤ B + c := add_le_add hB le_rfl

end PrivateLearningProof
-- END Utility

-- BEGIN Concentration
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace PrivateLearningProof
open PrivLearn.Generic

variable {X : Type*} [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]

noncomputable def loss (h : X → Bool) (p : X × Bool) : ℝ :=
  if h p.1 ≠ p.2 then 1 else 0

lemma integral_loss (P : Measure (X × Bool)) (h : X → Bool) :
    ∫ p, loss h p ∂P = err P h := by
  classical
  have he : loss h = ({p : X × Bool | h p.1 ≠ p.2}).indicator (fun _ => (1 : ℝ)) := by
    funext p
    by_cases hp : h p.1 ≠ p.2 <;> simp [loss, hp]
  rw [he, integral_indicator_const 1 (MeasurableSet.of_discrete)]
  simp [err, measureReal_def]

lemma loss_subgaussian (P : Measure (X × Bool)) [IsProbabilityMeasure P] (h : X → Bool) :
    HasSubgaussianMGF (fun p => loss h p - err P h) (1 / 4) P := by
  have hh := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := loss h) (a := 0) (b := 1)
    (measurable_of_countable _).aemeasurable
    (ae_of_all _ fun p => by unfold loss; split_ifs <;> norm_num)
  norm_num [integral_loss] at hh ⊢
  exact hh

omit [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X] in
lemma loss_sum {n : ℕ} (z : Fin n → X × Bool) (h : X → Bool) :
    ∑ i, loss h (z i) = ((Finset.univ.filter fun i => h (z i).1 ≠ (z i).2).card : ℝ) := by
  classical
  simp only [loss, Finset.sum_boole]

omit [Fintype X] [DiscreteMeasurableSpace X] in
lemma centered_loss_sum (P : Measure (X × Bool)) {n : ℕ} (hn : 0 < n)
    (z : Fin n → X × Bool) (h : X → Bool) :
    ∑ i, (loss h (z i) - err P h) = (n : ℝ) * (errT z h - err P h) := by
  rw [Finset.sum_sub_distrib, loss_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold errT
  have hn' : (n : ℝ) ≠ 0 := by positivity
  field_simp

lemma single_hypothesis_concentration (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (h : X → Bool) {ρ : ℝ} (hρ : 0 < ρ) :
    (Measure.pi fun _ : Fin n => P).real {z | ρ ≤ |errT z h - err P h|} ≤
      2 * Real.exp (-2 * (n : ℝ) * ρ ^ 2) := by
  classical
  let μ := Measure.pi fun _ : Fin n => P
  let Y : Fin n → (Fin n → X × Bool) → ℝ := fun i z => loss h (z i) - err P h
  have hb : ∀ i : Fin n, HasSubgaussianMGF (Y i) (1 / 4) μ := by
    intro i
    have hp : HasSubgaussianMGF (fun p => loss h p - err P h) (1 / 4)
        (μ.map (Function.eval i)) := by
      dsimp only [μ]
      rw [(measurePreserving_eval (fun _ : Fin n => P) i).map_eq]
      exact loss_subgaussian P h
    exact HasSubgaussianMGF.of_map (μ := μ) (Y := Function.eval i)
      (X := fun p => loss h p - err P h) (measurable_pi_apply i).aemeasurable hp
  have hi : iIndepFun Y μ :=
    iIndepFun_pi (fun _ : Fin n => (measurable_of_countable
      (fun p : X × Bool => loss h p - err P h)).aemeasurable)
  have hni : iIndepFun (fun i z => -(Y i z)) μ :=
    hi.comp (fun _ => fun t : ℝ => -t) (fun _ => measurable_neg)
  have hn' : 0 < (n : ℝ) := by positivity
  have ht := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hi
    (s := Finset.univ) (fun i _ => hb i) (mul_nonneg hn'.le hρ.le)
  have hnt := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hni
    (s := Finset.univ) (fun i _ => (hb i).neg) (mul_nonneg hn'.le hρ.le)
  have he : -(↑n * ρ) ^ 2 / (2 * ((∑ _i : Fin n, (1 / 4 : ℝ≥0) : ℝ≥0) : ℝ)) =
      -2 * (n : ℝ) * ρ ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    field_simp
    ring
  rw [he] at ht hnt
  have hs : {z | ρ ≤ |errT z h - err P h|} ⊆
      {z | (n : ℝ) * ρ ≤ ∑ i, Y i z} ∪
      {z | (n : ℝ) * ρ ≤ ∑ i, -(Y i z)} := by
    intro z hz
    change ρ ≤ |errT z h - err P h| at hz
    rcases le_abs.mp hz with hz | hz
    · left
      change (n : ℝ) * ρ ≤ ∑ i, (loss h (z i) - err P h)
      rw [centered_loss_sum P hn]
      exact mul_le_mul_of_nonneg_left hz hn'.le
    · right
      change (n : ℝ) * ρ ≤ ∑ i, -(loss h (z i) - err P h)
      rw [Finset.sum_neg_distrib, centered_loss_sum P hn]
      nlinarith [mul_le_mul_of_nonneg_left hz hn'.le]
  exact (measureReal_mono hs).trans ((measureReal_union_le _ _).trans (by linarith))

lemma uniform_concentration (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (H : Finset (X → Bool)) {n : ℕ} (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ) :
    (Measure.pi fun _ : Fin n => P) {z | ∃ h ∈ H, ρ ≤ |errT z h - err P h|} ≤
      ENNReal.ofReal (2 * (H.card : ℝ) * Real.exp (-2 * (n : ℝ) * ρ ^ 2)) := by
  classical
  let μ := Measure.pi fun _ : Fin n => P
  have he : {z : Fin n → X × Bool | ∃ h ∈ H, ρ ≤ |errT z h - err P h|} =
      ⋃ h ∈ H, {z | ρ ≤ |errT z h - err P h|} := by ext z; simp
  have hb : μ.real {z | ∃ h ∈ H, ρ ≤ |errT z h - err P h|} ≤
      2 * (H.card : ℝ) * Real.exp (-2 * (n : ℝ) * ρ ^ 2) := by
    rw [he]
    calc
      _ ≤ ∑ h ∈ H, μ.real {z | ρ ≤ |errT z h - err P h|} := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _h ∈ H, 2 * Real.exp (-2 * (n : ℝ) * ρ ^ 2) :=
        Finset.sum_le_sum fun h _ => single_hypothesis_concentration P hn h hρ
      _ = _ := by simp; ring
  have hr := ENNReal.ofReal_le_ofReal hb
  rw [ofReal_measureReal (by finiteness)] at hr
  exact hr

end PrivateLearningProof
-- END Concentration

-- BEGIN SampleBound
namespace PrivateLearningProof

lemma sample_bound {K n : ℕ} (hK : 0 < K) {ε α β : ℝ}
    (hε : 0 < ε) (hα : 0 < α) (hβ : 0 < β) (hβhalf : β < 1 / 2)
    (hn : 18 * (Real.log K + Real.log (1 / β)) *
      max (1 / (ε * α)) (1 / α ^ 2) ≤ (n : ℝ)) :
    0 < n ∧ 2 * (K : ℝ) * Real.exp (-2 * (n : ℝ) * (α / 3) ^ 2) +
      (K : ℝ) * Real.exp (-ε * (n : ℝ) * α / 6) ≤ β := by
  have hK' : 0 < (K : ℝ) := by positivity
  have hK1 : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  let L := Real.log K + Real.log (1 / β)
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hK1
  have hβ1 : β < 1 := by linarith
  have hlogβ : 0 < Real.log (1 / β) := Real.log_pos ((lt_div_iff₀ hβ).2 (by linarith))
  have hL : 0 < L := add_pos_of_nonneg_of_pos hlogK hlogβ
  have hα2 : 0 < α ^ 2 := sq_pos_of_pos hα
  have hεα : 0 < ε * α := mul_pos hε hα
  have hmax : 0 < max (1 / (ε * α)) (1 / α ^ 2) :=
    lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hn' : 0 < (n : ℝ) := lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) hL) hmax) hn
  refine ⟨by exact_mod_cast hn', ?_⟩
  have ha : 18 * L / α ^ 2 ≤ (n : ℝ) := by
    calc
      _ = 18 * L * (1 / α ^ 2) := by ring
      _ ≤ 18 * L * max (1 / (ε * α)) (1 / α ^ 2) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _ ≤ _ := hn
  have he : 18 * L / (ε * α) ≤ (n : ℝ) := by
    calc
      _ = 18 * L * (1 / (ε * α)) := by ring
      _ ≤ 18 * L * max (1 / (ε * α)) (1 / α ^ 2) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ ≤ _ := hn
  have ha' := (div_le_iff₀ hα2).1 ha
  have he' := (div_le_iff₀ hεα).1 he
  have htail : Real.exp (-2 * (n : ℝ) * (α / 3) ^ 2) ≤ Real.exp (-3 * L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hweight : Real.exp (-ε * (n : ℝ) * α / 6) ≤ Real.exp (-3 * L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hexp1 : Real.exp (-L) = β / K := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log hK', Real.exp_log (by positivity : 0 < 1 / β)]
    field_simp
  have hexp3 : Real.exp (-3 * L) = (β / K) ^ 3 := by
    rw [show -3 * L = -L + -L + -L by ring, Real.exp_add, Real.exp_add, hexp1]
    ring
  have hnorm : 3 * (K : ℝ) * (β / K) ^ 3 = 3 * β ^ 3 / (K : ℝ) ^ 2 := by
    field_simp
  have hβ2 : 3 * β ^ 2 ≤ 1 := by
    nlinarith [mul_self_lt_mul_self hβ.le hβhalf]
  have hβ3 : 3 * β ^ 3 ≤ β := by
    nlinarith [mul_le_mul_of_nonneg_left hβ2 hβ.le]
  have hK2 : 1 ≤ (K : ℝ) ^ 2 := by nlinarith
  calc
    _ ≤ 3 * (K : ℝ) * Real.exp (-3 * L) := by
      nlinarith [mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ 2 * (K : ℝ)),
        mul_le_mul_of_nonneg_left hweight hK'.le]
    _ = 3 * β ^ 3 / (K : ℝ) ^ 2 := by rw [hexp3, hnorm]
    _ ≤ β := (div_le_iff₀ (sq_pos_of_pos hK')).2 (by
      nlinarith [mul_le_mul_of_nonneg_left hK2 hβ.le])

end PrivateLearningProof
-- END SampleBound

-- BEGIN NativeRoot
open MeasureTheory

namespace PrivLearn.Generic

/-- Theorem 3.4 (p. 11, generic private learner), in its quantitative form. There is an absolute
constant `C > 0` such that for every finite example domain `X`, every finite nonempty class
`H = C_d` of hypotheses `X → {0,1}` and all `ε > 0`, `α, β ∈ (0, 1/2)`, the exponential
mechanism `A^ε_q` (a) is `ε`-differentially private, and (b) for every distribution `P` on
`X × {0,1}` and every
`n ≥ C (ln|H| + ln(1/β)) max{1/(εα), 1/α²}`, run on `n` i.i.d. examples from `P` it outputs a
hypothesis with `err(h) > OPT + α` with probability at most `β`. -/
theorem theorem_3_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type) [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
        (H : Finset (X → Bool)) (hH : H.Nonempty) (ε α β : ℝ),
        0 < ε → 0 < α → α < 1 / 2 → 0 < β → β < 1 / 2 →
        (∀ n : ℕ, IsDP (fun z : Fin n → X × Bool => expMech H ε z) ε) ∧
        ∀ (P : Measure (X × Bool)) [IsProbabilityMeasure P] (n : ℕ),
          C * (Real.log H.card + Real.log (1 / β)) * max (1 / (ε * α)) (1 / α ^ 2) ≤ n →
          ∫⁻ z, expMech H ε z {h | OPT P H hH + α < err P h} ∂(Measure.pi fun _ : Fin n => P)
            ≤ ENNReal.ofReal β := by
  refine ⟨18, by norm_num, ?_⟩
  intro X _ _ _ H hH ε α β hε hα hαhalf hβ hβhalf
  have _ := hαhalf
  refine ⟨PrivateLearningProof.mechanism_private H hH ε hε, ?_⟩
  intro P _ n hn
  obtain ⟨hnpos, htotal⟩ := PrivateLearningProof.sample_bound
    (Finset.card_pos.mpr hH) hε hα hβ hβhalf hn
  have hc := PrivateLearningProof.uniform_concentration P H hnpos (by positivity : 0 < α / 3)
  have hu := PrivateLearningProof.accuracy_of_uniform_bound P H hH ε α hε n hnpos _ hc
  refine hu.trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal htotal

end PrivLearn.Generic
-- END NativeRoot

open PrivLearn.Generic MeasureTheory

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type) [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
        (H : Finset (X → Bool)) (hH : H.Nonempty) (ε α β : ℝ),
        0 < ε → 0 < α → α < 1 / 2 → 0 < β → β < 1 / 2 →
        (∀ n : ℕ, IsDP (fun z : Fin n → X × Bool => expMech H ε z) ε) ∧
        ∀ (P : Measure (X × Bool)) [IsProbabilityMeasure P] (n : ℕ),
          C * (Real.log H.card + Real.log (1 / β)) * max (1 / (ε * α)) (1 / α ^ 2) ≤ n →
          ∫⁻ z, expMech H ε z {h | OPT P H hH + α < err P h} ∂(Measure.pi fun _ : Fin n => P)
            ≤ ENNReal.ofReal β :=
  PrivLearn.Generic.theorem_3_4

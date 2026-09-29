-- Prove2me | solution 1 for VapnikChervonenkis.Entropy.lemma3_entropy_rate_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:58:19.259489+00:00
-- url     : https://prove2.me/submissions/315ea97a-3d70-40cd-8baa-0fecdeb91a01

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Entropy_entropy

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

lemma aux_e3l_idx_le {X : Type*} (S : Set (Set X)) {n : ℕ} (x : Fin n → X) :
    Shared.index S x ≤ 2 ^ n := by
  unfold Shared.index
  exact (Finset.card_le_univ _).trans (by simp)

lemma aux_e3l_logb_nonneg {X : Type*} (S : Set (Set X)) {n : ℕ} (x : Fin n → X) :
    0 ≤ Real.logb 2 (Shared.index S x : ℝ) := by
  rcases Nat.eq_zero_or_pos (Shared.index S x) with h | h
  · simp [h]
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

lemma aux_e3l_logb_le {X : Type*} (S : Set (Set X)) {n : ℕ} (x : Fin n → X) :
    Real.logb 2 (Shared.index S x : ℝ) ≤ n := by
  rcases Nat.eq_zero_or_pos (Shared.index S x) with h | h
  · simp [h]
  · calc Real.logb 2 (Shared.index S x : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ n) := by
          apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h)
          exact_mod_cast aux_e3l_idx_le S x
      _ = n := by simp [Real.logb_pow]

lemma aux_e3l_idx_mul {X : Type*} (S : Set (Set X)) {l m : ℕ} (z : Fin (l + m) → X) :
    Shared.index S z ≤ Shared.index S (fun i : Fin l => z (Fin.castAdd m i)) *
      Shared.index S (fun j : Fin m => z (Fin.natAdd l j)) := by
  classical
  unfold Shared.index
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun t : Finset (Fin (l + m)) =>
    (Finset.univ.filter (fun i : Fin l => Fin.castAdd m i ∈ t),
      Finset.univ.filter (fun j : Fin m => Fin.natAdd l j ∈ t)))
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
    obtain ⟨A, hA, hAt⟩ := ht
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_ofPred_eq]
    refine ⟨⟨A, hA, fun i => ?_⟩, ⟨A, hA, fun j => ?_⟩⟩
    · simp [hAt]
    · simp [hAt]
  · intro t _ t' _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · have := congrArg (fun s => i ∈ s) h1
      simpa using this
    · have := congrArg (fun s => j ∈ s) h2
      simpa using this

lemma aux_e3l_logb_sub {X : Type*} (S : Set (Set X)) {l m : ℕ} (z : Fin (l + m) → X) :
    Real.logb 2 (Shared.index S z : ℝ) ≤
      Real.logb 2 (Shared.index S (fun i : Fin l => z (Fin.castAdd m i)) : ℝ) +
      Real.logb 2 (Shared.index S (fun j : Fin m => z (Fin.natAdd l j)) : ℝ) := by
  have ha := aux_e3l_logb_nonneg S (fun i : Fin l => z (Fin.castAdd m i))
  have hb := aux_e3l_logb_nonneg S (fun j : Fin m => z (Fin.natAdd l j))
  have hmul := aux_e3l_idx_mul S z
  rcases Nat.eq_zero_or_pos (Shared.index S z) with h | h
  · simp only [h, Nat.cast_zero, Real.logb_zero]; linarith
  · have hpa : 0 < Shared.index S (fun i : Fin l => z (Fin.castAdd m i)) := by
      rcases Nat.eq_zero_or_pos (Shared.index S (fun i : Fin l => z (Fin.castAdd m i))) with h' | h'
      · rw [h', zero_mul] at hmul; omega
      · exact h'
    have hpb : 0 < Shared.index S (fun j : Fin m => z (Fin.natAdd l j)) := by
      rcases Nat.eq_zero_or_pos (Shared.index S (fun j : Fin m => z (Fin.natAdd l j))) with h' | h'
      · rw [h', mul_zero] at hmul; omega
      · exact h'
    rw [← Real.logb_mul (by positivity) (by positivity)]
    apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h)
    exact_mod_cast hmul

lemma aux_e3l_mp {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (l m : ℕ) :
    MeasurePreserving (fun p : (Fin l → X) × (Fin m → X) => (Fin.append p.1 p.2 : Fin (l + m) → X))
      ((Measure.pi fun _ : Fin l => P).prod (Measure.pi fun _ : Fin m => P))
      (Measure.pi fun _ : Fin (l + m) => P) := by
  have h1 := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : Fin l ⊕ Fin m => X)
    (fun _ : Fin l ⊕ Fin m => P)
  have h2 := measurePreserving_piCongrLeft (α := fun _ : Fin (l + m) => X)
    (fun _ : Fin (l + m) => P) finSumFinEquiv
  have := h2.comp h1
  convert this using 1
  funext p
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [Fin.append_left, Function.comp_apply]
    show p.1 i = (Equiv.piCongrLeft (fun _ => X) finSumFinEquiv)
      ((Equiv.sumPiEquivProdPi fun _ => X).symm p) (finSumFinEquiv (Sum.inl i))
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
  · simp only [Fin.append_right, Function.comp_apply]
    show p.2 j = (Equiv.piCongrLeft (fun _ => X) finSumFinEquiv)
      ((Equiv.sumPiEquivProdPi fun _ => X).symm p) (finSumFinEquiv (Sum.inr j))
    rw [Equiv.piCongrLeft_apply_apply]
    rfl

lemma aux_e3l_meas {X : Type*} [MeasurableSpace X] (S : Set (Set X))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) (n : ℕ) :
    Measurable (fun x : Fin n → X => Real.logb 2 (Shared.index S x : ℝ)) :=
  (measurable_from_nat (f := fun k : ℕ => Real.logb 2 (k : ℝ))).comp (hΔ n)

lemma aux_e3l_bounds {X : Type*} [MeasurableSpace X] (S : Set (Set X)) (P : Measure X)
    [IsProbabilityMeasure P]
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) (n : ℕ) :
    0 ≤ entropy S P n ∧ entropy S P n ≤ n := by
  unfold entropy
  have hint : Integrable (fun x : Fin n → X => Real.logb 2 (Shared.index S x : ℝ))
      (Measure.pi fun _ : Fin n => P) := by
    refine Integrable.of_bound (aux_e3l_meas S hΔ n).aestronglyMeasurable n
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_e3l_logb_nonneg S x)]
    exact aux_e3l_logb_le S x
  refine ⟨integral_nonneg fun x => aux_e3l_logb_nonneg S x, ?_⟩
  calc ∫ x, Real.logb 2 (Shared.index S x : ℝ) ∂(Measure.pi fun _ : Fin n => P)
      ≤ ∫ _x, (n : ℝ) ∂(Measure.pi fun _ : Fin n => P) :=
        integral_mono hint (integrable_const _) fun x => aux_e3l_logb_le S x
    _ = n := by simp

lemma aux_e3l_subadd {X : Type*} [MeasurableSpace X] (S : Set (Set X)) (P : Measure X)
    [IsProbabilityMeasure P]
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) (l m : ℕ) :
    entropy S P (l + m) ≤ entropy S P l + entropy S P m := by
  unfold entropy
  have hmp := aux_e3l_mp P l m
  set μ := (Measure.pi fun _ : Fin l => P).prod (Measure.pi fun _ : Fin m => P) with hμ
  have hint : ∀ n : ℕ, Integrable (fun x : Fin n → X => Real.logb 2 (Shared.index S x : ℝ))
      (Measure.pi fun _ : Fin n => P) := by
    intro n
    refine Integrable.of_bound (aux_e3l_meas S hΔ n).aestronglyMeasurable n
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_e3l_logb_nonneg S x)]
    exact aux_e3l_logb_le S x
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact (aux_e3l_meas S hΔ (l + m)).aestronglyMeasurable)]
  have hint1 : Integrable (fun p : (Fin l → X) × (Fin m → X) =>
      Real.logb 2 (Shared.index S p.1 : ℝ)) μ := by
    refine Integrable.of_bound ((aux_e3l_meas S hΔ l).comp measurable_fst).aestronglyMeasurable l
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_e3l_logb_nonneg S _)]
    exact aux_e3l_logb_le S _
  have hint2 : Integrable (fun p : (Fin l → X) × (Fin m → X) =>
      Real.logb 2 (Shared.index S p.2 : ℝ)) μ := by
    refine Integrable.of_bound ((aux_e3l_meas S hΔ m).comp measurable_snd).aestronglyMeasurable m
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_e3l_logb_nonneg S _)]
    exact aux_e3l_logb_le S _
  have hint3 : Integrable (fun p : (Fin l → X) × (Fin m → X) =>
      Real.logb 2 (Shared.index S (Fin.append p.1 p.2 : Fin (l + m) → X) : ℝ)) μ := by
    refine Integrable.of_bound ((aux_e3l_meas S hΔ (l + m)).comp
      hmp.measurable).aestronglyMeasurable (l + m : ℕ) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_e3l_logb_nonneg S _)]
    exact aux_e3l_logb_le S _
  calc ∫ p, Real.logb 2 (Shared.index S (Fin.append p.1 p.2 : Fin (l + m) → X) : ℝ) ∂μ
      ≤ ∫ p, (Real.logb 2 (Shared.index S p.1 : ℝ) + Real.logb 2 (Shared.index S p.2 : ℝ)) ∂μ := by
        refine integral_mono hint3 (hint1.add hint2) fun p => ?_
        have := aux_e3l_logb_sub S (Fin.append p.1 p.2 : Fin (l + m) → X)
        simpa only [Fin.append_left, Fin.append_right] using this
    _ = ∫ p, Real.logb 2 (Shared.index S p.1 : ℝ) ∂μ +
          ∫ p, Real.logb 2 (Shared.index S p.2 : ℝ) ∂μ := integral_add hint1 hint2
    _ = _ := by
        rw [hμ, integral_fun_fst (fun x : Fin l → X => Real.logb 2 (Shared.index S x : ℝ)),
          integral_fun_snd (fun x : Fin m → X => Real.logb 2 (Shared.index S x : ℝ))]
        simp

end VapnikChervonenkis.Entropy

open VapnikChervonenkis VapnikChervonenkis.Entropy
open MeasureTheory Filter Topology

theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧
      Tendsto (fun l : ℕ => entropy S P l / (l : ℝ)) atTop (𝓝 c) := by
  have hsub : Subadditive (fun l : ℕ => entropy S P l) := fun a b => aux_e3l_subadd S P hΔ a b
  have hdiv : ∀ n : ℕ, 0 ≤ entropy S P n / (n : ℝ) ∧ entropy S P n / (n : ℝ) ≤ 1 := by
    intro n
    obtain ⟨h0, h1⟩ := aux_e3l_bounds S P hΔ n
    refine ⟨div_nonneg h0 (Nat.cast_nonneg n), ?_⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · rw [div_le_one (by exact_mod_cast hn)]; exact h1
  have hbdd : BddBelow (Set.range fun n : ℕ => entropy S P n / (n : ℝ)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact (hdiv n).1⟩
  have ht := hsub.tendsto_lim hbdd
  exact ⟨hsub.lim, ge_of_tendsto' ht fun n => (hdiv n).1, le_of_tendsto' ht fun n => (hdiv n).2, ht⟩

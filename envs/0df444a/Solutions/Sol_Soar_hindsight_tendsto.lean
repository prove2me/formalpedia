-- Prove2me | solution 1 for Soar.hindsight_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:26:04.055978+00:00
-- url     : https://prove2.me/submissions/e9defe2e-3f73-4b0f-87f8-d0be415dba50

import Mathlib
import Definitions.Def_SoarModel

open MeasureTheory Filter Topology

namespace SoarHindAux

lemma mp_split {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (m k : ℕ) :
    MeasurePreserving
      (fun x : Fin (m + k) → Z =>
        ((fun i => x (Fin.castAdd k i)), (fun i => x (Fin.natAdd m i))))
      (Measure.pi fun _ => P)
      ((Measure.pi fun _ : Fin m => P).prod (Measure.pi fun _ : Fin k => P)) := by
  have h1 := MeasurePreserving.symm _
    (measurePreserving_piCongrLeft (fun _ : Fin (m + k) => P) finSumFinEquiv)
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin m ⊕ Fin k => Z) (fun _ => P)
  have h3 := h2.comp h1
  convert h3 using 1
  funext x
  ext i <;> simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi] <;> rfl

lemma map_left {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (m k : ℕ) :
    (Measure.pi fun _ : Fin (m + k) => P).map (fun x i => x (Fin.castAdd k i)) =
      Measure.pi fun _ => P := by
  have h := mp_split P m k
  have : (fun (x : Fin (m + k) → Z) (i : Fin m) => x (Fin.castAdd k i)) =
      Prod.fst ∘ (fun x : Fin (m + k) → Z =>
        ((fun i => x (Fin.castAdd k i)), (fun i => x (Fin.natAdd m i)))) := rfl
  rw [this, ← Measure.map_map measurable_fst h.measurable, h.map_eq, Measure.map_fst_prod]
  simp

lemma map_right {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (m k : ℕ) :
    (Measure.pi fun _ : Fin (m + k) => P).map (fun x i => x (Fin.natAdd m i)) =
      Measure.pi fun _ => P := by
  have h := mp_split P m k
  have : (fun (x : Fin (m + k) → Z) (i : Fin k) => x (Fin.natAdd m i)) =
      Prod.snd ∘ (fun x : Fin (m + k) → Z =>
        ((fun i => x (Fin.castAdd k i)), (fun i => x (Fin.natAdd m i)))) := rfl
  rw [this, ← Measure.map_map measurable_snd h.measurable, h.map_eq, Measure.map_snd_prod]
  simp

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

instance pairProb (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (n : ℕ) : IsProbabilityMeasure (SoarPairMeasure P Q n) := by
  unfold SoarPairMeasure; infer_instance

def splitL (m k : ℕ) (p : (Fin (m + k) → X) × (Fin (m + k) → Y)) :
    (Fin m → X) × (Fin m → Y) :=
  (fun i => p.1 (Fin.castAdd k i), fun i => p.2 (Fin.castAdd k i))

def splitR (m k : ℕ) (p : (Fin (m + k) → X) × (Fin (m + k) → Y)) :
    (Fin k → X) × (Fin k → Y) :=
  (fun i => p.1 (Fin.natAdd m i), fun i => p.2 (Fin.natAdd m i))

lemma measurable_splitL (m k : ℕ) : Measurable (splitL (X := X) (Y := Y) m k) := by
  unfold splitL; fun_prop

lemma measurable_splitR (m k : ℕ) : Measurable (splitR (X := X) (Y := Y) m k) := by
  unfold splitR; fun_prop

lemma map_splitL (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (m k : ℕ) :
    (SoarPairMeasure P Q (m + k)).map (splitL m k) = SoarPairMeasure P Q m := by
  unfold SoarPairMeasure
  have hf : Measurable (fun (x : Fin (m + k) → X) (i : Fin m) => x (Fin.castAdd k i)) := by
    fun_prop
  have hg : Measurable (fun (x : Fin (m + k) → Y) (i : Fin m) => x (Fin.castAdd k i)) := by
    fun_prop
  have : splitL (X := X) (Y := Y) m k =
      Prod.map (fun (x : Fin (m + k) → X) (i : Fin m) => x (Fin.castAdd k i))
        (fun (x : Fin (m + k) → Y) (i : Fin m) => x (Fin.castAdd k i)) := rfl
  rw [this, ← Measure.map_prod_map _ _ hf hg, map_left, map_left]

lemma map_splitR (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (m k : ℕ) :
    (SoarPairMeasure P Q (m + k)).map (splitR m k) = SoarPairMeasure P Q k := by
  unfold SoarPairMeasure
  have hf : Measurable (fun (x : Fin (m + k) → X) (i : Fin k) => x (Fin.natAdd m i)) := by
    fun_prop
  have hg : Measurable (fun (x : Fin (m + k) → Y) (i : Fin k) => x (Fin.natAdd m i)) := by
    fun_prop
  have : splitR (X := X) (Y := Y) m k =
      Prod.map (fun (x : Fin (m + k) → X) (i : Fin k) => x (Fin.natAdd m i))
        (fun (x : Fin (m + k) → Y) (i : Fin k) => x (Fin.natAdd m i)) := rfl
  rw [this, ← Measure.map_prod_map _ _ hf hg, map_right, map_right]

lemma meas_S (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (n : ℕ) :
    Measurable (fun p : (Fin n → X) × (Fin n → Y) => SoarHindsightSum φ p.1 p.2) := by
  unfold SoarHindsightSum
  refine Measurable.iSup fun σ => ?_
  refine Finset.measurable_sum _ fun t _ => ?_
  have hg : Measurable fun p : (Fin n → X) × (Fin n → Y) => ((p.1 t, p.2 (σ t)) : X × Y) := by
    fun_prop
  have := hφ.comp hg
  exact this

lemma S_ge_sum (φ : X → Y → ℝ) {n : ℕ} (x : Fin n → X) (y : Fin n → Y)
    (σ : Equiv.Perm (Fin n)) : ∑ t, φ (x t) (y (σ t)) ≤ SoarHindsightSum φ x y :=
  le_ciSup (f := fun σ : Equiv.Perm (Fin n) => ∑ t, φ (x t) (y (σ t)))
    (Set.finite_range _).bddAbove σ

lemma S_abs (φ : X → Y → ℝ) (C : ℝ) (hC : SoarBounded φ C) {n : ℕ} (x : Fin n → X)
    (y : Fin n → Y) : |SoarHindsightSum φ x y| ≤ n * |C| := by
  rw [abs_le]
  constructor
  · refine le_trans ?_ (S_ge_sum φ x y 1)
    calc -(n * |C|) = ∑ _t : Fin n, -|C| := by simp
      _ ≤ _ := Finset.sum_le_sum fun t _ => neg_le_of_abs_le ((hC _ _).trans (le_abs_self C))
  · unfold SoarHindsightSum
    apply ciSup_le; intro σ
    calc ∑ t, φ (x t) (y (σ t)) ≤ ∑ _t : Fin n, |C| :=
          Finset.sum_le_sum fun t _ => (le_abs_self _).trans ((hC _ _).trans (le_abs_self C))
      _ = n * |C| := by simp

lemma S_add (φ : X → Y → ℝ) {m k : ℕ} (p : (Fin (m + k) → X) × (Fin (m + k) → Y)) :
    SoarHindsightSum φ (splitL m k p).1 (splitL m k p).2 +
      SoarHindsightSum φ (splitR m k p).1 (splitR m k p).2 ≤ SoarHindsightSum φ p.1 p.2 := by
  obtain ⟨x, y⟩ := p
  obtain ⟨σ1, h1⟩ := exists_eq_ciSup_of_finite
    (f := fun σ : Equiv.Perm (Fin m) => ∑ t, φ (x (Fin.castAdd k t)) (y (Fin.castAdd k (σ t))))
  obtain ⟨σ2, h2⟩ := exists_eq_ciSup_of_finite
    (f := fun σ : Equiv.Perm (Fin k) => ∑ t, φ (x (Fin.natAdd m t)) (y (Fin.natAdd m (σ t))))
  have e1 : SoarHindsightSum φ (splitL m k (x, y)).1 (splitL m k (x, y)).2 =
      ∑ t, φ (x (Fin.castAdd k t)) (y (Fin.castAdd k (σ1 t))) := h1.symm
  have e2 : SoarHindsightSum φ (splitR m k (x, y)).1 (splitR m k (x, y)).2 =
      ∑ t, φ (x (Fin.natAdd m t)) (y (Fin.natAdd m (σ2 t))) := h2.symm
  rw [e1, e2]
  let σ : Equiv.Perm (Fin (m + k)) :=
    (finSumFinEquiv.symm.trans (Equiv.sumCongr σ1 σ2)).trans finSumFinEquiv
  refine le_trans (le_of_eq ?_) (S_ge_sum φ x y σ)
  rw [Fin.sum_univ_add]
  simp [σ]

end SoarHindAux

open SoarHindAux in
theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (φ : X → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : SoarBounded φ C) :
    Tendsto (fun n : ℕ => SoarHindsight P Q φ n) atTop (𝓝 (SoarLimit P Q φ)) ∧
      ∀ n : ℕ, 1 ≤ n → SoarHindsight P Q φ n ≤ SoarLimit P Q φ := by
  set a : ℕ → ℝ := fun n => ∫ p, SoarHindsightSum φ p.1 p.2 ∂SoarPairMeasure P Q n with ha
  have hH : ∀ n, SoarHindsight P Q φ n = a n / n := fun n => rfl
  have hint : ∀ n, Integrable (fun p : (Fin n → X) × (Fin n → Y) => SoarHindsightSum φ p.1 p.2)
      (SoarPairMeasure P Q n) := fun n =>
    Integrable.of_bound (meas_S φ hφ n).aestronglyMeasurable (n * |C|)
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact S_abs φ C hC p.1 p.2)
  have hsup : ∀ m k, a m + a k ≤ a (m + k) := by
    intro m k
    have hL : ∫ p, SoarHindsightSum φ (splitL m k p).1 (splitL m k p).2
        ∂SoarPairMeasure P Q (m + k) = a m := by
      rw [ha]; dsimp only
      rw [← map_splitL P Q m k, integral_map (measurable_splitL m k).aemeasurable]
      rw [map_splitL P Q m k]; exact (meas_S φ hφ m).aestronglyMeasurable
    have hR : ∫ p, SoarHindsightSum φ (splitR m k p).1 (splitR m k p).2
        ∂SoarPairMeasure P Q (m + k) = a k := by
      rw [ha]; dsimp only
      rw [← map_splitR P Q m k, integral_map (measurable_splitR m k).aemeasurable]
      rw [map_splitR P Q m k]; exact (meas_S φ hφ k).aestronglyMeasurable
    have iL : Integrable (fun p => SoarHindsightSum φ (splitL m k p).1 (splitL m k p).2)
        (SoarPairMeasure P Q (m + k)) :=
      Integrable.of_bound ((meas_S φ hφ m).comp (measurable_splitL m k)).aestronglyMeasurable
        (m * |C|) (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact S_abs φ C hC _ _)
    have iR : Integrable (fun p => SoarHindsightSum φ (splitR m k p).1 (splitR m k p).2)
        (SoarPairMeasure P Q (m + k)) :=
      Integrable.of_bound ((meas_S φ hφ k).comp (measurable_splitR m k)).aestronglyMeasurable
        (k * |C|) (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact S_abs φ C hC _ _)
    rw [← hL, ← hR, ← integral_add iL iR]
    exact integral_mono (iL.add iR) (hint (m + k)) fun p => S_add φ p
  have habs : ∀ n, |a n| ≤ n * |C| := by
    intro n
    have := norm_integral_le_of_norm_le_const (μ := SoarPairMeasure P Q n)
      (f := fun p : (Fin n → X) × (Fin n → Y) => SoarHindsightSum φ p.1 p.2) (C := n * |C|)
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact S_abs φ C hC p.1 p.2)
    simpa [Real.norm_eq_abs] using this
  have hHb : ∀ n, |SoarHindsight P Q φ n| ≤ |C| := by
    intro n
    rw [hH]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [abs_div, abs_of_pos hn', div_le_iff₀ hn']
      linarith [habs n]
  have hsub : Subadditive (fun n => -a n) := fun m k => by have := hsup m k; linarith
  have hbdd : BddBelow (Set.range fun n => (fun n => -a n) n / n) := by
    refine ⟨-|C|, ?_⟩
    rintro _ ⟨n, rfl⟩
    have := (abs_le.1 (hHb n)).2
    rw [hH] at this
    simp only [neg_div]
    linarith
  have ht := hsub.tendsto_lim hbdd
  have ht' : Tendsto (fun n => SoarHindsight P Q φ n) atTop (𝓝 (-hsub.lim)) := by
    have := ht.neg
    simp only [neg_div, neg_neg] at this
    exact this
  have hle : ∀ n, n ≠ 0 → SoarHindsight P Q φ n ≤ -hsub.lim := by
    intro n hn
    have := hsub.lim_le_div hbdd hn
    rw [hH]; simp only [neg_div] at this; linarith
  have hlim : SoarLimit P Q φ = -hsub.lim := by
    apply le_antisymm
    · exact ciSup_le fun n => hle (n + 1) (by omega)
    · have hB : BddAbove (Set.range fun n => SoarHindsight P Q φ (n + 1)) := by
        refine ⟨|C|, ?_⟩
        rintro _ ⟨n, rfl⟩
        exact (abs_le.1 (hHb (n + 1))).2
      exact le_of_tendsto' ((tendsto_add_atTop_iff_nat 1).2 ht') fun n => le_ciSup hB n
  refine ⟨hlim ▸ ht', fun n hn => hlim ▸ hle n (by omega)⟩


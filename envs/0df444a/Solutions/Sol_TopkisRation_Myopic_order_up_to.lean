-- Prove2me | solution 1 for TopkisRation.Myopic.order_up_to
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:42:35.876197+00:00
-- url     : https://prove2.me/submissions/6b63513a-a19a-434f-a78a-2e4e70bdf3a3

import Definitions.Def_TopkisRation_Myopic_MultiPeriod
import Theorems.Thm_TopkisRation_Myopic_C_convex_continuous

namespace TopkisRation.Myopic.T4aux
open TopkisRation.Myopic

open MeasureTheory Filter Topology

variable {n : ℕ}

def DomE (n : ℕ) : Set (ℝ × (Fin n → ℝ)) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2}

structure PerOK (M : Model n) : Prop where
  a0 : ∀ t ∈ Finset.Icc 1 M.k, 0 ≤ M.a t
  a1 : ∀ t ∈ Finset.Icc 1 M.k, M.a t ≤ 1
  hc : ∀ t ∈ Finset.Icc 1 M.k, ContinuousOn (M.h t) (Set.Ici 0)
  prob : ∀ t ∈ Finset.Icc 1 M.k, IsProbabilityMeasure (M.μ t)
  nonneg : ∀ t ∈ Finset.Icc 1 M.k, ∀ᵐ x ∂(M.μ t), 0 ≤ x
  mean : ∀ t ∈ Finset.Icc 1 M.k, ∀ j, Integrable (fun x : Fin n → ℝ => x j) (M.μ t)
  v1 : ∀ z, M.v₁ z = 0
  v2u : UpperSemicontinuous M.v₂
  v2b : ∀ Z : ℝ, ∃ A, 0 ≤ A ∧ ∀ y ≤ Z, |M.v₂ y| ≤ A * (1 + |y|)

def BoundT (M : Model n) (t : ℕ) : Prop :=
  ∀ Z : ℝ, ∃ A, 0 ≤ A ∧ ∀ z b, 0 ≤ z → z ≤ Z → 0 ≤ b → |M.g t z b| ≤ A * (1 + ∑ j, b j)

def UscT (M : Model n) (t : ℕ) : Prop :=
  UpperSemicontinuousOn (fun q : ℝ × (Fin n → ℝ) => M.g t q.1 q.2) (DomE n)

lemma usc_comp {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Y → ℝ} {D : Set Y}
    (hf : UpperSemicontinuousOn f D) {φ : X → Y} {T : Set X} {x : X} (hx : x ∈ T)
    (hφ : ContinuousWithinAt φ T x) (hmaps : Set.MapsTo φ T D) :
    UpperSemicontinuousWithinAt (fun x => f (φ x)) T x := by
  intro y hy
  exact (hφ.tendsto_nhdsWithin hmaps).eventually (hf (φ x) (hmaps hx) y hy)

lemma sum_nonneg' {b : Fin n → ℝ} (hb : 0 ≤ b) : 0 ≤ ∑ j, b j :=
  Finset.sum_nonneg (fun j _ => hb j)

lemma le_sum' {b : Fin n → ℝ} (hb : 0 ≤ b) (j : Fin n) : b j ≤ ∑ i, b i :=
  Finset.single_le_sum (fun i _ => hb i) (Finset.mem_univ j)

lemma feas_mem {z : ℝ} {B : Fin n → ℝ} (hz : 0 ≤ z) (hB : 0 ≤ B) :
    B ∈ TopkisRation.Levels.feasible z B :=
  ⟨hB, le_rfl, by simp [hz]⟩

lemma bound0 (M : Model n) (hM : PerOK M) : BoundT M 0 := by
  intro Z
  obtain ⟨A, hA, hv⟩ := hM.v2b Z
  refine ⟨A * (1 + |Z|), by positivity, ?_⟩
  intro z b hz hzZ hb
  have hs := sum_nonneg' hb
  show |M.v₁ z + M.v₂ (z - ∑ j, b j)| ≤ _
  rw [hM.v1, zero_add]
  refine (hv _ (by linarith)).trans ?_
  have h1 : |z - ∑ j, b j| ≤ |Z| + ∑ j, b j :=
    abs_le.2 ⟨by linarith [abs_nonneg Z], by linarith [le_abs_self Z]⟩
  have h2 : A * (1 + |z - ∑ j, b j|) ≤ A * (1 + (|Z| + ∑ j, b j)) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  nlinarith [mul_nonneg (mul_nonneg hA (abs_nonneg Z)) hs]

lemma usc0 (M : Model n) (hM : PerOK M) : UscT M 0 := by
  have : (fun q : ℝ × (Fin n → ℝ) => M.g 0 q.1 q.2) = fun q => M.v₂ (q.1 - ∑ j, q.2 j) := by
    funext q
    show M.v₁ q.1 + M.v₂ (q.1 - ∑ j, q.2 j) = _
    rw [hM.v1, zero_add]
  unfold UscT
  rw [this]
  intro q hq
  have hc : Continuous fun q : ℝ × (Fin n → ℝ) => q.1 - ∑ j, q.2 j :=
    continuous_fst.sub (continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_snd)
  exact usc_comp (D := Set.univ) (hM.v2u.upperSemicontinuousOn _) hq hc.continuousWithinAt
    (Set.mapsTo_univ _ _)

lemma obj_bound (M : Model n) (hM : PerOK M) (t : ℕ) (ht : t + 1 ≤ M.k) (hB : BoundT M t)
    (Z : ℝ) :
    ∃ R, 0 ≤ R ∧ ∀ z B, 0 ≤ z → z ≤ Z → 0 ≤ B → ∀ u ∈ TopkisRation.Levels.feasible z B,
      |M.obj (t+1) (M.g t) z B u| ≤ R * (1 + ∑ j, B j) := by
  have ht' : t + 1 ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨by omega, ht⟩
  obtain ⟨A, hA, hg⟩ := hB Z
  obtain ⟨H, hH⟩ := (isCompact_Icc (a := (0:ℝ)) (b := Z)).exists_bound_of_continuousOn
    ((hM.hc _ ht').mono Set.Icc_subset_Ici_self)
  have hP : 0 ≤ ∑ j, |M.p (t+1) j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  refine ⟨|H| + A + ∑ j, |M.p (t+1) j|, by positivity, ?_⟩
  intro z B hz hzZ hB0 u hu
  obtain ⟨hu0, huB, hsum⟩ := hu
  have hs := sum_nonneg' hB0
  have hsum0 : 0 ≤ ∑ j, (B j - u j) := Finset.sum_nonneg (fun j _ => by linarith [huB j])
  have hw0 : 0 ≤ z - ∑ j, (B j - u j) := by linarith
  have hwz : z - ∑ j, (B j - u j) ≤ Z := by linarith
  have ha0 := hM.a0 _ ht'
  have ha1 := hM.a1 _ ht'
  have hau : 0 ≤ M.a (t+1) • u := fun j => by
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; exact mul_nonneg ha0 (hu0 j)
  have hau_sum : ∑ j, (M.a (t+1) • u) j ≤ ∑ j, B j := Finset.sum_le_sum (fun j _ => by
    simp only [Pi.smul_apply, smul_eq_mul]
    have e1 : 0 ≤ u j := hu0 j
    have e2 : u j ≤ B j := huB j
    nlinarith)
  have h1 : |M.p (t+1) ⬝ᵥ u| ≤ (∑ j, |M.p (t+1) j|) * ∑ j, B j := by
    unfold dotProduct
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (hu0 j)]
    exact mul_le_mul_of_nonneg_left ((huB j).trans (le_sum' hB0 j)) (abs_nonneg _)
  have h2 : |M.h (t+1) (z - ∑ j, (B j - u j))| ≤ |H| := by
    have := hH _ ⟨hw0, hwz⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self H)
  have h3 := hg _ _ hw0 hwz hau
  have h3' : A * (1 + ∑ j, (M.a (t+1) • u) j) ≤ A * (1 + ∑ j, B j) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  show |M.p (t+1) ⬝ᵥ u + M.h (t+1) (z - ∑ j, (B j - u j)) +
      M.g t (z - ∑ j, (B j - u j)) (M.a (t+1) • u)| ≤ _
  have h4 := abs_add_three (M.p (t+1) ⬝ᵥ u) (M.h (t+1) (z - ∑ j, (B j - u j)))
      (M.g t (z - ∑ j, (B j - u j)) (M.a (t+1) • u))
  nlinarith [abs_nonneg H, mul_nonneg (abs_nonneg H) hs, mul_nonneg hA hs]

lemma stage_bound (M : Model n) (hM : PerOK M) (t : ℕ) (ht : t + 1 ≤ M.k) (hB : BoundT M t)
    (Z : ℝ) :
    ∃ R, 0 ≤ R ∧ ∀ z B, 0 ≤ z → z ≤ Z → 0 ≤ B →
      BddBelow (M.obj (t+1) (M.g t) z B '' TopkisRation.Levels.feasible z B) ∧
      |M.stage (t+1) (M.g t) z B| ≤ R * (1 + ∑ j, B j) := by
  obtain ⟨R, hR, h⟩ := obj_bound M hM t ht hB Z
  refine ⟨R, hR, fun z B hz hzZ hB0 => ?_⟩
  have hbdd : BddBelow (M.obj (t+1) (M.g t) z B '' TopkisRation.Levels.feasible z B) :=
    ⟨-(R * (1 + ∑ j, B j)), by
      rintro _ ⟨u, hu, rfl⟩
      exact (abs_le.1 (h z B hz hzZ hB0 u hu)).1⟩
  refine ⟨hbdd, ?_⟩
  have hne : (M.obj (t+1) (M.g t) z B '' TopkisRation.Levels.feasible z B).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ (feas_mem hz hB0)⟩
  unfold Model.stage
  refine abs_le.2 ⟨le_csInf hne ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (abs_le.1 (h z B hz hzZ hB0 u hu)).1
  · exact (csInf_le hbdd (Set.mem_image_of_mem _ (feas_mem hz hB0))).trans
      (abs_le.1 (h z B hz hzZ hB0 B (feas_mem hz hB0))).2

lemma aesm_of_uscOn {μ : Measure (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : UpperSemicontinuousOn f (Set.Ici 0)) (hae : ∀ᵐ x ∂μ, 0 ≤ x) :
    AEStronglyMeasurable f μ := by
  have hT : MeasurableSet (Set.Ici (0 : Fin n → ℝ)) := isClosed_Ici.measurableSet
  have hm : Measurable ((Set.Ici (0 : Fin n → ℝ)).indicator f) := by
    refine measurable_of_Iio (fun c => ?_)
    obtain ⟨u, hu, hEq⟩ := upperSemicontinuousOn_iff_preimage_Iio.1 hf c
    rw [Set.indicator_preimage, Set.ite, Set.inter_comm, hEq]
    exact (hT.inter hu.measurableSet).union ((measurable_zero measurableSet_Iio).diff hT)
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [hae] with x hx
  exact Set.indicator_of_mem (show x ∈ Set.Ici 0 from hx) f

lemma stage_usc (M : Model n) (hM : PerOK M) (t : ℕ) (ht : t + 1 ≤ M.k) (hB : BoundT M t)
    (hU : UscT M t) :
    UpperSemicontinuousOn (fun q : ℝ × (Fin n → ℝ) => M.stage (t+1) (M.g t) q.1 q.2)
      (DomE n) := by
  have ht' : t + 1 ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨by omega, ht⟩
  rintro ⟨z0, B0⟩ ⟨hz0, hB0⟩ y hy
  simp only at hz0 hB0 hy ⊢
  have hne : (M.obj (t+1) (M.g t) z0 B0 '' TopkisRation.Levels.feasible z0 B0).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ (feas_mem hz0 hB0)⟩
  obtain ⟨_, ⟨u0, hu0, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne hy
  obtain ⟨hu00, hu0B, hu0s⟩ := hu0
  have hs0nn : ∀ j, 0 ≤ B0 j - u0 j := fun j => by
    have := hu0B j; simp only at this; linarith
  have hs0B : ∀ j, B0 j - u0 j ≤ B0 j := fun j => by
    have := hu00 j; simp only [Pi.zero_apply] at this; linarith
  let θ : ℝ → ℝ := fun z => min z z0 / z0
  have hθ0 : ∀ z, 0 ≤ z → 0 ≤ θ z := fun z hz => div_nonneg (le_min hz hz0) hz0
  have hθ1 : ∀ z, 0 ≤ z → θ z ≤ 1 := by
    intro z hz
    rcases eq_or_lt_of_le hz0 with h | h
    · simp [θ, ← h]
    · exact (div_le_one h).2 (min_le_right _ _)
  have hθz : ∀ z, 0 ≤ z → θ z * z0 ≤ z := by
    intro z hz
    rcases eq_or_lt_of_le hz0 with h | h
    · simp [θ, ← h, hz]
    · simp only [θ]; rw [div_mul_cancel₀ _ h.ne']; exact min_le_left _ _
  let U : ℝ × (Fin n → ℝ) → (Fin n → ℝ) :=
    fun q j => q.2 j - min (B0 j - u0 j) (q.2 j) * θ q.1
  have hUc : Continuous U := by
    refine continuous_pi (fun j => ?_)
    exact ((continuous_apply j).comp continuous_snd).sub
      ((continuous_const.min ((continuous_apply j).comp continuous_snd)).mul
        ((continuous_fst.min continuous_const).div_const z0))
  have hUf : ∀ q ∈ DomE n, U q ∈ TopkisRation.Levels.feasible q.1 q.2 := by
    rintro ⟨z, B⟩ ⟨hz, hB⟩
    simp only at hz hB ⊢
    have hm0 : ∀ j, 0 ≤ min (B0 j - u0 j) (B j) := fun j => le_min (hs0nn j) (hB j)
    have hmB : ∀ j, min (B0 j - u0 j) (B j) ≤ B j := fun j => min_le_right _ _
    refine ⟨fun j => ?_, fun j => ?_, ?_⟩
    · simp only [U, Pi.zero_apply]
      nlinarith [mul_le_mul_of_nonneg_left (hθ1 z hz) (hm0 j), hmB j]
    · simp only [U]
      nlinarith [mul_nonneg (hm0 j) (hθ0 z hz)]
    · simp only [U, sub_sub_cancel]
      calc ∑ j, min (B0 j - u0 j) (B j) * θ z ≤ ∑ j, (B0 j - u0 j) * θ z :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (min_le_left _ _) (hθ0 z hz))
        _ = θ z * ∑ j, (B0 j - u0 j) := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
        _ ≤ θ z * z0 := mul_le_mul_of_nonneg_left hu0s (hθ0 z hz)
        _ ≤ z := hθz z hz
  have hU0 : U (z0, B0) = u0 := by
    funext j
    simp only [U]
    have : min (B0 j - u0 j) (B0 j) * θ z0 = B0 j - u0 j := by
      rcases eq_or_lt_of_le hz0 with h | h
      · have hz : ∑ i, (B0 i - u0 i) = 0 := le_antisymm (by rw [h]; exact hu0s) (Finset.sum_nonneg (fun i _ => hs0nn i))
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hs0nn i)).1 hz j (Finset.mem_univ _)
        rw [this]; simp [θ, ← h]
      · rw [min_eq_left (hs0B j)]
        simp only [θ, min_self, div_self h.ne', mul_one]
    rw [this]; ring
  let W : ℝ × (Fin n → ℝ) → ℝ := fun q => q.1 - ∑ j, (q.2 j - U q j)
  have hWc : Continuous W := continuous_fst.sub (continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp continuous_snd).sub ((continuous_apply j).comp hUc))
  have hWm : Set.MapsTo W (DomE n) (Set.Ici 0) := by
    intro q hq
    have := (hUf q hq).2.2
    show 0 ≤ q.1 - ∑ j, (q.2 j - U q j)
    linarith
  have hDm : Set.MapsTo (fun q => (W q, M.a (t+1) • U q)) (DomE n) (DomE n) := by
    intro q hq
    refine ⟨hWm hq, fun j => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact mul_nonneg (hM.a0 _ ht') ((hUf q hq).1 j)
  have hq0 : ((z0, B0) : ℝ × (Fin n → ℝ)) ∈ DomE n := ⟨hz0, hB0⟩
  have hp1 : Continuous fun q => M.p (t+1) ⬝ᵥ U q := by
    simp only [dotProduct]
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul ((continuous_apply i).comp hUc))
  have hp2 : ContinuousWithinAt (fun q => M.h (t+1) (W q)) (DomE n) (z0, B0) :=
    ((hM.hc _ ht').comp hWc.continuousOn hWm).continuousWithinAt hq0
  have hp3 := usc_comp hU (φ := fun q => (W q, M.a (t+1) • U q)) hq0
    (Continuous.continuousWithinAt (by
      exact hWc.prodMk (hUc.const_smul (M.a (t+1))))) hDm
  have hΦ := (hp1.continuousWithinAt.upperSemicontinuousWithinAt.add
    hp2.upperSemicontinuousWithinAt).add hp3
  have hΦ0 : M.obj (t+1) (M.g t) z0 B0 u0 < y := hlt
  rw [← hU0] at hΦ0
  have hev := hΦ y hΦ0
  filter_upwards [hev, self_mem_nhdsWithin] with q hq hqD
  obtain ⟨R, -, hst⟩ := stage_bound M hM t ht hB q.1
  have hbdd := (hst q.1 q.2 hqD.1 le_rfl hqD.2).1
  exact lt_of_le_of_lt (csInf_le hbdd (Set.mem_image_of_mem _ (hUf q hqD))) hq

lemma stage_int (M : Model n) (hM : PerOK M) (t : ℕ) (ht : t + 1 ≤ M.k) (hB : BoundT M t)
    (hU : UscT M t) (z : ℝ) (b : Fin n → ℝ) (hz : 0 ≤ z) (hb : 0 ≤ b) :
    Integrable (fun x => M.stage (t+1) (M.g t) z (b + x)) (M.μ (t+1)) := by
  have ht' : t + 1 ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨by omega, ht⟩
  have := hM.prob _ ht'
  have hS := stage_usc M hM t ht hB hU
  have haesm : AEStronglyMeasurable (fun x => M.stage (t+1) (M.g t) z (b + x)) (M.μ (t+1)) := by
    refine aesm_of_uscOn (fun ξ hξ => ?_) (hM.nonneg _ ht')
    exact usc_comp hS (φ := fun x => (z, b + x)) hξ
      (by fun_prop : Continuous fun x : Fin n → ℝ => (z, b + x)).continuousWithinAt
      (fun x hx => ⟨hz, add_nonneg hb hx⟩)
  obtain ⟨R, hR, hst⟩ := stage_bound M hM t ht hB z
  have hint : Integrable (fun ξ : Fin n → ℝ => R * (1 + ∑ j, b j) + R * ∑ j, ξ j) (M.μ (t+1)) :=
    (integrable_const _).add ((integrable_finsetSum _ fun j _ => hM.mean _ ht' j).const_mul R)
  refine hint.mono' haesm ?_
  filter_upwards [hM.nonneg _ ht'] with ξ hξ
  have := (hst z (b + ξ) hz le_rfl (add_nonneg hb hξ)).2
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply, Finset.sum_add_distrib] at this
  linarith

lemma bound_succ (M : Model n) (hM : PerOK M) (t : ℕ) (ht : t + 1 ≤ M.k) (hB : BoundT M t)
    (hU : UscT M t) : BoundT M (t+1) := by
  have ht' : t + 1 ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨by omega, ht⟩
  have := hM.prob _ ht'
  intro Z
  obtain ⟨R, hR, hst⟩ := stage_bound M hM t ht hB Z
  have hS : 0 ≤ ∫ ξ, ∑ j, ξ j ∂(M.μ (t+1)) := integral_nonneg_of_ae (by
    filter_upwards [hM.nonneg _ ht'] with ξ hξ; exact sum_nonneg' hξ)
  refine ⟨R * (1 + ∫ ξ, ∑ j, ξ j ∂(M.μ (t+1))), by positivity, ?_⟩
  intro z b hz hzZ hb
  show |∫ ξ, M.stage (t+1) (M.g t) z (b + ξ) ∂(M.μ (t+1))| ≤ _
  have hsi : Integrable (fun ξ : Fin n → ℝ => ∑ j, ξ j) (M.μ (t+1)) :=
    integrable_finsetSum _ fun j _ => hM.mean _ ht' j
  have hint : Integrable (fun ξ : Fin n → ℝ => R * (1 + ∑ j, b j) + R * ∑ j, ξ j) (M.μ (t+1)) :=
    (integrable_const _).add (hsi.const_mul R)
  have := norm_integral_le_of_norm_le hint (by
    filter_upwards [hM.nonneg _ ht'] with ξ hξ
    have := (hst z (b + ξ) hz hzZ (add_nonneg hb hξ)).2
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply, Finset.sum_add_distrib] at this
    linarith)
  rw [Real.norm_eq_abs, integral_add (integrable_const _) (hsi.const_mul R), integral_const,
    integral_const_mul] at this
  simp only [probReal_univ, one_smul] at this
  refine this.trans ?_
  nlinarith [mul_nonneg (mul_nonneg hR hS) (sum_nonneg' hb)]

lemma usc_succ (M : Model n) (hM : PerOK M) (t : ℕ) (ht : t + 1 ≤ M.k) (hB : BoundT M t)
    (hU : UscT M t) : UscT M (t+1) := by
  have ht' : t + 1 ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨by omega, ht⟩
  have := hM.prob _ ht'
  rintro ⟨z0, b0⟩ ⟨hz0, hb0⟩ y hy
  simp only at hz0 hb0
  have hSU := stage_usc M hM t ht hB hU
  let st : ℝ × (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun q ξ => M.stage (t+1) (M.g t) q.1 (q.2 + ξ)
  let F : ℝ × (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun q ξ => st q ξ ⊔ st (z0, b0) ξ
  obtain ⟨R, hR, hst⟩ := stage_bound M hM t ht hB (z0 + 1)
  have hsi : Integrable (fun ξ : Fin n → ℝ => ∑ j, ξ j) (M.μ (t+1)) :=
    integrable_finsetSum _ fun j _ => hM.mean _ ht' j
  let bound : (Fin n → ℝ) → ℝ := fun ξ => R * (1 + (∑ j, b0 j + 1)) + R * ∑ j, ξ j
  have hbi : Integrable bound (M.μ (t+1)) := (integrable_const _).add (hsi.const_mul R)
  have hsc : Continuous fun q : ℝ × (Fin n → ℝ) => ∑ j, q.2 j :=
    continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_snd
  have hnear : ∀ᶠ q in 𝓝[DomE n] ((z0, b0) : ℝ × (Fin n → ℝ)),
      q ∈ DomE n ∧ q.1 < z0 + 1 ∧ ∑ j, q.2 j < ∑ j, b0 j + 1 := by
    refine (eventually_mem_nhdsWithin (a := ((z0, b0) : ℝ × (Fin n → ℝ))) (s := DomE n)).and (Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_)
    exact ((continuous_fst.tendsto _).eventually (eventually_lt_nhds (by simp))).and
      ((hsc.tendsto _).eventually (eventually_lt_nhds (by simp)))
  have hint : ∀ q ∈ DomE n, Integrable (st q) (M.μ (t+1)) := fun q hq =>
    stage_int M hM t ht hB hU q.1 q.2 hq.1 hq.2
  have hq0 : ((z0, b0) : ℝ × (Fin n → ℝ)) ∈ DomE n := ⟨hz0, hb0⟩
  have hlim : Tendsto (fun q => ∫ ξ, F q ξ ∂(M.μ (t+1))) (𝓝[DomE n] (z0, b0))
      (𝓝 (∫ ξ, st (z0, b0) ξ ∂(M.μ (t+1)))) := by
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbi ?_
    · filter_upwards [hnear] with q hq
      exact ((hint q hq.1).sup (hint _ hq0)).aestronglyMeasurable
    · filter_upwards [hnear] with q hq
      filter_upwards [hM.nonneg _ ht'] with ξ hξ
      have h1 := (hst q.1 (q.2 + ξ) hq.1.1 hq.2.1.le (add_nonneg hq.1.2 hξ)).2
      have h2 := (hst z0 (b0 + ξ) hz0 (by linarith) (add_nonneg hb0 hξ)).2
      simp only [Pi.add_apply, Finset.sum_add_distrib] at h1 h2
      have hRs := mul_le_mul_of_nonneg_left hq.2.2.le hR
      rw [Real.norm_eq_abs]
      refine abs_le.2 ⟨?_, ?_⟩
      · have := (abs_le.1 h1).1
        have : st q ξ ≤ F q ξ := le_sup_left
        simp only [bound]; nlinarith
      · refine sup_le ?_ ?_
        · have := (abs_le.1 h1).2; simp only [bound]; nlinarith
        · have := (abs_le.1 h2).2; simp only [bound]; nlinarith
    · filter_upwards [hM.nonneg _ ht'] with ξ hξ
      have husc : UpperSemicontinuousWithinAt (fun q => st q ξ) (DomE n) (z0, b0) :=
        usc_comp hSU (φ := fun q : ℝ × (Fin n → ℝ) => (q.1, q.2 + ξ)) hq0
          (by fun_prop : Continuous fun q : ℝ × (Fin n → ℝ) => (q.1, q.2 + ξ)).continuousWithinAt
          (fun q hq => ⟨hq.1, add_nonneg hq.2 hξ⟩)
      rw [tendsto_order]
      refine ⟨fun a ha => Eventually.of_forall (fun q => lt_of_lt_of_le ha le_sup_right),
        fun a ha => (husc a ha).mono (fun q hq => sup_lt_iff.2 ⟨hq, ha⟩)⟩
  have hy' : ∫ ξ, st (z0, b0) ξ ∂(M.μ (t+1)) < y := hy
  filter_upwards [hlim.eventually (eventually_lt_nhds hy'), hnear] with q h1 h2
  show ∫ ξ, st q ξ ∂(M.μ (t+1)) < y
  exact lt_of_le_of_lt (integral_mono (hint q h2.1) ((hint q h2.1).sup (hint _ hq0))
    (fun ξ => le_sup_left)) h1

lemma good_all (M : Model n) (hM : PerOK M) : ∀ t, t ≤ M.k → BoundT M t ∧ UscT M t
  | 0, _ => ⟨bound0 M hM, usc0 M hM⟩
  | t+1, ht =>
    have ih := good_all M hM t (by omega)
    ⟨bound_succ M hM t ht ih.1 ih.2, usc_succ M hM t ht ih.1 ih.2⟩

lemma period_props (M : Model n) (hM : PerOK M) (c : ℝ) :
    UpperSemicontinuousOn (fun z => c * z + M.g M.k z 0) (Set.Ici 0) ∧
    ∀ Z : ℝ, ∃ R, ∀ z, 0 ≤ z → z ≤ Z → |c * z + M.g M.k z 0| ≤ R := by
  obtain ⟨hB, hU⟩ := good_all M hM M.k le_rfl
  refine ⟨fun z hz => ?_, fun Z => ?_⟩
  · exact (continuous_const.mul continuous_id).continuousWithinAt.upperSemicontinuousWithinAt.add
      (usc_comp hU (φ := fun z : ℝ => (z, (0 : Fin n → ℝ))) hz
        (by fun_prop : Continuous fun z : ℝ => (z, (0 : Fin n → ℝ))).continuousWithinAt
        (fun z hz => ⟨hz, le_rfl⟩))
  · obtain ⟨A, hA, hg⟩ := hB Z
    refine ⟨|c| * |Z| + A, fun z hz hzZ => ?_⟩
    have h1 := hg z 0 hz hzZ le_rfl
    simp only [Pi.zero_apply, Finset.sum_const_zero, add_zero, mul_one] at h1
    have h2 : |c * z| ≤ |c| * |Z| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg hz]; exact hzZ.trans (le_abs_self Z)) (abs_nonneg c)
    exact (abs_add_le _ _).trans (by linarith)

def GoodC (f : ℝ → ℝ) : Prop := UpperSemicontinuous f ∧ ∀ Z : ℝ, ∃ A, ∀ y ≤ Z, |f y| ≤ A

lemma C_good (G : ℝ → ℝ) (hG : UpperSemicontinuousOn G (Set.Ici 0))
    (hGb : ∀ Z : ℝ, ∃ R, ∀ z, 0 ≤ z → z ≤ Z → |G z| ≤ R) :
    GoodC (fun w => sInf (G '' Set.Ici (max w 0))) := by
  have hne : ∀ w : ℝ, (G '' Set.Ici (max w 0)).Nonempty := fun w =>
    ⟨_, Set.mem_image_of_mem G (Set.mem_Ici.2 le_rfl)⟩
  by_cases hbdd : BddBelow (G '' Set.Ici 0)
  · obtain ⟨L, hL⟩ := hbdd
    have hbd : ∀ w : ℝ, BddBelow (G '' Set.Ici (max w 0)) := fun w =>
      ⟨L, by
        rintro _ ⟨z, hz, rfl⟩
        exact hL ⟨z, Set.mem_Ici.2 (le_trans (le_max_right _ _) (Set.mem_Ici.1 hz)), rfl⟩⟩
    refine ⟨fun w0 y hy => ?_, fun Z => ?_⟩
    · obtain ⟨_, ⟨z0, hz0, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne w0) hy
      let ζ : ℝ → ℝ := fun w => max (max w 0) z0
      have hζc : Continuous ζ := by fun_prop
      have hζ0 : ζ w0 = z0 := max_eq_right hz0
      have h := usc_comp hG (φ := ζ) (T := Set.univ) (Set.mem_univ w0) hζc.continuousWithinAt
        (fun w _ => Set.mem_Ici.2 (le_trans (le_max_right w 0) (le_max_left _ _))) y (by simpa [hζ0] using hlt)
      rw [nhdsWithin_univ] at h
      filter_upwards [h] with w hw
      exact lt_of_le_of_lt (csInf_le (hbd w) (Set.mem_image_of_mem G (Set.mem_Ici.2 (le_max_left (max w 0) z0)))) hw
    · obtain ⟨R, hR⟩ := hGb (max Z 0)
      refine ⟨|L| + |R|, fun y hy => abs_le.2 ⟨?_, ?_⟩⟩
      · have : L ≤ sInf (G '' Set.Ici (max y 0)) := le_csInf (hne y) (by
          rintro _ ⟨z, hz, rfl⟩
          exact hL ⟨z, Set.mem_Ici.2 (le_trans (le_max_right _ _) (Set.mem_Ici.1 hz)), rfl⟩)
        linarith [neg_abs_le L, abs_nonneg R]
      · have h1 := csInf_le (hbd y) (Set.mem_image_of_mem G (Set.mem_Ici.2 (le_refl (max y 0))))
        have h2 := hR (max y 0) (le_max_right _ _) (max_le_max hy le_rfl)
        linarith [(abs_le.1 h2).2, le_abs_self R, abs_nonneg L]
  · have h0 : (fun w => sInf (G '' Set.Ici (max w 0))) = fun _ => 0 := by
      funext w
      apply Real.sInf_of_not_bddBelow
      rintro ⟨L, hL⟩
      apply hbdd
      obtain ⟨R, hR⟩ := hGb (max w 0)
      refine ⟨min L (-R), ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      rcases le_or_gt z (max w 0) with h | h
      · exact (min_le_right _ _).trans (abs_le.1 (hR z hz h)).1
      · exact (min_le_left _ _).trans (hL ⟨z, h.le, rfl⟩)
    rw [h0]
    exact ⟨continuous_const.upperSemicontinuous, fun Z => ⟨0, fun y _ => by simp⟩⟩

lemma salv_ok {f : ℝ → ℝ} (hf : GoodC f) (c : ℝ) :
    UpperSemicontinuous (fun y => -c * y + f y) ∧
    ∀ Z : ℝ, ∃ A, 0 ≤ A ∧ ∀ y ≤ Z, |-c * y + f y| ≤ A * (1 + |y|) := by
  refine ⟨(continuous_const.mul continuous_id).upperSemicontinuous.add hf.1, fun Z => ?_⟩
  obtain ⟨A, hA⟩ := hf.2 Z
  refine ⟨|c| + |A|, by positivity, fun y hy => ?_⟩
  have h1 := hA y hy
  have h2 : |-c * y| = |c| * |y| := by rw [abs_mul, abs_neg]
  have := abs_add_le (-c * y) (f y)
  nlinarith [abs_nonneg c, abs_nonneg y, le_abs_self A, abs_nonneg A, mul_nonneg (abs_nonneg A) (abs_nonneg y)]

lemma perOK_of (Q : MultiModel n) (hQ : Q.Standing) (m : ℕ) (hm : m ∈ Finset.Icc 1 Q.N)
    (v : ℝ → ℝ) (hvu : UpperSemicontinuous v)
    (hvb : ∀ Z : ℝ, ∃ A, 0 ≤ A ∧ ∀ y ≤ Z, |v y| ≤ A * (1 + |y|)) :
    PerOK ((Q.P m).withSalvage (fun _ => 0) v) := by
  have hS := hQ.period m hm
  exact
    { a0 := hS.a_nonneg
      a1 := fun t ht => by
        show (Q.P m).a t ≤ 1
        rcases hQ.a01 m hm t ht with h | h <;> rw [h] <;> norm_num
      hc := hS.h_cont
      prob := hS.μ_prob
      nonneg := hS.μ_nonneg
      mean := hS.μ_mean
      v1 := fun _ => rfl
      v2u := hvu
      v2b := hvb }

lemma crev_good (Q : MultiModel n) (hQ : Q.Standing) : ∀ r, r ≤ Q.N → GoodC (Q.Crev r)
  | 0, _ => by
    show GoodC (fun w => (Q.c (Q.N + 1) - Q.v) * max w 0)
    refine ⟨(continuous_const.mul (continuous_id.max continuous_const)).upperSemicontinuous,
      fun Z => ⟨|Q.c (Q.N + 1) - Q.v| * |Z|, fun y hy => ?_⟩⟩
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (hy.trans (le_abs_self Z)) (abs_nonneg Z)
  | r+1, hr => by
    have ih := crev_good Q hQ r (by omega)
    have hm : Q.N - r ∈ Finset.Icc 1 Q.N := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    obtain ⟨hvu, hvb⟩ := salv_ok ih (Q.c (Q.N - r + 1))
    have hP := perOK_of Q hQ (Q.N - r) hm _ hvu hvb
    obtain ⟨hG1, hG2⟩ := period_props _ hP (Q.c (Q.N - r))
    exact C_good _ hG1 hG2

lemma C_eq (Q : MultiModel n) (m : ℕ) (hm : m ≤ Q.N) (w : ℝ) :
    Q.C m w = sInf ((fun z => Q.gtilde m z) '' Set.Ici (max w 0)) := by
  have h1 : Q.N + 1 - m = (Q.N - m) + 1 := by omega
  have h2 : Q.N - (Q.N - m) = m := by omega
  have h3 : Q.N + 1 - (m + 1) = Q.N - m := by omega
  unfold MultiModel.gtilde MultiModel.C
  rw [h1, h3]
  simp only [MultiModel.Crev]
  rw [h2]

lemma C_flat (Q : MultiModel n) (m : ℕ) (hm : m ≤ Q.N) (x : ℝ) (hx : 0 ≤ x)
    (hmin : ∀ z, 0 ≤ z → Q.gtilde m x ≤ Q.gtilde m z) :
    (∀ w, w ≤ x → Q.C m w = Q.gtilde m x) ∧ ∀ w, Q.gtilde m x ≤ Q.C m w := by
  have hlow : ∀ w, ∀ v ∈ (fun z => Q.gtilde m z) '' Set.Ici (max w 0), Q.gtilde m x ≤ v := by
    rintro w _ ⟨z, hz, rfl⟩
    exact hmin z (le_trans (le_max_right _ _) hz)
  have hne : ∀ w : ℝ, ((fun z => Q.gtilde m z) '' Set.Ici (max w 0)).Nonempty := fun w =>
    ⟨_, Set.mem_image_of_mem _ (Set.mem_Ici.2 le_rfl)⟩
  refine ⟨fun w hw => ?_, fun w => ?_⟩
  · rw [C_eq Q m hm]
    exact le_antisymm (csInf_le ⟨_, hlow w⟩ ⟨x, max_le hw hx, rfl⟩) (le_csInf (hne w) (hlow w))
  · rw [C_eq Q m hm]
    exact le_csInf (hne w) (hlow w)

lemma cmp_eq (P0 : Model n) (va vb : ℝ → ℝ) (hM2 : PerOK (P0.withSalvage (fun _ => 0) vb))
    (K X : ℝ) (hv : ∀ y ≤ X, va y = vb y + K) :
    ∀ t, t ≤ P0.k → ∀ z b, 0 ≤ z → z ≤ X → 0 ≤ b →
      (P0.withSalvage (fun _ => 0) va).g t z b = (P0.withSalvage (fun _ => 0) vb).g t z b + K
  | 0, _, z, b, hz, hzX, hb => by
      show 0 + va (z - ∑ j, b j) = (0 + vb (z - ∑ j, b j)) + K
      rw [hv _ (by linarith [sum_nonneg' hb])]; ring
  | t+1, ht, z, b, hz, hzX, hb => by
      have ih := cmp_eq P0 va vb hM2 K X hv t (by omega)
      have ht2 : t + 1 ≤ (P0.withSalvage (fun _ => 0) vb).k := ht
      have ht' : t + 1 ∈ Finset.Icc 1 (P0.withSalvage (fun _ => 0) vb).k :=
        Finset.mem_Icc.2 ⟨by omega, ht⟩
      obtain ⟨hB, hU⟩ := good_all _ hM2 t (by omega)
      have : IsProbabilityMeasure (P0.μ (t+1)) := hM2.prob _ ht'
      have hpt : ∀ ξ : Fin n → ℝ, 0 ≤ ξ →
          (P0.withSalvage (fun _ => 0) va).stage (t+1) ((P0.withSalvage (fun _ => 0) va).g t) z (b+ξ)
          = (P0.withSalvage (fun _ => 0) vb).stage (t+1) ((P0.withSalvage (fun _ => 0) vb).g t) z (b+ξ)
            + K := by
        intro ξ hξ
        have hB0 : 0 ≤ b + ξ := add_nonneg hb hξ
        obtain ⟨R, hR, hst⟩ := stage_bound _ hM2 t ht2 hB z
        obtain ⟨hbdd2, -⟩ := hst z (b+ξ) hz le_rfl hB0
        have hobj : ∀ u ∈ TopkisRation.Levels.feasible z (b+ξ),
            (P0.withSalvage (fun _ => 0) va).obj (t+1) ((P0.withSalvage (fun _ => 0) va).g t) z (b+ξ) u
            = (P0.withSalvage (fun _ => 0) vb).obj (t+1) ((P0.withSalvage (fun _ => 0) vb).g t) z
              (b+ξ) u + K := by
          intro u hu
          obtain ⟨hu0, huB, hs⟩ := hu
          have hs0 : 0 ≤ ∑ j, ((b + ξ) j - u j) := Finset.sum_nonneg (fun j _ => by
            have := huB j; linarith)
          have hau : 0 ≤ P0.a (t+1) • u := fun j => by
            simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            exact mul_nonneg (hM2.a0 _ ht') (hu0 j)
          show P0.p (t+1) ⬝ᵥ u + P0.h (t+1) (z - ∑ j, ((b + ξ) j - u j)) +
              (P0.withSalvage (fun _ => 0) va).g t (z - ∑ j, ((b + ξ) j - u j)) (P0.a (t+1) • u) =
            P0.p (t+1) ⬝ᵥ u + P0.h (t+1) (z - ∑ j, ((b + ξ) j - u j)) +
              (P0.withSalvage (fun _ => 0) vb).g t (z - ∑ j, ((b + ξ) j - u j)) (P0.a (t+1) • u) + K
          rw [ih _ _ (by linarith) (by linarith) hau]; ring
        have hne1 : ((P0.withSalvage (fun _ => 0) va).obj (t+1) ((P0.withSalvage (fun _ => 0) va).g t)
            z (b+ξ) '' TopkisRation.Levels.feasible z (b+ξ)).Nonempty :=
          ⟨_, Set.mem_image_of_mem _ (feas_mem hz hB0)⟩
        have hne2 : ((P0.withSalvage (fun _ => 0) vb).obj (t+1) ((P0.withSalvage (fun _ => 0) vb).g t)
            z (b+ξ) '' TopkisRation.Levels.feasible z (b+ξ)).Nonempty :=
          ⟨_, Set.mem_image_of_mem _ (feas_mem hz hB0)⟩
        have hbdd1 : BddBelow ((P0.withSalvage (fun _ => 0) va).obj (t+1)
            ((P0.withSalvage (fun _ => 0) va).g t) z (b+ξ) '' TopkisRation.Levels.feasible z (b+ξ)) :=
          ⟨sInf ((P0.withSalvage (fun _ => 0) vb).obj (t+1) ((P0.withSalvage (fun _ => 0) vb).g t)
            z (b+ξ) '' TopkisRation.Levels.feasible z (b+ξ)) + K, by
            rintro _ ⟨u, hu, rfl⟩
            rw [hobj u hu]
            linarith [csInf_le hbdd2 ⟨u, hu, rfl⟩]⟩
        unfold Model.stage
        apply le_antisymm
        · have : sInf ((P0.withSalvage (fun _ => 0) va).obj (t+1)
              ((P0.withSalvage (fun _ => 0) va).g t) z (b+ξ) '' TopkisRation.Levels.feasible z (b+ξ))
              - K ≤ sInf ((P0.withSalvage (fun _ => 0) vb).obj (t+1)
              ((P0.withSalvage (fun _ => 0) vb).g t) z (b+ξ) '' TopkisRation.Levels.feasible z (b+ξ)) := by
            refine le_csInf hne2 ?_
            rintro _ ⟨u, hu, rfl⟩
            have := csInf_le hbdd1 ⟨u, hu, rfl⟩
            rw [hobj u hu] at this
            linarith
          linarith
        · refine le_csInf hne1 ?_
          rintro _ ⟨u, hu, rfl⟩
          rw [hobj u hu]
          linarith [csInf_le hbdd2 ⟨u, hu, rfl⟩]
      show ∫ ξ, (P0.withSalvage (fun _ => 0) va).stage (t+1) ((P0.withSalvage (fun _ => 0) va).g t) z
          (b + ξ) ∂(P0.μ (t+1)) =
        ∫ ξ, (P0.withSalvage (fun _ => 0) vb).stage (t+1) ((P0.withSalvage (fun _ => 0) vb).g t) z
          (b + ξ) ∂(P0.μ (t+1)) + K
      have hae : ∀ᵐ ξ ∂(P0.μ (t+1)), 0 ≤ ξ := hM2.nonneg _ ht'
      rw [integral_congr_ae (by filter_upwards [hae] with ξ hξ; exact hpt ξ hξ)]
      have hi : Integrable (fun ξ => (P0.withSalvage (fun _ => 0) vb).stage (t+1)
          ((P0.withSalvage (fun _ => 0) vb).g t) z (b + ξ)) (P0.μ (t+1)) :=
        stage_int _ hM2 t ht2 hB hU z b hz hb
      rw [integral_add hi (integrable_const K), integral_const]
      simp


/-! ### Supporting lines of convex holding costs -/

lemma support_line (h : ℝ → ℝ) (hc : ConvexOn ℝ (Set.Ici 0) h) (W : ℝ) (hW : 0 < W) :
    ∃ s : ℝ, Tendsto (fun ε => (h (W + ε) - h W) / ε) (𝓝[>] 0) (𝓝 s) ∧
      ∀ w, 0 ≤ w → h W + s * (w - W) ≤ h w := by
  set q : ℝ → ℝ := fun ε => (h (W + ε) - h W) / ε with hq
  have hsec : ∀ x y, 0 ≤ x → 0 ≤ y → x ≠ W → y ≠ W → x ≤ y →
      (h x - h W) / (x - W) ≤ (h y - h W) / (y - W) := fun x y hx hy hxW hyW hxy =>
    hc.secant_mono (Set.mem_Ici.2 hW.le) (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hy) hxW hyW hxy
  have hqe : ∀ ε, q ε = (h (W + ε) - h W) / ((W + ε) - W) := by
    intro ε; simp only [hq, add_sub_cancel_left]
  have hmono : MonotoneOn q (Set.Ioi 0) := by
    intro a ha b hb hab
    rw [hqe, hqe]
    exact hsec _ _ (by linarith [Set.mem_Ioi.1 ha]) (by linarith [Set.mem_Ioi.1 hb])
      (by linarith [Set.mem_Ioi.1 ha]) (by linarith [Set.mem_Ioi.1 hb]) (by linarith)
  have hlow : ∀ ε, 0 < ε → (h 0 - h W) / (0 - W) ≤ q ε := by
    intro ε hε
    rw [hqe]
    exact hsec _ _ le_rfl (by linarith) (by linarith) (by linarith) (by linarith)
  have hbdd : BddBelow (q '' Set.Ioi 0) :=
    ⟨(h 0 - h W) / (0 - W), by rintro _ ⟨ε, hε, rfl⟩; exact hlow ε hε⟩
  refine ⟨sInf (q '' Set.Ioi 0), hmono.tendsto_nhdsGT hbdd, fun w hw => ?_⟩
  rcases lt_trichotomy w W with hwW | hwW | hwW
  · -- left of W: the left secant slope is below every right difference quotient
    have hle : (h w - h W) / (w - W) ≤ sInf (q '' Set.Ioi 0) := by
      refine le_csInf ⟨q 1, 1, Set.mem_Ioi.2 one_pos, rfl⟩ ?_
      rintro _ ⟨ε, hε, rfl⟩
      rw [hqe]
      exact hsec _ _ hw (by linarith [Set.mem_Ioi.1 hε]) hwW.ne
        (by linarith [Set.mem_Ioi.1 hε]) (by linarith [Set.mem_Ioi.1 hε])
    have hneg : w - W < 0 := by linarith
    rw [div_le_iff_of_neg hneg] at hle
    linarith
  · subst hwW; simp
  · have hle : sInf (q '' Set.Ioi 0) ≤ q (w - W) :=
      csInf_le hbdd ⟨w - W, Set.mem_Ioi.2 (by linarith), rfl⟩
    have hpos : 0 < w - W := by linarith
    have : q (w - W) * (w - W) = h w - h W := by
      simp only [hq, add_sub_cancel]
      field_simp
    nlinarith

/-! ### Linear lower bounds through the interval recursion (1) -/

lemma lb_interval (M : Model n) (hM : PerOK M) (hp : ∀ t ∈ Finset.Icc 1 M.k, ∀ j, 0 ≤ M.p t j)
    (s : ℕ → ℝ) (W : ℝ)
    (hs : ∀ t ∈ Finset.Icc 1 M.k, ∀ w, 0 ≤ w → M.h t W + s t * (w - W) ≤ M.h t w)
    (α0 β0 : ℝ) (hv : ∀ y, α0 + β0 * y ≤ M.v₂ y) :
    ∀ t, t ≤ M.k → ∃ α γ : ℝ, 0 ≤ γ ∧ ∀ z b, 0 ≤ z → 0 ≤ b →
      α + (β0 + ∑ τ ∈ Finset.Icc 1 t, s τ) * z - γ * ∑ j, b j ≤ M.g t z b
  | 0, _ => by
    refine ⟨α0, |β0|, abs_nonneg _, fun z b hz hb => ?_⟩
    show _ ≤ M.v₁ z + M.v₂ (z - ∑ j, b j)
    rw [hM.v1, zero_add]
    have h1 := hv (z - ∑ j, b j)
    have hs0 := sum_nonneg' hb
    simp only [Finset.Icc_eq_empty_of_lt (show (1:ℕ) > 0 by omega), Finset.sum_empty, add_zero]
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self β0) hs0]
  | t+1, ht => by
    obtain ⟨α, γ, hγ, ih⟩ := lb_interval M hM hp s W hs α0 β0 hv t (by omega)
    have ht' : t + 1 ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨by omega, ht⟩
    have := hM.prob _ ht'
    set β := β0 + ∑ τ ∈ Finset.Icc 1 t, s τ with hβ
    set κ := s (t+1) + β with hκ
    have hβ' : β0 + ∑ τ ∈ Finset.Icc 1 (t+1), s τ = κ := by
      rw [Finset.sum_Icc_succ_top (by omega)]; rw [hκ, hβ]; ring
    rw [hβ']
    set A := α + M.h (t+1) W - s (t+1) * W with hA
    set γ' := γ + |κ| with hγ'
    have ha0 := hM.a0 _ ht'
    have ha1 := hM.a1 _ ht'
    -- pointwise bound on the stage function
    have hstage : ∀ B : Fin n → ℝ, 0 ≤ B → ∀ z, 0 ≤ z →
        A + κ * z - γ' * ∑ j, B j ≤ M.stage (t+1) (M.g t) z B := by
      intro B hB z hz
      unfold Model.stage
      refine le_csInf ⟨_, Set.mem_image_of_mem _ (feas_mem hz hB)⟩ ?_
      rintro _ ⟨u, ⟨hu0, huB, hsum⟩, rfl⟩
      set w := z - ∑ j, (B j - u j) with hw
      have hs0 : 0 ≤ ∑ j, (B j - u j) := Finset.sum_nonneg (fun j _ => by
        have := huB j; linarith)
      have hw0 : 0 ≤ w := by rw [hw]; linarith
      have hwz : w ≤ z := by rw [hw]; linarith
      have hSu : ∑ j, (B j - u j) ≤ ∑ j, B j := by
        have : 0 ≤ ∑ j, u j := sum_nonneg' hu0
        rw [Finset.sum_sub_distrib]; linarith
      have hzw : z - ∑ j, B j ≤ w := by linarith
      have hpu : 0 ≤ M.p (t+1) ⬝ᵥ u :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (hp _ ht' j) (hu0 j))
      have hau : 0 ≤ M.a (t+1) • u := fun j => by
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact mul_nonneg ha0 (hu0 j)
      have hsau : ∑ j, (M.a (t+1) • u) j ≤ ∑ j, B j := by
        have h1 : ∑ j, (M.a (t+1) • u) j = M.a (t+1) * ∑ j, u j := by
          simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        have h2 : ∑ j, u j ≤ ∑ j, B j := Finset.sum_le_sum (fun j _ => huB j)
        have h3 : 0 ≤ ∑ j, u j := sum_nonneg' hu0
        rw [h1]; nlinarith
      have hg := ih w (M.a (t+1) • u) hw0 hau
      have hh := hs (t+1) ht' w hw0
      have hk : κ * z - |κ| * ∑ j, B j ≤ κ * w := by
        have : |κ * (w - z)| ≤ |κ| * ∑ j, B j := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _)
        linarith [neg_abs_le (κ * (w - z))]
      show A + κ * z - γ' * ∑ j, B j ≤ M.p (t+1) ⬝ᵥ u + M.h (t+1) w + M.g t w (M.a (t+1) • u)
      rw [hA, hγ']
      have : γ * ∑ j, (M.a (t+1) • u) j ≤ γ * ∑ j, B j := mul_le_mul_of_nonneg_left hsau hγ
      nlinarith
    obtain ⟨hB, hU⟩ := good_all M hM t (by omega)
    have hmean : Integrable (fun ξ : Fin n → ℝ => ∑ j, ξ j) (M.μ (t+1)) :=
      integrable_finsetSum _ fun j _ => hM.mean _ ht' j
    refine ⟨A - γ' * ∫ ξ, ∑ j, ξ j ∂(M.μ (t+1)), γ', by positivity, fun z b hz hb => ?_⟩
    show _ ≤ ∫ ξ, M.stage (t+1) (M.g t) z (b + ξ) ∂(M.μ (t+1))
    have hi := stage_int M hM t ht hB hU z b hz hb
    have hlow : Integrable (fun ξ : Fin n → ℝ => (A + κ * z - γ' * ∑ j, b j) - γ' * ∑ j, ξ j)
        (M.μ (t+1)) := (integrable_const _).sub (hmean.const_mul γ')
    have hmono := integral_mono_ae hlow hi (by
      filter_upwards [hM.nonneg _ ht'] with ξ hξ
      have := hstage (b + ξ) (add_nonneg hb hξ) z hz
      simp only [Pi.add_apply, Finset.sum_add_distrib] at this
      linarith)
    rw [integral_sub (integrable_const _) (hmean.const_mul γ'), integral_const,
      integral_const_mul] at hmono
    simp only [probReal_univ, one_smul] at hmono
    linarith

/-! ### Assumption (D′) bounds the total slope from below -/

lemma kappa_ge (Q : MultiModel n) (i : ℕ) (W η : ℝ) (s : ℕ → ℕ → ℝ)
    (hs : ∀ j ∈ Finset.Icc i Q.N, ∀ t ∈ Finset.Icc 1 (Q.P j).k,
      Tendsto (fun ε => ((Q.P j).h t (W + ε) - (Q.P j).h t W) / ε) (𝓝[>] 0) (𝓝 (s j t)))
    (hD : (η : EReal) ≤ TopkisRation.Levels.rightDeriv (fun w => Q.c i * w +
      (∑ j ∈ Finset.Icc i Q.N, ∑ t ∈ Finset.Icc 1 (Q.P j).k, (Q.P j).h t w) - Q.v * w) W) :
    η ≤ Q.c i - Q.v + ∑ j ∈ Finset.Icc i Q.N, ∑ t ∈ Finset.Icc 1 (Q.P j).k, s j t := by
  set F : ℝ → ℝ := fun w => Q.c i * w +
      (∑ j ∈ Finset.Icc i Q.N, ∑ t ∈ Finset.Icc 1 (Q.P j).k, (Q.P j).h t w) - Q.v * w with hF
  have hlim : Tendsto (fun ε => (F (W + ε) - F W) / ε) (𝓝[>] 0)
      (𝓝 (Q.c i - Q.v + ∑ j ∈ Finset.Icc i Q.N, ∑ t ∈ Finset.Icc 1 (Q.P j).k, s j t)) := by
    have h1 : Tendsto (fun ε => Q.c i - Q.v + ∑ j ∈ Finset.Icc i Q.N,
        ∑ t ∈ Finset.Icc 1 (Q.P j).k, ((Q.P j).h t (W + ε) - (Q.P j).h t W) / ε) (𝓝[>] 0)
        (𝓝 (Q.c i - Q.v + ∑ j ∈ Finset.Icc i Q.N, ∑ t ∈ Finset.Icc 1 (Q.P j).k, s j t)) :=
      tendsto_const_nhds.add (tendsto_finset_sum _ fun j hj =>
        tendsto_finset_sum _ fun t ht => hs j hj t ht)
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := ne_of_gt (Set.mem_Ioi.1 hε)
    have hnum : F (W + ε) - F W = (Q.c i - Q.v) * ε + ∑ j ∈ Finset.Icc i Q.N,
        ∑ t ∈ Finset.Icc 1 (Q.P j).k, ((Q.P j).h t (W + ε) - (Q.P j).h t W) := by
      simp only [hF, Finset.sum_sub_distrib]; ring
    rw [hnum, add_div, mul_div_assoc, div_self hε0, mul_one, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_div]
  have hE : Tendsto (fun ε => (((F (W + ε) - F W) / ε : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 ((Q.c i - Q.v + ∑ j ∈ Finset.Icc i Q.N, ∑ t ∈ Finset.Icc 1 (Q.P j).k, s j t : ℝ) :
        EReal)) := EReal.tendsto_coe.2 hlim
  have hrd : TopkisRation.Levels.rightDeriv F W =
      ((Q.c i - Q.v + ∑ j ∈ Finset.Icc i Q.N, ∑ t ∈ Finset.Icc 1 (Q.P j).k, s j t : ℝ) :
        EReal) := hE.liminf_eq
  rw [hrd] at hD
  exact EReal.coe_le_coe_iff.1 hD

/-! ### Linear lower bounds for `g̃ᵐ` and `Cₘ` -/

/-- Total slope `cᵢ − v + Σ_{j ≥ i} Σₜ s j t` of the costs from period `i` on. -/
noncomputable def kap (Q : MultiModel n) (s : ℕ → ℕ → ℝ) (i : ℕ) : ℝ :=
  Q.c i - Q.v + ∑ j ∈ Finset.Icc i Q.N, ∑ t ∈ Finset.Icc 1 (Q.P j).k, s j t

lemma kap_succ (Q : MultiModel n) (s : ℕ → ℕ → ℝ) (i : ℕ) (hi : i ≤ Q.N) :
    kap Q s i = Q.c i - Q.c (i + 1) + kap Q s (i + 1) +
      ∑ t ∈ Finset.Icc 1 (Q.P i).k, s i t := by
  unfold kap
  rw [Finset.Icc_eq_cons_Ioc hi, Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
  ring

lemma gtilde_lb (Q : MultiModel n) (hQ : Q.Standing) (i : ℕ) (hi : i ∈ Finset.Icc 1 Q.N)
    (W : ℝ) (s : ℕ → ℕ → ℝ)
    (hsupp : ∀ t ∈ Finset.Icc 1 (Q.P i).k, ∀ w, 0 ≤ w →
      (Q.P i).h t W + s i t * (w - W) ≤ (Q.P i).h t w)
    (α0 β0 : ℝ) (hC : ∀ y, α0 + β0 * y ≤ Q.C (i + 1) y) :
    ∃ α, ∀ z, 0 ≤ z → α + (Q.c i - Q.c (i + 1) + β0 +
      ∑ t ∈ Finset.Icc 1 (Q.P i).k, s i t) * z ≤ Q.gtilde i z := by
  have hi' := Finset.mem_Icc.1 hi
  have hgood : GoodC (Q.C (i + 1)) := crev_good Q hQ (Q.N + 1 - (i + 1)) (by omega)
  obtain ⟨hvu, hvb⟩ := salv_ok hgood (Q.c (i + 1))
  have hP := perOK_of Q hQ i hi _ hvu hvb
  have hp := (hQ.period i hi).p_nonneg
  obtain ⟨α, γ, -, hlb⟩ := lb_interval _ hP hp (s i) W hsupp α0 (β0 - Q.c (i + 1))
    (fun y => by show _ ≤ -Q.c (i + 1) * y + Q.C (i + 1) y; linarith [hC y])
    (Q.P i).k le_rfl
  refine ⟨α, fun z hz => ?_⟩
  have := hlb z 0 hz le_rfl
  simp only [Pi.zero_apply, Finset.sum_const_zero, mul_zero, sub_zero] at this
  show _ ≤ Q.c i * z + _
  nlinarith

lemma C_lb (Q : MultiModel n) (hQ : Q.Standing) (W : ℝ) (s : ℕ → ℕ → ℝ)
    (hsupp : ∀ j ∈ Finset.Icc 1 Q.N, ∀ t ∈ Finset.Icc 1 (Q.P j).k, ∀ w, 0 ≤ w →
      (Q.P j).h t W + s j t * (w - W) ≤ (Q.P j).h t w)
    (hκ : ∀ i ∈ Finset.Icc 1 Q.N, 0 ≤ kap Q s i) :
    ∀ r, r ≤ Q.N → ∃ α, ∀ y, α + kap Q s (Q.N + 1 - r) * y ≤ Q.C (Q.N + 1 - r) y
  | 0, _ => by
    refine ⟨0, fun y => ?_⟩
    have hk : kap Q s (Q.N + 1) = Q.c (Q.N + 1) - Q.v := by
      unfold kap; rw [Finset.Icc_eq_empty (by omega)]; simp
    simp only [Nat.sub_zero, hk, zero_add]
    show _ ≤ Q.Crev (Q.N + 1 - (Q.N + 1)) y
    simp only [Nat.sub_self, MultiModel.Crev]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.2 hQ.v_le)
  | r+1, hr => by
    obtain ⟨α0, ih⟩ := C_lb Q hQ W s hsupp hκ r (by omega)
    have hi : Q.N - r ∈ Finset.Icc 1 Q.N := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have e1 : Q.N + 1 - (r + 1) = Q.N - r := by omega
    have e2 : Q.N + 1 - r = Q.N - r + 1 := by omega
    rw [e1]
    rw [e2] at ih
    obtain ⟨α, hα⟩ := gtilde_lb Q hQ (Q.N - r) hi W s (hsupp _ hi) α0 _ ih
    rw [← kap_succ Q s _ (by omega)] at hα
    have hk := hκ _ hi
    refine ⟨α, fun y => ?_⟩
    rw [C_eq Q _ (by omega)]
    refine le_csInf ⟨_, Set.mem_image_of_mem _ (Set.mem_Ici.2 le_rfl)⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    have hz' := Set.mem_Ici.1 hz
    have h1 := hα z ((le_max_right _ _).trans hz')
    have h2 : kap Q s (Q.N - r) * y ≤ kap Q s (Q.N - r) * z :=
      mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hz') hk
    linarith

end TopkisRation.Myopic.T4aux

open TopkisRation.Myopic TopkisRation.Myopic.T4aux Filter Topology

theorem solution {n : ℕ} (Q : MultiModel n) (hQ : Q.Standing)
    (m : ℕ) (hm : m ∈ Finset.Icc 1 Q.N) :
    (∃ x : ℝ, 0 ≤ x ∧ ∀ z, 0 ≤ z → Q.gtilde m x ≤ Q.gtilde m z) ∧
    ∀ x : ℝ, 0 ≤ x → (∀ z, 0 ≤ z → Q.gtilde m x ≤ Q.gtilde m z) →
      ∀ w z : ℝ, max w 0 ≤ z → Q.gtilde m (max w x) ≤ Q.gtilde m z := by
  have hm' := Finset.mem_Icc.1 hm
  obtain ⟨hconv, hcont⟩ := (C_convex_continuous Q hQ).2 m hm
  refine ⟨?_, ?_⟩
  · -- existence of a minimizer, from (D′)
    have hD : ∀ i, ∃ η : ℝ, i ∈ Finset.Icc 1 Q.N → 0 < η ∧ ∀ᶠ w in atTop, (η : EReal) ≤
        TopkisRation.Levels.rightDeriv (fun w => Q.c i * w +
          (∑ j ∈ Finset.Icc i Q.N, ∑ t ∈ Finset.Icc 1 (Q.P j).k, (Q.P j).h t w) -
          Q.v * w) w := by
      intro i
      by_cases hi : i ∈ Finset.Icc 1 Q.N
      · obtain ⟨η, hη, h⟩ := hQ.D' i hi
        exact ⟨η, fun _ => ⟨hη, h⟩⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose η hη using hD
    have hev : ∀ᶠ w in atTop, 1 ≤ w ∧ ∀ i ∈ Finset.Icc 1 Q.N, (η i : EReal) ≤
        TopkisRation.Levels.rightDeriv (fun w => Q.c i * w +
          (∑ j ∈ Finset.Icc i Q.N, ∑ t ∈ Finset.Icc 1 (Q.P j).k, (Q.P j).h t w) -
          Q.v * w) w :=
      (eventually_ge_atTop 1).and ((Filter.eventually_all_finset _).2 fun i hi => (hη i hi).2)
    obtain ⟨W, hW1, hWD⟩ := hev.exists
    have hsx : ∀ j t, ∃ s : ℝ, j ∈ Finset.Icc 1 Q.N → t ∈ Finset.Icc 1 (Q.P j).k →
        Tendsto (fun ε => ((Q.P j).h t (W + ε) - (Q.P j).h t W) / ε) (𝓝[>] 0) (𝓝 s) ∧
        ∀ w, 0 ≤ w → (Q.P j).h t W + s * (w - W) ≤ (Q.P j).h t w := by
      intro j t
      by_cases hj : j ∈ Finset.Icc 1 Q.N
      · by_cases ht : t ∈ Finset.Icc 1 (Q.P j).k
        · obtain ⟨s, h1, h2⟩ := support_line _ ((hQ.period j hj).h_convex t ht) W (by linarith)
          exact ⟨s, fun _ _ => ⟨h1, h2⟩⟩
        · exact ⟨0, fun _ h => absurd h ht⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose s hs using hsx
    have hκη : ∀ i ∈ Finset.Icc 1 Q.N, η i ≤ kap Q s i := by
      intro i hi
      have hi' := Finset.mem_Icc.1 hi
      exact kappa_ge Q i W (η i) s (fun j hj t ht =>
        (hs j t (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hj).1; omega,
          (Finset.mem_Icc.1 hj).2⟩) ht).1) (hWD i hi)
    have hκ : ∀ i ∈ Finset.Icc 1 Q.N, 0 ≤ kap Q s i := fun i hi =>
      ((hη i hi).1.le).trans (hκη i hi)
    have hsupp : ∀ j ∈ Finset.Icc 1 Q.N, ∀ t ∈ Finset.Icc 1 (Q.P j).k, ∀ w, 0 ≤ w →
        (Q.P j).h t W + s j t * (w - W) ≤ (Q.P j).h t w := fun j hj t ht => (hs j t hj ht).2
    obtain ⟨α0, hC⟩ := C_lb Q hQ W s hsupp hκ (Q.N - m) (by omega)
    have e : Q.N + 1 - (Q.N - m) = m + 1 := by omega
    rw [e] at hC
    obtain ⟨α, hα⟩ := gtilde_lb Q hQ m hm W s (hsupp m hm) α0 _ hC
    rw [← kap_succ Q s m hm'.2] at hα
    set K := kap Q s m with hK
    have hKpos : 0 < K := lt_of_lt_of_le (hη m hm).1 (hκη m hm)
    set g0 := Q.gtilde m 0
    set R := |g0 - α| / K + 1 with hR
    have hR0 : 0 ≤ R := by positivity
    have hKR : K * R = |g0 - α| + K := by
      rw [hR, mul_add, mul_div_cancel₀ _ hKpos.ne', mul_one]
    obtain ⟨x, hxR, hxmin⟩ := (isCompact_Icc (a := (0:ℝ)) (b := R)).exists_isMinOn
      ⟨0, Set.mem_Icc.2 ⟨le_rfl, hR0⟩⟩ (hcont.mono Set.Icc_subset_Ici_self)
    refine ⟨x, hxR.1, fun z hz => ?_⟩
    rcases le_or_gt z R with hzR | hzR
    · exact hxmin (Set.mem_Icc.2 ⟨hz, hzR⟩)
    · have h0 : Q.gtilde m x ≤ g0 := hxmin (Set.mem_Icc.2 ⟨le_rfl, hR0⟩)
      have h1 := hα z hz
      have h2 : K * R ≤ K * z := mul_le_mul_of_nonneg_left hzR.le hKpos.le
      linarith [le_abs_self (g0 - α)]
  · -- ordering up to `w ∨ x` is optimal, by convexity
    intro x hx0 hmin w z hwz
    have hz0 : 0 ≤ z := (le_max_right w 0).trans hwz
    have hwz' : w ≤ z := (le_max_left w 0).trans hwz
    rcases le_or_gt w x with h | h
    · rw [max_eq_right h]
      exact hmin z hz0
    · rw [max_eq_left h.le]
      exact hconv.le_right_of_left_le'' (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 hz0) h hwz'
        (hmin w (hx0.trans h.le))

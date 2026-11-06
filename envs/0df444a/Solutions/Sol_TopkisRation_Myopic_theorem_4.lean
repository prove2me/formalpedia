-- Prove2me | solution 1 for TopkisRation.Myopic.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:32:31.376253+00:00
-- url     : https://prove2.me/submissions/e746274b-ebaa-4988-b0fd-0fe50959b708

import Definitions.Def_TopkisRation_Myopic_MultiPeriod
import Theorems.Thm_TopkisRation_Myopic_ybar_N_finite
import Theorems.Thm_TopkisRation_Myopic_eq_20
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

end TopkisRation.Myopic.T4aux

open TopkisRation.Myopic

theorem solution {n : ℕ} (Q : MultiModel n) (hQ : Q.Standing)
    (hv : Q.v = Q.c (Q.N + 1))
    (ybar : ℕ → WithTop ℝ)
    (hy : ∀ i ∈ Finset.Icc 1 Q.N, IsMyopicLevel (Q.gmyopic i) (ybar i))
    (m : ℕ) (hm : m ∈ Finset.Icc 1 Q.N)
    (hmono : MonotoneOn ybar (Set.Icc m Q.N)) :
    (∃ y : ℝ, ybar m = y ∧
      ∀ w z : ℝ, max w 0 ≤ z → Q.gtilde m (max w y) ≤ Q.gtilde m z) ∧
    (m < Q.N → ∀ y' : ℝ, ybar (m + 1) = y' →
      ∀ t ∈ Finset.Icc 1 (Q.P m).k, ∀ z : ℝ, 0 ≤ z → z ≤ y' →
      ∀ B : Fin n → ℝ, 0 ≤ B → ∀ u ∈ TopkisRation.Levels.feasible z B,
      let Ma := (Q.P m).withSalvage (fun _ => 0)
        (fun y => -Q.c (m + 1) * y + Q.C (m + 1) y)
      let Ml := (Q.P m).withSalvage (fun _ => 0)
        (fun y => -Q.c (m + 1) * y)
      IsMinOn (Ma.obj t (Ma.g (t - 1)) z B) (TopkisRation.Levels.feasible z B) u ↔
        IsMinOn (Ml.obj t (Ml.g (t - 1)) z B) (TopkisRation.Levels.feasible z B) u) := by
  have hm' := Finset.mem_Icc.mp hm
  have hN1 : 1 ≤ Q.N := by omega
  -- Step A: all levels ȳᵢ, m ≤ i ≤ N, are finite.
  have hNtop : ybar Q.N ≠ ⊤ :=
    ybar_N_finite Q hQ hv hN1 (ybar Q.N) (hy Q.N (Finset.mem_Icc.2 ⟨hN1, le_rfl⟩))
  have hreal : ∀ i, m ≤ i → i ≤ Q.N → ∃ x : ℝ, ybar i = x ∧ 0 ≤ x ∧
      ∀ z, 0 ≤ z → Q.gmyopic i x ≤ Q.gmyopic i z := by
    intro i hmi hiN
    have hle : ybar i ≤ ybar Q.N :=
      hmono ⟨hmi, hiN⟩ ⟨by omega, le_rfl⟩ hiN
    have hne : ybar i ≠ ⊤ := ne_top_of_le_ne_top hNtop hle
    rcases hy i (Finset.mem_Icc.2 ⟨by omega, hiN⟩) with ⟨h1, _⟩ | h
    · exact absurd h1 hne
    · exact h
  -- Step B: each ȳᵢ minimizes the actual cost g̃ⁱ on [0, ∞).
  have hCN : ∀ y, Q.C (Q.N + 1) y = 0 := by
    intro y
    simp [MultiModel.C, MultiModel.Crev, hv]
  have hgN : ∀ z, Q.gtilde Q.N z = Q.gmyopic Q.N z := by
    intro z
    unfold MultiModel.gtilde MultiModel.gmyopic
    simp only [hCN, add_zero]
  have hminT : ∀ r, ∀ i, i = Q.N - r → m ≤ i → ∀ x : ℝ, ybar i = x →
      ∀ z, 0 ≤ z → Q.gtilde i x ≤ Q.gtilde i z := by
    intro r
    induction r with
    | zero =>
      intro i hi hmi x hx z hz
      simp only [Nat.sub_zero] at hi
      subst hi
      obtain ⟨x', hx', _, hmin⟩ := hreal Q.N hmi le_rfl
      rw [hx] at hx'
      have : x = x' := WithTop.coe_injective hx'
      subst this
      rw [hgN, hgN]
      exact hmin z hz
    | succ r ih =>
      intro i hi hmi x hx z hz
      have hiN : i < Q.N := by
        have : i ≤ Q.N := by omega
        rcases Nat.lt_or_ge i Q.N with h | h
        · exact h
        · exfalso
          have : r + 1 ≤ Q.N := by
            by_contra hc
            have : Q.N - (r+1) = 0 := by omega
            omega
          omega
      have hi1 : i + 1 = Q.N - r := by omega
      obtain ⟨x1, hx1, hx10, -⟩ := hreal (i + 1) (by omega) (by omega)
      have hmin1 := ih (i + 1) hi1 (by omega) x1 hx1
      obtain ⟨x', hx', hx'0, hminm⟩ := hreal i hmi hiN.le
      rw [hx] at hx'
      have : x = x' := WithTop.coe_injective hx'
      subst this
      have hxle : x ≤ x1 := by
        have h := hmono ⟨hmi, hiN.le⟩ ⟨by omega, by omega⟩ (Nat.le_succ i)
        rw [hx, hx1] at h
        exact WithTop.coe_le_coe.mp h
      obtain ⟨h20a, h20b⟩ := eq_20 Q hQ (i + 1) (by omega) (by omega) x1 hx10 hmin1
      simp only [Nat.add_sub_cancel] at h20a h20b
      rw [h20a x hx'0 hxle]
      rcases le_or_gt z x1 with hz1 | hz1
      · rw [h20a z hz hz1]
        linarith [hminm z hz]
      · linarith [hminm z hz, h20b z hz1.le]
  refine ⟨?_, ?_⟩
  -- Part (a)
  · obtain ⟨y, hyy, hy0, -⟩ := hreal m le_rfl hm'.2
    have hmin := hminT (Q.N - m) m (by omega) le_rfl y hyy
    have hconv := ((C_convex_continuous Q hQ).2 m hm).1
    refine ⟨y, hyy, fun w z hwz => ?_⟩
    have hz0 : 0 ≤ z := (le_max_right w 0).trans hwz
    have hwz' : w ≤ z := (le_max_left w 0).trans hwz
    rcases le_or_gt w y with h | h
    · rw [max_eq_right h]
      exact hmin z hz0
    · rw [max_eq_left h.le]
      exact hconv.le_right_of_left_le'' (Set.mem_Ici.2 hy0) (Set.mem_Ici.2 hz0) h hwz'
        (hmin w (hy0.trans h.le))
  -- Part (b)
  · intro hmN y' hy' t ht z hz hzy B _ u hu
    intro Ma Ml
    obtain ⟨x1, hx1, hx10, -⟩ := hreal (m + 1) (by omega) (by omega)
    rw [hy'] at hx1
    have : y' = x1 := WithTop.coe_injective hx1
    subst this
    have hmin1 := hminT (Q.N - (m + 1)) (m + 1) (by omega) (by omega) y' hy'
    have hm1 : m + 1 ≤ Q.N := by omega
    obtain ⟨hflat, -⟩ := T4aux.C_flat Q (m + 1) hm1 y' hx10 hmin1
    have hP2 : T4aux.PerOK ((Q.P m).withSalvage (fun _ => 0) (fun y => -Q.c (m + 1) * y)) := by
      obtain ⟨hvu, hvb⟩ := T4aux.salv_ok (f := fun _ => 0)
        ⟨continuous_const.upperSemicontinuous, fun Z => ⟨0, fun y _ => by simp⟩⟩ (Q.c (m + 1))
      simp only [add_zero] at hvu hvb
      exact T4aux.perOK_of Q hQ m hm _ hvu hvb
    have hcmp := T4aux.cmp_eq (Q.P m) (fun y => -Q.c (m + 1) * y + Q.C (m + 1) y)
      (fun y => -Q.c (m + 1) * y) hP2 (Q.C (m + 1) y') y'
      (fun y hy => by rw [hflat y hy, hflat y' le_rfl])
    have ht' := Finset.mem_Icc.mp ht
    have ha : 0 ≤ (Q.P m).a t := (hQ.period m hm).a_nonneg t ht
    have hobj : ∀ v ∈ TopkisRation.Levels.feasible z B,
        Ma.obj t (Ma.g (t - 1)) z B v = Ml.obj t (Ml.g (t - 1)) z B v + Q.C (m + 1) y' := by
      intro v hv'
      obtain ⟨hv0, hvB, hs⟩ := hv'
      have hs0 : 0 ≤ ∑ j, (B j - v j) := Finset.sum_nonneg (fun j _ => by
        have := hvB j; linarith)
      have hav : 0 ≤ (Q.P m).a t • v := fun j => by
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact mul_nonneg ha (hv0 j)
      have := hcmp (t - 1) (by omega) (z - ∑ j, (B j - v j)) ((Q.P m).a t • v)
        (by linarith) (by linarith) hav
      show (Q.P m).p t ⬝ᵥ v + (Q.P m).h t (z - ∑ j, (B j - v j)) +
          Ma.g (t - 1) (z - ∑ j, (B j - v j)) ((Q.P m).a t • v) =
        (Q.P m).p t ⬝ᵥ v + (Q.P m).h t (z - ∑ j, (B j - v j)) +
          Ml.g (t - 1) (z - ∑ j, (B j - v j)) ((Q.P m).a t • v) + Q.C (m + 1) y'
      rw [this]; ring
    constructor
    · intro h v hv'
      have := h hv'
      simp only [Set.mem_ofPred_eq, hobj v hv', hobj u hu] at this ⊢
      linarith
    · intro h v hv'
      have := h hv'
      simp only [Set.mem_ofPred_eq] at this ⊢
      rw [hobj v hv', hobj u hu]
      linarith

-- Prove2me | solution 1 for TopkisRation.Myopic.C_convex_continuous
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:25:29.284642+00:00
-- url     : https://prove2.me/submissions/8dd63237-f6f6-4091-839b-ad9da26b5286

import Definitions.Def_TopkisRation_Myopic_MultiPeriod



namespace TopkisRation.Myopic

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

lemma cmp_le (P0 : Model n) (va vb : ℝ → ℝ) (hM1 : PerOK (P0.withSalvage (fun _ => 0) va))
    (hM2 : PerOK (P0.withSalvage (fun _ => 0) vb))
    (K : ℝ) (hv : ∀ y, vb y + K ≤ va y) :
    ∀ t, t ≤ P0.k → ∀ z b, 0 ≤ z → 0 ≤ b →
      (P0.withSalvage (fun _ => 0) vb).g t z b + K ≤ (P0.withSalvage (fun _ => 0) va).g t z b
  | 0, _, z, b, hz, hb => by
      show (0 + vb (z - ∑ j, b j)) + K ≤ 0 + va (z - ∑ j, b j)
      linarith [hv (z - ∑ j, b j)]
  | t+1, ht, z, b, hz, hb => by
      have ih := cmp_le P0 va vb hM1 hM2 K hv t (by omega)
      have ht2 : t + 1 ≤ (P0.withSalvage (fun _ => 0) vb).k := ht
      have ht1 : t + 1 ≤ (P0.withSalvage (fun _ => 0) va).k := ht
      have ht' : t + 1 ∈ Finset.Icc 1 (P0.withSalvage (fun _ => 0) vb).k :=
        Finset.mem_Icc.2 ⟨by omega, ht⟩
      obtain ⟨hB, hU⟩ := good_all _ hM2 t (by omega)
      obtain ⟨hB1, hU1⟩ := good_all _ hM1 t (by omega)
      have : IsProbabilityMeasure (P0.μ (t+1)) := hM2.prob _ ht'
      have hpt : ∀ ξ : Fin n → ℝ, 0 ≤ ξ →
          (P0.withSalvage (fun _ => 0) vb).stage (t+1) ((P0.withSalvage (fun _ => 0) vb).g t) z (b+ξ)
            + K ≤
          (P0.withSalvage (fun _ => 0) va).stage (t+1) ((P0.withSalvage (fun _ => 0) va).g t) z (b+ξ)
            := by
        intro ξ hξ
        have hB0 : 0 ≤ b + ξ := add_nonneg hb hξ
        obtain ⟨R, hR, hst⟩ := stage_bound _ hM2 t ht2 hB z
        obtain ⟨hbdd2, -⟩ := hst z (b+ξ) hz le_rfl hB0
        have hobj : ∀ u ∈ TopkisRation.Levels.feasible z (b+ξ),
            (P0.withSalvage (fun _ => 0) vb).obj (t+1) ((P0.withSalvage (fun _ => 0) vb).g t) z
              (b+ξ) u + K ≤
            (P0.withSalvage (fun _ => 0) va).obj (t+1) ((P0.withSalvage (fun _ => 0) va).g t) z (b+ξ) u
              := by
          intro u hu
          obtain ⟨hu0, huB, hs⟩ := hu
          have hau : 0 ≤ P0.a (t+1) • u := fun j => by
            simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            exact mul_nonneg (hM2.a0 _ ht') (hu0 j)
          show P0.p (t+1) ⬝ᵥ u + P0.h (t+1) (z - ∑ j, ((b + ξ) j - u j)) +
              (P0.withSalvage (fun _ => 0) vb).g t (z - ∑ j, ((b + ξ) j - u j)) (P0.a (t+1) • u) + K ≤
            P0.p (t+1) ⬝ᵥ u + P0.h (t+1) (z - ∑ j, ((b + ξ) j - u j)) +
              (P0.withSalvage (fun _ => 0) va).g t (z - ∑ j, ((b + ξ) j - u j)) (P0.a (t+1) • u)
          have := ih (z - ∑ j, ((b + ξ) j - u j)) (P0.a (t+1) • u) (by linarith) hau
          linarith
        have hne1 : ((P0.withSalvage (fun _ => 0) va).obj (t+1) ((P0.withSalvage (fun _ => 0) va).g t)
            z (b+ξ) '' TopkisRation.Levels.feasible z (b+ξ)).Nonempty :=
          ⟨_, Set.mem_image_of_mem _ (feas_mem hz hB0)⟩
        unfold Model.stage
        refine le_csInf hne1 ?_
        rintro _ ⟨u, hu, rfl⟩
        have h1 := hobj u hu
        have h2 := csInf_le hbdd2 ⟨u, hu, rfl⟩
        linarith
      show ∫ ξ, (P0.withSalvage (fun _ => 0) vb).stage (t+1) ((P0.withSalvage (fun _ => 0) vb).g t) z
          (b + ξ) ∂(P0.μ (t+1)) + K ≤
        ∫ ξ, (P0.withSalvage (fun _ => 0) va).stage (t+1) ((P0.withSalvage (fun _ => 0) va).g t) z
          (b + ξ) ∂(P0.μ (t+1))
      have hae : ∀ᵐ ξ ∂(P0.μ (t+1)), 0 ≤ ξ := hM2.nonneg _ ht'
      have hi : Integrable (fun ξ => (P0.withSalvage (fun _ => 0) vb).stage (t+1)
          ((P0.withSalvage (fun _ => 0) vb).g t) z (b + ξ)) (P0.μ (t+1)) :=
        stage_int _ hM2 t ht2 hB hU z b hz hb
      have hi1 : Integrable (fun ξ => (P0.withSalvage (fun _ => 0) va).stage (t+1)
          ((P0.withSalvage (fun _ => 0) va).g t) z (b + ξ)) (P0.μ (t+1)) :=
        stage_int _ hM1 t ht1 hB1 hU1 z b hz hb
      have h1 : ∫ ξ, ((P0.withSalvage (fun _ => 0) vb).stage (t+1)
          ((P0.withSalvage (fun _ => 0) vb).g t) z (b + ξ) + K) ∂(P0.μ (t+1)) =
          ∫ ξ, (P0.withSalvage (fun _ => 0) vb).stage (t+1) ((P0.withSalvage (fun _ => 0) vb).g t) z
          (b + ξ) ∂(P0.μ (t+1)) + K := by
        rw [integral_add hi (integrable_const K), integral_const]; simp
      rw [← h1]
      exact integral_mono_ae (hi.add (integrable_const K)) hi1
        (by filter_upwards [hae] with ξ hξ; exact hpt ξ hξ)

theorem eq_20_core (Q : MultiModel n) (hQ : Q.Standing)
    (m : ℕ) (hm2 : 2 ≤ m) (hmN : m ≤ Q.N)
    (x : ℝ) (hx : 0 ≤ x)
    (hmin : ∀ z, 0 ≤ z → Q.gtilde m x ≤ Q.gtilde m z) :
    (∀ z, 0 ≤ z → z ≤ x →
      Q.gtilde (m - 1) z = Q.gmyopic (m - 1) z + Q.C m x) ∧
    ∀ z, x ≤ z →
      Q.gmyopic (m - 1) z + Q.C m x ≤ Q.gtilde (m - 1) z := by
  obtain ⟨hflat, hge⟩ := C_flat Q m hmN x hx hmin
  have hCm : Q.C m x = Q.gtilde m x := hflat x le_rfl
  have hm1 : m - 1 ∈ Finset.Icc 1 Q.N := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hmm : m - 1 + 1 = m := by omega
  have hP2 : PerOK ((Q.P (m-1)).withSalvage (fun _ => 0) (fun y => -Q.c m * y)) := by
    obtain ⟨hvu, hvb⟩ := salv_ok (f := fun _ => 0)
      ⟨continuous_const.upperSemicontinuous, fun Z => ⟨0, fun y _ => by simp⟩⟩ (Q.c m)
    simp only [add_zero] at hvu hvb
    exact perOK_of Q hQ (m-1) hm1 _ hvu hvb
  have hgood : GoodC (Q.C m) := crev_good Q hQ (Q.N + 1 - m) (by omega)
  obtain ⟨hvu, hvb⟩ := salv_ok hgood (Q.c m)
  have hP1 := perOK_of Q hQ (m-1) hm1 _ hvu hvb
  have hgt : ∀ z, Q.gtilde (m-1) z = Q.c (m-1) * z + ((Q.P (m-1)).withSalvage (fun _ => 0)
      (fun y => -Q.c m * y + Q.C m y)).g (Q.P (m-1)).k z 0 := by
    intro z; simp only [MultiModel.gtilde, hmm]
  have hgm : ∀ z, Q.gmyopic (m-1) z = Q.c (m-1) * z + ((Q.P (m-1)).withSalvage (fun _ => 0)
      (fun y => -Q.c m * y)).g (Q.P (m-1)).k z 0 := by
    intro z; simp only [MultiModel.gmyopic, hmm]
  constructor
  · intro z hz hzx
    rw [hgt, hgm, cmp_eq (Q.P (m-1)) _ _ hP2 (Q.C m x) x
      (fun y hy => by rw [hflat y hy, hCm]) (Q.P (m-1)).k le_rfl z 0 hz hzx le_rfl]
    ring
  · intro z hxz
    rw [hgt, hgm]
    have := cmp_le (Q.P (m-1)) _ _ hP1 hP2 (Q.C m x) (fun y => by
      rw [hCm]; linarith [hge y]) (Q.P (m-1)).k le_rfl z 0 (hx.trans hxz) le_rfl
    linarith

lemma domE_convex : Convex ℝ (DomE n) := by
  intro q1 hq1 q2 hq2 a b ha hb _
  refine ⟨?_, fun j => ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    nlinarith [hq1.1, hq2.1]
  · have e1 : (0:ℝ) ≤ q1.2 j := hq1.2 j
    have e2 : (0:ℝ) ≤ q2.2 j := hq2.2 j
    simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    nlinarith

def ConvT (M : Model n) (t : ℕ) : Prop :=
  ConvexOn ℝ (DomE n) (fun q : ℝ × (Fin n → ℝ) => M.g t q.1 q.2)

lemma conv0 (M : Model n) (hM : PerOK M) (hv2 : ConvexOn ℝ Set.univ M.v₂) : ConvT M 0 := by
  refine ⟨domE_convex, fun q1 _ q2 _ a b ha hb hab => ?_⟩
  show M.v₁ _ + M.v₂ (_ - ∑ j, _) ≤ a • (M.v₁ _ + M.v₂ (_ - ∑ j, _)) +
    b • (M.v₁ _ + M.v₂ (_ - ∑ j, _))
  rw [hM.v1, hM.v1, hM.v1]
  simp only [zero_add]
  have key : (a • q1 + b • q2).1 - ∑ j, (a • q1 + b • q2).2 j =
      a • (q1.1 - ∑ j, q1.2 j) + b • (q2.1 - ∑ j, q2.2 j) := by
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [key]
  exact hv2.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

lemma stage_conv (M : Model n) (hM : PerOK M)
    (hcx : ∀ t ∈ Finset.Icc 1 M.k, ConvexOn ℝ (Set.Ici 0) (M.h t))
    (t : ℕ) (ht : t + 1 ≤ M.k) (hB : BoundT M t) (hC : ConvT M t) :
    ConvexOn ℝ (DomE n) (fun q : ℝ × (Fin n → ℝ) => M.stage (t+1) (M.g t) q.1 q.2) := by
  have ht' : t + 1 ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨by omega, ht⟩
  refine ⟨domE_convex, ?_⟩
  rintro ⟨z1, B1⟩ ⟨hz1, hB1⟩ ⟨z2, B2⟩ ⟨hz2, hB2⟩ a b ha hb hab
  simp only at hz1 hB1 hz2 hB2
  have hmix : (a • (z1, B1) + b • (z2, B2) : ℝ × (Fin n → ℝ)) = (a * z1 + b * z2, a • B1 + b • B2) := by
    simp [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  simp only [hmix, smul_eq_mul]
  have hzm : 0 ≤ a * z1 + b * z2 := by positivity
  have hBm : 0 ≤ a • B1 + b • B2 := add_nonneg (smul_nonneg ha hB1) (smul_nonneg hb hB2)
  obtain ⟨R1, -, hst1⟩ := stage_bound M hM t ht hB z1
  obtain ⟨R2, -, hst2⟩ := stage_bound M hM t ht hB z2
  obtain ⟨R3, -, hst3⟩ := stage_bound M hM t ht hB (a * z1 + b * z2)
  have hbd1 := (hst1 z1 B1 hz1 le_rfl hB1).1
  have hbd2 := (hst2 z2 B2 hz2 le_rfl hB2).1
  have hbd3 := (hst3 _ _ hzm le_rfl hBm).1
  have hne1 : (M.obj (t+1) (M.g t) z1 B1 '' TopkisRation.Levels.feasible z1 B1).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ (feas_mem hz1 hB1)⟩
  have hne2 : (M.obj (t+1) (M.g t) z2 B2 '' TopkisRation.Levels.feasible z2 B2).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ (feas_mem hz2 hB2)⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨_, ⟨u1, hu1, rfl⟩, h1⟩ := exists_lt_of_csInf_lt hne1 (lt_add_of_pos_right
    (sInf (M.obj (t+1) (M.g t) z1 B1 '' TopkisRation.Levels.feasible z1 B1)) hε)
  obtain ⟨_, ⟨u2, hu2, rfl⟩, h2⟩ := exists_lt_of_csInf_lt hne2 (lt_add_of_pos_right
    (sInf (M.obj (t+1) (M.g t) z2 B2 '' TopkisRation.Levels.feasible z2 B2)) hε)
  obtain ⟨hu10, hu1B, hu1s⟩ := hu1
  obtain ⟨hu20, hu2B, hu2s⟩ := hu2
  set u := a • u1 + b • u2 with hu_def
  have hsum : ∑ j, ((a • B1 + b • B2) j - u j) =
      a * ∑ j, (B1 j - u1 j) + b * ∑ j, (B2 j - u2 j) := by
    simp only [hu_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hu : u ∈ TopkisRation.Levels.feasible (a * z1 + b * z2) (a • B1 + b • B2) := by
    refine ⟨add_nonneg (smul_nonneg ha hu10) (smul_nonneg hb hu20),
      add_le_add (smul_le_smul_of_nonneg_left hu1B ha) (smul_le_smul_of_nonneg_left hu2B hb), ?_⟩
    rw [hsum]; nlinarith
  set w1 := z1 - ∑ j, (B1 j - u1 j)
  set w2 := z2 - ∑ j, (B2 j - u2 j)
  have hw1 : 0 ≤ w1 := by simp only [w1]; linarith
  have hw2 : 0 ≤ w2 := by simp only [w2]; linarith
  have hw : a * z1 + b * z2 - ∑ j, ((a • B1 + b • B2) j - u j) = a • w1 + b • w2 := by
    rw [hsum]; simp only [w1, w2, smul_eq_mul]; ring
  have hα : M.a (t+1) • u = a • (M.a (t+1) • u1) + b • (M.a (t+1) • u2) := by
    simp only [hu_def, smul_add, smul_comm (M.a (t+1)) a, smul_comm (M.a (t+1)) b]
  have hq1 : ((w1, M.a (t+1) • u1) : ℝ × (Fin n → ℝ)) ∈ DomE n :=
    ⟨hw1, smul_nonneg (hM.a0 _ ht') hu10⟩
  have hq2 : ((w2, M.a (t+1) • u2) : ℝ × (Fin n → ℝ)) ∈ DomE n :=
    ⟨hw2, smul_nonneg (hM.a0 _ ht') hu20⟩
  have hG := hC.2 hq1 hq2 ha hb hab
  have hmix2 : (a • (w1, M.a (t+1) • u1) + b • (w2, M.a (t+1) • u2) : ℝ × (Fin n → ℝ)) =
      (a • w1 + b • w2, M.a (t+1) • u) := by
    rw [hα]; simp [Prod.smul_mk, Prod.mk_add_mk]
  rw [hmix2] at hG
  simp only [smul_eq_mul] at hG
  have hH := (hcx _ ht').2 (Set.mem_Ici.2 hw1) (Set.mem_Ici.2 hw2) ha hb hab
  simp only [smul_eq_mul] at hH
  have hobj : M.obj (t+1) (M.g t) (a * z1 + b * z2) (a • B1 + b • B2) u ≤
      a * M.obj (t+1) (M.g t) z1 B1 u1 + b * M.obj (t+1) (M.g t) z2 B2 u2 := by
    show M.p (t+1) ⬝ᵥ u + M.h (t+1) (a * z1 + b * z2 - ∑ j, ((a • B1 + b • B2) j - u j)) +
        M.g t (a * z1 + b * z2 - ∑ j, ((a • B1 + b • B2) j - u j)) (M.a (t+1) • u) ≤
      a * (M.p (t+1) ⬝ᵥ u1 + M.h (t+1) w1 + M.g t w1 (M.a (t+1) • u1)) +
      b * (M.p (t+1) ⬝ᵥ u2 + M.h (t+1) w2 + M.g t w2 (M.a (t+1) • u2))
    rw [hw]
    simp only [smul_eq_mul]
    have hp : M.p (t+1) ⬝ᵥ u = a * M.p (t+1) ⬝ᵥ u1 + b * M.p (t+1) ⬝ᵥ u2 := by
      simp only [hu_def, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [hp]
    nlinarith
  have hS := csInf_le hbd3 ⟨u, hu, rfl⟩
  unfold Model.stage
  nlinarith [mul_le_mul_of_nonneg_left h1.le ha, mul_le_mul_of_nonneg_left h2.le hb]

lemma int_conv (M : Model n) (hM : PerOK M)
    (hcx : ∀ t ∈ Finset.Icc 1 M.k, ConvexOn ℝ (Set.Ici 0) (M.h t))
    (t : ℕ) (ht : t + 1 ≤ M.k) (hB : BoundT M t) (hU : UscT M t) (hC : ConvT M t) :
    ConvT M (t+1) := by
  have ht' : t + 1 ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨by omega, ht⟩
  have : IsProbabilityMeasure (M.μ (t+1)) := hM.prob _ ht'
  have hSC := stage_conv M hM hcx t ht hB hC
  refine ⟨domE_convex, fun q1 hq1 q2 hq2 a b ha hb hab => ?_⟩
  have hqm := domE_convex hq1 hq2 ha hb hab
  show ∫ ξ, M.stage (t+1) (M.g t) (a • q1 + b • q2).1 ((a • q1 + b • q2).2 + ξ) ∂(M.μ (t+1)) ≤
    a • ∫ ξ, M.stage (t+1) (M.g t) q1.1 (q1.2 + ξ) ∂(M.μ (t+1)) +
    b • ∫ ξ, M.stage (t+1) (M.g t) q2.1 (q2.2 + ξ) ∂(M.μ (t+1))
  have i1 := stage_int M hM t ht hB hU q1.1 q1.2 hq1.1 hq1.2
  have i2 := stage_int M hM t ht hB hU q2.1 q2.2 hq2.1 hq2.2
  have i3 := stage_int M hM t ht hB hU _ _ hqm.1 hqm.2
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul a) (i2.const_mul b)]
  refine integral_mono_ae i3 ((i1.const_mul a).add (i2.const_mul b)) ?_
  filter_upwards [hM.nonneg _ ht'] with ξ hξ
  have hp1 : ((q1.1, q1.2 + ξ) : ℝ × (Fin n → ℝ)) ∈ DomE n := ⟨hq1.1, add_nonneg hq1.2 hξ⟩
  have hp2 : ((q2.1, q2.2 + ξ) : ℝ × (Fin n → ℝ)) ∈ DomE n := ⟨hq2.1, add_nonneg hq2.2 hξ⟩
  have := hSC.2 hp1 hp2 ha hb hab
  have e : (a • ((q1.1, q1.2 + ξ) : ℝ × (Fin n → ℝ)) + b • (q2.1, q2.2 + ξ)) =
      ((a • q1 + b • q2).1, (a • q1 + b • q2).2 + ξ) := by
    refine Prod.ext (by simp) ?_
    funext j
    simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have : ξ j = (a + b) * ξ j := by rw [hab, one_mul]
    linarith
  rw [e] at this
  simpa using this

lemma good_conv (M : Model n) (hM : PerOK M)
    (hcx : ∀ t ∈ Finset.Icc 1 M.k, ConvexOn ℝ (Set.Ici 0) (M.h t))
    (hv2 : ConvexOn ℝ Set.univ M.v₂) : ∀ t, t ≤ M.k → ConvT M t
  | 0, _ => conv0 M hM hv2
  | t+1, ht =>
    have ih := good_conv M hM hcx hv2 t (by omega)
    have hg := good_all M hM t (by omega)
    int_conv M hM hcx t ht hg.1 hg.2 ih

def LscZ (M : Model n) (t : ℕ) : Prop :=
  ∀ b0 : Fin n → ℝ, 0 ≤ b0 →
    LowerSemicontinuousWithinAt (fun q : ℝ × (Fin n → ℝ) => M.g t q.1 q.2) (DomE n) (0, b0)

lemma lsc_comp {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Y → ℝ} {D : Set Y}
    {p : Y} (hf : LowerSemicontinuousWithinAt f D p) {φ : X → Y} {T : Set X} {x : X}
    (hφ : Tendsto φ (𝓝[T] x) (𝓝[D] p)) (hφx : φ x = p) :
    LowerSemicontinuousWithinAt (fun x => f (φ x)) T x := by
  intro y hy
  simp only [hφx] at hy
  exact hφ.eventually (hf y hy)

lemma lscz0 (M : Model n) (hM : PerOK M) (hv : Continuous M.v₂) : LscZ M 0 := by
  have : (fun q : ℝ × (Fin n → ℝ) => M.g 0 q.1 q.2) = fun q => M.v₂ (q.1 - ∑ j, q.2 j) := by
    funext q
    show M.v₁ q.1 + M.v₂ (q.1 - ∑ j, q.2 j) = _
    rw [hM.v1, zero_add]
  intro b0 _
  rw [this]
  have hc : Continuous fun q : ℝ × (Fin n → ℝ) => q.1 - ∑ j, q.2 j :=
    continuous_fst.sub (continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_snd)
  exact (hv.comp hc).continuousWithinAt.lowerSemicontinuousWithinAt

lemma stage_lscz (M : Model n) (hM : PerOK M) (t : ℕ) (ht : t + 1 ≤ M.k) (hB : BoundT M t)
    (hL : LscZ M t) (B0 : Fin n → ℝ) (hB0 : 0 ≤ B0) :
    LowerSemicontinuousWithinAt (fun q : ℝ × (Fin n → ℝ) => M.stage (t+1) (M.g t) q.1 q.2)
      (DomE n) (0, B0) := by
  have ht' : t + 1 ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨by omega, ht⟩
  intro y hy
  simp only at hy
  obtain ⟨R0, -, hst0⟩ := stage_bound M hM t ht hB 0
  have hle : M.stage (t+1) (M.g t) 0 B0 ≤
      M.p (t+1) ⬝ᵥ B0 + M.h (t+1) 0 + M.g t 0 (M.a (t+1) • B0) := by
    have := csInf_le (hst0 0 B0 le_rfl le_rfl hB0).1
      (Set.mem_image_of_mem (M.obj (t+1) (M.g t) 0 B0) (feas_mem le_rfl hB0))
    refine this.trans (le_of_eq ?_)
    show M.p (t+1) ⬝ᵥ B0 + M.h (t+1) (0 - ∑ j, (B0 j - B0 j)) +
      M.g t (0 - ∑ j, (B0 j - B0 j)) (M.a (t+1) • B0) = _
    simp
  set δ := (M.p (t+1) ⬝ᵥ B0 + M.h (t+1) 0 + M.g t 0 (M.a (t+1) • B0) - y) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hch : ∀ q : ℝ × (Fin n → ℝ), ∃ u : Fin n → ℝ, q ∈ DomE n →
      u ∈ TopkisRation.Levels.feasible q.1 q.2 ∧
      M.obj (t+1) (M.g t) q.1 q.2 u < M.stage (t+1) (M.g t) q.1 q.2 + δ := by
    intro q
    by_cases hq : q ∈ DomE n
    · obtain ⟨R, -, hst⟩ := stage_bound M hM t ht hB q.1
      have hne : (M.obj (t+1) (M.g t) q.1 q.2 '' TopkisRation.Levels.feasible q.1 q.2).Nonempty :=
        ⟨_, Set.mem_image_of_mem _ (feas_mem hq.1 hq.2)⟩
      obtain ⟨_, ⟨u, hu, rfl⟩, h⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right
        (sInf (M.obj (t+1) (M.g t) q.1 q.2 '' TopkisRation.Levels.feasible q.1 q.2)) hδ0)
      exact ⟨u, fun _ => ⟨hu, h⟩⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose U hU using hch
  have hq0 : ((0, B0) : ℝ × (Fin n → ℝ)) ∈ DomE n := ⟨le_rfl, hB0⟩
  let l := 𝓝[DomE n] ((0, B0) : ℝ × (Fin n → ℝ))
  have hD : ∀ᶠ q in l, q ∈ DomE n := self_mem_nhdsWithin
  have hfst : Tendsto (fun q : ℝ × (Fin n → ℝ) => q.1) l (𝓝 0) :=
    (continuous_fst.tendsto ((0, B0) : ℝ × (Fin n → ℝ))).mono_left nhdsWithin_le_nhds
  have hsnd : ∀ j, Tendsto (fun q : ℝ × (Fin n → ℝ) => q.2 j) l (𝓝 (B0 j)) := fun j =>
    (((continuous_apply j).comp continuous_snd).tendsto ((0, B0) : ℝ × (Fin n → ℝ))).mono_left
      nhdsWithin_le_nhds
  have hUt : Tendsto U l (𝓝 B0) := by
    refine tendsto_pi_nhds.2 (fun j => ?_)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun q => q.2 j - q.1)
      (h := fun q => q.2 j) ?_ (hsnd j) ?_ ?_
    · simpa using (hsnd j).sub hfst
    · filter_upwards [hD] with q hq
      obtain ⟨hu0, huB, hs⟩ := (hU q hq).1
      have : q.2 j - U q j ≤ ∑ i, (q.2 i - U q i) :=
        Finset.single_le_sum (f := fun i => q.2 i - U q i)
          (fun i _ => by have := huB i; simp only at this ⊢; linarith) (Finset.mem_univ j)
      linarith
    · filter_upwards [hD] with q hq
      exact (hU q hq).1.2.1 j
  let W : ℝ × (Fin n → ℝ) → ℝ := fun q => q.1 - ∑ j, (q.2 j - U q j)
  have hWD : ∀ᶠ q in l, 0 ≤ W q ∧ W q ≤ q.1 := by
    filter_upwards [hD] with q hq
    obtain ⟨hu0, huB, hs⟩ := (hU q hq).1
    have : 0 ≤ ∑ j, (q.2 j - U q j) := Finset.sum_nonneg (fun i _ => by
      have := huB i; simp only at this ⊢; linarith)
    exact ⟨by simp only [W]; linarith, by simp only [W]; linarith⟩
  have hWt : Tendsto W l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfst
      (hWD.mono fun q hq => hq.1) (hWD.mono fun q hq => hq.2)
  have hpc : Continuous fun v : Fin n → ℝ => M.p (t+1) ⬝ᵥ v := by
    simp only [dotProduct]
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))
  have e1 : ∀ᶠ q in l, M.p (t+1) ⬝ᵥ B0 - δ < M.p (t+1) ⬝ᵥ U q :=
    ((hpc.tendsto B0).comp hUt).eventually (eventually_gt_nhds (by linarith))
  have hWt' : Tendsto W l (𝓝[Set.Ici 0] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hWt, hWD.mono fun q hq => hq.1⟩
  have e2 : ∀ᶠ q in l, M.h (t+1) 0 - δ < M.h (t+1) (W q) :=
    (((hM.hc _ ht') 0 Set.self_mem_Ici).tendsto.comp hWt').eventually
      (eventually_gt_nhds (by linarith))
  have hψ : Tendsto (fun q => (W q, M.a (t+1) • U q)) l (𝓝[DomE n] (0, M.a (t+1) • B0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hWt.prodMk_nhds (hUt.const_smul _), ?_⟩
    filter_upwards [hWD, hD] with q hq hqD
    exact ⟨hq.1, smul_nonneg (hM.a0 _ ht') (hU q hqD).1.1⟩
  have e3 : ∀ᶠ q in l, M.g t 0 (M.a (t+1) • B0) - δ < M.g t (W q) (M.a (t+1) • U q) :=
    hψ.eventually (hL _ (smul_nonneg (hM.a0 _ ht') hB0) _ (by simp only; linarith))
  filter_upwards [e1, e2, e3, hD] with q h1 h2 h3 hq
  have h4 := (hU q hq).2
  have h5 : M.obj (t+1) (M.g t) q.1 q.2 (U q) =
      M.p (t+1) ⬝ᵥ U q + M.h (t+1) (W q) + M.g t (W q) (M.a (t+1) • U q) := rfl
  show y < M.stage (t+1) (M.g t) q.1 q.2
  linarith

lemma lscz_succ (M : Model n) (hM : PerOK M) (t : ℕ) (ht : t + 1 ≤ M.k) (hB : BoundT M t)
    (hU : UscT M t) (hL : LscZ M t) : LscZ M (t+1) := by
  have ht' : t + 1 ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨by omega, ht⟩
  have : IsProbabilityMeasure (M.μ (t+1)) := hM.prob _ ht'
  intro b0 hb0 y hy
  let st : ℝ × (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun q ξ => M.stage (t+1) (M.g t) q.1 (q.2 + ξ)
  let F : ℝ × (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun q ξ => st q ξ ⊓ st (0, b0) ξ
  obtain ⟨R, hR, hst⟩ := stage_bound M hM t ht hB 1
  have hsi : Integrable (fun ξ : Fin n → ℝ => ∑ j, ξ j) (M.μ (t+1)) :=
    integrable_finsetSum _ fun j _ => hM.mean _ ht' j
  let bound : (Fin n → ℝ) → ℝ := fun ξ => R * (1 + (∑ j, b0 j + 1)) + R * ∑ j, ξ j
  have hbi : Integrable bound (M.μ (t+1)) := (integrable_const _).add (hsi.const_mul R)
  have hsc : Continuous fun q : ℝ × (Fin n → ℝ) => ∑ j, q.2 j :=
    continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_snd
  have hnear : ∀ᶠ q in 𝓝[DomE n] ((0, b0) : ℝ × (Fin n → ℝ)),
      q ∈ DomE n ∧ q.1 < 1 ∧ ∑ j, q.2 j < ∑ j, b0 j + 1 := by
    refine (eventually_mem_nhdsWithin (a := ((0, b0) : ℝ × (Fin n → ℝ))) (s := DomE n)).and
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_)
    exact ((continuous_fst.tendsto _).eventually (eventually_lt_nhds (by simp))).and
      ((hsc.tendsto _).eventually (eventually_lt_nhds (by simp)))
  have hint : ∀ q ∈ DomE n, Integrable (st q) (M.μ (t+1)) := fun q hq =>
    stage_int M hM t ht hB hU q.1 q.2 hq.1 hq.2
  have hq0 : ((0, b0) : ℝ × (Fin n → ℝ)) ∈ DomE n := ⟨le_rfl, hb0⟩
  have hlim : Tendsto (fun q => ∫ ξ, F q ξ ∂(M.μ (t+1))) (𝓝[DomE n] (0, b0))
      (𝓝 (∫ ξ, st (0, b0) ξ ∂(M.μ (t+1)))) := by
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbi ?_
    · filter_upwards [hnear] with q hq
      exact ((hint q hq.1).inf (hint _ hq0)).aestronglyMeasurable
    · filter_upwards [hnear] with q hq
      filter_upwards [hM.nonneg _ ht'] with ξ hξ
      have h1 := (hst q.1 (q.2 + ξ) hq.1.1 hq.2.1.le (add_nonneg hq.1.2 hξ)).2
      have h2 := (hst 0 (b0 + ξ) le_rfl zero_le_one (add_nonneg hb0 hξ)).2
      simp only [Pi.add_apply, Finset.sum_add_distrib] at h1 h2
      have hRs := mul_le_mul_of_nonneg_left hq.2.2.le hR
      have hRb : 0 ≤ R * ∑ j, b0 j := mul_nonneg hR (sum_nonneg' hb0)
      rw [Real.norm_eq_abs]
      refine abs_le.2 ⟨?_, ?_⟩
      · refine le_inf ?_ ?_
        · have := (abs_le.1 h1).1; simp only [bound]; nlinarith
        · have := (abs_le.1 h2).1; simp only [bound]; nlinarith
      · have := (abs_le.1 h1).2
        have : F q ξ ≤ st q ξ := inf_le_left
        simp only [bound]; nlinarith
    · filter_upwards [hM.nonneg _ ht'] with ξ hξ
      have hlsc : LowerSemicontinuousWithinAt (fun q => st q ξ) (DomE n) (0, b0) := by
        refine lsc_comp (stage_lscz M hM t ht hB hL (b0 + ξ) (add_nonneg hb0 hξ))
          (φ := fun q : ℝ × (Fin n → ℝ) => (q.1, q.2 + ξ)) ?_ (by simp)
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have : Continuous fun q : ℝ × (Fin n → ℝ) => (q.1, q.2 + ξ) := by fun_prop
          have h := (this.tendsto ((0, b0) : ℝ × (Fin n → ℝ))).mono_left
            (nhdsWithin_le_nhds (s := DomE n))
          simpa using h
        · filter_upwards [self_mem_nhdsWithin] with q hq
          exact ⟨hq.1, add_nonneg hq.2 hξ⟩
      rw [tendsto_order]
      refine ⟨fun a ha => (hlsc a ha).mono (fun q hq => lt_inf_iff.2 ⟨hq, ha⟩),
        fun a ha => Eventually.of_forall (fun q => lt_of_le_of_lt inf_le_right ha)⟩
  have hy' : y < ∫ ξ, st (0, b0) ξ ∂(M.μ (t+1)) := hy
  filter_upwards [hlim.eventually (eventually_gt_nhds hy'), hnear] with q h1 h2
  show y < ∫ ξ, st q ξ ∂(M.μ (t+1))
  exact lt_of_lt_of_le h1 (integral_mono ((hint q h2.1).inf (hint _ hq0)) (hint q h2.1)
    (fun ξ => inf_le_left))

lemma lscz_all (M : Model n) (hM : PerOK M) (hv : Continuous M.v₂) :
    ∀ t, t ≤ M.k → LscZ M t
  | 0, _ => lscz0 M hM hv
  | t+1, ht =>
    have ih := lscz_all M hM hv t (by omega)
    have hg := good_all M hM t (by omega)
    lscz_succ M hM t ht hg.1 hg.2 ih

lemma period_cc (M : Model n) (hM : PerOK M)
    (hcx : ∀ t ∈ Finset.Icc 1 M.k, ConvexOn ℝ (Set.Ici 0) (M.h t))
    (hv2 : ConvexOn ℝ Set.univ M.v₂) (hvc : Continuous M.v₂) (c : ℝ) :
    ConvexOn ℝ (Set.Ici 0) (fun z => c * z + M.g M.k z 0) ∧
    ContinuousOn (fun z => c * z + M.g M.k z 0) (Set.Ici 0) := by
  have hC := good_conv M hM hcx hv2 M.k le_rfl
  have hL := lscz_all M hM hvc M.k le_rfl
  have hU := (period_props M hM c).1
  have hcv : ConvexOn ℝ (Set.Ici 0) (fun z => c * z + M.g M.k z 0) := by
    refine ⟨convex_Ici 0, fun z1 hz1 z2 hz2 a b ha hb hab => ?_⟩
    have hq1 : ((z1, (0 : Fin n → ℝ)) : ℝ × (Fin n → ℝ)) ∈ DomE n := ⟨hz1, le_rfl⟩
    have hq2 : ((z2, (0 : Fin n → ℝ)) : ℝ × (Fin n → ℝ)) ∈ DomE n := ⟨hz2, le_rfl⟩
    have := hC.2 hq1 hq2 ha hb hab
    have e : (a • ((z1, (0 : Fin n → ℝ)) : ℝ × (Fin n → ℝ)) + b • (z2, 0)) = (a • z1 + b • z2, 0) := by
      simp [Prod.smul_mk, Prod.mk_add_mk]
    rw [e] at this
    simp only [smul_eq_mul] at this ⊢
    nlinarith
  refine ⟨hcv, fun z0 hz0 => ?_⟩
  rcases eq_or_lt_of_le (Set.mem_Ici.1 hz0) with h | h
  · subst h
    rw [continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
    refine ⟨?_, hU 0 hz0⟩
    have hl := lsc_comp (hL 0 le_rfl) (φ := fun z : ℝ => (z, (0 : Fin n → ℝ))) (T := Set.Ici 0)
      (x := 0) ?_ rfl
    · exact (continuous_const.mul continuous_id).continuousWithinAt.lowerSemicontinuousWithinAt.add hl
    · refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((by fun_prop : Continuous fun z : ℝ => (z, (0 : Fin n → ℝ))).tendsto 0).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact ⟨hz, le_rfl⟩
  · have := hcv.continuousOn_interior
    rw [interior_Ici] at this
    exact ((this.continuousAt (Ioi_mem_nhds h)).continuousWithinAt)

lemma C_conv (G : ℝ → ℝ) (hG : ConvexOn ℝ (Set.Ici 0) G)
    (hGb : ∀ Z : ℝ, ∃ R, ∀ z, 0 ≤ z → z ≤ Z → |G z| ≤ R) :
    ConvexOn ℝ Set.univ (fun w => sInf (G '' Set.Ici (max w 0))) := by
  have hne : ∀ w : ℝ, (G '' Set.Ici (max w 0)).Nonempty := fun w =>
    ⟨_, Set.mem_image_of_mem G (Set.mem_Ici.2 le_rfl)⟩
  by_cases hbdd0 : BddBelow (G '' Set.Ici 0)
  · obtain ⟨L, hL⟩ := hbdd0
    have hbdd : ∀ w : ℝ, BddBelow (G '' Set.Ici (max w 0)) := fun w =>
      ⟨L, by
        rintro _ ⟨z, hz, rfl⟩
        exact hL ⟨z, Set.mem_Ici.2 (le_trans (le_max_right _ _) (Set.mem_Ici.1 hz)), rfl⟩⟩
    refine ⟨convex_univ, fun w1 _ w2 _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨_, ⟨z1, hz1, rfl⟩, h1⟩ := exists_lt_of_csInf_lt (hne w1)
      (lt_add_of_pos_right (sInf (G '' Set.Ici (max w1 0))) hε)
    obtain ⟨_, ⟨z2, hz2, rfl⟩, h2⟩ := exists_lt_of_csInf_lt (hne w2)
      (lt_add_of_pos_right (sInf (G '' Set.Ici (max w2 0))) hε)
    have hz1' := Set.mem_Ici.1 hz1
    have hz2' := Set.mem_Ici.1 hz2
    have hz10 : 0 ≤ z1 := le_trans (le_max_right _ _) hz1'
    have hz20 : 0 ≤ z2 := le_trans (le_max_right _ _) hz2'
    have hw1 : w1 ≤ z1 := le_trans (le_max_left _ _) hz1'
    have hw2 : w2 ≤ z2 := le_trans (le_max_left _ _) hz2'
    have hz : a * z1 + b * z2 ∈ Set.Ici (max (a * w1 + b * w2) 0) := by
      refine Set.mem_Ici.2 (max_le ?_ (by positivity))
      nlinarith [mul_le_mul_of_nonneg_left hw1 ha, mul_le_mul_of_nonneg_left hw2 hb]
    have hcv := hG.2 (Set.mem_Ici.2 hz10) (Set.mem_Ici.2 hz20) ha hb hab
    simp only [smul_eq_mul] at hcv
    have := csInf_le (hbdd _) (Set.mem_image_of_mem G hz)
    nlinarith [mul_le_mul_of_nonneg_left h1.le ha, mul_le_mul_of_nonneg_left h2.le hb]
  · have h0 : (fun w => sInf (G '' Set.Ici (max w 0))) = fun _ => 0 := by
      funext w
      apply Real.sInf_of_not_bddBelow
      rintro ⟨L, hL⟩
      apply hbdd0
      obtain ⟨R, hR⟩ := hGb (max w 0)
      refine ⟨min L (-R), ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      rcases le_or_gt z (max w 0) with h | h
      · exact (min_le_right _ _).trans (abs_le.1 (hR z hz h)).1
      · exact (min_le_left _ _).trans (hL ⟨z, h.le, rfl⟩)
    rw [h0]
    exact convexOn_const 0 convex_univ

def Strong (f : ℝ → ℝ) : Prop := GoodC f ∧ ConvexOn ℝ Set.univ f ∧ Continuous f

lemma lin_conv (c : ℝ) : ConvexOn ℝ Set.univ (fun y : ℝ => -c * y) :=
  ⟨convex_univ, fun x _ y _ a b _ _ _ => le_of_eq (by simp only [smul_eq_mul]; ring)⟩

lemma crev_strong (Q : MultiModel n) (hQ : Q.Standing) : ∀ r, r ≤ Q.N → Strong (Q.Crev r)
  | 0, h0 => by
    refine ⟨crev_good Q hQ 0 h0, ?_, ?_⟩
    · show ConvexOn ℝ Set.univ (fun w => (Q.c (Q.N + 1) - Q.v) * max w 0)
      have hcv : 0 ≤ Q.c (Q.N + 1) - Q.v := sub_nonneg.2 hQ.v_le
      refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
      simp only [smul_eq_mul]
      have : max (a * x + b * y) 0 ≤ a * max x 0 + b * max y 0 :=
        max_le (by nlinarith [mul_le_mul_of_nonneg_left (le_max_left x 0) ha,
          mul_le_mul_of_nonneg_left (le_max_left y 0) hb])
          (by nlinarith [mul_nonneg ha (le_max_right x 0), mul_nonneg hb (le_max_right y 0)])
      nlinarith [mul_le_mul_of_nonneg_left this hcv]
    · show Continuous (fun w => (Q.c (Q.N + 1) - Q.v) * max w 0)
      fun_prop
  | r+1, hr => by
    have ih := crev_strong Q hQ r (by omega)
    have hm : Q.N - r ∈ Finset.Icc 1 Q.N := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    obtain ⟨hvu, hvb⟩ := salv_ok ih.1 (Q.c (Q.N - r + 1))
    have hP := perOK_of Q hQ (Q.N - r) hm _ hvu hvb
    have hS := hQ.period (Q.N - r) hm
    obtain ⟨hG1, hG2⟩ := period_props _ hP (Q.c (Q.N - r))
    have hv2 : ConvexOn ℝ Set.univ (fun y => -Q.c (Q.N - r + 1) * y + Q.Crev r y) :=
      (lin_conv _).add ih.2.1
    have hvc : Continuous (fun y => -Q.c (Q.N - r + 1) * y + Q.Crev r y) :=
      (continuous_const.mul continuous_id).add ih.2.2
    obtain ⟨hcv, -⟩ := period_cc _ hP hS.h_convex hv2 hvc (Q.c (Q.N - r))
    have hconv := C_conv _ hcv hG2
    refine ⟨C_good _ hG1 hG2, hconv, ?_⟩
    exact continuousOn_univ.1 (hconv.continuousOn isOpen_univ)

theorem C_cc_core (Q : MultiModel n) (hQ : Q.Standing) :
    (∀ m ∈ Finset.Icc 1 (Q.N + 1),
      ConvexOn ℝ Set.univ (Q.C m) ∧ Continuous (Q.C m)) ∧
    (∀ m ∈ Finset.Icc 1 Q.N,
      ConvexOn ℝ (Set.Ici 0) (Q.gtilde m) ∧ ContinuousOn (Q.gtilde m) (Set.Ici 0)) := by
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · have hm' := Finset.mem_Icc.1 hm
    have := crev_strong Q hQ (Q.N + 1 - m) (by omega)
    exact ⟨this.2.1, this.2.2⟩
  · have hm' := Finset.mem_Icc.1 hm
    have ih := crev_strong Q hQ (Q.N + 1 - (m + 1)) (by omega)
    obtain ⟨hvu, hvb⟩ := salv_ok ih.1 (Q.c (m + 1))
    have hP := perOK_of Q hQ m hm _ hvu hvb
    have hS := hQ.period m hm
    have hv2 : ConvexOn ℝ Set.univ (fun y => -Q.c (m + 1) * y + Q.Crev (Q.N + 1 - (m + 1)) y) :=
      (lin_conv _).add ih.2.1
    have hvc : Continuous (fun y => -Q.c (m + 1) * y + Q.Crev (Q.N + 1 - (m + 1)) y) :=
      (continuous_const.mul continuous_id).add ih.2.2
    exact period_cc _ hP hS.h_convex hv2 hvc (Q.c m)

end TopkisRation.Myopic

open TopkisRation.Myopic
variable {n : ℕ}

theorem solution (Q : MultiModel n) (hQ : Q.Standing) :
    (∀ m ∈ Finset.Icc 1 (Q.N + 1),
      ConvexOn ℝ Set.univ (Q.C m) ∧ Continuous (Q.C m)) ∧
    (∀ m ∈ Finset.Icc 1 Q.N,
      ConvexOn ℝ (Set.Ici 0) (Q.gtilde m) ∧ ContinuousOn (Q.gtilde m) (Set.Ici 0)) := by
  exact C_cc_core Q hQ

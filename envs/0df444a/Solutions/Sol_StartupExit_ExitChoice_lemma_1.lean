-- Prove2me | solution 1 for StartupExit.ExitChoice.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:35:54.733142+00:00
-- url     : https://prove2.me/submissions/8aa9c942-c8f4-4e44-ac06-3767d7acbf25

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_OrderStats

set_option autoImplicit false
open MeasureTheory StartupExit.ExitChoice

lemma hasDerivAt_H (x : ℝ) : HasDerivAt H (1 / 2 : ℝ) x := by
  have := ((hasDerivAt_id x).add_const (1 : ℝ)).div_const 2
  have e : H = fun x => (x + 1) / 2 := rfl
  rw [e]
  simpa using this

lemma hasDerivAt_Hpow (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => H y ^ (k + 1)) (((k : ℝ) + 1) * H x ^ k / 2) x := by
  refine ((hasDerivAt_H x).pow (k + 1)).congr_deriv ?_
  simp; ring

lemma unif_univ : unifMeasure Set.univ = 1 := by
  simp only [unifMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Icc, smul_eq_mul]
  rw [show (1 : ℝ) - (-1) = 2 by norm_num, ENNReal.ofReal_ofNat]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

instance : IsProbabilityMeasure unifMeasure := ⟨unif_univ⟩

lemma unif_Iic (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    unifMeasure (Set.Iic x) = ENNReal.ofReal (H x) := by
  have : Set.Iic x ∩ Set.Icc (-1 : ℝ) 1 = Set.Icc (-1) x := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [hx.2]⟩
  simp only [unifMeasure, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, this,
    Real.volume_Icc, smul_eq_mul]
  have h2 : (2 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; unfold H; ring

lemma unif_Ioi (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    unifMeasure (Set.Ioi x) = ENNReal.ofReal (1 - H x) := by
  have : Set.Ioi x ∩ Set.Icc (-1 : ℝ) 1 = Set.Ioc x 1 := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith [hx.1], h2⟩
  simp only [unifMeasure, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioi, this,
    Real.volume_Ioc, smul_eq_mul]
  have h2 : (2 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; unfold H; ring

lemma H_nonneg (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : 0 ≤ H x := by
  unfold H; linarith [hx.1]
lemma H_le_one (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : H x ≤ 1 := by
  unfold H; linarith [hx.2]

lemma part1' (z : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Measure.pi (fun _ : Fin z => unifMeasure) (Set.pi Set.univ (fun _ => Set.Iic x)) =
      ENNReal.ofReal (H x ^ z) := by
  rw [Measure.pi_pi]
  simp only [unif_Iic x hx]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow (H_nonneg x hx)]

lemma part1 (z : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Measure.pi (fun _ : Fin z => unifMeasure) {v : Fin z → ℝ | ∀ i, v i ≤ x} =
      ENNReal.ofReal (H x ^ z) := by
  rw [← part1' z x hx]
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic]

lemma part2 (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Measure.pi (fun _ : Fin (n + 2) => unifMeasure)
        {v : Fin (n + 2) → ℝ | (Finset.univ.filter (fun i => x < v i)).card ≤ 1} =
      ENNReal.ofReal (H x ^ (n + 2) + ((n : ℝ) + 2) * ((1 - H x) * H x ^ (n + 1))) := by
  set μ := Measure.pi (fun _ : Fin (n + 2) => unifMeasure) with hμ
  let A0 : Set (Fin (n + 2) → ℝ) := Set.pi Set.univ (fun _ => Set.Iic x)
  let A : Fin (n + 2) → Set (Fin (n + 2) → ℝ) :=
    fun j => Set.pi Set.univ (fun i => if i = j then Set.Ioi x else Set.Iic x)
  have hA0m : MeasurableSet A0 := MeasurableSet.univ_pi (fun _ => measurableSet_Iic)
  have hAm : ∀ j, MeasurableSet (A j) := fun j =>
    MeasurableSet.univ_pi (fun i => by
      by_cases h : i = j
      · simp only [h, if_true]; exact measurableSet_Ioi
      · simp only [h, if_false]; exact measurableSet_Iic)
  have hset : {v : Fin (n + 2) → ℝ | (Finset.univ.filter (fun i => x < v i)).card ≤ 1} =
      A0 ∪ ⋃ j, A j := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, A0, A, Set.mem_pi,
      Set.mem_univ, true_implies, Set.mem_Iic]
    constructor
    · intro h
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h1
      · left
        intro i
        by_contra hi
        have : i ∈ Finset.univ.filter (fun i => x < v i) := by simp; linarith
        rw [Finset.card_eq_zero] at h0
        simp [h0] at this
      · right
        obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h1
        refine ⟨j, fun i => ?_⟩
        by_cases hij : i = j
        · subst hij; simp
          have : i ∈ Finset.univ.filter (fun i => x < v i) := by rw [hj]; simp
          simpa using this
        · simp only [hij, if_false, Set.mem_Iic]
          by_contra hi
          have : i ∈ Finset.univ.filter (fun i => x < v i) := by simp; linarith
          rw [hj] at this; simp at this; exact hij this
    · rintro (h | ⟨j, hj⟩)
      · have : Finset.univ.filter (fun i => x < v i) = ∅ := by
          ext i; simp; exact h i
        rw [this]; simp
      · have : Finset.univ.filter (fun i => x < v i) ⊆ {j} := by
          intro i hi
          simp at hi
          by_contra hij
          have := hj i
          simp only [Finset.mem_singleton] at hij
          simp [hij] at this
          linarith
        calc _ ≤ ({j} : Finset _).card := Finset.card_le_card this
          _ = 1 := by simp
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro j j' hjj'
    rw [Function.onFun, Set.disjoint_left]
    intro v hv hv'
    simp only [A, Set.mem_pi, Set.mem_univ, true_implies] at hv hv'
    have h1 := hv j
    have h2 := hv' j
    simp [hjj'] at h2 h1
    linarith
  have hdisj0 : Disjoint A0 (⋃ j, A j) := by
    rw [Set.disjoint_left]
    intro v hv hv'
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hv'
    simp only [A0, A, Set.mem_pi, Set.mem_univ, true_implies] at hv hj
    have := hj j
    simp at this
    have h3 := Set.mem_Iic.1 (hv j)
    linarith
  rw [hset, measure_union hdisj0 (MeasurableSet.iUnion hAm), measure_iUnion hdisj hAm,
    tsum_fintype]
  have hA0 : μ A0 = ENNReal.ofReal (H x ^ (n + 2)) := part1' (n + 2) x hx
  have hAj : ∀ j, μ (A j) = ENNReal.ofReal ((1 - H x) * H x ^ (n + 1)) := by
    intro j
    simp only [A, hμ, Measure.pi_pi]
    have : ∀ i : Fin (n + 2), unifMeasure (if i = j then Set.Ioi x else Set.Iic x) =
        if i = j then ENNReal.ofReal (1 - H x) else ENNReal.ofReal (H x) := by
      intro i; by_cases h : i = j <;> simp [h, unif_Ioi x hx, unif_Iic x hx]
    simp only [this]
    rw [Finset.prod_ite]
    simp [Finset.filter_eq', Finset.filter_ne']
    rw [← ENNReal.ofReal_pow (H_nonneg x hx), ← ENNReal.ofReal_mul (by linarith [H_le_one x hx])]
  simp only [hAj, hA0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnn1 : 0 ≤ (1 - H x) * H x ^ (n + 1) :=
    mul_nonneg (by linarith [H_le_one x hx]) (pow_nonneg (H_nonneg x hx) _)
  have hc : ((n + 2 : ℕ) : ENNReal) = ENNReal.ofReal ((n : ℝ) + 2) := by
    rw [show ((n : ℝ) + 2) = ((n + 2 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  rw [hc, ← ENNReal.ofReal_mul (p := (n : ℝ) + 2) (q := (1 - H x) * H x ^ (n + 1))
    (by positivity), ← ENNReal.ofReal_add (pow_nonneg (H_nonneg x hx) _)
    (mul_nonneg (by positivity) hnn1)]

theorem solution (z : ℕ) :
    (1 ≤ z → ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Measure.pi (fun _ : Fin z => unifMeasure) {v : Fin z → ℝ | ∀ i, v i ≤ x} =
        ENNReal.ofReal (Fcdf x z)) ∧
    (2 ≤ z → ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Measure.pi (fun _ : Fin z => unifMeasure)
          {v : Fin z → ℝ | (Finset.univ.filter (fun i => x < v i)).card ≤ 1} =
        ENNReal.ofReal (Gcdf x z)) ∧
    (1 ≤ z → ∀ x ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (fun y => Fcdf y z) (fdens x z) x) ∧
    (2 ≤ z → ∀ x ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (fun y => Gcdf y z) (gdens x z) x) := by
  refine ⟨fun _ x hx => part1 z x hx, fun hz x hx => ?_, fun hz x _ => ?_, fun hz x _ => ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, z = n + 2 := ⟨z - 2, by omega⟩
    rw [part2 n x hx]
    congr 1
    unfold Gcdf
    rw [show n + 2 - 1 = n + 1 from rfl]
    push_cast
    ring
  · obtain ⟨n, rfl⟩ : ∃ n, z = n + 1 := ⟨z - 1, by omega⟩
    refine (hasDerivAt_Hpow n x).congr_deriv ?_
    simp [fdens, h]
    push_cast
    ring
  · obtain ⟨n, rfl⟩ : ∃ n, z = n + 2 := ⟨z - 2, by omega⟩
    have hA := hasDerivAt_Hpow n x
    have hB := hasDerivAt_Hpow (n + 1) x
    have hG := (hA.const_mul ((n : ℝ) + 2)).sub (hB.const_mul ((n : ℝ) + 1))
    have e : (fun y => Gcdf y (n + 2)) =
        fun y => ((n : ℝ) + 2) * H y ^ (n + 1) - ((n : ℝ) + 1) * H y ^ (n + 2) := by
      funext y; simp only [Gcdf]; push_cast; ring_nf
    rw [e]
    refine hG.congr_deriv ?_
    simp [gdens, h]
    push_cast
    ring

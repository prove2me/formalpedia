-- Prove2me | solution 1 for TFIMPhaseDiagram.Classical.Supplement.prop_26
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:48:26.669981+00:00
-- url     : https://prove2.me/submissions/f1ab9e8b-7955-40c3-988d-6fa618b16fcb

import Definitions.Def_TFIMPhaseDiagram_Classical_Supplement_deviations
import Theorems.Thm_TFIMPhaseDiagram_Classical_prop_8

set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators ENNReal symmDiff
noncomputable section

namespace TFIMPhaseDiagram.Classical.Supplement.P26A
open TFIMPhaseDiagram.Classical TFIMPhaseDiagram.Classical.Supplement

lemma mem_jumpUpper (τ : PathData) (A : Finset ℕ) (t : ℝ) :
    t ∈ jumpUpper τ A ↔ ∀ k ∈ A, τ.2.2 k ≤ t := by
  simp [jumpUpper]

lemma pv_expand (τ : PathData) (t : ℝ) :
    pathValue τ t = ∑ A ∈ (Finset.range τ.1).powerset,
      (spin τ.2.1 * (-2 : ℝ) ^ A.card) * (jumpUpper τ A).indicator (fun _ => (1:ℝ)) t := by
  unfold pathValue
  set s := Finset.range τ.1
  have h1 : (-1 : ℝ) ^ (s.filter (fun k => τ.2.2 k ≤ t)).card =
      ∏ k ∈ s, ((-2) * (if τ.2.2 k ≤ t then (1:ℝ) else 0) + 1) := by
    have : ∀ k, ((-2) * (if τ.2.2 k ≤ t then (1:ℝ) else 0) + 1) = if τ.2.2 k ≤ t then -1 else 1 := by
      intro k; split_ifs <;> norm_num
    simp only [this]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rw [h1, Finset.prod_add, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro A hA
  rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const]
  have h2 : ∏ k ∈ A, (if τ.2.2 k ≤ t then (1:ℝ) else 0) =
      (jumpUpper τ A).indicator (fun _ => (1:ℝ)) t := by
    by_cases hall : ∀ k ∈ A, τ.2.2 k ≤ t
    · rw [Finset.prod_eq_one (fun k hk => if_pos (hall k hk)),
        Set.indicator_of_mem ((mem_jumpUpper τ A t).2 hall)]
    · push Not at hall
      obtain ⟨k, hk, hkt⟩ := hall
      rw [Finset.prod_eq_zero hk (if_neg (not_le.2 hkt)),
        Set.indicator_of_notMem (fun h => absurd ((mem_jumpUpper τ A t).1 h k hk) (not_le.2 hkt))]
  rw [h2]; ring


lemma jumpUpper_meas (τ : PathData) (A : Finset ℕ) : MeasurableSet (jumpUpper τ A) :=
  Finset.measurableSet_biInter A (fun _ _ => measurableSet_Ici)

lemma inner_const_ind (r : ℝ) (S : Set ℝ) (hs : MeasurableSet S) (hμs : circleVolume S ≠ ∞) :
    inner ℝ (constL2 r) (indicatorConstLp 2 hs hμs (1 : ℝ)) = r * circleVolume.real S := by
  rw [real_inner_comm, L2.inner_indicatorConstLp_one]
  have hc : (constL2 r : ℝ → ℝ) =ᵐ[circleVolume] fun _ => r := MemLp.coeFn_toLp _
  rw [setIntegral_congr_ae hs (hc.mono (fun x hx _ => hx))]
  rw [setIntegral_const, smul_eq_mul, mul_comm]

lemma inner_path (r : ℝ) (τ : PathData) :
    inner ℝ (constL2 r) (pathL2 τ) = r * ∫ t, pathValue τ t ∂circleVolume := by
  unfold pathL2
  rw [inner_sum]
  simp only [inner_smul_right]
  have hint : ∀ A : Finset ℕ, Integrable ((jumpUpper τ A).indicator (fun _ => (1:ℝ))) circleVolume :=
    fun A => (integrable_const (1:ℝ)).indicator (jumpUpper_meas τ A)
  rw [show (fun t => pathValue τ t) = fun t => ∑ A ∈ (Finset.range τ.1).powerset,
      (spin τ.2.1 * (-2 : ℝ) ^ A.card) * (jumpUpper τ A).indicator (fun _ => (1:ℝ)) t from
      funext (pv_expand τ)]
  rw [integral_finset_sum _ (fun A _ => (hint A).const_mul _), Finset.mul_sum]
  apply Finset.sum_congr rfl; intro A _
  rw [integral_const_mul, integral_indicator_const _ (jumpUpper_meas τ A), smul_eq_mul, mul_one]
  have := inner_const_ind r (jumpUpper τ A) (jumpUpper_meas τ A) (measure_ne_top _ _)
  erw [this]
  ring


open Topology in
lemma symm_tendsto (A : Finset ℕ) (U0 : ℕ → ℝ) :
    Tendsto (fun U : ℕ → ℝ => circleVolume ((⋂ k ∈ A, Set.Ici (U k)) ∆ (⋂ k ∈ A, Set.Ici (U0 k))))
      (𝓝 U0) (𝓝 0) := by
  rcases A.eq_empty_or_nonempty with hA | hA
  · subst hA; simp
  have hset : ∀ U : ℕ → ℝ, (⋂ k ∈ A, Set.Ici (U k)) = Set.Ici (A.sup' hA U) := by
    intro U; ext t; simp [Finset.sup'_le_iff]
  simp only [hset]
  have hbound : ∀ U : ℕ → ℝ, circleVolume (Set.Ici (A.sup' hA U) ∆ Set.Ici (A.sup' hA U0)) ≤
      ENNReal.ofReal |A.sup' hA U - A.sup' hA U0| := by
    intro U
    set a := A.sup' hA U; set a0 := A.sup' hA U0
    have hsub : Set.Ici a ∆ Set.Ici a0 ⊆ Set.Icc (min a a0) (max a a0) := by
      intro t ht
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [Set.mem_Ici, not_le] at h1 h2
        exact ⟨le_trans (min_le_left _ _) h1, le_trans h2.le (le_max_right _ _)⟩
      · simp only [Set.mem_Ici, not_le] at h1 h2
        exact ⟨le_trans (min_le_right _ _) h1, le_trans h2.le (le_max_left _ _)⟩
    calc circleVolume (Set.Ici a ∆ Set.Ici a0) ≤ volume (Set.Ici a ∆ Set.Ici a0) :=
          Measure.restrict_apply_le _ _
      _ ≤ volume (Set.Icc (min a a0) (max a a0)) := measure_mono hsub
      _ = ENNReal.ofReal |a - a0| := by rw [Real.volume_Icc, max_sub_min_eq_abs, abs_sub_comm]
  have hcont : Tendsto (fun U : ℕ → ℝ => A.sup' hA U) (𝓝 U0) (𝓝 (A.sup' hA U0)) := by
    have := ContinuousAt.finset_sup'_apply (s := A) (f := fun k (U : ℕ → ℝ) => U k) (x := U0) hA
      (fun k _ => (continuous_apply k).continuousAt)
    exact this
  have hlim : Tendsto (fun U : ℕ → ℝ => ENNReal.ofReal |A.sup' hA U - A.sup' hA U0|) (𝓝 U0) (𝓝 0) := by
    have h1 : Tendsto (fun U : ℕ → ℝ => |A.sup' hA U - A.sup' hA U0|) (𝓝 U0) (𝓝 0) := by
      have := (hcont.sub_const (A.sup' hA U0)).abs
      simpa using this
    simpa using (ENNReal.tendsto_ofReal h1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun U => zero_le') hbound

lemma pathL2_cont (d : ℕ) (b : Bool) : Continuous (fun U : ℕ → ℝ => pathL2 (d, b, U)) := by
  unfold pathL2
  dsimp only
  apply continuous_finsetSum _ (fun A _ => ?_)
  have hc : Continuous (fun U : ℕ → ℝ => (indicatorConstLp 2
      (Finset.measurableSet_biInter A (fun _ _ => measurableSet_Ici) : MeasurableSet (⋂ k ∈ A, Set.Ici (U k)))
      (measure_ne_top circleVolume _) (1 : ℝ) : CircleL2)) :=
    continuous_indicatorConstLp_set (μ := circleVolume) (p := 2) ENNReal.ofNat_ne_top
      (fun U0 => symm_tendsto A U0)
  exact (continuous_const (y := (spin b * (-2 : ℝ) ^ A.card))).smul hc

lemma pathL2_meas : Measurable pathL2 := by
  apply measurable_from_prod_countable_right
  intro d
  apply measurable_from_prod_countable_right
  intro b
  exact (pathL2_cont d b).measurable

end TFIMPhaseDiagram.Classical.Supplement.P26A

namespace TFIMPhaseDiagram.Classical.P26M
open TFIMPhaseDiagram.Classical Matrix
open scoped Nat

lemma localZ_eq {n : ℕ} (i : Fin n) :
    localPauli .Z i = diagonal (fun a : Bits n => if a i then (-1 : ℂ) else 1) := by
  ext a b
  simp only [localPauli, pauliString, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    rw [Finset.prod_eq_single i]
    · simp [pauliEntry, QAlgorithms.pauliZ]
    · intro k _ hk; simp [hk, pauliEntry]
    · simp
  · rw [if_neg hab]
    obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
      by_contra h; push Not at h; exact hab (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    by_cases hki : k = i
    · simp [hki, pauliEntry, QAlgorithms.pauliZ, diagonal_apply]
      subst hki; simp [hk]
    · simp [hki, pauliEntry, hk]

def flipAt {n : ℕ} (i : Fin n) (a : Bits n) : Bits n := Function.update a i (!(a i))

lemma flipAt_flipAt {n : ℕ} (i : Fin n) (a : Bits n) : flipAt i (flipAt i a) = a := by
  funext k; unfold flipAt; by_cases h : k = i
  · subst h; simp
  · simp [Function.update_of_ne h]

lemma flipAt_comm {n : ℕ} (i j : Fin n) (a : Bits n) : flipAt i (flipAt j a) = flipAt j (flipAt i a) := by
  funext k; unfold flipAt
  by_cases hi : k = i <;> by_cases hj : k = j
  · subst hi; subst hj; rfl
  · subst hi; simp [Function.update_of_ne hj, Function.update_of_ne (Ne.symm hj)]
  · subst hj; simp [Function.update_of_ne hi, Function.update_of_ne (Ne.symm hi)]
  · simp [Function.update_of_ne hi, Function.update_of_ne hj]

lemma localX_eq {n : ℕ} (i : Fin n) :
    localPauli .X i = Matrix.of (fun a b : Bits n => if b = flipAt i a then (1 : ℂ) else 0) := by
  ext a b
  simp only [localPauli, pauliString, Matrix.of_apply]
  by_cases hb : b = flipAt i a
  · rw [if_pos hb]; subst hb
    apply Finset.prod_eq_one; intro k _
    by_cases hk : k = i
    · subst hk; simp [pauliEntry, QAlgorithms.pauliX, flipAt]
    · simp [hk, pauliEntry, flipAt, Function.update_apply, Matrix.one_apply]
  · rw [if_neg hb]
    have : ∃ k, ¬ (if k = i then a k ≠ b k else a k = b k) := by
      by_contra h; push Not at h; apply hb; funext k
      have := h k
      by_cases hk : k = i
      · subst hk; simp only [if_true] at this; unfold flipAt; simp
        cases ha : a k <;> cases hb' : b k <;> simp_all
      · simp only [hk, if_false] at this; unfold flipAt; rw [Function.update_of_ne hk]; exact this.symm
    obtain ⟨k, hk⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    by_cases hki : k = i
    · subst hki; simp only [if_true, not_not] at hk
      simp [pauliEntry, QAlgorithms.pauliX, hk]
    · simp only [hki, if_false] at hk
      simp [hki, pauliEntry, hk]

lemma perm_mul {n : ℕ} (f g : Bits n → Bits n) :
    (Matrix.of (fun a b : Bits n => if b = f a then (1 : ℂ) else 0)) *
      (Matrix.of (fun a b : Bits n => if b = g a then (1 : ℂ) else 0)) =
      Matrix.of (fun a b : Bits n => if b = g (f a) then (1 : ℂ) else 0) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']; simp

lemma X_comm {n : ℕ} (i j : Fin n) : Commute (localPauli .X i) (localPauli .X j) := by
  unfold Commute SemiconjBy
  rw [localX_eq, localX_eq, perm_mul, perm_mul]
  simp only [flipAt_comm j i]

lemma X_sq {n : ℕ} (i : Fin n) : localPauli .X i * localPauli .X i = 1 := by
  rw [localX_eq, perm_mul]
  ext a b; simp [flipAt_flipAt, Matrix.one_apply, eq_comm]

lemma pow_inv {n : ℕ} (A : QMat n) (hA : A * A = 1) (k : ℕ) : A ^ k = if Even k then 1 else A := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    by_cases hk : Even k
    · rw [if_pos hk, if_neg (by rw [Nat.even_add_one]; exact not_not.2 hk), one_mul]
    · rw [if_neg hk, if_pos (by rw [Nat.even_add_one]; exact hk), hA]

lemma hasSum_even_cosh (t : ℝ) :
    HasSum (fun k : ℕ => if Even k then t ^ k / (k ! : ℝ) else 0) (Real.cosh t) := by
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m) (fun a b h => by simpa using h) _)]
  · have e : (fun k : ℕ => if Even k then t ^ k / (k ! : ℝ) else 0) ∘ (fun m : ℕ => 2 * m) =
        fun m => t ^ (2 * m) / ((2 * m) ! : ℝ) := by
      funext m; simp
    rw [e]; exact Real.hasSum_cosh t
  · intro x hx; rw [if_neg]; rintro ⟨m, hm⟩; exact hx ⟨m, by simp only; omega⟩

lemma hasSum_odd_sinh (t : ℝ) :
    HasSum (fun k : ℕ => if Even k then 0 else t ^ k / (k ! : ℝ)) (Real.sinh t) := by
  rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m + 1) (fun a b h => by simpa using h) _)]
  · have e : (fun k : ℕ => if Even k then 0 else t ^ k / (k ! : ℝ)) ∘ (fun m : ℕ => 2 * m + 1) =
        fun m => t ^ (2 * m + 1) / ((2 * m + 1) ! : ℝ) := by
      funext m; simp [Nat.even_add_one]
    rw [e]; exact Real.hasSum_sinh t
  · intro x hx; rw [if_pos]; by_contra h
    obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.1 h
    exact hx ⟨m, by simp only; omega⟩

lemma exp_inv {n : ℕ} (A : QMat n) (hA : A * A = 1) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • A) = ((Real.cosh t : ℝ) : ℂ) • (1 : QMat n) + ((Real.sinh t : ℝ) : ℂ) • A := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  apply HasSum.tsum_eq
  have h1 := (Complex.hasSum_ofReal.2 (hasSum_even_cosh t)).smul_const (1 : QMat n)
  have h2 := (Complex.hasSum_ofReal.2 (hasSum_odd_sinh t)).smul_const A
  have e : (fun k : ℕ => ((k ! : ℂ)⁻¹) • (((t : ℂ) • A) ^ k)) = fun k =>
      ((if Even k then t ^ k / (k ! : ℝ) else 0 : ℝ) : ℂ) • (1 : QMat n) +
        ((if Even k then 0 else t ^ k / (k ! : ℝ) : ℝ) : ℂ) • A := by
    funext k
    rw [smul_pow, pow_inv A hA k, smul_smul]
    by_cases hk : Even k
    · rw [if_pos hk, if_pos hk, if_pos hk]; simp; ring
    · rw [if_neg hk, if_neg hk, if_neg hk]; simp; congr 1; ring
  rw [e]
  exact h1.add h2


instance u01_prob' : IsProbabilityMeasure TFIMPhaseDiagram.Classical.uniform01 :=
  ⟨by simp [TFIMPhaseDiagram.Classical.uniform01]⟩

lemma mass_nonneg (η : ℝ) (hη : 0 ≤ η) (p : Bool) (d : ℕ) : 0 ≤ parityMass η p d := by
  unfold parityMass
  split_ifs <;> try positivity

lemma mass_hasSum (η : ℝ) (hη : 0 ≤ η) (p : Bool) : HasSum (fun d => parityMass η p d) 1 := by
  by_cases h0 : η = 0
  · subst h0
    have : (fun d => parityMass 0 p d) = fun d => if d = (if p then 1 else 0) then 1 else 0 := by
      funext d; simp [parityMass]
    rw [this]
    convert hasSum_ite_eq (if p then 1 else 0) (1:ℝ)
  have hpos : 0 < η := lt_of_le_of_ne hη (Ne.symm h0)
  cases p
  · have hc := (Real.hasSum_cosh η).div_const (Real.cosh η)
    rw [div_self (Real.cosh_pos η).ne'] at hc
    rw [← (Function.Injective.hasSum_iff (g := fun n : ℕ => 2 * n) (fun a b h => by simpa using h) _)]
    · have e : (fun d => parityMass η false d) ∘ (fun n : ℕ => 2 * n) =
          fun i => η ^ (2 * i) / ↑(2 * i)! / Real.cosh η := by
        funext n; simp only [Function.comp, parityMass, h0, if_false, Bool.false_eq_true]
        rw [if_pos (by omega)]; field_simp
      rw [e]; exact hc
    · intro x hx
      simp only [parityMass, h0, if_false, Bool.false_eq_true]
      rw [if_neg]; intro h; exact hx ⟨x / 2, by show 2 * (x / 2) = x; omega⟩
  · have hs : 0 < Real.sinh η := Real.sinh_pos_iff.2 hpos
    have hc := (Real.hasSum_sinh η).div_const (Real.sinh η)
    rw [div_self hs.ne'] at hc
    rw [← (Function.Injective.hasSum_iff (g := fun n : ℕ => 2 * n + 1) (fun a b h => by simpa using h) _)]
    · have e : (fun d => parityMass η true d) ∘ (fun n : ℕ => 2 * n + 1) =
          fun i => η ^ (2 * i + 1) / ↑(2 * i + 1)! / Real.sinh η := by
        funext n; simp only [Function.comp, parityMass, h0, if_false, if_true]
        rw [if_pos (by omega)]; field_simp
      rw [e]; exact hc
    · intro x hx
      simp only [parityMass, h0, if_false, if_true]
      rw [if_neg]; intro h; exact hx ⟨x / 2, by show 2 * (x / 2) + 1 = x; omega⟩

lemma parityLaw_prob (η : ℝ) (hη : 0 ≤ η) (p : Bool) : IsProbabilityMeasure (parityLaw η p) := by
  constructor
  unfold parityLaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (mass_nonneg η hη p) (mass_hasSum η hη p).summable,
    (mass_hasSum η hη p).tsum_eq, ENNReal.ofReal_one]

instance bern_prob : IsProbabilityMeasure (finiteLaw (fun _ : Bool => (1/2 : ℝ))) := by
  constructor
  unfold finiteLaw
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]; norm_num

lemma pathLaw_prob (η : ℝ) (hη : 0 ≤ η) (p : Bool) : IsProbabilityMeasure (pathLaw η p) := by
  haveI := parityLaw_prob η hη p
  unfold pathLaw; infer_instance


abbrev Zs : QMat 1 := localPauli .Z 0
abbrev Xs : QMat 1 := localPauli .X 0

lemma sum_bits1 (f : Bits 1 → ℂ) : ∑ a, f a = f (fun _ => false) + f (fun _ => true) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  simp only [Equiv.funUnique_symm_apply]
  rw [add_comm]; rfl

lemma ZZ : Zs * Zs = 1 := by
  show localPauli .Z 0 * localPauli .Z 0 = 1
  rw [localZ_eq, diagonal_mul_diagonal]
  ext a b; simp only [diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

lemma ZX_anti : Zs * Xs + Xs * Zs = 0 := by
  show localPauli .Z 0 * localPauli .X 0 + localPauli .X 0 * localPauli .Z 0 = 0
  rw [localZ_eq, localX_eq]
  ext a b
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply,
    Matrix.zero_apply]
  by_cases hb : b = flipAt 0 a
  · subst hb; simp only [if_true, mul_one, one_mul]
    simp only [flipAt, Function.update_self]
    cases a 0 <;> simp
  · simp [hb]

lemma tr_Z : Matrix.trace Zs = 0 := by
  show Matrix.trace (localPauli .Z (0 : Fin 1)) = 0
  rw [localZ_eq, trace_diagonal, sum_bits1]; simp

lemma tr_X : Matrix.trace Xs = 0 := by
  show Matrix.trace (localPauli .X (0 : Fin 1)) = 0
  rw [localX_eq]; unfold Matrix.trace; rw [sum_bits1]
  simp only [Matrix.diag, Matrix.of_apply]
  have h1 : (fun _ : Fin 1 => false) ≠ flipAt 0 (fun _ => false) := fun h => by
    have := congrFun h 0; simp [flipAt] at this
  have h2 : (fun _ : Fin 1 => true) ≠ flipAt 0 (fun _ => true) := fun h => by
    have := congrFun h 0; simp [flipAt] at this
  rw [if_neg h1, if_neg h2]; simp

lemma tr_one : Matrix.trace (1 : QMat 1) = 2 := by
  rw [Matrix.trace_one]; simp

lemma sq_AB (a b : ℂ) : (a • Zs + b • Xs) * (a • Zs + b • Xs) = (a ^ 2 + b ^ 2) • (1 : QMat 1) := by
  have e : (a • Zs + b • Xs) * (a • Zs + b • Xs) =
      (a * a) • (Zs * Zs) + (a * b) • (Zs * Xs + Xs * Zs) + (b * b) • (Xs * Xs) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
    rw [mul_comm b a]; abel
  rw [e, ZZ, ZX_anti, X_sq]
  simp only [smul_zero, add_zero]
  rw [← add_smul]; ring_nf

lemma tr_exp_A (r η : ℝ) (hη : 0 < η) :
    Matrix.trace (NormedSpace.exp ((r : ℂ) • Zs + (η : ℂ) • Xs)) =
      ((2 * Real.cosh (Real.sqrt (η ^ 2 + r ^ 2)) : ℝ) : ℂ) := by
  set R := Real.sqrt (η ^ 2 + r ^ 2)
  have hR : 0 < R := Real.sqrt_pos.2 (by positivity)
  set A := (r : ℂ) • Zs + (η : ℂ) • Xs
  set B := ((1 / R : ℝ) : ℂ) • A
  have hB : B * B = 1 := by
    simp only [B, A]
    rw [smul_mul_smul_comm, sq_AB, smul_smul]
    have : ((1 / R : ℝ) : ℂ) * ((1 / R : ℝ) : ℂ) * ((r : ℂ) ^ 2 + (η : ℂ) ^ 2) = 1 := by
      have hR2 : R ^ 2 = η ^ 2 + r ^ 2 := Real.sq_sqrt (by positivity)
      have : ((r : ℂ) ^ 2 + (η : ℂ) ^ 2) = ((R ^ 2 : ℝ) : ℂ) := by rw [hR2]; push_cast; ring
      rw [this]; push_cast
      have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
      field_simp
    rw [this, one_smul]
  have hA : A = (R : ℂ) • B := by
    simp only [B]; rw [smul_smul]; push_cast
    rw [mul_one_div_cancel (by exact_mod_cast hR.ne'), one_smul]
  rw [hA, exp_inv B hB R, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, tr_one]
  have htB : Matrix.trace B = 0 := by
    simp only [B, A]; rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      tr_Z, tr_X]; simp
  rw [htB]; push_cast; ring

lemma tr_exp_X (η : ℝ) :
    Matrix.trace (NormedSpace.exp ((η : ℂ) • Xs)) = ((2 * Real.cosh η : ℝ) : ℂ) := by
  rw [exp_inv Xs (X_sq 0) η, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, tr_one, tr_X]
  push_cast; ring

end TFIMPhaseDiagram.Classical.P26M


namespace TFIMPhaseDiagram.Classical.P26Aux

lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hc := Real.cosh_pos x
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc.ne'
  have e : Real.sinh / Real.cosh = Real.tanh := by
    funext y; simp [Real.tanh_eq_sinh_div_cosh]
  rw [e] at h
  have h1 : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
    have := Real.cosh_sq_sub_sinh_sq x; nlinarith
  rw [h1] at h
  exact h

def gq (x : ℝ) : ℝ := Real.tanh x / x

lemma gq_strictAnti : StrictAntiOn gq (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (((hasDerivAt_tanh x).continuousAt).div continuousAt_id (ne_of_gt hx)).continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : (0:ℝ) < x := hx
    have hd : HasDerivAt gq ((1 / Real.cosh x ^ 2 * x - Real.tanh x * 1) / x ^ 2) x :=
      (hasDerivAt_tanh x).div (hasDerivAt_id x) hx0.ne'
    rw [hd.deriv]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have hc := Real.cosh_pos x
    have hs : 2 * x < Real.sinh (2 * x) := Real.self_lt_sinh_iff.2 (by linarith)
    rw [Real.sinh_two_mul] at hs
    rw [Real.tanh_eq_sinh_div_cosh]
    have : 1 / Real.cosh x ^ 2 * x - Real.sinh x / Real.cosh x * 1 =
        (x - Real.sinh x * Real.cosh x) / Real.cosh x ^ 2 := by field_simp
    rw [this]
    apply div_neg_of_neg_of_pos _ (by positivity)
    linarith

def rad (η r : ℝ) : ℝ := Real.sqrt (η ^ 2 + r ^ 2)

lemma rad_pos (η r : ℝ) (hη : 0 < η) : 0 < rad η r := Real.sqrt_pos.2 (by positivity)

lemma rad_sq (η r : ℝ) : rad η r ^ 2 = η ^ 2 + r ^ 2 := Real.sq_sqrt (by positivity)

lemma rad_ge (η r : ℝ) (hη : 0 ≤ η) : η ≤ rad η r :=
  Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg r])

lemma rad_strictMono (η b : ℝ) (hb : 0 < b) : StrictMonoOn (fun m => rad η (b * m)) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [rad]
  apply Real.sqrt_lt_sqrt (by positivity)
  have hx0 : 0 ≤ x := hx
  have hxy' : 0 < y + x := by linarith
  nlinarith [mul_pos (mul_pos hb hb) (mul_pos (sub_pos.2 hxy) hxy')]

lemma hasDerivAt_rad (η r : ℝ) (hη : 0 < η) : HasDerivAt (rad η) (r / rad η r) r := by
  have h := (hasDerivAt_pow 2 r).const_add (η ^ 2)
  have h2 := h.sqrt (by nlinarith [sq_nonneg r, sq_pos_of_pos hη] : (0:ℝ) < η ^ 2 + r ^ 2).ne'
  have e : r / rad η r = (2:ℕ) * r ^ (2 - 1) / (2 * Real.sqrt (η ^ 2 + r ^ 2)) := by
    unfold rad; push_cast; field_simp
  rw [e]; exact h2

def phiS (b η r : ℝ) : ℝ := Real.log (Real.cosh (rad η r) / Real.cosh η) - r ^ 2 / (2 * b)

lemma hasDerivAt_phiS (b η r : ℝ) (hη : 0 < η) :
    HasDerivAt (phiS b η) (r * (Real.tanh (rad η r) / rad η r - 1 / b)) r := by
  have hR := rad_pos η r hη
  have h1 : HasDerivAt (fun r => Real.cosh (rad η r) / Real.cosh η)
      (Real.sinh (rad η r) * (r / rad η r) / Real.cosh η) r :=
    ((Real.hasDerivAt_cosh _).comp r (hasDerivAt_rad η r hη)).div_const _
  have h2 := h1.log (by positivity)
  have h3 : HasDerivAt (fun r : ℝ => r ^ 2 / (2 * b)) (2 * r / (2 * b)) r := by
    have := ((hasDerivAt_id r).pow 2).div_const (2 * b); simpa using this
  have h4 := h2.sub h3
  have e : r * (Real.tanh (rad η r) / rad η r - 1 / b) =
      Real.sinh (rad η r) * (r / rad η r) / Real.cosh η / (Real.cosh (rad η r) / Real.cosh η) -
        2 * r / (2 * b) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    have := Real.cosh_pos (rad η r); have := Real.cosh_pos η
    by_cases hb : b = 0
    · subst hb; simp; field_simp
    · field_simp
  rw [e]
  exact h4


lemma gq_cont (x : ℝ) (hx : 0 < x) : ContinuousAt gq x :=
  ((hasDerivAt_tanh x).continuousAt).div continuousAt_id (ne_of_gt hx)

lemma rad_cont (η : ℝ) : Continuous (rad η) := by
  unfold rad; fun_prop

lemma rad_zero (η : ℝ) (hη : 0 ≤ η) : rad η 0 = η := by
  unfold rad; simp [Real.sqrt_sq hη]

lemma tanh_lt_one' (x : ℝ) : Real.tanh x < 1 := Real.tanh_lt_one x

theorem exists_unique_mag (b η : ℝ) (hb : 0 < b) (hη : 0 < η) (hsup : 1 < b / η * Real.tanh η) :
    ∃! m : ℝ, 0 < m ∧ m < 1 ∧ gq (rad η (b * m)) = 1 / b := by
  set F : ℝ → ℝ := fun m => gq (rad η (b * m))
  have hF0 : 1 / b < F 0 := by
    simp only [F, mul_zero, rad_zero η hη.le, gq]
    rw [div_lt_div_iff₀ hb hη]
    have : b / η * Real.tanh η * η = b * Real.tanh η := by field_simp
    nlinarith
  have hF1 : F 1 < 1 / b := by
    simp only [F, mul_one]
    have h1 : b < rad η b := by
      unfold rad
      rw [show b = Real.sqrt (b ^ 2) from (Real.sqrt_sq hb.le).symm]
      apply Real.sqrt_lt_sqrt (by positivity)
      rw [Real.sq_sqrt (by positivity)]; nlinarith
    have h2 : gq (rad η b) < gq b := gq_strictAnti (show (0:ℝ) < b from hb)
      (show (0:ℝ) < rad η b from rad_pos η b hη) h1
    have h3 : gq b < 1 / b := by
      unfold gq; exact div_lt_div_of_pos_right (tanh_lt_one' b) hb
    linarith
  have hcont : ContinuousOn F (Set.Icc 0 1) := by
    intro m hm
    have h1 : ContinuousAt (fun m : ℝ => rad η (b * m)) m :=
      ((rad_cont η).comp (continuous_const.mul continuous_id)).continuousAt
    exact (ContinuousAt.comp (f := fun m : ℝ => rad η (b * m)) (gq_cont _ (rad_pos η _ hη)) h1).continuousWithinAt
  have hanti : StrictAntiOn F (Set.Ici 0) := by
    intro x hx y hy hxy
    exact gq_strictAnti (rad_pos η _ hη) (rad_pos η _ hη) (rad_strictMono η b hb hx hy hxy)
  obtain ⟨m, hm, hFm⟩ := intermediate_value_Ioo' (zero_le_one) hcont ⟨hF1, hF0⟩
  refine ⟨m, ⟨hm.1, hm.2, hFm⟩, ?_⟩
  rintro m' ⟨h1, h2, h3⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := hanti (show (0:ℝ) ≤ m' from h1.le) (show (0:ℝ) ≤ m from hm.1.le) hlt
    have hFm' : gq (rad η (b * m)) = 1 / b := hFm
    simp only [F] at this; rw [h3, hFm'] at this; exact lt_irrefl _ this
  · have := hanti (show (0:ℝ) ≤ m from hm.1.le) (show (0:ℝ) ≤ m' from h1.le) hlt
    have hFm' : gq (rad η (b * m)) = 1 / b := hFm
    simp only [F] at this; rw [h3, hFm'] at this; exact lt_irrefl _ this


def psiF (b η t : ℝ) : ℝ := Real.log (Real.cosh t / Real.cosh η) - (t ^ 2 - η ^ 2) / (2 * b)
def GF (b t : ℝ) : ℝ := Real.tanh t - t / b

lemma phiS_eq (b η r : ℝ) : phiS b η r = psiF b η (rad η r) := by
  unfold phiS psiF; rw [rad_sq]; ring_nf

lemma hasDerivAt_psiF (b η t : ℝ) : HasDerivAt (psiF b η) (GF b t) t := by
  have h1 : HasDerivAt (fun t => Real.cosh t / Real.cosh η) (Real.sinh t / Real.cosh η) t :=
    (Real.hasDerivAt_cosh t).div_const _
  have h2 := h1.log (by have := Real.cosh_pos t; have := Real.cosh_pos η; positivity)
  have h3 : HasDerivAt (fun t : ℝ => (t ^ 2 - η ^ 2) / (2 * b)) (2 * t / (2 * b)) t := by
    have := (((hasDerivAt_pow 2 t)).sub_const (η ^ 2)).div_const (2 * b)
    simpa using this
  have h4 := h2.sub h3
  have e : GF b t = Real.sinh t / Real.cosh η / (Real.cosh t / Real.cosh η) - 2 * t / (2 * b) := by
    unfold GF; rw [Real.tanh_eq_sinh_div_cosh]
    have := Real.cosh_pos t; have := Real.cosh_pos η
    by_cases hb : b = 0
    · subst hb; simp; field_simp
    · field_simp
  rw [e]; exact h4

lemma GF_concave (b : ℝ) (hb : 0 < b) : ConcaveOn ℝ (Set.Ici 0) (GF b) := by
  have hd : ∀ t, HasDerivAt (GF b) (1 / Real.cosh t ^ 2 - 1 / b) t := by
    intro t; unfold GF
    exact (hasDerivAt_tanh t).sub ((hasDerivAt_id' t).div_const b)
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
  · exact fun t _ => (hd t).continuousAt.continuousWithinAt
  · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro s hs t ht hst
    rw [(hd s).deriv, (hd t).deriv]
    have hs0 : (0:ℝ) < s := hs
    have hc : Real.cosh s ≤ Real.cosh t := Real.cosh_le_cosh.2 (by
      rw [abs_of_pos hs0, abs_of_pos (lt_of_lt_of_le hs0 hst)]; exact hst)
    have hcs := Real.cosh_pos s
    have : 1 / Real.cosh t ^ 2 ≤ 1 / Real.cosh s ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hcs.le hc 2)
    linarith

theorem quad_gap (b η : ℝ) (hb : 0 < b) (hη : 0 < η) (hsup : 1 < b / η * Real.tanh η)
    (ms : ℝ) (hms0 : 0 < ms) (hmsG : gq (rad η (b * ms)) = 1 / b) (m : ℝ) (hm : 0 ≤ m) :
    η * (b / η * Real.tanh η - 1) / 8 * (m - ms) ^ 2 ≤ phiS b η (b * ms) - phiS b η (b * m) := by
  set Rs := rad η (b * ms)
  set R := rad η (b * m)
  have hRs0 : 0 < Rs := rad_pos η _ hη
  have hR0 : 0 < R := rad_pos η _ hη
  have hRsη : η < Rs := by
    have h1 : Rs ^ 2 = η ^ 2 + (b * ms) ^ 2 := rad_sq η _
    have : η ^ 2 < Rs ^ 2 := by rw [h1]; have := mul_pos hb hms0; nlinarith
    nlinarith
  have hRη : η ≤ R := rad_ge η _ hη.le
  have hGRs : GF b Rs = 0 := by
    unfold GF; unfold gq at hmsG
    rw [div_eq_div_iff hRs0.ne' hb.ne'] at hmsG
    field_simp; linarith
  have hGη : 0 < GF b η := by
    unfold GF
    have : b / η * Real.tanh η * η = b * Real.tanh η := by field_simp
    rw [sub_pos, div_lt_iff₀ hb]; nlinarith
  have hRsb : Rs ^ 2 ≤ b * (Rs + η) := by
    have ht : Real.tanh Rs < 1 := Real.tanh_lt_one Rs
    have hRseq : Rs = b * Real.tanh Rs := by
      have h := hGRs; unfold GF at h
      have : Rs / b = Real.tanh Rs := by linarith
      rw [div_eq_iff hb.ne'] at this; linarith
    have h1 : b * Real.tanh Rs < b * 1 := mul_lt_mul_of_pos_left ht hb
    have h2 : Rs < b := by linarith
    have h3 : Rs * Rs < b * Rs := mul_lt_mul_of_pos_right h2 hRs0
    have h4 : 0 ≤ b * η := mul_nonneg hb.le hη.le
    nlinarith
  set c0 := GF b η / (Rs - η)
  have hc0 : 0 < c0 := div_pos hGη (by linarith)
  have hconc := GF_concave b hb
  have lin_below : ∀ t, η ≤ t → t ≤ Rs → c0 * (Rs - t) ≤ GF b t := by
    intro t h1 h2
    have hd : 0 < Rs - η := by linarith
    have ha : 0 ≤ (Rs - t) / (Rs - η) := div_nonneg (by linarith) hd.le
    have hb' : 0 ≤ (t - η) / (Rs - η) := div_nonneg (by linarith) hd.le
    have hab : (Rs - t) / (Rs - η) + (t - η) / (Rs - η) = 1 := by field_simp; ring
    have := hconc.2 (show η ∈ Set.Ici (0:ℝ) from hη.le) (show Rs ∈ Set.Ici (0:ℝ) from hRs0.le) ha hb' hab
    simp only [smul_eq_mul, hGRs, mul_zero, add_zero] at this
    have e : (Rs - t) / (Rs - η) * η + (t - η) / (Rs - η) * Rs = t := by field_simp; ring
    rw [e] at this
    calc c0 * (Rs - t) = (Rs - t) / (Rs - η) * GF b η := by simp only [c0]; field_simp
      _ ≤ GF b t := this
  have lin_above : ∀ t, Rs ≤ t → GF b t ≤ -(c0 * (t - Rs)) := by
    intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, hGRs, sub_self, mul_zero, neg_zero]
    have hd : 0 < t - η := by linarith
    have hd' : 0 < Rs - η := by linarith
    have ha : 0 ≤ (t - Rs) / (t - η) := div_nonneg (by linarith) hd.le
    have hb' : 0 ≤ (Rs - η) / (t - η) := div_nonneg (by linarith) hd.le
    have hab : (t - Rs) / (t - η) + (Rs - η) / (t - η) = 1 := by field_simp; ring
    have := hconc.2 (show η ∈ Set.Ici (0:ℝ) from hη.le) (show t ∈ Set.Ici (0:ℝ) by
      show (0:ℝ) ≤ t; linarith) ha hb' hab
    simp only [smul_eq_mul] at this
    have e : (t - Rs) / (t - η) * η + (Rs - η) / (t - η) * t = Rs := by field_simp; ring
    rw [e, hGRs] at this
    have k2 : (t - Rs) * GF b η + (Rs - η) * GF b t ≤ 0 := by
      have e2 : (t - Rs) * GF b η + (Rs - η) * GF b t =
          (t - η) * ((t - Rs) / (t - η) * GF b η + (Rs - η) / (t - η) * GF b t) := by
        field_simp
      rw [e2]; exact mul_nonpos_of_nonneg_of_nonpos hd.le this
    have e3 : -(c0 * (t - Rs)) = -(GF b η * (t - Rs)) / (Rs - η) := by
      simp only [c0]; field_simp
    rw [e3, le_div_iff₀ hd']
    linarith
  -- integrated gap for psi
  have gap_psi : c0 / 2 * (R - Rs) ^ 2 ≤ psiF b η Rs - psiF b η R := by
    set K : ℝ → ℝ := fun t => psiF b η t + c0 / 2 * (t - Rs) ^ 2
    have hK : ∀ t, HasDerivAt K (GF b t + c0 * (t - Rs)) t := by
      intro t
      have h1 := (hasDerivAt_psiF b η t).add ((((hasDerivAt_id' t).sub_const Rs).pow 2).const_mul (c0 / 2))
      have e : GF b t + c0 * (t - Rs) = GF b t + c0 / 2 * (((2:ℕ):ℝ) * (t - Rs) ^ (2 - 1) * 1) := by
        norm_num; ring
      rw [e]; exact h1
    have hKc : Continuous K := continuous_iff_continuousAt.2 (fun t => (hK t).continuousAt)
    have hKd : Differentiable ℝ K := fun t => (hK t).differentiableAt
    have hKR : K R ≤ K Rs := by
      rcases le_total R Rs with hle | hle
      · have hmono := monotoneOn_of_deriv_nonneg (convex_Icc R Rs) hKc.continuousOn
          hKd.differentiableOn (fun t ht => by
            rw [interior_Icc] at ht
            rw [(hK t).deriv]
            have := lin_below t (by linarith [ht.1]) ht.2.le
            linarith)
        exact hmono ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
      · have hanti := antitoneOn_of_deriv_nonpos (convex_Icc Rs R) hKc.continuousOn
          hKd.differentiableOn (fun t ht => by
            rw [interior_Icc] at ht
            rw [(hK t).deriv]
            have := lin_above t ht.1.le
            linarith)
        exact hanti ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
    have : K Rs = psiF b η Rs := by simp [K]
    rw [this] at hKR
    simp only [K] at hKR
    linarith
  -- distance bound
  set u := b * ms
  set x := b * m
  have hu0 : 0 < u := mul_pos hb hms0
  have hx0 : 0 ≤ x := mul_nonneg hb.le hm
  have hRsq : R ^ 2 = η ^ 2 + x ^ 2 := rad_sq η _
  have hRssq : Rs ^ 2 = η ^ 2 + u ^ 2 := rad_sq η _
  have hRle : R ≤ η + x := by
    show Real.sqrt (η ^ 2 + x ^ 2) ≤ η + x
    rw [show η + x = Real.sqrt ((η + x) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have huRs : u ≤ Rs := by
    show u ≤ Real.sqrt (η ^ 2 + u ^ 2)
    rw [show u = Real.sqrt (u ^ 2) from (Real.sqrt_sq hu0.le).symm]
    apply Real.sqrt_le_sqrt
    rw [Real.sq_sqrt (sq_nonneg u)]; nlinarith
  have hsum : 0 < R + Rs := by linarith
  have hfac : (R - Rs) * (R + Rs) = (x - u) * (x + u) := by
    have : R ^ 2 - Rs ^ 2 = x ^ 2 - u ^ 2 := by rw [hRsq, hRssq]; ring
    linear_combination this
  have hkey : u * (R + Rs) ≤ 2 * Rs * (x + u) := by
    have h1 : u * R ≤ u * (η + x) := mul_le_mul_of_nonneg_left hRle hu0.le
    have h2 : u * η ≤ u * Rs := mul_le_mul_of_nonneg_left hRsη.le hu0.le
    have h3 : u * x ≤ Rs * x := mul_le_mul_of_nonneg_right huRs hx0
    have h4 : u * Rs ≤ Rs * Rs := mul_le_mul_of_nonneg_right huRs hRs0.le
    nlinarith
  have hdist : (x - u) ^ 2 * u ^ 2 / (4 * Rs ^ 2) ≤ (R - Rs) ^ 2 := by
    have h4R : (0:ℝ) < 4 * Rs ^ 2 := by positivity
    rw [div_le_iff₀ h4R]
    have hk2 : (u * (R + Rs)) ^ 2 ≤ (2 * Rs * (x + u)) ^ 2 := pow_le_pow_left₀ (by positivity) hkey 2
    have hsq : (R - Rs) ^ 2 * (R + Rs) ^ 2 = (x - u) ^ 2 * (x + u) ^ 2 := by
      rw [← mul_pow, ← mul_pow, hfac]
    have hpos : 0 < (R + Rs) ^ 2 := by positivity
    have : (x - u) ^ 2 * u ^ 2 * (R + Rs) ^ 2 ≤ (R - Rs) ^ 2 * (4 * Rs ^ 2) * (R + Rs) ^ 2 := by
      calc (x - u) ^ 2 * u ^ 2 * (R + Rs) ^ 2 = (x - u) ^ 2 * (u * (R + Rs)) ^ 2 := by ring
        _ ≤ (x - u) ^ 2 * (2 * Rs * (x + u)) ^ 2 := mul_le_mul_of_nonneg_left hk2 (sq_nonneg _)
        _ = 4 * Rs ^ 2 * ((x - u) ^ 2 * (x + u) ^ 2) := by ring
        _ = (R - Rs) ^ 2 * (4 * Rs ^ 2) * (R + Rs) ^ 2 := by rw [← hsq]; ring
    exact le_of_mul_le_mul_right this hpos
  have hxu : (x - u) ^ 2 = b ^ 2 * (m - ms) ^ 2 := by simp only [x, u]; ring
  -- constant comparison
  have hgap : η * (b / η * Real.tanh η - 1) / 8 = b * GF b η / 8 := by
    unfold GF; field_simp
  rw [phiS_eq, phiS_eq, hgap]
  have hd' : 0 < Rs - η := by linarith
  have hconst : b * GF b η / 8 ≤ c0 / 2 * (b ^ 2 * u ^ 2 / (4 * Rs ^ 2)) := by
    have e : c0 / 2 * (b ^ 2 * u ^ 2 / (4 * Rs ^ 2)) =
        b * GF b η / 8 * (b * u ^ 2 / (Rs ^ 2 * (Rs - η))) := by
      simp only [c0]; field_simp; norm_num
    rw [e]
    apply le_mul_of_one_le_right (by positivity)
    rw [one_le_div (by positivity)]
    have hu2 : u ^ 2 = (Rs - η) * (Rs + η) := by
      rw [show (Rs - η) * (Rs + η) = Rs ^ 2 - η ^ 2 by ring, hRssq]; ring
    calc Rs ^ 2 * (Rs - η) ≤ b * (Rs + η) * (Rs - η) := mul_le_mul_of_nonneg_right hRsb hd'.le
      _ = b * u ^ 2 := by rw [hu2]; ring
  calc b * GF b η / 8 * (m - ms) ^ 2 ≤ c0 / 2 * (b ^ 2 * u ^ 2 / (4 * Rs ^ 2)) * (m - ms) ^ 2 :=
        mul_le_mul_of_nonneg_right hconst (sq_nonneg _)
    _ = c0 / 2 * ((x - u) ^ 2 * u ^ 2 / (4 * Rs ^ 2)) := by rw [hxu]; ring
    _ ≤ c0 / 2 * (R - Rs) ^ 2 := mul_le_mul_of_nonneg_left hdist (by positivity)
    _ ≤ psiF b η Rs - psiF b η R := gap_psi

end TFIMPhaseDiagram.Classical.P26Aux

namespace TFIMPhaseDiagram.Classical.Supplement.P26F
open TFIMPhaseDiagram.Classical TFIMPhaseDiagram.Classical.Supplement
  TFIMPhaseDiagram.Classical.Supplement.P26A TFIMPhaseDiagram.Classical.P26M
  TFIMPhaseDiagram.Classical.P26Aux MeasureTheory

lemma pauli_all_I : pauliString (fun _ : Fin 1 => Pauli.I) = 1 := by
  ext a b
  simp only [pauliString, pauliEntry, Matrix.one_apply]
  rw [Fin.prod_univ_one]
  by_cases h : a = b
  · subst h; simp
  · have : a 0 ≠ b 0 := fun e => h (funext (fun k => by rw [Subsingleton.elim k 0]; exact e))
    simp [h, this]

lemma ham_eq (r η : ℝ) : hamiltonian (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => r) (fun _ => η) =
    (r : ℂ) • Zs + (η : ℂ) • Xs := by
  unfold hamiltonian hz hx
  simp [Fin.sum_univ_one]

lemma hx_eq (η : ℝ) : hx (fun _ : Fin 1 => η) = (η : ℂ) • Xs := by
  unfold hx; simp [Fin.sum_univ_one]

lemma pathValue_joint : Measurable (fun q : PathData × ℝ => pathValue q.1 q.2) := by
  have e : (fun q : PathData × ℝ => pathValue q.1 q.2) =
      (fun r : ℕ × ((Bool × (ℕ → ℝ)) × ℝ) => spin r.2.1.1 *
        (-1 : ℝ) ^ ((Finset.range r.1).filter (fun j => r.2.1.2 j ≤ r.2.2)).card) ∘
        (MeasurableEquiv.prodAssoc : (ℕ × (Bool × (ℕ → ℝ))) × ℝ ≃ᵐ ℕ × ((Bool × (ℕ → ℝ)) × ℝ)) := by
    funext q; rfl
  rw [e]
  refine Measurable.comp ?_ MeasurableEquiv.prodAssoc.measurable
  apply measurable_from_prod_countable_right
  intro d
  simp only
  apply Measurable.mul
  · exact (measurable_of_countable (fun b : Bool => spin b)).comp (measurable_fst.comp measurable_fst)
  · apply (measurable_of_countable (fun n : ℕ => (-1 : ℝ) ^ n)).comp
    have : (fun y : (Bool × (ℕ → ℝ)) × ℝ => ((Finset.range d).filter (fun j => y.1.2 j ≤ y.2)).card) =
        fun y => ∑ j ∈ Finset.range d, (if y.1.2 j ≤ y.2 then 1 else 0) := by
      funext y; rw [Finset.card_filter]
    rw [this]
    exact Finset.measurable_sum _ (fun j _ => Measurable.ite
      (measurableSet_le ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)) measurable_snd)
      measurable_const measurable_const)

lemma pv_int_meas : Measurable (fun τ : PathData => ∫ t, pathValue τ t ∂circleVolume) := by
  have hF : StronglyMeasurable (fun q : PathData × ℝ => pathValue q.1 q.2) :=
    pathValue_joint.stronglyMeasurable
  exact (hF.integral_prod_right (ν := circleVolume)).measurable

theorem expect_eq (r η : ℝ) (hη : 0 < η) :
    ∫ τ, Real.exp (r * ∫ t, pathValue τ t ∂circleVolume) ∂pathLaw η false =
      Real.cosh (Real.sqrt (η ^ 2 + r ^ 2)) / Real.cosh η := by
  set P1 : Fin 1 → Pauli := fun _ => .I
  obtain ⟨-, -, -, -, hid, -, -⟩ := TFIMPhaseDiagram.Classical.prop_8 (n := 1) one_pos
    (0 : Matrix (Fin 1) (Fin 1) ℝ) (by simp [Matrix.IsSymm]) (fun _ => r) (fun _ => η)
    (fun _ => hη.le) P1 3 le_rfl
  have hy : yCount P1 = 0 := by simp [yCount, P1]
  have hps : ∀ σ, pathSign P1 σ = 1 := by intro σ; simp [pathSign, P1]
  have hflip : flipSet P1 = ∅ := by simp [flipSet, P1, hasFlip]
  have hxs : xSubset (∅ : Finset (Fin 1)) = 1 := by
    rw [show xSubset (∅ : Finset (Fin 1)) = pauliString (fun _ : Fin 1 => Pauli.I) by
      unfold xSubset; congr 1]
    exact pauli_all_I
  simp only [hy, pow_zero, one_mul, hps, mul_one, hflip, hxs] at hid
  rw [show pauliString P1 = 1 from pauli_all_I, one_mul] at hid
  unfold matrixExp at hid
  rw [ham_eq, tr_exp_A r η hη, hx_eq, tr_exp_X] at hid
  -- identify the integral
  haveI : IsProbabilityMeasure (pathLaw η false) := pathLaw_prob η hη.le false
  have hint : ∫ σ, Real.exp (pathPotential (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => r) σ) ∂nu (fun _ => η) P1 =
      ∫ τ, Real.exp (r * ∫ t, pathValue τ t ∂circleVolume) ∂pathLaw η false := by
    have hnu : nu (fun _ => η) P1 = Measure.pi (fun _ : Fin 1 => pathLaw η false) := by
      unfold nu; rfl
    rw [hnu]
    have hmp := measurePreserving_eval (fun _ : Fin 1 => pathLaw η false) 0
    have hpot : ∀ σ : Fin 1 → PathData, pathPotential (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => r) σ =
        r * ∫ t, pathValue (σ 0) t ∂circleVolume := by
      intro σ
      unfold pathPotential potential circleVolume
      simp only [Matrix.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, zero_add,
        Fin.sum_univ_one]
      rw [integral_Icc_eq_integral_Ico, integral_const_mul]
    simp only [hpot]
    conv_rhs => rw [← hmp.map_eq]
    rw [integral_map (measurable_pi_apply 0).aemeasurable
      (Real.measurable_exp.comp (pv_int_meas.const_mul r)).aestronglyMeasurable]
  rw [hint] at hid
  have hc : (0:ℝ) < Real.cosh η := Real.cosh_pos η
  have h2 : ((2 * Real.cosh (Real.sqrt (η ^ 2 + r ^ 2)) : ℝ) : ℂ) =
      ((2 * Real.cosh η * ∫ τ, Real.exp (r * ∫ t, pathValue τ t ∂circleVolume) ∂pathLaw η false : ℝ) : ℂ) := by
    rw [hid]; push_cast; ring
  have h3 := Complex.ofReal_injective h2
  field_simp
  linarith


lemma cumulant_const (r η : ℝ) (hη : 0 < η) :
    cumulant η (constL2 r) = Real.log (Real.cosh (Real.sqrt (η ^ 2 + r ^ 2)) / Real.cosh η) := by
  unfold cumulant nuL2
  have hm : AEStronglyMeasurable (fun σ : CircleL2 => Real.exp (inner ℝ (constL2 r) σ))
      (Measure.map pathL2 (pathLaw η false)) :=
    (Real.continuous_exp.comp (continuous_const.inner continuous_id)).aestronglyMeasurable
  rw [integral_map P26A.pathL2_meas.aemeasurable hm]
  simp only [P26A.inner_path]
  rw [expect_eq r η hη]

lemma circleVolume_univ : circleVolume.real Set.univ = 1 := by
  unfold circleVolume
  simp [Measure.real]

lemma norm_constL2_sq (r : ℝ) : ‖constL2 r‖ ^ 2 = r ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  have hc : (constL2 r : ℝ → ℝ) =ᵐ[circleVolume] fun _ => r := MemLp.coeFn_toLp _
  have h2 : (fun a => inner ℝ ((constL2 r : ℝ → ℝ) a) ((constL2 r : ℝ → ℝ) a))
      =ᵐ[circleVolume] fun _ => r * r :=
    hc.mono (fun x hx => by simp only [hx, RCLike.inner_apply, conj_trivial])
  rw [integral_congr_ae h2, integral_const, smul_eq_mul, circleVolume_univ]
  ring

lemma scalarPhi_eq (b η r : ℝ) (hη : 0 < η) : scalarPhi b η r = P26Aux.phiS b η r := by
  unfold scalarPhi phi P26Aux.phiS P26Aux.rad
  rw [cumulant_const r η hη, norm_constL2_sq]

end TFIMPhaseDiagram.Classical.Supplement.P26F

open TFIMPhaseDiagram.Classical.Supplement in
theorem solution (b η : ℝ) (h : supercritical b η) :
    (∀ r : ℝ, HasDerivAt (scalarPhi b η)
      (r * (Real.tanh (radius η r) / radius η r - 1/b)) r) ∧
    (∃! m : ℝ, IsMagnetization b η m) ∧
    IsMagnetization b η (magnetization b η) ∧
    (deriv (scalarPhi b η) (b * magnetization b η) = 0 ↔
      Real.tanh (radius η (b * magnetization b η)) /
        radius η (b * magnetization b η) = 1/b) ∧
    0 < scalarGap b η ∧
    (∀ m : ℝ, 0 ≤ m → scalarGap b η * (m - magnetization b η)^2 ≤
      scalarPhi b η (b * magnetization b η) - scalarPhi b η (b*m)) := by
  obtain ⟨hb, hη, hsup⟩ := h
  have hfun : scalarPhi b η = TFIMPhaseDiagram.Classical.P26Aux.phiS b η :=
    funext (fun r => P26F.scalarPhi_eq b η r hη)
  have hD : ∀ r : ℝ, HasDerivAt (scalarPhi b η)
      (r * (Real.tanh (radius η r) / radius η r - 1/b)) r := by
    intro r; rw [hfun]; exact TFIMPhaseDiagram.Classical.P26Aux.hasDerivAt_phiS b η r hη
  have hEU : ∃! m : ℝ, IsMagnetization b η m :=
    TFIMPhaseDiagram.Classical.P26Aux.exists_unique_mag b η hb hη hsup
  have hex : ∃ m, IsMagnetization b η m := hEU.exists
  have hM : IsMagnetization b η (magnetization b η) := by
    unfold magnetization; rw [dif_pos hex]; exact Classical.choose_spec hex
  refine ⟨hD, hEU, hM, ?_, ?_, ?_⟩
  · rw [(hD _).deriv]
    have hm0 := hM.1
    have hne : b * magnetization b η ≠ 0 := (mul_pos hb hm0).ne'
    constructor
    · intro h0
      have := (mul_eq_zero.1 h0).resolve_left hne
      linarith
    · intro h1; rw [h1]; ring
  · unfold scalarGap
    have : 0 < b / η * Real.tanh η - 1 := by linarith
    positivity
  · intro m hm
    rw [hfun]
    exact TFIMPhaseDiagram.Classical.P26Aux.quad_gap b η hb hη hsup _ hM.1 hM.2.2 m hm


-- Prove2me | solution 1 for TFIMPhaseDiagram.Classical.Supplement.lemma_27
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:18:15.619512+00:00
-- url     : https://prove2.me/submissions/25216146-603b-4b3d-b933-536b5fab7567
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_TFIMPhaseDiagram_Classical_Supplement_deviations
import Theorems.Thm_TFIMPhaseDiagram_Classical_prop_8
import Theorems.Thm_TFIMPhaseDiagram_Classical_Supplement_cumulant_le_integral_const

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

set_option linter.unusedSectionVars false
section P30Msec
open scoped Nat
namespace TFIMPhaseDiagram.Classical.P30M

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ν : Measure ℝ} [IsFiniteMeasure ν]

/-- `X g ω = ∫ g(t) w(ω,t) dν(t)`. -/
def X (ν : Measure ℝ) (w : Ω → ℝ → ℝ) (g : ℝ → ℝ) (ω : Ω) : ℝ := ∫ t, g t * w ω t ∂ν

lemma X_bound (w : Ω → ℝ → ℝ) (hw : ∀ ω t, |w ω t| ≤ 1) (g : ℝ → ℝ) (hg : Integrable g ν)
    (ω : Ω) : |X ν w g ω| ≤ ∫ t, |g t| ∂ν := by
  unfold X
  refine (abs_integral_le_integral_abs).trans ?_
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => abs_nonneg _) hg.abs
  exact Filter.Eventually.of_forall fun t => by
    show |g t * w ω t| ≤ |g t|
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hw ω t)

lemma X_meas (w : Ω → ℝ → ℝ) (hw : Measurable (Function.uncurry w)) (g : ℝ → ℝ)
    (hg : Measurable g) : Measurable (X ν w g) := by
  have h : StronglyMeasurable (fun p : Ω × ℝ => g p.2 * w p.1 p.2) :=
    ((hg.comp measurable_snd).mul hw).stronglyMeasurable
  exact (h.integral_prod_right (ν := ν)).measurable

/-- Moment identity: `E[X^n] = ∫ ∏ g(t_i) · c(t) d(ν^n)` with `c(t) = E ∏ w(·,t_i)`. -/
lemma moment_eq (w : Ω → ℝ → ℝ) (hw : ∀ ω t, |w ω t| ≤ 1) (hwm : Measurable (Function.uncurry w))
    (g : ℝ → ℝ) (hg : Integrable g ν) (hgm : Measurable g) (n : ℕ) :
    ∫ ω, X ν w g ω ^ n ∂μ =
      ∫ t : Fin n → ℝ, (∏ i, g (t i)) * ∫ ω, ∏ i, w ω (t i) ∂μ ∂(Measure.pi fun _ => ν) := by
  have hpow : ∀ ω, X ν w g ω ^ n =
      ∫ t : Fin n → ℝ, ∏ i, (g (t i) * w ω (t i)) ∂(Measure.pi fun _ => ν) := by
    intro ω
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin n) (s : ℝ) => g s * w ω s)]
    simp [X]
  simp_rw [hpow]
  have hint : Integrable (Function.uncurry fun (ω : Ω) (t : Fin n → ℝ) => ∏ i, (g (t i) * w ω (t i)))
      (μ.prod (Measure.pi fun _ => ν)) := by
    have hbound : Integrable (fun p : Ω × (Fin n → ℝ) => ∏ i, |g (p.2 i)|)
        (μ.prod (Measure.pi fun _ => ν)) := by
      have : Integrable (fun t : Fin n → ℝ => ∏ i, |g (t i)|) (Measure.pi fun _ => ν) :=
        Integrable.fintype_prod (f := fun (_ : Fin n) (s : ℝ) => |g s|) (fun _ => hg.abs)
      exact this.comp_snd μ
    refine hbound.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · apply Measurable.aestronglyMeasurable
      apply Finset.measurable_prod
      intro i _
      exact (hgm.comp ((measurable_pi_apply i).comp measurable_snd)).mul
        (hwm.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
    · simp only [Function.uncurry, Real.norm_eq_abs, Finset.abs_prod]
      apply Finset.prod_le_prod (fun i _ => abs_nonneg _)
      intro i _
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hw _ _)
  rw [integral_integral_swap hint]
  congr 1; funext t
  simp_rw [Finset.prod_mul_distrib]
  rw [integral_const_mul]


lemma moment_le (w : Ω → ℝ → ℝ) (hw : ∀ ω t, |w ω t| ≤ 1) (hwm : Measurable (Function.uncurry w))
    (hc : ∀ (m : ℕ) (t : Fin m → ℝ), 0 ≤ ∫ ω, ∏ i, w ω (t i) ∂μ)
    (g : ℝ → ℝ) (hg : Integrable g ν) (hgm : Measurable g) (n : ℕ) :
    ∫ ω, X ν w g ω ^ n ∂μ ≤ ∫ ω, X ν w (fun t => |g t|) ω ^ n ∂μ := by
  rw [moment_eq w hw hwm g hg hgm n, moment_eq w hw hwm _ hg.abs hgm.abs n]
  have hcm : Measurable (fun t : Fin n → ℝ => ∫ ω, ∏ i, w ω (t i) ∂μ) := by
    have h : StronglyMeasurable (fun p : (Fin n → ℝ) × Ω => ∏ i, w p.2 (p.1 i)) := by
      apply Measurable.stronglyMeasurable
      apply Finset.measurable_prod
      intro i _
      exact hwm.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))
    exact (h.integral_prod_right (ν := μ)).measurable
  have hcb : ∀ t : Fin n → ℝ, |∫ ω, ∏ i, w ω (t i) ∂μ| ≤ 1 := by
    intro t
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |∏ i, w ω (t i)| ∂μ ≤ ∫ _ω, (1:ℝ) ∂μ := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
            (integrable_const _)
          exact Filter.Eventually.of_forall fun ω => by
            show |∏ i, w ω (t i)| ≤ 1
            rw [Finset.abs_prod]
            exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => hw _ _)
      _ = 1 := by simp
  have hP : Integrable (fun t : Fin n → ℝ => ∏ i, |g (t i)|) (Measure.pi fun _ => ν) :=
    Integrable.fintype_prod (f := fun (_ : Fin n) (s : ℝ) => |g s|) (fun _ => hg.abs)
  have hgP : Measurable (fun t : Fin n → ℝ => ∏ i, g (t i)) :=
    Finset.measurable_prod _ (fun i _ => hgm.comp (measurable_pi_apply i))
  have hgaP : Measurable (fun t : Fin n → ℝ => ∏ i, |g (t i)|) :=
    Finset.measurable_prod _ (fun i _ => hgm.abs.comp (measurable_pi_apply i))
  have hint : ∀ G : (Fin n → ℝ) → ℝ, Measurable G → (∀ t, |G t| ≤ ∏ i, |g (t i)|) →
      Integrable (fun t => G t * ∫ ω, ∏ i, w ω (t i) ∂μ) (Measure.pi fun _ => ν) := by
    intro G hG hGb
    refine hP.mono' (hG.mul hcm).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |G t| * |∫ ω, ∏ i, w ω (t i) ∂μ| ≤ (∏ i, |g (t i)|) * 1 :=
          mul_le_mul (hGb t) (hcb t) (abs_nonneg _) (Finset.prod_nonneg fun i _ => abs_nonneg _)
      _ = _ := mul_one _
  apply integral_mono (hint _ hgP (fun t => by rw [Finset.abs_prod]))
    (hint _ hgaP (fun t => by rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => abs_nonneg _)]))
  intro t
  apply mul_le_mul_of_nonneg_right _ (hc n t)
  rw [← Finset.abs_prod]; exact le_abs_self _

lemma cosh_le (w : Ω → ℝ → ℝ) (hw : ∀ ω t, |w ω t| ≤ 1) (hwm : Measurable (Function.uncurry w))
    (hc : ∀ (m : ℕ) (t : Fin m → ℝ), 0 ≤ ∫ ω, ∏ i, w ω (t i) ∂μ)
    (g : ℝ → ℝ) (hg : Integrable g ν) (hgm : Measurable g) :
    ∫ ω, Real.cosh (X ν w g ω) ∂μ ≤ ∫ ω, Real.cosh (X ν w (fun t => |g t|) ω) ∂μ := by
  set L := ∫ t, |g t| ∂ν
  have hcs : ∀ x : ℝ, Real.cosh x = ∑' m : ℕ, x ^ (2 * m) / ((2 * m)! : ℝ) :=
    fun x => (Real.hasSum_cosh x).tsum_eq.symm
  have hLs : Summable (fun m : ℕ => L ^ (2 * m) / ((2 * m)! : ℝ)) := (Real.hasSum_cosh L).summable
  have key : ∀ h : ℝ → ℝ, Integrable h ν → Measurable h → (∫ t, |h t| ∂ν) = L →
      (∀ m : ℕ, Integrable (fun ω => X ν w h ω ^ (2 * m) / ((2 * m)! : ℝ)) μ) ∧
      Summable (fun m : ℕ => ∫ ω, ‖X ν w h ω ^ (2 * m) / ((2 * m)! : ℝ)‖ ∂μ) ∧
      ∫ ω, Real.cosh (X ν w h ω) ∂μ = ∑' m : ℕ, ∫ ω, X ν w h ω ^ (2 * m) / ((2 * m)! : ℝ) ∂μ := by
    intro h hh hhm hL
    have hb : ∀ ω, |X ν w h ω| ≤ L := fun ω => hL ▸ X_bound w hw h hh ω
    have hm : Measurable (X ν w h) := X_meas w hwm h hhm
    have hpt : ∀ (m : ℕ) ω, ‖X ν w h ω ^ (2 * m) / ((2 * m)! : ℝ)‖ ≤ L ^ (2 * m) / ((2 * m)! : ℝ) := by
      intro m ω
      rw [Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
      gcongr
      exact hb ω
    have hI : ∀ m : ℕ, Integrable (fun ω => X ν w h ω ^ (2 * m) / ((2 * m)! : ℝ)) μ := fun m =>
      Integrable.of_bound ((hm.pow_const _).div_const _).aestronglyMeasurable _
        (Filter.Eventually.of_forall (hpt m))
    have hS : Summable (fun m : ℕ => ∫ ω, ‖X ν w h ω ^ (2 * m) / ((2 * m)! : ℝ)‖ ∂μ) := by
      refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun _ => norm_nonneg _) (fun m => ?_) hLs
      calc ∫ ω, ‖X ν w h ω ^ (2 * m) / ((2 * m)! : ℝ)‖ ∂μ ≤ ∫ _ω, L ^ (2 * m) / ((2 * m)! : ℝ) ∂μ :=
            integral_mono (hI m).norm (integrable_const _) (hpt m)
        _ = _ := by simp
    refine ⟨hI, hS, ?_⟩
    simp_rw [hcs]
    exact (integral_tsum_of_summable_integral_norm hI hS).symm
  obtain ⟨hI1, hS1, he1⟩ := key g hg hgm rfl
  obtain ⟨hI2, hS2, he2⟩ := key (fun t => |g t|) hg.abs hgm.abs (by simp [L])
  rw [he1, he2]
  refine Summable.tsum_le_tsum (fun m => ?_) (Summable.of_norm_bounded hS1 (fun m => norm_integral_le_integral_norm _))
    (Summable.of_norm_bounded hS2 (fun m => norm_integral_le_integral_norm _))
  rw [integral_div, integral_div]
  exact div_le_div_of_nonneg_right (moment_le w hw hwm hc g hg hgm (2 * m)) (by positivity)

end TFIMPhaseDiagram.Classical.P30M

end P30Msec

namespace TFIMPhaseDiagram.Classical.Supplement.P30
open TFIMPhaseDiagram.Classical TFIMPhaseDiagram.Classical.Supplement

lemma pathValue_abs (σ : PathData) (t : ℝ) : |pathValue σ t| = 1 := by
  unfold pathValue spin
  rcases neg_one_pow_eq_or ℝ ((Finset.range σ.1).filter (fun k => σ.2.2 k ≤ t)).card with h | h <;>
    split_ifs <;> simp [h]


abbrev μU : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => uniform01)

def wd (d : ℕ) (U : ℕ → ℝ) (t : ℝ) : ℝ := pathValue (d, false, U) t

lemma wd_meas (d : ℕ) : Measurable (Function.uncurry (wd d)) := by
  have : Function.uncurry (wd d) = (fun q : PathData × ℝ => pathValue q.1 q.2) ∘
      (fun p : (ℕ → ℝ) × ℝ => (((d, false, p.1) : PathData), p.2)) := by
    funext p; rfl
  rw [this]
  refine P26F.pathValue_joint.comp ?_
  exact (measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk measurable_snd

lemma wd_abs (d : ℕ) (U : ℕ → ℝ) (t : ℝ) : |wd d U t| ≤ 1 := (pathValue_abs _ t).le

lemma wd_eq_prod (d : ℕ) (U : ℕ → ℝ) (t : ℝ) :
    wd d U t = ∏ k ∈ Finset.range d, (if U k ≤ t then (-1 : ℝ) else 1) := by
  unfold wd pathValue
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  simp [spin]

lemma int_prod_range (d : ℕ) (h : ℝ → ℝ) (hm : Measurable h) :
    ∫ U, ∏ k ∈ Finset.range d, h (U k) ∂μU = (∫ u, h u ∂uniform01) ^ d := by
  set I := Finset.range d
  have e : (fun U : ℕ → ℝ => ∏ k ∈ I, h (U k)) =
      (fun x : I → ℝ => ∏ k : I, h (x k)) ∘ I.restrict := by
    funext U; simp only [Function.comp, Finset.restrict]
    exact (Finset.prod_coe_sort I (fun k => h (U k))).symm
  rw [e]
  have hmap := integral_map (μ := μU) (φ := (I.restrict : (ℕ → ℝ) → (I → ℝ)))
    (Finset.measurable_restrict _).aemeasurable
    (f := fun x : I → ℝ => ∏ k : I, h (x k))
    (Finset.measurable_prod _ (fun k _ => hm.comp (measurable_pi_apply k))).aestronglyMeasurable
  rw [Function.comp_def, ← hmap]
  rw [Measure.infinitePi_map_restrict,
    integral_fintype_prod_eq_prod (fun (_ : I) (u : ℝ) => h u)]
  simp [I]

lemma corr_nonneg (d : ℕ) (hd : Even d) (m : ℕ) (t : Fin m → ℝ) :
    0 ≤ ∫ U, ∏ i, wd d U (t i) ∂μU := by
  have e : (fun U : ℕ → ℝ => ∏ i, wd d U (t i)) = fun U => ∏ k ∈ Finset.range d,
      (fun u : ℝ => ∏ i, (if u ≤ t i then (-1 : ℝ) else 1)) (U k) := by
    funext U
    simp only [wd_eq_prod]
    exact Finset.prod_comm
  have hmeas : Measurable (fun u : ℝ => ∏ i, (if u ≤ t i then (-1 : ℝ) else 1)) :=
    Finset.measurable_prod _ (fun i _ => Measurable.ite measurableSet_Iic measurable_const
      measurable_const)
  rw [e, int_prod_range d (fun u : ℝ => ∏ i, (if u ≤ t i then (-1 : ℝ) else 1)) hmeas]
  exact hd.pow_nonneg _


lemma cosh_cmp (d : ℕ) (hd : Even d) (g : ℝ → ℝ) (hg : Integrable g circleVolume) (hgm : Measurable g) :
    ∫ U, Real.cosh (P30M.X circleVolume (wd d) g U) ∂μU ≤
      ∫ U, Real.cosh (P30M.X circleVolume (wd d) (fun t => |g t|) U) ∂μU :=
  P30M.cosh_le (wd d) (wd_abs d) (wd_meas d) (corr_nonneg d hd) g hg hgm

lemma f_int (f : CircleL2) : Integrable (fun t => f t) circleVolume :=
  (Lp.memLp f).integrable (by norm_num)

lemma ind_mul (f : ℝ → ℝ) (S : Set ℝ) :
    (fun t => f t * S.indicator (fun _ => (1:ℝ)) t) = S.indicator f := by
  funext t
  by_cases h : t ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

lemma inner_ind_gen (f : CircleL2) (S : Set ℝ) (hs : MeasurableSet S) (hμs : circleVolume S ≠ ⊤) :
    inner ℝ (indicatorConstLp 2 hs hμs (1:ℝ)) f = ∫ t, f t * S.indicator (fun _ => (1:ℝ)) t ∂circleVolume := by
  rw [L2.inner_indicatorConstLp_one, ind_mul, integral_indicator hs]

lemma inner_gen (f : CircleL2) (τ : PathData) :
    inner ℝ f (pathL2 τ) = ∫ t, f t * pathValue τ t ∂circleVolume := by
  unfold pathL2
  rw [inner_sum]
  simp only [inner_smul_right]
  have hint : ∀ A : Finset ℕ, Integrable (fun t => f t * (jumpUpper τ A).indicator (fun _ => (1:ℝ)) t)
      circleVolume := fun A => by
    rw [ind_mul (fun t => f t)]; exact (f_int f).indicator (P26A.jumpUpper_meas τ A)
  rw [show (fun t => f t * pathValue τ t) = fun t => ∑ A ∈ (Finset.range τ.1).powerset,
      (spin τ.2.1 * (-2 : ℝ) ^ A.card) * (f t * (jumpUpper τ A).indicator (fun _ => (1:ℝ)) t) from
      funext fun t => by rw [P26A.pv_expand, Finset.mul_sum]; congr 1; funext A; ring]
  rw [integral_finsetSum _ (fun A _ => (hint A).const_mul _)]
  apply Finset.sum_congr rfl; intro A _
  rw [integral_const_mul]
  congr 1
  rw [real_inner_comm]
  erw [inner_ind_gen f (jumpUpper τ A) (P26A.jumpUpper_meas τ A) (measure_ne_top _ _)]


lemma bern_int (H : Bool → ℝ) :
    ∫ b, H b ∂(finiteLaw (fun _ : Bool => (1/2 : ℝ))) = (1/2) * H false + (1/2) * H true := by
  unfold finiteLaw
  rw [integral_finsetSum_measure (fun i _ =>
    (Integrable.of_finite (μ := Measure.dirac i)).smul_measure ENNReal.ofReal_ne_top)]
  simp [integral_smul_measure]
  ring

lemma pathLaw_decomp (η : ℝ) (hη : 0 < η) (G : PathData → ℝ) (hG : Measurable G) (C : ℝ)
    (hb : ∀ τ, |G τ| ≤ C) :
    HasSum (fun d => parityMass η false d *
        ((1/2) * ∫ U, G (d, false, U) ∂μU + (1/2) * ∫ U, G (d, true, U) ∂μU))
      (∫ τ, G τ ∂pathLaw η false) := by
  haveI := P26M.parityLaw_prob η hη.le false
  haveI := P26M.pathLaw_prob η hη.le false
  have hbnd : ∀ τ, ‖G τ‖ ≤ C := fun τ => by rw [Real.norm_eq_abs]; exact hb τ
  have hInt : Integrable G (pathLaw η false) :=
    Integrable.of_bound hG.aestronglyMeasurable C (Filter.Eventually.of_forall hbnd)
  unfold pathLaw at hInt ⊢
  rw [integral_prod _ hInt]
  have hinner : ∀ d : ℕ, ∫ q, G (d, q) ∂((finiteLaw (fun _ : Bool => (1/2 : ℝ))).prod μU) =
      (1/2) * ∫ U, G (d, false, U) ∂μU + (1/2) * ∫ U, G (d, true, U) ∂μU := by
    intro d
    have hm : Measurable (fun q : Bool × (ℕ → ℝ) => G (d, q)) := hG.comp measurable_prodMk_left
    have hI : Integrable (fun q : Bool × (ℕ → ℝ) => G (d, q))
        ((finiteLaw (fun _ : Bool => (1/2 : ℝ))).prod μU) :=
      Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall fun q => hbnd _)
    rw [integral_prod _ hI, bern_int]
  simp_rw [hinner]
  have hF : Integrable (fun d : ℕ => (1/2) * ∫ U, G (d, false, U) ∂μU +
      (1/2) * ∫ U, G (d, true, U) ∂μU) (parityLaw η false) := by
    refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun d => ?_)
    have h1 : ‖∫ U, G (d, false, U) ∂μU‖ ≤ C := norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun U => hbnd _) |>.trans (by simp)
    have h2 : ‖∫ U, G (d, true, U) ∂μU‖ ≤ C := norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun U => hbnd _) |>.trans (by simp)
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have : ‖(1/2 : ℝ)‖ = 1/2 := by norm_num
    rw [this]; linarith
  unfold parityLaw at hF ⊢
  have hs := hasSum_integral_measure hF
  refine hs.congr_fun ?_
  intro d
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (P26M.mass_nonneg η hη.le false d),
    smul_eq_mul]


def Fg (g : ℝ → ℝ) (τ : PathData) : ℝ := ∫ t, g t * pathValue τ t ∂circleVolume

lemma Fg_false (g : ℝ → ℝ) (d : ℕ) (U : ℕ → ℝ) : Fg g (d, false, U) = P30M.X circleVolume (wd d) g U := rfl

lemma Fg_true (g : ℝ → ℝ) (d : ℕ) (U : ℕ → ℝ) : Fg g (d, true, U) = - Fg g (d, false, U) := by
  unfold Fg
  rw [← integral_neg]
  congr 1; funext t
  simp [pathValue, spin]

lemma Fg_bound (g : ℝ → ℝ) (hg : Integrable g circleVolume) (τ : PathData) :
    |Fg g τ| ≤ ∫ t, |g t| ∂circleVolume := by
  unfold Fg
  refine (abs_integral_le_integral_abs).trans ?_
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => abs_nonneg _) hg.abs
  exact Filter.Eventually.of_forall fun t => by
    show |g t * pathValue τ t| ≤ |g t|
    rw [abs_mul, pathValue_abs, mul_one]

lemma Fg_meas (g : ℝ → ℝ) (hgm : Measurable g) : Measurable (Fg g) := by
  have h : StronglyMeasurable (fun q : PathData × ℝ => g q.2 * pathValue q.1 q.2) :=
    ((hgm.comp measurable_snd).mul P26F.pathValue_joint).stronglyMeasurable
  exact (h.integral_prod_right (ν := circleVolume)).measurable

lemma Fg_zero (g : ℝ → ℝ) (U : ℕ → ℝ) : Fg g (0, false, U) = ∫ t, g t ∂circleVolume := by
  unfold Fg; congr 1; funext t; simp [pathValue, spin]

lemma mass_zero (η : ℝ) (hη : 0 < η) : parityMass η false 0 = 1 / Real.cosh η := by
  simp [parityMass, hη.ne']

lemma mass_odd (η : ℝ) (d : ℕ) (hd : parityMass η false d ≠ 0) (hη : 0 < η) : Even d := by
  unfold parityMass at hd
  rw [if_neg hη.ne'] at hd
  simp only [Bool.false_eq_true, if_false] at hd
  split_ifs at hd with h
  · exact Nat.even_iff.2 h
  · exact absurd rfl hd

theorem AB_ineq (η : ℝ) (hη : 0 < η) (g : ℝ → ℝ) (hg : Integrable g circleVolume) (hgm : Measurable g) :
    (1 / Real.cosh η) * (Real.cosh (∫ t, |g t| ∂circleVolume) - Real.cosh (∫ t, g t ∂circleVolume)) ≤
      ∫ τ, Real.exp (Fg (fun t => |g t|) τ) ∂pathLaw η false - ∫ τ, Real.exp (Fg g τ) ∂pathLaw η false := by
  haveI := P26M.pathLaw_prob η hη.le false
  set L := ∫ t, |g t| ∂circleVolume
  have hgam : Measurable (fun t => |g t|) := hgm.abs
  have hb1 : ∀ τ, |Fg (fun t => |g t|) τ| ≤ L := fun τ => by
    have := Fg_bound _ hg.abs τ; simpa [L] using this
  have hb2 : ∀ τ, |Fg g τ| ≤ L := Fg_bound g hg
  have hE : ∀ (h : ℝ → ℝ), (∀ τ, |Fg h τ| ≤ L) → ∀ τ, |Real.exp (Fg h τ)| ≤ Real.exp L := by
    intro h hh τ
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (le_of_abs_le (hh τ))
  set G : PathData → ℝ := fun τ => Real.exp (Fg (fun t => |g t|) τ) - Real.exp (Fg g τ)
  have hGm : Measurable G :=
    (Real.measurable_exp.comp (Fg_meas _ hgam)).sub (Real.measurable_exp.comp (Fg_meas _ hgm))
  have hGb : ∀ τ, |G τ| ≤ 2 * Real.exp L := fun τ => by
    refine (abs_sub _ _).trans ?_
    linarith [hE _ hb1 τ, hE _ hb2 τ]
  have hint : ∀ h : ℝ → ℝ, Measurable h → (∀ τ, |Fg h τ| ≤ L) →
      Integrable (fun τ => Real.exp (Fg h τ)) (pathLaw η false) := fun h hm hh =>
    Integrable.of_bound (Real.measurable_exp.comp (Fg_meas _ hm)).aestronglyMeasurable (Real.exp L)
      (Filter.Eventually.of_forall fun τ => by rw [Real.norm_eq_abs]; exact hE h hh τ)
  rw [← integral_sub (hint _ hgam hb1) (hint _ hgm hb2)]
  have hsum := pathLaw_decomp η hη G hGm _ hGb
  -- each term equals mass * (E cosh X_|g| - E cosh X_g)
  have hUint : ∀ (h : ℝ → ℝ) (d : ℕ) (b : Bool), Measurable h → (∀ τ, |Fg h τ| ≤ L) →
      Integrable (fun U => Real.exp (Fg h (d, b, U))) μU := fun h d b hm hh =>
    Integrable.of_bound ((Real.measurable_exp.comp (Fg_meas _ hm)).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable (Real.exp L)
      (Filter.Eventually.of_forall fun U => by rw [Real.norm_eq_abs]; exact hE h hh _)
  have hterm : ∀ d : ℕ, (1/2) * ∫ U, G (d, false, U) ∂μU + (1/2) * ∫ U, G (d, true, U) ∂μU =
      ∫ U, Real.cosh (P30M.X circleVolume (wd d) (fun t => |g t|) U) ∂μU -
        ∫ U, Real.cosh (P30M.X circleVolume (wd d) g U) ∂μU := by
    intro d
    have i1 := hUint _ d false hgam hb1
    have i2 := hUint _ d false hgm hb2
    have i3 := hUint _ d true hgam hb1
    have i4 := hUint _ d true hgm hb2
    simp only [Fg_true] at i3 i4
    have c1 : ∫ U, Real.cosh (P30M.X circleVolume (wd d) (fun t => |g t|) U) ∂μU =
        ((∫ U, Real.exp (Fg (fun t => |g t|) (d, false, U)) ∂μU) +
          ∫ U, Real.exp (-Fg (fun t => |g t|) (d, false, U)) ∂μU) / 2 := by
      simp_rw [Real.cosh_eq, ← Fg_false]
      rw [integral_div, integral_add i1 i3]
    have c2 : ∫ U, Real.cosh (P30M.X circleVolume (wd d) g U) ∂μU =
        ((∫ U, Real.exp (Fg g (d, false, U)) ∂μU) +
          ∫ U, Real.exp (-Fg g (d, false, U)) ∂μU) / 2 := by
      simp_rw [Real.cosh_eq, ← Fg_false]
      rw [integral_div, integral_add i2 i4]
    rw [c1, c2]
    simp only [G, Fg_true]
    rw [integral_sub i1 i2, integral_sub i3 i4]
    ring
  simp_rw [hterm] at hsum
  have h0 := le_hasSum hsum 0 (fun d hd => by
    by_cases hm : parityMass η false d = 0
    · rw [hm, zero_mul]
    · have hev := mass_odd η d hm hη
      exact mul_nonneg (P26M.mass_nonneg η hη.le false d)
        (sub_nonneg.2 (cosh_cmp d hev g hg hgm)))
  refine le_trans (le_of_eq ?_) h0
  rw [mass_zero η hη]
  congr 1
  have e1 : ∀ U : ℕ → ℝ, P30M.X circleVolume (wd 0) (fun t => |g t|) U = L := fun U => by
    rw [← Fg_false, Fg_zero]
  have e2 : ∀ U : ℕ → ℝ, P30M.X circleVolume (wd 0) g U = ∫ t, g t ∂circleVolume := fun U => by
    rw [← Fg_false, Fg_zero]
  simp [e1, e2]


lemma cumulant_eq (η : ℝ) (g : CircleL2) :
    cumulant η g = Real.log (∫ τ, Real.exp (Fg (fun t => g t) τ) ∂pathLaw η false) := by
  unfold cumulant nuL2
  have hm : AEStronglyMeasurable (fun σ : CircleL2 => Real.exp (inner ℝ g σ))
      (Measure.map pathL2 (pathLaw η false)) :=
    (Real.continuous_exp.comp (continuous_const.inner continuous_id)).aestronglyMeasurable
  rw [integral_map P26A.pathL2_meas.aemeasurable hm]
  simp only [inner_gen, Fg]

lemma circleMean_eq (f : CircleL2) : circleMean f = ∫ t, f t ∂circleVolume := by
  unfold circleMean
  rw [L2.inner_def]
  have hc : ((constL2 1 : CircleL2) : ℝ → ℝ) =ᵐ[circleVolume] fun _ => (1:ℝ) := MemLp.coeFn_toLp _
  refine integral_congr_ae (hc.mono fun t ht => ?_)
  simp only [ht]
  simp

lemma log_sub_ge (A B : ℝ) (hA : 0 < A) (hB : 0 < B) : (A - B) / A ≤ Real.log A - Real.log B := by
  have := Real.log_le_sub_one_of_pos (div_pos hB hA)
  rw [Real.log_div hB.ne' hA.ne'] at this
  rw [sub_div, div_self hA.ne']
  linarith

lemma cosh_identity (l v : ℝ) :
    Real.exp (-l) * (Real.cosh l - Real.cosh v) =
      (1 - Real.exp (v - l)) * (1 - Real.exp (-v - l)) / 2 := by
  rw [Real.cosh_eq, Real.cosh_eq, sub_eq_add_neg v l, sub_eq_add_neg (-v) l, Real.exp_add, Real.exp_add]
  have h1 : Real.exp (-l) * Real.exp l = 1 := by rw [← Real.exp_add]; simp
  have h3 : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (1/2 : ℝ) * h1 - (1/2 : ℝ) * Real.exp (-l) ^ 2 * h3

end TFIMPhaseDiagram.Classical.Supplement.P30

namespace TFIMPhaseDiagram.Classical.Supplement.P30
theorem prop30_local (b η : ℝ) (h : supercritical b η) (f : CircleL2)
    (a z : ℝ) (ha : 0 ≤ a) (hz : 0 ≤ z) (hl : a ≤ l1Norm f) (hu : l1Norm f ≤ z) :
    let absf : CircleL2 := (Lp.memLp f).norm.toLp (fun t => ‖f t‖)
    let v := |circleMean f|
    let B := (1 / Real.cosh η) / 2 *
      (1-Real.exp (v-l1Norm f)) * (1-Real.exp (-v-l1Norm f))
    let C := (1 / Real.cosh η) * Real.exp (-z) * (1-Real.exp (-a)) / 2 * (l1Norm f-v)
    phi b η absf - phi b η f = cumulant η absf - cumulant η f ∧
    B ≤ phi b η absf - phi b η f ∧ C ≤ B ∧ 0 ≤ C := by
  intro absf v B C
  obtain ⟨hb, hη, -⟩ := h
  set l := l1Norm f with hldef
  have hnorm : ‖absf‖ = ‖f‖ := by
    simp only [absf]
    rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_norm]
  have h1 : phi b η absf - phi b η f = cumulant η absf - cumulant η f := by
    unfold phi; rw [hnorm]; ring
  have hv0 : 0 ≤ v := abs_nonneg _
  have hvl : v ≤ l := by
    simp only [v, l, l1Norm, circleMean_eq]
    exact abs_integral_le_integral_abs
  have hcB : 0 ≤ 1 / Real.cosh η := by have := Real.cosh_pos η; positivity
  have hC0 : 0 ≤ C := by
    have : 0 ≤ 1 - Real.exp (-a) := by
      have := Real.exp_le_one_iff.2 (show -a ≤ 0 by linarith); linarith
    have : 0 ≤ l - v := by linarith
    simp only [C]; positivity
  have hCB : C ≤ B := by
    simp only [C, B]
    have e1 : 0 ≤ 1 - Real.exp (-a) := by
      have := Real.exp_le_one_iff.2 (show -a ≤ 0 by linarith); linarith
    have e2 : 1 - Real.exp (-a) ≤ 1 - Real.exp (-v - l) := by
      have := Real.exp_le_exp.2 (show -v - l ≤ -a by linarith); linarith
    set x := l - v with hx
    have hx0 : 0 ≤ x := by linarith
    have e3 : x * Real.exp (-z) ≤ 1 - Real.exp (v - l) := by
      have hvx : v - l = -x := by rw [hx]; ring
      rw [hvx]
      have k1 : x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
        have := Real.add_one_le_exp x
        have hm : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (-x)]
      have k2 : Real.exp (-z) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
      nlinarith
    have e4 : 0 ≤ 1 - Real.exp (v - l) := by
      have := Real.exp_le_one_iff.2 (show v - l ≤ 0 by linarith); linarith
    have : Real.exp (-z) * (1 - Real.exp (-a)) * x ≤
        (1 - Real.exp (v - l)) * (1 - Real.exp (-v - l)) := by
      calc Real.exp (-z) * (1 - Real.exp (-a)) * x = (x * Real.exp (-z)) * (1 - Real.exp (-a)) := by ring
        _ ≤ (1 - Real.exp (v - l)) * (1 - Real.exp (-v - l)) :=
            mul_le_mul e3 e2 e1 e4
    calc 1 / Real.cosh η * Real.exp (-z) * (1 - Real.exp (-a)) / 2 * x
        = 1 / Real.cosh η / 2 * (Real.exp (-z) * (1 - Real.exp (-a)) * x) := by ring
      _ ≤ 1 / Real.cosh η / 2 * ((1 - Real.exp (v - l)) * (1 - Real.exp (-v - l))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  refine ⟨h1, ?_, hCB, hC0⟩
  rw [h1]
  -- cumulants as path expectations
  have hfi := f_int f
  have hfm : Measurable (fun t => f t) := (Lp.stronglyMeasurable f).measurable
  have habs : ∀ τ, Fg (fun t => absf t) τ = Fg (fun t => |f t|) τ := by
    intro τ
    unfold Fg
    have hc : ((absf : CircleL2) : ℝ → ℝ) =ᵐ[circleVolume] fun t => ‖f t‖ := MemLp.coeFn_toLp _
    refine integral_congr_ae (hc.mono fun t ht => ?_)
    simp only [ht, Real.norm_eq_abs]
  rw [cumulant_eq, cumulant_eq]
  simp_rw [habs]
  haveI := P26M.pathLaw_prob η hη.le false
  set A := ∫ τ, Real.exp (Fg (fun t => |f t|) τ) ∂pathLaw η false
  set Bq := ∫ τ, Real.exp (Fg (fun t => f t) τ) ∂pathLaw η false
  have hint : ∀ g : ℝ → ℝ, Measurable g → Integrable g circleVolume →
      Integrable (fun τ => Real.exp (Fg g τ)) (pathLaw η false) := fun g hm hg =>
    Integrable.of_bound (Real.measurable_exp.comp (Fg_meas _ hm)).aestronglyMeasurable
      (Real.exp (∫ t, |g t| ∂circleVolume)) (Filter.Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (le_of_abs_le (Fg_bound g hg τ)))
  have hA0 : 0 < A := integral_exp_pos (hint _ hfm.abs hfi.abs)
  have hB0 : 0 < Bq := integral_exp_pos (hint _ hfm hfi)
  have hAl : A ≤ Real.exp l := by
    calc A ≤ ∫ _τ, Real.exp l ∂pathLaw η false :=
          integral_mono (hint _ hfm.abs hfi.abs) (integrable_const _) (fun τ => Real.exp_le_exp.2 (by
            have := Fg_bound (fun t => |f t|) hfi.abs τ
            simp only [abs_abs] at this
            exact le_of_abs_le this))
      _ = Real.exp l := by simp
  have hAB := AB_ineq η hη (fun t => f t) hfi hfm
  have hcv : Real.cosh (∫ t, f t ∂circleVolume) = Real.cosh v := by
    simp only [v, circleMean_eq, Real.cosh_abs]
  rw [hcv] at hAB
  change (1 / Real.cosh η) * (Real.cosh l - Real.cosh v) ≤ A - Bq at hAB
  have hcosh : Real.cosh v ≤ Real.cosh l := by
    exact Real.cosh_le_cosh.2 (abs_le_abs_of_nonneg hv0 hvl)
  have hABnn : 0 ≤ A - Bq := le_trans (by positivity) hAB
  have hlog := log_sub_ge A Bq hA0 hB0
  have hdiv : (A - Bq) * Real.exp (-l) ≤ (A - Bq) / A := by
    rw [le_div_iff₀ hA0]
    have : Real.exp (-l) * A ≤ 1 := by
      calc Real.exp (-l) * A ≤ Real.exp (-l) * Real.exp l :=
            mul_le_mul_of_nonneg_left hAl (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hid := cosh_identity l v
  calc B = 1 / Real.cosh η * (Real.exp (-l) * (Real.cosh l - Real.cosh v)) := by
        simp only [B]; rw [hid]; ring
    _ ≤ (A - Bq) * Real.exp (-l) := by
        rw [show 1 / Real.cosh η * (Real.exp (-l) * (Real.cosh l - Real.cosh v)) =
          (1 / Real.cosh η * (Real.cosh l - Real.cosh v)) * Real.exp (-l) by ring]
        exact mul_le_mul_of_nonneg_right hAB (Real.exp_pos _).le
    _ ≤ (A - Bq) / A := hdiv
    _ ≤ _ := hlog

end TFIMPhaseDiagram.Classical.Supplement.P30

namespace TFIMPhaseDiagram.Classical.Supplement.L27
open TFIMPhaseDiagram.Classical TFIMPhaseDiagram.Classical.Supplement

lemma coe_const (r : ℝ) : ((constL2 r : CircleL2) : ℝ → ℝ) =ᵐ[circleVolume] fun _ => r :=
  MemLp.coeFn_toLp _

lemma normsq (g : CircleL2) : ‖g‖ ^ 2 = ∫ t, (g t) ^ 2 ∂circleVolume := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1; funext t; simp [sq]

lemma normsq_sub (g : CircleL2) (r : ℝ) :
    ‖g - constL2 r‖ ^ 2 = ∫ t, (g t - r) ^ 2 ∂circleVolume := by
  rw [normsq]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub g (constL2 r), coe_const r] with t h1 h2
  rw [h1, Pi.sub_apply, h2]


lemma cum_const_bounds (η : ℝ) (hη : 0 < η) (r : ℝ) :
    0 ≤ cumulant η (constL2 r) ∧ cumulant η (constL2 r) ≤ |r| := by
  rw [P26F.cumulant_const r η hη]
  set R := Real.sqrt (η ^ 2 + r ^ 2)
  have hR1 : η ≤ R := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg r])
  have hR2 : R ≤ η + |r| := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs r, abs_nonneg r]
  have hcη := Real.cosh_pos η
  constructor
  · apply Real.log_nonneg
    rw [le_div_iff₀ hcη, one_mul]
    exact Real.cosh_le_cosh.2 (by rw [abs_of_pos hη, abs_of_nonneg (hη.le.trans hR1)]; exact hR1)
  · rw [Real.log_le_iff_le_exp (div_pos (Real.cosh_pos _) hcη), div_le_iff₀ hcη]
    have h1 : Real.cosh R ≤ Real.cosh (η + |r|) :=
      Real.cosh_le_cosh.2 (by rw [abs_of_nonneg (hη.le.trans hR1), abs_of_nonneg (by positivity)]; exact hR2)
    have h2 : Real.cosh (η + |r|) ≤ Real.exp |r| * Real.cosh η := by
      rw [Real.cosh_add]
      have hs : Real.sinh η ≤ Real.cosh η := (Real.sinh_lt_cosh η).le
      have hsr : 0 ≤ Real.sinh |r| := Real.sinh_nonneg_iff.2 (abs_nonneg r)
      have he : Real.exp |r| = Real.cosh |r| + Real.sinh |r| := (Real.cosh_add_sinh _).symm
      rw [he]; nlinarith
    linarith

lemma cum_const_cont (η : ℝ) (hη : 0 < η) : Continuous (fun r : ℝ => cumulant η (constL2 r)) := by
  have : (fun r : ℝ => cumulant η (constL2 r)) =
      fun r => Real.log (Real.cosh (Real.sqrt (η ^ 2 + r ^ 2)) / Real.cosh η) := by
    funext r; exact P26F.cumulant_const r η hη
  rw [this]
  apply Continuous.log (by fun_prop)
  intro r; exact (div_pos (Real.cosh_pos _) (Real.cosh_pos _)).ne'

def absL (q : CircleL2) : CircleL2 := (Lp.memLp q).norm.toLp (fun t => ‖q t‖)

lemma absL_coe (q : CircleL2) : ((absL q : CircleL2) : ℝ → ℝ) =ᵐ[circleVolume] fun t => |q t| := by
  filter_upwards [MemLp.coeFn_toLp (Lp.memLp q).norm] with t ht
  rw [absL, ht, Real.norm_eq_abs]

lemma smul_coe (b : ℝ) (g : CircleL2) : ((b • g : CircleL2) : ℝ → ℝ) =ᵐ[circleVolume] fun t => b * g t := by
  filter_upwards [Lp.coeFn_smul b g] with t ht
  rw [ht, Pi.smul_apply, smul_eq_mul]

lemma abs_smul_eq (b : ℝ) (hb : 0 ≤ b) (q : CircleL2) :
    (Lp.memLp (b • q)).norm.toLp (fun t => ‖(b • q : CircleL2) t‖) = b • absL q := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (Lp.memLp (b • q)).norm, smul_coe b q, smul_coe b (absL q),
    absL_coe q] with t h1 h2 h3 h4
  rw [h1, h3, h2, h4, Real.norm_eq_abs, abs_mul, abs_of_nonneg hb]

lemma l1_smul (b : ℝ) (hb : 0 ≤ b) (q : CircleL2) : l1Norm (b • q) = b * l1Norm q := by
  unfold l1Norm
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [smul_coe b q] with t ht
  rw [ht, abs_mul, abs_of_nonneg hb]

lemma mean_smul (b : ℝ) (q : CircleL2) : circleMean (b • q) = b * circleMean q := by
  rw [P30.circleMean_eq, P30.circleMean_eq, ← integral_const_mul]
  exact integral_congr_ae (smul_coe b q)

lemma int_sq (g : CircleL2) : Integrable (fun t => (g t) ^ 2) circleVolume :=
  (Lp.memLp g).integrable_sq


lemma phi_le_int (b η : ℝ) (hb : 0 < b) (hη : 0 < η) (G : CircleL2) :
    phi b η G ≤ ∫ t, scalarPhi b η (G t) ∂circleVolume := by
  have hGm : Measurable (fun t => G t) := (Lp.stronglyMeasurable G).measurable
  have hcI : Integrable (fun t => cumulant η (constL2 (G t))) circleVolume := by
    refine (P30.f_int G).abs.mono' ((cum_const_cont η hη).measurable.comp hGm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    have := cum_const_bounds η hη (G t)
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
  have hsq : Integrable (fun t => (G t) ^ 2 / (2 * b)) circleVolume := (int_sq G).div_const _
  have e : (fun t => scalarPhi b η (G t)) = fun t => cumulant η (constL2 (G t)) - (G t) ^ 2 / (2 * b) := by
    funext t; unfold scalarPhi phi; rw [P26F.norm_constL2_sq]
  rw [e, integral_sub hcI hsq, integral_div, ← normsq]
  unfold phi
  have := cumulant_le_integral_const η hη G
  linarith

lemma phaseDist_eq (m : ℝ) (hm : 0 ≤ m) (q : CircleL2) :
    phaseDistanceSq m q = ∫ t, (|q t| - m) ^ 2 ∂circleVolume +
      2 * m * (l1Norm q - |circleMean q|) := by
  unfold phaseDistanceSq
  rw [normsq_sub, normsq_sub]
  have hq := int_sq q
  have hqi := P30.f_int q
  have ex : ∀ r : ℝ, ∫ t, (q t - r) ^ 2 ∂circleVolume =
      ∫ t, (q t) ^ 2 ∂circleVolume - 2 * r * ∫ t, q t ∂circleVolume + r ^ 2 := by
    intro r
    have e : (fun t => (q t - r) ^ 2) = fun t => ((q t) ^ 2 - 2 * r * q t) + r ^ 2 := by
      funext t; ring
    have h1 : Integrable (fun t => (q t) ^ 2 - 2 * r * q t) circleVolume := hq.sub (hqi.const_mul _)
    rw [e, integral_add h1 (integrable_const _), integral_sub hq (hqi.const_mul _),
      integral_const_mul]
    simp [P26F.circleVolume_univ]
  have ea : ∫ t, (|q t| - m) ^ 2 ∂circleVolume =
      ∫ t, (q t) ^ 2 ∂circleVolume - 2 * m * ∫ t, |q t| ∂circleVolume + m ^ 2 := by
    have e : (fun t => (|q t| - m) ^ 2) = fun t => ((q t) ^ 2 - 2 * m * |q t|) + m ^ 2 := by
      funext t; rw [sub_sq, sq_abs]; ring
    have h1 : Integrable (fun t => (q t) ^ 2 - 2 * m * |q t|) circleVolume :=
      hq.sub (hqi.abs.const_mul _)
    rw [e, integral_add h1 (integrable_const _), integral_sub hq (hqi.abs.const_mul _),
      integral_const_mul]
    simp [P26F.circleVolume_univ]
  rw [ex, ex, ea, P30.circleMean_eq]
  unfold l1Norm
  set I := ∫ t, q t ∂circleVolume
  rcases le_total 0 I with hI | hI
  · rw [abs_of_nonneg hI]
    rw [min_eq_left (by nlinarith [mul_nonneg hm hI])]
    ring
  · rw [abs_of_nonpos hI]
    rw [min_eq_right (by nlinarith [mul_nonneg hm (neg_nonneg.2 hI)])]
    ring


lemma sq_int_le (g : ℝ → ℝ) (hg : Integrable g circleVolume) (hg2 : Integrable (fun t => (g t) ^ 2) circleVolume) :
    (∫ t, g t ∂circleVolume) ^ 2 ≤ ∫ t, (g t) ^ 2 ∂circleVolume := by
  set c := ∫ t, g t ∂circleVolume
  have h0 : 0 ≤ ∫ t, (g t - c) ^ 2 ∂circleVolume := integral_nonneg fun t => sq_nonneg _
  have e : (fun t => (g t - c) ^ 2) = fun t => ((g t) ^ 2 - 2 * c * g t) + c ^ 2 := by
    funext t; ring
  have h1 : Integrable (fun t => (g t) ^ 2 - 2 * c * g t) circleVolume := hg2.sub (hg.const_mul _)
  rw [e, integral_add h1 (integrable_const _), integral_sub hg2 (hg.const_mul _), integral_const_mul] at h0
  simp [P26F.circleVolume_univ] at h0
  nlinarith

lemma scalarPhi_cont (b η : ℝ) (hη : 0 < η) : Continuous (scalarPhi b η) := by
  have : scalarPhi b η = fun r => cumulant η (constL2 r) - r ^ 2 / (2 * b) := by
    funext r; unfold scalarPhi phi; rw [P26F.norm_constL2_sq]
  rw [this]; exact (cum_const_cont η hη).sub (by fun_prop)

lemma scalarPhi_bound (b η : ℝ) (hb : 0 < b) (hη : 0 < η) (r : ℝ) :
    |scalarPhi b η r| ≤ |r| + r ^ 2 / (2 * b) := by
  unfold scalarPhi phi; rw [P26F.norm_constL2_sq]
  have := cum_const_bounds η hη r
  have h2 : 0 ≤ r ^ 2 / (2 * b) := by positivity
  rw [abs_le]; constructor <;> linarith

end TFIMPhaseDiagram.Classical.Supplement.L27

open TFIMPhaseDiagram.Classical TFIMPhaseDiagram.Classical.Supplement
  TFIMPhaseDiagram.Classical.Supplement.L27 in
theorem solution (b η : ℝ) (h : supercritical b η) :
    IsMagnetization b η (magnetization b η) ∧ 0 < functionalGap b η ∧
    ∀ q : CircleL2, functionalGap b η * phaseDistanceSq (magnetization b η) q ≤
      phi b η (constL2 (b * magnetization b η)) - phi b η (b • q) := by
  have h' := h
  obtain ⟨hb, hη, hsup⟩ := h
  have hEU : ∃! m : ℝ, IsMagnetization b η m :=
    TFIMPhaseDiagram.Classical.P26Aux.exists_unique_mag b η hb hη hsup
  have hex : ∃ m, IsMagnetization b η m := hEU.exists
  have hM : IsMagnetization b η (magnetization b η) := by
    unfold magnetization; rw [dif_pos hex]; exact Classical.choose_spec hex
  set m := magnetization b η with hmdef
  have hm0 : 0 < m := hM.1
  set c1 := scalarGap b η with hc1def
  have hc1 : 0 < c1 := by
    simp only [hc1def, scalarGap]
    have : 0 < b / η * Real.tanh η - 1 := by linarith
    positivity
  set c3 := b / Real.cosh η * Real.exp (-3*b*m/2) * (1-Real.exp (-b*m/2)) / (4*m) with hc3def
  have hc3 : 0 < c3 := by
    have : 0 < 1 - Real.exp (-b*m/2) := by
      have := Real.exp_lt_exp.2 (show -b*m/2 < 0 by nlinarith)
      rw [Real.exp_zero] at this; linarith
    have := Real.cosh_pos η
    simp only [hc3def]; positivity
  have hfg : functionalGap b η = min (c1 / 13) c3 := rfl
  have hfg0 : 0 < functionalGap b η := by rw [hfg]; exact lt_min (by positivity) hc3
  refine ⟨hM, hfg0, fun q => ?_⟩
  have hfg1 : functionalGap b η ≤ c1 / 13 := by rw [hfg]; exact min_le_left _ _
  have hfg3 : functionalGap b η ≤ c3 := by rw [hfg]; exact min_le_right _ _
  -- scalar gap
  have quad : ∀ x : ℝ, 0 ≤ x → c1 * (x - m) ^ 2 ≤ scalarPhi b η (b * m) - scalarPhi b η (b * x) := by
    intro x hx
    rw [P26F.scalarPhi_eq _ _ _ hη, P26F.scalarPhi_eq _ _ _ hη]
    exact TFIMPhaseDiagram.Classical.P26Aux.quad_gap b η hb hη hsup m hm0 hM.2.2 x hx
  set G : CircleL2 := b • absL q with hGdef
  have hGc : ∀ᵐ t ∂circleVolume, G t = b * |q t| := by
    filter_upwards [smul_coe b (absL q), absL_coe q] with t h1 h2
    rw [h1, h2]
  have hqm : Measurable (fun t => q t) := (Lp.stronglyMeasurable q).measurable
  have hqi := P30.f_int q
  have hq2 := int_sq q
  set D2 := ∫ t, (|q t| - m) ^ 2 ∂circleVolume with hD2def
  have hD20 : 0 ≤ D2 := integral_nonneg fun t => sq_nonneg _
  have hDint : Integrable (fun t => (|q t| - m) ^ 2) circleVolume := by
    have e : (fun t => (|q t| - m) ^ 2) = fun t => ((q t) ^ 2 - 2 * m * |q t|) + m ^ 2 := by
      funext t; rw [sub_sq, sq_abs]; ring
    rw [e]; exact (hq2.sub (hqi.abs.const_mul _)).add (integrable_const _)
  -- step (29)
  have h29 : c1 * D2 ≤ phi b η (constL2 (b * m)) - phi b η G := by
    have hle := phi_le_int b η hb hη G
    have hcongr : ∫ t, scalarPhi b η (G t) ∂circleVolume = ∫ t, scalarPhi b η (b * |q t|) ∂circleVolume :=
      integral_congr_ae (hGc.mono fun t ht => by dsimp only; rw [ht])
    rw [hcongr] at hle
    have hsI : Integrable (fun t => scalarPhi b η (b * |q t|)) circleVolume := by
      have hb2 : Integrable (fun t => abs (b * |q t|) + (b * |q t|) ^ 2 / (2 * b)) circleVolume := by
        have e : (fun t => abs (b * |q t|) + (b * |q t|) ^ 2 / (2 * b)) =
            fun t => b * |q t| + (b ^ 2 / (2 * b)) * (q t) ^ 2 := by
          funext t; rw [abs_mul, abs_abs, abs_of_pos hb, mul_pow, sq_abs]; ring
        rw [e]; exact (hqi.abs.const_mul _).add (hq2.const_mul _)
      refine hb2.mono' ((scalarPhi_cont b η hη).measurable.comp
        (measurable_const.mul hqm.abs)).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs]; exact scalarPhi_bound b η hb hη _
    have hmono : ∫ t, c1 * (|q t| - m) ^ 2 ∂circleVolume ≤
        ∫ t, (scalarPhi b η (b * m) - scalarPhi b η (b * |q t|)) ∂circleVolume :=
      integral_mono (hDint.const_mul _)
        ((integrable_const _).sub hsI) (fun t => quad _ (abs_nonneg _))
    rw [integral_const_mul, integral_sub (integrable_const _) hsI] at hmono
    simp only [integral_const, P26F.circleVolume_univ, smul_eq_mul, one_mul] at hmono
    have : phi b η (constL2 (b * m)) = scalarPhi b η (b * m) := rfl
    rw [this]
    linarith
  -- bookkeeping
  have hPD := phaseDist_eq m hm0.le q
  set Lq := l1Norm q with hLqdef
  set Iq := |circleMean q| with hIqdef
  have hLI : Iq ≤ Lq := by
    simp only [hIqdef, hLqdef, l1Norm, P30.circleMean_eq]; exact abs_integral_le_integral_abs
  have hIq0 : 0 ≤ Iq := abs_nonneg _
  have hGeq : (Lp.memLp (b • q)).norm.toLp (fun t => ‖(b • q : CircleL2) t‖) = G :=
    abs_smul_eq b hb.le q
  have hl1 : l1Norm (b • q) = b * Lq := l1_smul b hb.le q
  have hmean : |circleMean (b • q)| = b * Iq := by rw [mean_smul, abs_mul, abs_of_pos hb]
  have hl0 : 0 ≤ l1Norm (b • q) := integral_nonneg fun t => abs_nonneg _
  have hdiff0 : 0 ≤ phi b η G - phi b η (b • q) := by
    have pr := P30.prop30_local b η h' (b • q) 0 (l1Norm (b • q)) le_rfl hl0 hl0 le_rfl
    dsimp only at pr
    rw [hGeq] at pr
    obtain ⟨-, hB, hCB, hC0⟩ := pr
    linarith
  have hLq : (Lq - m) ^ 2 ≤ D2 := by
    have e : Lq - m = ∫ t, (|q t| - m) ∂circleVolume := by
      rw [integral_sub hqi.abs (integrable_const _)]
      simp [hLqdef, l1Norm, P26F.circleVolume_univ]
    rw [e]
    exact sq_int_le _ (hqi.abs.sub (integrable_const _)) hDint
  have hPD0 : 0 ≤ D2 + 2 * m * (Lq - Iq) := by nlinarith
  rw [hPD]
  by_cases hcase : m ^ 2 / 4 ≤ D2
  · set sD := Real.sqrt D2
    have hs : sD ^ 2 = D2 := Real.sq_sqrt hD20
    have hs0 : 0 ≤ sD := Real.sqrt_nonneg _
    have h1 : |Lq - m| ≤ sD := Real.abs_le_sqrt hLq
    have h2 : |m / 2| ≤ sD := Real.abs_le_sqrt (by nlinarith)
    rw [abs_of_pos (by linarith)] at h2
    have hLs : Lq - m ≤ sD := le_of_abs_le h1
    have h13 : D2 + 2 * m * (Lq - Iq) ≤ 13 * D2 := by nlinarith
    calc functionalGap b η * (D2 + 2 * m * (Lq - Iq)) ≤ (c1 / 13) * (D2 + 2 * m * (Lq - Iq)) :=
          mul_le_mul_of_nonneg_right hfg1 hPD0
      _ ≤ (c1 / 13) * (13 * D2) := mul_le_mul_of_nonneg_left h13 (by positivity)
      _ = c1 * D2 := by ring
      _ ≤ _ := by linarith
  · push_neg at hcase
    have hlo : m / 2 ≤ Lq := by nlinarith
    have hhi : Lq ≤ 3 * m / 2 := by nlinarith
    have hbm := mul_pos hb hm0
    have k1 := mul_le_mul_of_nonneg_left hlo hb.le
    have k2 := mul_le_mul_of_nonneg_left hhi hb.le
    have pr := P30.prop30_local b η h' (b • q) (b * m / 2) (3 * b * m / 2) (by linarith)
      (by linarith) (by rw [hl1]; linarith) (by rw [hl1]; linarith)
    dsimp only at pr
    rw [hGeq] at pr
    obtain ⟨-, hB, hCB, hC0⟩ := pr
    rw [hl1, hmean] at hCB hB
    have hCe : 1 / Real.cosh η * Real.exp (-(3 * b * m / 2)) * (1 - Real.exp (-(b * m / 2))) / 2 *
        (b * Lq - b * Iq) = c3 * (2 * m * (Lq - Iq)) := by
      have ea : Real.exp (-(3 * b * m / 2)) = Real.exp (-3 * b * m / 2) := by ring_nf
      have eb : Real.exp (-(b * m / 2)) = Real.exp (-b * m / 2) := by ring_nf
      rw [ea, eb, hc3def]
      field_simp
      ring
    rw [hCe] at hCB
    have k1 : functionalGap b η * D2 ≤ c1 * D2 :=
      mul_le_mul_of_nonneg_right (hfg1.trans (by linarith)) hD20
    have k2 : functionalGap b η * (2 * m * (Lq - Iq)) ≤ c3 * (2 * m * (Lq - Iq)) :=
      mul_le_mul_of_nonneg_right hfg3 (mul_nonneg (mul_nonneg two_pos.le hm0.le) (sub_nonneg.2 hLI))
    have k3 : c3 * (2 * m * (Lq - Iq)) ≤ phi b η G - phi b η (b • q) := hCB.trans hB
    have e : functionalGap b η * (D2 + 2 * m * (Lq - Iq)) =
        functionalGap b η * D2 + functionalGap b η * (2 * m * (Lq - Iq)) := by ring
    rw [e]; linarith

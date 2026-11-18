-- Prove2me | solution 1 for ResolvingNRM.IRT.prop1_part1_ho_one_resolve
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-18T03:17:32.37993+00:00
-- url     : https://prove2.me/submissions/807bf1c1-90b9-46b0-b93d-00a88ed35e52

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model
import Theorems.Thm_ResolvingNRM_IRT_poisson_tail_bound
import Theorems.Thm_ResolvingNRM_IRT_hindsight_le_dlp

open RLPBidPrice.Unbiased Matrix ResolvingNRM.IRT Finset

namespace ResolvingNRM.IRT.Part1

/-- L1 norm on `Fin n → ℝ` written as an explicit finite sum. -/
def sumAbs {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ j, |v j|

/-- Squared L2 norm on `Fin n → ℝ` written as an explicit finite sum. -/
def sumSq {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ j, v j ^ 2

lemma sumAbs_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ sumAbs v :=
  sum_nonneg fun j _ => abs_nonneg (v j)

lemma abs_le_sumAbs {n : ℕ} (v : Fin n → ℝ) (j : Fin n) : |v j| ≤ sumAbs v :=
  single_le_sum (f := fun k => |v k|) (fun k _ => abs_nonneg (v k)) (mem_univ j)

lemma sumAbs_sub_comm {n : ℕ} (x z : Fin n → ℝ) : sumAbs (z - x) = sumAbs (x - z) := by
  unfold sumAbs
  refine sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply, abs_sub_comm]

lemma sumAbs_smul_pos {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (v : Fin n → ℝ) :
    sumAbs (c • v) = c * sumAbs v := by
  unfold sumAbs
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc]

lemma sumSq_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ sumSq v :=
  sum_nonneg fun j _ => sq_nonneg (v j)

lemma eq_zero_of_dot_self_nonpos {n : ℕ} {v : Fin n → ℝ} (h : v ⬝ᵥ v ≤ 0) : v = 0 := by
  ext j
  have hj0 : 0 ≤ v j * v j := mul_self_nonneg (v j)
  have hjle : v j * v j ≤ v ⬝ᵥ v :=
    single_le_sum (f := fun k => v k * v k) (fun k _ => mul_self_nonneg (v k)) (mem_univ j)
  have hzero : v j * v j = 0 := le_antisymm (le_trans hjle h) hj0
  exact mul_self_eq_zero.mp hzero

lemma continuous_sumAbs {n : ℕ} : Continuous (sumAbs : (Fin n → ℝ) → ℝ) := by
  unfold sumAbs
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).abs

lemma continuous_sumSq {n : ℕ} : Continuous (sumSq : (Fin n → ℝ) → ℝ) := by
  unfold sumSq
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).pow 2

lemma continuous_dot_const_left {n : ℕ} (a : Fin n → ℝ) :
    Continuous (fun v : Fin n → ℝ => a ⬝ᵥ v) := by
  unfold dotProduct
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

lemma continuous_dot_const_right {n : ℕ} (w : Fin n → ℝ) :
    Continuous (fun v : Fin n → ℝ => v ⬝ᵥ w) := by
  unfold dotProduct
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const

/-- Compactness of `K_I = {v | sumAbs v = 1 ∧ ∀ w ∈ D_I, v ⬝ᵥ w ≤ 0}`. -/
lemma isCompact_KI {n : ℕ} {ι : Type*} (a : ι → Fin n → ℝ) (I : Finset ι) :
    IsCompact {v : Fin n → ℝ | sumAbs v = 1 ∧ ∀ w : Fin n → ℝ, (∀ i ∈ I, a i ⬝ᵥ w ≤ 0) → v ⬝ᵥ w ≤ 0} := by
  set D : Set (Fin n → ℝ) := {w | ∀ i ∈ I, a i ⬝ᵥ w ≤ 0}
  set K : Set (Fin n → ℝ) := {v | sumAbs v = 1 ∧ ∀ w ∈ D, v ⬝ᵥ w ≤ 0}
  have hsub : K ⊆ Set.Icc (-1 : Fin n → ℝ) 1 := by
    intro v hv
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have hj : |v j| ≤ 1 := hv.1 ▸ abs_le_sumAbs v j
      exact (abs_le.mp hj).1
    · have hj : |v j| ≤ 1 := hv.1 ▸ abs_le_sumAbs v j
      exact (abs_le.mp hj).2
  have hclosed1 : IsClosed {v : Fin n → ℝ | sumAbs v = 1} :=
    isClosed_eq continuous_sumAbs continuous_const
  have hclosed2 : IsClosed {v : Fin n → ℝ | ∀ w ∈ D, v ⬝ᵥ w ≤ 0} := by
    have heq : {v : Fin n → ℝ | ∀ w ∈ D, v ⬝ᵥ w ≤ 0} =
        ⋂ (w : Fin n → ℝ) (_ : w ∈ D), {v : Fin n → ℝ | v ⬝ᵥ w ≤ 0} := by
      ext v; simp
    rw [heq]
    exact isClosed_biInter fun w _ => isClosed_le (continuous_dot_const_right w) continuous_const
  have hKeq : K = Set.Icc (-1 : Fin n → ℝ) 1 ∩ ({v | sumAbs v = 1} ∩ {v | ∀ w ∈ D, v ⬝ᵥ w ≤ 0}) := by
    ext v
    simp only [K, Set.mem_inter_iff]
    exact ⟨fun hv => ⟨hsub hv, hv.1, hv.2⟩, fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩⟩
  change IsCompact K
  rw [hKeq]
  exact isCompact_Icc.inter_right (hclosed1.inter hclosed2)

/-- Strictly positive minimum of `f_I(v) = ∑_{i ∈ I} (a_i ⬝ᵥ v)⁺` on `K_I`. -/
lemma exists_pos_lb_KI {n : ℕ} {ι : Type*} (a : ι → Fin n → ℝ) (I : Finset ι) :
    ∃ cI : ℝ, 0 < cI ∧
      ∀ v : Fin n → ℝ, sumAbs v = 1 →
        (∀ w : Fin n → ℝ, (∀ i ∈ I, a i ⬝ᵥ w ≤ 0) → v ⬝ᵥ w ≤ 0) →
        cI ≤ ∑ i ∈ I, max (a i ⬝ᵥ v) 0 := by
  set K : Set (Fin n → ℝ) :=
    {v | sumAbs v = 1 ∧ ∀ w : Fin n → ℝ, (∀ i ∈ I, a i ⬝ᵥ w ≤ 0) → v ⬝ᵥ w ≤ 0}
  set f : (Fin n → ℝ) → ℝ := fun v => ∑ i ∈ I, max (a i ⬝ᵥ v) 0
  have hf_cont : Continuous f :=
    continuous_finsetSum _ fun i _ => (continuous_dot_const_left (a i)).max continuous_const
  have hf_pos : ∀ v ∈ K, 0 < f v := by
    intro v hv
    have hf0 : 0 ≤ f v := sum_nonneg fun i _ => le_max_right _ _
    rcases eq_or_lt_of_le hf0 with hzero | hpos
    · exfalso
      have hvD : ∀ i ∈ I, a i ⬝ᵥ v ≤ 0 := by
        intro i hi
        have hle : max (a i ⬝ᵥ v) 0 ≤ f v :=
          single_le_sum (f := fun k => max (a k ⬝ᵥ v) 0) (fun k _ => le_max_right _ _) hi
        exact le_trans (le_max_left _ _) (hle.trans hzero.symm.le)
      have hvv : v ⬝ᵥ v ≤ 0 := hv.2 v hvD
      have hv0 : v = 0 := eq_zero_of_dot_self_nonpos hvv
      have : sumAbs v = 0 := by simp [hv0, sumAbs]
      linarith [hv.1]
    · exact hpos
  by_cases hne : K.Nonempty
  · obtain ⟨v₀, hv₀K, hv₀min⟩ := (isCompact_KI a I).exists_isMinOn hne hf_cont.continuousOn
    refine ⟨f v₀, hf_pos v₀ hv₀K, fun v hv1 hv2 => hv₀min ⟨hv1, hv2⟩⟩
  · refine ⟨1, zero_lt_one, fun v hv1 hv2 => False.elim (hne ⟨v, hv1, hv2⟩)⟩

/-- Compact polyhedral error bound (Hoffman's lemma on compact polyhedra), depending only on `a`. -/
theorem compact_polyhedral_error_bound {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → Fin n → ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ (b : ι → ℝ),
      Set.Nonempty {z : Fin n → ℝ | ∀ i, a i ⬝ᵥ z ≤ b i} →
      IsCompact {z : Fin n → ℝ | ∀ i, a i ⬝ᵥ z ≤ b i} →
      ∀ x : Fin n → ℝ, ∃ z : Fin n → ℝ, (∀ i, a i ⬝ᵥ z ≤ b i) ∧
        sumAbs (z - x) ≤ H * ∑ i, max (a i ⬝ᵥ x - b i) 0 := by
  choose cI hcI_pos hcI_le using fun I : Finset ι => exists_pos_lb_KI a I
  set c : ℝ := (univ : Finset (Finset ι)).inf' univ_nonempty cI
  have hc_pos : 0 < c := (lt_inf'_iff univ_nonempty).mpr fun I _ => hcI_pos I
  refine ⟨1 / c, one_div_pos.mpr hc_pos, fun b hne hcomp x => ?_⟩
  set P : Set (Fin n → ℝ) := {z | ∀ i, a i ⬝ᵥ z ≤ b i}
  have hQ_cont : Continuous (fun z : Fin n → ℝ => sumSq (x - z)) :=
    continuous_sumSq.comp (continuous_const.sub continuous_id)
  obtain ⟨z, hzP, hzmin⟩ := hcomp.exists_isMinOn hne hQ_cont.continuousOn
  refine ⟨z, hzP, ?_⟩
  set d : Fin n → ℝ := x - z
  set I : Finset ι := univ.filter (fun i => a i ⬝ᵥ z = b i)
  -- First-order optimality on the tangent cone of active rows
  have hopt : ∀ w : Fin n → ℝ, (∀ i ∈ I, a i ⬝ᵥ w ≤ 0) → d ⬝ᵥ w ≤ 0 := by
    intro w hw
    by_contra hnot
    have hnot' : 0 < d ⬝ᵥ w := lt_of_not_ge hnot
    set stepBound : ι → ℝ := fun i =>
      if a i ⬝ᵥ z = b i then 1 else (b i - a i ⬝ᵥ z) / (1 + |a i ⬝ᵥ w|)
    have hstep_pos : ∀ i, 0 < stepBound i := by
      intro i
      dsimp [stepBound]
      split_ifs with hact
      · exact zero_lt_one
      · have hle : a i ⬝ᵥ z ≤ b i := hzP i
        have hlt : a i ⬝ᵥ z < b i := lt_of_le_of_ne hle hact
        have hden : 0 < 1 + |a i ⬝ᵥ w| := by linarith [abs_nonneg (a i ⬝ᵥ w)]
        exact div_pos (sub_pos.mpr hlt) hden
    set t0 : ℝ := (d ⬝ᵥ w) / (1 + sumSq w)
    have ht0_pos : 0 < t0 := div_pos hnot' (by linarith [sumSq_nonneg w])
    set S : Finset ℝ := insert t0 (univ.image stepBound)
    set t : ℝ := S.min' (insert_nonempty _ _)
    have ht_pos : 0 < t := by
      rw [lt_min'_iff]
      intro s hs
      rcases mem_insert.mp hs with rfl | hs'
      · exact ht0_pos
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hs'
        exact hstep_pos i
    have ht_le_t0 : t ≤ t0 := min'_le S t0 (mem_insert_self _ _)
    have ht_feas : z + t • w ∈ P := by
      intro i
      have hlin : a i ⬝ᵥ (z + t • w) = a i ⬝ᵥ z + t * (a i ⬝ᵥ w) := by
        simp [dotProduct_add, dotProduct_smul, smul_eq_mul]
      rw [hlin]
      by_cases hact : a i ⬝ᵥ z = b i
      · have hiI : i ∈ I := mem_filter.mpr ⟨mem_univ i, hact⟩
        have hwi : a i ⬝ᵥ w ≤ 0 := hw i hiI
        nlinarith [ht_pos.le]
      · have htle : t ≤ stepBound i :=
          min'_le S (stepBound i) (mem_insert_of_mem (mem_image_of_mem stepBound (mem_univ i)))
        have hstep_eq : stepBound i = (b i - a i ⬝ᵥ z) / (1 + |a i ⬝ᵥ w|) := if_neg hact
        rw [hstep_eq] at htle
        have hden : 0 < 1 + |a i ⬝ᵥ w| := by linarith [abs_nonneg (a i ⬝ᵥ w)]
        have hmul : t * (1 + |a i ⬝ᵥ w|) ≤ b i - a i ⬝ᵥ z := (le_div_iff₀ hden).mp htle
        have habs : a i ⬝ᵥ w ≤ |a i ⬝ᵥ w| := le_abs_self _
        nlinarith [ht_pos.le]
    have hQ_expand : sumSq (x - (z + t • w)) = sumSq d - 2 * t * (d ⬝ᵥ w) + t ^ 2 * sumSq w := by
      unfold sumSq dotProduct
      have hpt : ∀ j, (x j - (z j + t * w j)) ^ 2 =
          d j ^ 2 - 2 * t * (d j * w j) + t ^ 2 * w j ^ 2 := fun j => by
        dsimp [d]; ring
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simp_rw [hpt, sum_add_distrib, sum_sub_distrib, ← mul_sum]
    have hQ_lt : sumSq (x - (z + t • w)) < sumSq (x - z) := by
      change sumSq (x - (z + t • w)) < sumSq d
      rw [hQ_expand]
      have hden : 0 < 1 + sumSq w := by linarith [sumSq_nonneg w]
      have hmul : t * (1 + sumSq w) ≤ d ⬝ᵥ w := (le_div_iff₀ hden).mp ht_le_t0
      nlinarith [ht_pos, sumSq_nonneg w]
    have hQ_ge : sumSq (x - z) ≤ sumSq (x - (z + t • w)) := hzmin ht_feas
    linarith
  -- Normalize `d = x - z`
  rw [sumAbs_sub_comm]
  have hd0 : 0 ≤ sumAbs d := sumAbs_nonneg d
  rcases eq_or_lt_of_le hd0 with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg (one_div_nonneg.mpr hc_pos.le) (sum_nonneg fun i _ => le_max_right _ _)
  · set v : Fin n → ℝ := (sumAbs d)⁻¹ • d
    have hv1 : sumAbs v = 1 := by
      rw [sumAbs_smul_pos (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne']
    have hv2 : ∀ w : Fin n → ℝ, (∀ i ∈ I, a i ⬝ᵥ w ≤ 0) → v ⬝ᵥ w ≤ 0 := by
      intro w hw
      have e : v ⬝ᵥ w = (sumAbs d)⁻¹ * (d ⬝ᵥ w) := by
        simp [v, smul_dotProduct, smul_eq_mul]
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hpos.le) (hopt w hw)
    have hc_le : c ≤ ∑ i ∈ I, max (a i ⬝ᵥ v) 0 :=
      le_trans (inf'_le cI (mem_univ I)) (hcI_le I v hv1 hv2)
    have hscale : ∑ i ∈ I, max (a i ⬝ᵥ v) 0 = (sumAbs d)⁻¹ * ∑ i ∈ I, max (a i ⬝ᵥ x - b i) 0 := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hact : a i ⬝ᵥ z = b i := (mem_filter.mp hi).2
      have hlin : a i ⬝ᵥ v = (sumAbs d)⁻¹ * (a i ⬝ᵥ x - b i) := by
        have : a i ⬝ᵥ d = a i ⬝ᵥ x - a i ⬝ᵥ z := by simp [d, dotProduct_sub]
        simp [v, dotProduct_smul, smul_eq_mul, this, hact]
      rw [hlin]
      have hinv0 : 0 ≤ (sumAbs d)⁻¹ := inv_nonneg.mpr hpos.le
      rcases le_total 0 (a i ⬝ᵥ x - b i) with hge | hle
      · rw [max_eq_left (mul_nonneg hinv0 hge), max_eq_left hge]
      · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hinv0 hle), max_eq_right hle, mul_zero]
    rw [hscale] at hc_le
    have hmul : c * sumAbs d ≤ ∑ i ∈ I, max (a i ⬝ᵥ x - b i) 0 := by
      have := mul_le_mul_of_nonneg_left hc_le hpos.le
      rwa [mul_comm (sumAbs d), ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
    have hsub : ∑ i ∈ I, max (a i ⬝ᵥ x - b i) 0 ≤ ∑ i, max (a i ⬝ᵥ x - b i) 0 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ I) (fun i _ _ => le_max_right _ _)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc_pos]
    linarith [hmul, hsub]

/-- Attainment of `piValue A r C u` when `0 ≤ C` and `0 ≤ u`. -/
lemma piValue_attained {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (C : Fin m → ℝ) (hC : 0 ≤ C) (u : Fin n → ℝ) (hu : 0 ≤ u) :
    ∃ z : Fin n → ℝ, A *ᵥ z ≤ C ∧ 0 ≤ z ∧ z ≤ u ∧ piValue A r C u = r ⬝ᵥ z := by
  set F : Set (Fin n → ℝ) := {y | A *ᵥ y ≤ C} ∩ Set.Icc 0 u
  have hA_cont : Continuous (fun y : Fin n → ℝ => A *ᵥ y) :=
    continuous_pi fun l => continuous_dot_const_left (fun j => A l j)
  have hFc : IsCompact F := isCompact_Icc.inter_left (isClosed_le hA_cont continuous_const)
  have hFne : F.Nonempty := ⟨0, by simp [F, hC, hu]⟩
  obtain ⟨z, hzF, hzmax⟩ := hFc.exists_isMaxOn hFne (continuous_dot_const_left r).continuousOn
  refine ⟨z, hzF.1, hzF.2.1, hzF.2.2, ?_⟩
  unfold piValue
  apply IsGreatest.csSup_eq
  refine ⟨⟨z, hzF.1, hzF.2.1, hzF.2.2, rfl⟩, ?_⟩
  rintro v ⟨y, h1, h2, h3, rfl⟩
  exact hzmax ⟨h1, h2, h3⟩

lemma le_piValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (C : Fin m → ℝ) (u y : Fin n → ℝ)
    (h1 : A *ᵥ y ≤ C) (h2 : 0 ≤ y) (h3 : y ≤ u) : r ⬝ᵥ y ≤ piValue A r C u := by
  unfold piValue
  apply le_csSup
  · refine ⟨r ⬝ᵥ u, ?_⟩
    rintro v ⟨y', -, -, hy', rfl⟩
    unfold dotProduct
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy' j) (hr j)
  · exact ⟨y, h1, h2, h3, rfl⟩

/-- Optimal-face Lipschitz stability under upper-bound perturbations. -/
theorem optimal_face_stability {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ (C : Fin m → ℝ), 0 ≤ C → ∀ (u u' : Fin n → ℝ), 0 ≤ u → 0 ≤ u' →
      ∀ y : Fin n → ℝ, A *ᵥ y ≤ C → 0 ≤ y → y ≤ u → r ⬝ᵥ y = piValue A r C u →
        ∃ z : Fin n → ℝ, A *ᵥ z ≤ C ∧ 0 ≤ z ∧ z ≤ u' ∧ r ⬝ᵥ z = piValue A r C u' ∧
          ∀ j, |z j - y j| ≤ α * ∑ k, |u' k - u k| := by
  let ι := Fin m ⊕ Fin n ⊕ Fin n ⊕ Unit
  let row : ι → Fin n → ℝ
    | Sum.inl l => fun j => A l j
    | Sum.inr (Sum.inl j) => fun k => if k = j then -1 else 0
    | Sum.inr (Sum.inr (Sum.inl j)) => fun k => if k = j then 1 else 0
    | Sum.inr (Sum.inr (Sum.inr ())) => fun j => -r j
  obtain ⟨H, hH_pos, hH⟩ := compact_polyhedral_error_bound row
  set R : ℝ := ∑ j, r j
  have hR0 : 0 ≤ R := sum_nonneg fun j _ => hr j
  refine ⟨H * (1 + R), mul_nonneg hH_pos.le (by linarith), fun C hC u u' hu hu' y hyC hy0 hyu hyopt => ?_⟩
  set V' : ℝ := piValue A r C u'
  let rhs : ι → ℝ
    | Sum.inl l => C l
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl j)) => u' j
    | Sum.inr (Sum.inr (Sum.inr ())) => -V'
  -- Helper lemmas simplifying `row i ⬝ᵥ z`
  have hrow_cap : ∀ (l : Fin m) (z : Fin n → ℝ), row (Sum.inl l) ⬝ᵥ z = (A *ᵥ z) l := by
    intro l z; rfl
  have hrow_lo : ∀ (j : Fin n) (z : Fin n → ℝ), row (Sum.inr (Sum.inl j)) ⬝ᵥ z = -z j := by
    intro j z; simp [row, dotProduct]
  have hrow_hi : ∀ (j : Fin n) (z : Fin n → ℝ), row (Sum.inr (Sum.inr (Sum.inl j))) ⬝ᵥ z = z j := by
    intro j z; simp [row, dotProduct]
  have hrow_obj : ∀ (z : Fin n → ℝ), row (Sum.inr (Sum.inr (Sum.inr ()))) ⬝ᵥ z = -(r ⬝ᵥ z) := by
    intro z; simp [row, dotProduct, neg_mul, sum_neg_distrib]
  have hmem_iff : ∀ z : Fin n → ℝ, (∀ i, row i ⬝ᵥ z ≤ rhs i) ↔
      (A *ᵥ z ≤ C ∧ 0 ≤ z ∧ z ≤ u' ∧ V' ≤ r ⬝ᵥ z) := by
    intro z
    constructor
    · intro hz
      refine ⟨fun l => ?_, fun j => ?_, fun j => ?_, ?_⟩
      · simpa [hrow_cap, rhs] using hz (Sum.inl l)
      · have := hz (Sum.inr (Sum.inl j))
        simp only [hrow_lo, rhs, Pi.zero_apply] at this ⊢; linarith
      · simpa [hrow_hi, rhs] using hz (Sum.inr (Sum.inr (Sum.inl j)))
      · have := hz (Sum.inr (Sum.inr (Sum.inr ())))
        simp only [hrow_obj, rhs] at this; linarith
    · rintro ⟨h1, h2, h3, h4⟩ i
      rcases i with l | j | j | ⟨⟩
      · simpa [hrow_cap, rhs] using h1 l
      · have h2j : 0 ≤ z j := h2 j
        simp only [hrow_lo, rhs]; linarith
      · simpa [hrow_hi, rhs] using h3 j
      · simp only [hrow_obj, rhs]; linarith
  -- Nonemptiness and compactness of optimal face `P`
  obtain ⟨z', hz'C, hz'0, hz'u', hz'V⟩ := piValue_attained A r C hC u' hu'
  have hP_ne : Set.Nonempty {z : Fin n → ℝ | ∀ i, row i ⬝ᵥ z ≤ rhs i} :=
    ⟨z', (hmem_iff z').mpr ⟨hz'C, hz'0, hz'u', hz'V.le⟩⟩
  have hP_comp : IsCompact {z : Fin n → ℝ | ∀ i, row i ⬝ᵥ z ≤ rhs i} := by
    have hsub : {z : Fin n → ℝ | ∀ i, row i ⬝ᵥ z ≤ rhs i} ⊆ Set.Icc 0 u' := by
      intro z hz
      obtain ⟨_, h2, h3, _⟩ := (hmem_iff z).mp hz
      exact ⟨h2, h3⟩
    have hclosed : IsClosed {z : Fin n → ℝ | ∀ i, row i ⬝ᵥ z ≤ rhs i} := by
      have heq : {z : Fin n → ℝ | ∀ i, row i ⬝ᵥ z ≤ rhs i} =
          ⋂ i : ι, {z : Fin n → ℝ | row i ⬝ᵥ z ≤ rhs i} := by ext z; simp
      rw [heq]
      exact isClosed_iInter fun i => isClosed_le (continuous_dot_const_left (row i)) continuous_const
    have heq2 : {z : Fin n → ℝ | ∀ i, row i ⬝ᵥ z ≤ rhs i} =
        Set.Icc 0 u' ∩ {z : Fin n → ℝ | ∀ i, row i ⬝ᵥ z ≤ rhs i} :=
      (Set.inter_eq_self_of_subset_right hsub).symm
    rw [heq2]
    exact isCompact_Icc.inter_right hclosed
  -- Apply polyhedral error bound at `y`
  obtain ⟨z, hzP, hz_dist⟩ := hH rhs hP_ne hP_comp y
  obtain ⟨hzC, hz0, hzu', hzV⟩ := (hmem_iff z).mp hzP
  have hz_opt : r ⬝ᵥ z = V' := le_antisymm (le_piValue A r hr C u' z hzC hz0 hzu') hzV
  -- Value comparison by clipping `q j := min (z' j) (u j)`
  set q : Fin n → ℝ := fun j => min (z' j) (u j)
  have hq0 : 0 ≤ q := fun j => le_min (hz'0 j) (hu j)
  have hqu : q ≤ u := fun j => min_le_right _ _
  have hqC : A *ᵥ q ≤ C := by
    intro l
    calc (A *ᵥ q) l = ∑ j, A l j * q j := rfl
      _ ≤ ∑ j, A l j * z' j := sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (min_le_left _ _) (hA l j)
      _ = (A *ᵥ z') l := rfl
      _ ≤ C l := hz'C l
  have hV_diff : max (V' - r ⬝ᵥ y) 0 ≤ R * ∑ k, max (u' k - u k) 0 := by
    have hq_val : r ⬝ᵥ q ≤ r ⬝ᵥ y := by
      rw [hyopt]
      exact le_piValue A r hr C u q hqC hq0 hqu
    have hdiff : V' - r ⬝ᵥ y ≤ R * ∑ k, max (u' k - u k) 0 := by
      calc V' - r ⬝ᵥ y ≤ r ⬝ᵥ z' - r ⬝ᵥ q := by linarith [hz'V]
        _ = ∑ k, r k * (z' k - min (z' k) (u k)) := by
            simp [dotProduct, q, ← sum_sub_distrib, mul_sub]
        _ ≤ ∑ k, r k * max (u' k - u k) 0 := by
            refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hr k)
            have h1 : z' k - min (z' k) (u k) = max (z' k - u k) 0 := by
              rcases le_total (z' k) (u k) with hle | hge
              · rw [min_eq_left hle, sub_self, max_eq_right (sub_nonpos.mpr hle)]
              · rw [min_eq_right hge, max_eq_left (sub_nonneg.mpr hge)]
            rw [h1]
            exact max_le_max (by linarith [hz'u' k]) le_rfl
        _ ≤ ∑ k, r k * (∑ j, max (u' j - u j) 0) := by
            refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hr k)
            exact single_le_sum (f := fun j => max (u' j - u j) 0)
              (fun j _ => le_max_right _ _) (mem_univ k)
        _ = R * ∑ j, max (u' j - u j) 0 := by rw [← sum_mul]
    exact max_le hdiff (mul_nonneg hR0 (sum_nonneg fun k _ => le_max_right _ _))
  -- Sum violations over `ι`
  have hviol : ∑ i : ι, max (row i ⬝ᵥ y - rhs i) 0 ≤ (1 + R) * ∑ k, |u' k - u k| := by
    have hsplit_ι : (∑ i : ι, max (row i ⬝ᵥ y - rhs i) 0) =
        (∑ l : Fin m, max (row (Sum.inl l) ⬝ᵥ y - rhs (Sum.inl l)) 0) +
        (∑ j : Fin n, max (row (Sum.inr (Sum.inl j)) ⬝ᵥ y - rhs (Sum.inr (Sum.inl j))) 0) +
        (∑ j : Fin n, max (row (Sum.inr (Sum.inr (Sum.inl j))) ⬝ᵥ y - rhs (Sum.inr (Sum.inr (Sum.inl j)))) 0) +
        max (row (Sum.inr (Sum.inr (Sum.inr ()))) ⬝ᵥ y - rhs (Sum.inr (Sum.inr (Sum.inr ())))) 0 := by
      dsimp [ι]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type,
        Fintype.sum_unique (ι := Unit)]
      ring
    rw [hsplit_ι]
    have h1 : ∑ l : Fin m, max (row (Sum.inl l) ⬝ᵥ y - rhs (Sum.inl l)) 0 = 0 := by
      refine sum_eq_zero fun l _ => max_eq_right ?_
      simp only [hrow_cap, rhs]; linarith [hyC l]
    have h2 : ∑ j : Fin n, max (row (Sum.inr (Sum.inl j)) ⬝ᵥ y - rhs (Sum.inr (Sum.inl j))) 0 = 0 := by
      refine sum_eq_zero fun j _ => max_eq_right ?_
      have hy0j : 0 ≤ y j := hy0 j
      simp only [hrow_lo, rhs]; linarith
    have h3 : ∑ j : Fin n, max (row (Sum.inr (Sum.inr (Sum.inl j))) ⬝ᵥ y -
        rhs (Sum.inr (Sum.inr (Sum.inl j)))) 0 ≤ ∑ k, max (u k - u' k) 0 := by
      refine sum_le_sum fun k _ => ?_
      simp only [hrow_hi, rhs]
      exact max_le_max (by linarith [hyu k]) le_rfl
    have h4 : max (row (Sum.inr (Sum.inr (Sum.inr ()))) ⬝ᵥ y -
        rhs (Sum.inr (Sum.inr (Sum.inr ())))) 0 = max (V' - r ⬝ᵥ y) 0 := by
      simp only [hrow_obj, rhs]; congr 1; ring
    rw [h1, h2, h4, add_zero, zero_add]
    set Dminus : ℝ := ∑ k, max (u k - u' k) 0
    set Dplus : ℝ := ∑ k, max (u' k - u k) 0
    have hD_nonneg1 : 0 ≤ Dminus := sum_nonneg fun k _ => le_max_right _ _
    have hD_nonneg2 : 0 ≤ Dplus := sum_nonneg fun k _ => le_max_right _ _
    have hD_sum : Dminus + Dplus = ∑ k, |u' k - u k| := by
      dsimp [Dminus, Dplus]
      rw [← sum_add_distrib]
      refine sum_congr rfl fun k _ => ?_
      rcases le_total (u k) (u' k) with hle | hge
      · rw [max_eq_right (sub_nonpos.mpr hle), max_eq_left (sub_nonneg.mpr hle),
          abs_of_nonneg (sub_nonneg.mpr hle), zero_add]
      · rw [max_eq_left (sub_nonneg.mpr hge), max_eq_right (sub_nonpos.mpr hge),
          abs_of_nonpos (sub_nonpos.mpr hge), add_zero, neg_sub]
    calc ∑ j : Fin n, max (row (Sum.inr (Sum.inr (Sum.inl j))) ⬝ᵥ y -
            rhs (Sum.inr (Sum.inr (Sum.inl j)))) 0 + max (V' - r ⬝ᵥ y) 0
        ≤ Dminus + R * Dplus := add_le_add h3 hV_diff
      _ ≤ (1 + R) * (Dminus + Dplus) := by nlinarith
      _ = (1 + R) * ∑ k, |u' k - u k| := by rw [hD_sum]
  refine ⟨z, hzC, hz0, hzu', hz_opt, fun j => ?_⟩
  calc |z j - y j| ≤ sumAbs (z - y) := abs_le_sumAbs (z - y) j
    _ ≤ H * ∑ i : ι, max (row i ⬝ᵥ y - rhs i) 0 := hz_dist
    _ ≤ H * ((1 + R) * ∑ k, |u' k - u k|) := mul_le_mul_of_nonneg_left hviol hH_pos.le
    _ = H * (1 + R) * ∑ k, |u' k - u k| := (mul_assoc _ _ _).symm

end ResolvingNRM.IRT.Part1

namespace ResolvingNRM.IRT.Part2

/-! ### 1. Scalar Poisson PMF API -/

lemma pmf_nonneg (μ : ℝ) (k : ℕ) : 0 ≤ poissonPMF μ k := by
  unfold poissonPMF
  have : 0 ≤ max μ 0 := le_max_right _ _
  positivity

lemma pmf_zero (k : ℕ) : poissonPMF 0 k = if k = 0 then 1 else 0 := by
  unfold poissonPMF
  rw [max_self]
  rcases k with _ | k
  · simp
  · simp [zero_pow (Nat.succ_ne_zero k)]

lemma exp_series_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (x : ℝ)
  rwa [← Real.exp_eq_exp_ℝ] at h

lemma pmf_hasSum0 {μ : ℝ} (hμ : 0 ≤ μ) : HasSum (fun k : ℕ => poissonPMF μ k) 1 := by
  have h := (exp_series_hasSum μ).mul_left (Real.exp (-μ))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  refine h.congr_fun fun k => ?_
  unfold poissonPMF
  rw [max_eq_left hμ]
  ring

lemma pmf_hasSum0_any (μ : ℝ) : HasSum (fun k : ℕ => poissonPMF μ k) 1 := by
  have h0 : 0 ≤ max μ 0 := le_max_right _ _
  have h := pmf_hasSum0 h0
  refine h.congr_fun fun k => ?_
  simp [poissonPMF]

lemma pmf_summable (μ : ℝ) : Summable (fun k : ℕ => poissonPMF μ k) :=
  (pmf_hasSum0_any μ).summable

lemma pmf_tsum_eq_one (μ : ℝ) : (∑' k : ℕ, poissonPMF μ k) = 1 :=
  (pmf_hasSum0_any μ).tsum_eq

lemma pmf_hasSum1 {μ : ℝ} (hμ : 0 ≤ μ) :
    HasSum (fun k : ℕ => poissonPMF μ k * (k : ℝ)) μ := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
  have h := (pmf_hasSum0 hμ).mul_left μ
  rw [mul_one] at h
  refine h.congr_fun fun k => ?_
  unfold poissonPMF
  rw [max_eq_left hμ, Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma pmf_hasSum2_fall {μ : ℝ} (hμ : 0 ≤ μ) :
    HasSum (fun k : ℕ => poissonPMF μ k * ((k : ℝ) * ((k : ℝ) - 1))) (μ ^ 2) := by
  rw [← hasSum_nat_add_iff' 2]
  simp only [sum_range_succ, range_zero, sum_empty, Nat.cast_zero, Nat.cast_one, zero_mul,
    mul_zero, sub_self, add_zero, sub_zero]
  have h := (pmf_hasSum0 hμ).mul_left (μ ^ 2)
  rw [mul_one] at h
  refine h.congr_fun fun k => ?_
  unfold poissonPMF
  rw [max_eq_left hμ, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma pmf_hasSum2 {μ : ℝ} (hμ : 0 ≤ μ) :
    HasSum (fun k : ℕ => poissonPMF μ k * (k : ℝ) ^ 2) (μ ^ 2 + μ) := by
  have h := (pmf_hasSum2_fall hμ).add (pmf_hasSum1 hμ)
  refine h.congr_fun fun k => ?_
  ring

/-- Scalar Poisson convolution over `range (k + 1)`. -/
lemma pmf_conv {μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (k : ℕ) :
    ∑ a ∈ range (k + 1), poissonPMF μ a * poissonPMF ν (k - a) = poissonPMF (μ + ν) k := by
  have hμν : 0 ≤ μ + ν := add_nonneg hμ hν
  have hterm : ∀ a ∈ range (k + 1),
      poissonPMF μ a * poissonPMF ν (k - a) =
        Real.exp (-(μ + ν)) / (k.factorial : ℝ) * (μ ^ a * ν ^ (k - a) * (k.choose a : ℝ)) := by
    intro a ha
    have hak : a ≤ k := Nat.lt_succ_iff.mp (mem_range.mp ha)
    have hch_nat : k.choose a * a.factorial * (k - a).factorial = k.factorial :=
      Nat.choose_mul_factorial_mul_factorial hak
    have hch : (k.choose a : ℝ) * (a.factorial : ℝ) * ((k - a).factorial : ℝ) = (k.factorial : ℝ) := by
      exact_mod_cast hch_nat
    unfold poissonPMF
    rw [max_eq_left hμ, max_eq_left hν, neg_add, Real.exp_add]
    have hf1 : (a.factorial : ℝ) ≠ 0 := by positivity
    have hf2 : ((k - a).factorial : ℝ) ≠ 0 := by positivity
    have hf3 : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    rw [← hch]
    ring
  rw [sum_congr rfl hterm, ← mul_sum, ← add_pow μ ν k]
  unfold poissonPMF
  rw [max_eq_left hμν]
  ring

/-! ### 2. Product `HasSum` over any `Fintype` -/

lemma hasSum_fintype_prod {ι : Type*} [Fintype ι] (f : ι → ℕ → ℝ) (s : ι → ℝ)
    (hf0 : ∀ b m, 0 ≤ f b m) (hfs : ∀ b, HasSum (f b) (s b)) :
    HasSum (fun k : ι → ℕ => ∏ b, f b (k b)) (∏ b, s b) := by
  classical
  have hs0 : ∀ b, 0 ≤ s b := fun b => (hfs b).nonneg fun m => hf0 b m
  have hpart_le : ∀ b M, ∑ m ∈ range M, f b m ≤ s b := fun b M =>
    sum_le_hasSum (range M) (fun m _ => hf0 b m) (hfs b)
  let box : ℕ → Finset (ι → ℕ) := fun M => Fintype.piFinset fun _ => range M
  have hbox_eq : ∀ M, (∑ k ∈ box M, ∏ b, f b (k b)) = ∏ b, ∑ m ∈ range M, f b m :=
    fun M => (prod_univ_sum (fun _ => range M) f).symm
  have hupper : ∀ F : Finset (ι → ℕ), (∑ k ∈ F, ∏ b, f b (k b)) ≤ ∏ b, s b := by
    intro F
    set M := F.sup (fun k => univ.sup k) + 1
    have hsub : F ⊆ box M := by
      intro k hk
      dsimp [box]
      rw [Fintype.mem_piFinset]
      intro b
      rw [mem_range]
      have h1 : k b ≤ univ.sup k := le_sup (f := k) (mem_univ b)
      have h2 : univ.sup k ≤ F.sup (fun k => univ.sup k) := le_sup (f := fun k => univ.sup k) hk
      omega
    calc ∑ k ∈ F, ∏ b, f b (k b)
        ≤ ∑ k ∈ box M, ∏ b, f b (k b) :=
          sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => prod_nonneg fun b _ => hf0 b _
      _ = ∏ b, ∑ m ∈ range M, f b m := hbox_eq M
      _ ≤ ∏ b, s b := prod_le_prod (fun b _ => sum_nonneg fun m _ => hf0 b m)
          (fun b _ => hpart_le b M)
  have htend_M : Filter.Tendsto (fun M => ∏ b, ∑ m ∈ range M, f b m)
      Filter.atTop (nhds (∏ b, s b)) :=
    tendsto_finsetProd univ fun b _ => (hfs b).tendsto_sum_nat
  rw [HasSum, tendsto_order]
  refine ⟨fun l hl => ?_, fun u hu => Filter.Eventually.of_forall fun F => lt_of_le_of_lt (hupper F) hu⟩
  obtain ⟨M, hM⟩ := ((tendsto_order.mp htend_M).1 l hl).exists
  refine Filter.eventually_atTop.mpr ⟨box M, fun F hF => lt_of_lt_of_le hM ?_⟩
  rw [← hbox_eq M]
  exact sum_le_sum_of_subset_of_nonneg hF fun k _ _ => prod_nonneg fun b _ => hf0 b _

/-- Product Poisson PMF on `ι → ℕ`. -/
noncomputable def prodPMF {ι : Type*} [Fintype ι] (μ : ι → ℝ) (k : ι → ℕ) : ℝ :=
  ∏ b, poissonPMF (μ b) (k b)

lemma prodPMF_nonneg {ι : Type*} [Fintype ι] (μ : ι → ℝ) (k : ι → ℕ) :
    0 ≤ prodPMF μ k :=
  prod_nonneg fun b _ => pmf_nonneg (μ b) (k b)

lemma prodPMF_hasSum0 {ι : Type*} [Fintype ι] (μ : ι → ℝ) :
    HasSum (prodPMF μ) 1 := by
  have h := hasSum_fintype_prod (fun b m => poissonPMF (μ b) m) (fun _ => 1)
    (fun b m => pmf_nonneg (μ b) m) (fun b => pmf_hasSum0_any (μ b))
  rw [prod_const_one] at h
  exact h

lemma prodPMF_summable {ι : Type*} [Fintype ι] (μ : ι → ℝ) : Summable (prodPMF μ) :=
  (prodPMF_hasSum0 μ).summable

lemma prodPMF_tsum_eq_one {ι : Type*} [Fintype ι] (μ : ι → ℝ) : (∑' k, prodPMF μ k) = 1 :=
  (prodPMF_hasSum0 μ).tsum_eq

/-- Single-coordinate marginal of `prodPMF` against a bounded nonneg test function `g`. -/
lemma prodPMF_marginal_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) (b₀ : ι) (g : ℕ → ℝ) (hg0 : ∀ m, 0 ≤ g m)
    (hgs : Summable (fun m => poissonPMF (μ b₀) m * g m)) :
    HasSum (fun k : ι → ℕ => prodPMF μ k * g (k b₀))
      (∑' m : ℕ, poissonPMF (μ b₀) m * g m) := by
  let f : ι → ℕ → ℝ := fun b m =>
    if b = b₀ then poissonPMF (μ b) m * g m else poissonPMF (μ b) m
  let s : ι → ℝ := fun b =>
    if b = b₀ then ∑' m, poissonPMF (μ b₀) m * g m else 1
  have hf0 : ∀ b m, 0 ≤ f b m := by
    intro b m; dsimp [f]; split_ifs
    · exact mul_nonneg (pmf_nonneg _ _) (hg0 m)
    · exact pmf_nonneg _ _
  have hfs : ∀ b, HasSum (f b) (s b) := by
    intro b; dsimp [f, s]; split_ifs with hb
    · subst hb; exact hgs.hasSum
    · exact pmf_hasSum0_any (μ b)
  have hprod := hasSum_fintype_prod f s hf0 hfs
  have hs_eq : (∏ b, s b) = ∑' m, poissonPMF (μ b₀) m * g m := by
    simp [s]
  rw [hs_eq] at hprod
  refine hprod.congr_fun fun k => ?_
  dsimp [f, prodPMF]
  rw [← mul_prod_erase univ (fun b => poissonPMF (μ b) (k b)) (mem_univ b₀)]
  rw [← mul_prod_erase univ (fun b => if b = b₀ then poissonPMF (μ b) (k b) * g (k b) else poissonPMF (μ b) (k b)) (mem_univ b₀)]
  have herase : ∏ b ∈ univ.erase b₀,
      (if b = b₀ then poissonPMF (μ b) (k b) * g (k b) else poissonPMF (μ b) (k b)) =
      ∏ b ∈ univ.erase b₀, poissonPMF (μ b) (k b) := by
    refine prod_congr rfl fun b hb => ?_
    rw [if_neg (ne_of_mem_erase hb)]
  rw [if_pos rfl, herase]
  ring

lemma prodPMF_coord_hasSum1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : ι → ℝ} (hμ : ∀ b, 0 ≤ μ b) (b₀ : ι) :
    HasSum (fun k : ι → ℕ => prodPMF μ k * (k b₀ : ℝ)) (μ b₀) := by
  have hs := pmf_hasSum1 (hμ b₀)
  have hm := prodPMF_marginal_one μ b₀ (fun m => (m : ℝ)) (fun m => Nat.cast_nonneg m) hs.summable
  rwa [hs.tsum_eq] at hm

lemma prodPMF_coord_hasSum2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : ι → ℝ} (hμ : ∀ b, 0 ≤ μ b) (b₀ : ι) :
    HasSum (fun k : ι → ℕ => prodPMF μ k * (k b₀ : ℝ) ^ 2) (μ b₀ ^ 2 + μ b₀) := by
  have hs := pmf_hasSum2 (hμ b₀)
  have hm := prodPMF_marginal_one μ b₀ (fun m => (m : ℝ) ^ 2) (fun m => sq_nonneg _) hs.summable
  rwa [hs.tsum_eq] at hm

/-! ### 3. Weighted Histogram Identity & Poissonization -/

/-- Histogram of a word `w : Fin N → B`. -/
def hist {B : Type*} [Fintype B] [DecidableEq B] {N : ℕ} (w : Fin N → B) (b : B) : ℕ :=
  (univ.filter fun i => w i = b).card

lemma hist_apply_eq_sum {B : Type*} [Fintype B] [DecidableEq B] {N : ℕ}
    (w : Fin N → B) (b : B) :
    hist w b = ∑ i : Fin N, if w i = b then 1 else 0 := by
  unfold hist
  rw [card_filter]

lemma sum_hist {B : Type*} [Fintype B] [DecidableEq B] {N : ℕ} (w : Fin N → B) :
    ∑ b : B, hist w b = N := by
  simp_rw [hist_apply_eq_sum]
  rw [sum_comm]
  simp

lemma hist_cons {B : Type*} [Fintype B] [DecidableEq B] {N : ℕ}
    (b₀ : B) (u : Fin N → B) (b : B) :
    hist (Fin.cons b₀ u) b = (if b₀ = b then 1 else 0) + hist u b := by
  rw [hist_apply_eq_sum, Fin.sum_univ_succ, Fin.cons_zero, ← hist_apply_eq_sum]
  rfl

/-- Weighted histogram sum over `w : Fin N → B` by word-length induction on `N`. -/
theorem weighted_hist_sum {B : Type*} [Fintype B] [DecidableEq B] (a : B → ℝ) :
    ∀ (N : ℕ) (k : B → ℕ),
      (∑ w : Fin N → B, if hist w = k then ∏ i, a (w i) else 0) =
        if ∑ b, k b = N then (N.factorial : ℝ) * ∏ b, (a b ^ k b / ((k b).factorial : ℝ)) else 0
  | 0, k => by
    have huniq : Unique (Fin 0 → B) := inferInstance
    rw [Fintype.sum_unique]
    have hhist0 : hist (default : Fin 0 → B) = 0 := by
      ext b; simp [hist]
    rw [hhist0]
    by_cases hk0 : k = 0
    · subst hk0
      simp
    · have hsum_pos : ∑ b, k b ≠ 0 := by
        intro h0
        apply hk0
        ext b
        exact (sum_eq_zero_iff_of_nonneg fun _ _ => Nat.zero_le _).mp h0 b (mem_univ b)
      rw [if_neg (Ne.symm hk0), if_neg hsum_pos]
  | N + 1, k => by
    by_cases hsum : ∑ b, k b = N + 1
    · rw [if_pos hsum]
      -- Split `w : Fin (N + 1) → B` into `(b₀, u)` via `Fin.consEquiv`
      have hsplit : (∑ w : Fin (N + 1) → B, if hist w = k then ∏ i, a (w i) else 0) =
          ∑ b₀ : B, ∑ u : Fin N → B,
            if hist (Fin.cons b₀ u) = k then a b₀ * ∏ i, a (u i) else 0 := by
        rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (N + 1) => B))]
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun b₀ _ => sum_congr rfl fun u _ => ?_
        simp [Fin.consEquiv, Fin.prod_univ_succ]
      rw [hsplit]
      set P : B → ℕ → ℝ := fun b m => a b ^ m / (m.factorial : ℝ)
      have hinner : ∀ b₀ : B,
          (∑ u : Fin N → B, if hist (Fin.cons b₀ u) = k then a b₀ * ∏ i, a (u i) else 0) =
            (k b₀ : ℝ) * ((N.factorial : ℝ) * ∏ b, P b (k b)) := by
        intro b₀
        rcases Nat.eq_zero_or_pos (k b₀) with hkb0 | hkb_pos
        · have hfalse : ∀ u : Fin N → B, hist (Fin.cons b₀ u) ≠ k := by
            intro u hu
            have := congr_fun hu b₀
            rw [hist_cons, if_pos rfl, hkb0] at this
            omega
          rw [sum_eq_zero fun u _ => if_neg (hfalse u), hkb0, Nat.cast_zero, zero_mul]
        · set k' : B → ℕ := Function.update k b₀ (k b₀ - 1)
          have hiff : ∀ u : Fin N → B, hist (Fin.cons b₀ u) = k ↔ hist u = k' := by
            intro u
            simp only [funext_iff, hist_cons, k', Function.update_apply]
            constructor
            · intro h b
              have hb := h b
              by_cases heq : b = b₀
              · subst heq; rw [if_pos rfl] at hb; rw [if_pos rfl]; omega
              · have hne : b₀ ≠ b := Ne.symm heq
                rw [if_neg hne] at hb
                rw [if_neg heq]
                omega
            · intro h b
              have hb := h b
              by_cases heq : b = b₀
              · subst heq; rw [if_pos rfl] at hb; rw [if_pos rfl]; omega
              · have hne : b₀ ≠ b := Ne.symm heq
                rw [if_neg heq] at hb
                rw [if_neg hne]
                omega
          have hpull : (∑ u : Fin N → B, if hist (Fin.cons b₀ u) = k then a b₀ * ∏ i, a (u i) else 0) =
              a b₀ * ∑ u : Fin N → B, if hist u = k' then ∏ i, a (u i) else 0 := by
            rw [mul_sum]
            refine sum_congr rfl fun u _ => ?_
            by_cases hu : hist (Fin.cons b₀ u) = k
            · rw [if_pos hu, if_pos ((hiff u).mp hu)]
            · rw [if_neg hu, if_neg (mt (hiff u).mpr hu), mul_zero]
          have hsum_k' : ∑ b, k' b = N := by
            have h1 := add_sum_erase univ k' (mem_univ b₀)
            have h2 := add_sum_erase univ k (mem_univ b₀)
            have her : ∑ b ∈ univ.erase b₀, k' b = ∑ b ∈ univ.erase b₀, k b := by
              refine sum_congr rfl fun b hb => ?_
              simp [k', Function.update_of_ne (ne_of_mem_erase hb)]
            have hb0' : k' b₀ = k b₀ - 1 := by simp [k']
            omega
          rw [hpull, weighted_hist_sum a N k', if_pos hsum_k']
          -- Relate `a b₀ * ∏ b, P b (k' b)` to `(k b₀ : ℝ) * ∏ b, P b (k b)`
          have hP_rel : a b₀ * ∏ b, P b (k' b) = (k b₀ : ℝ) * ∏ b, P b (k b) := by
            rw [← mul_prod_erase univ (fun b => P b (k' b)) (mem_univ b₀)]
            rw [← mul_prod_erase univ (fun b => P b (k b)) (mem_univ b₀)]
            have herP : ∏ b ∈ univ.erase b₀, P b (k' b) = ∏ b ∈ univ.erase b₀, P b (k b) := by
              refine prod_congr rfl fun b hb => ?_
              simp [k', Function.update_of_ne (ne_of_mem_erase hb)]
            rw [herP]
            obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkb_pos)
            have hk'b0 : k' b₀ = m := by simp [k', hm]
            rw [hk'b0, hm]
            dsimp [P]
            rw [Nat.factorial_succ]
            push_cast
            have hmf : (m.factorial : ℝ) ≠ 0 := by positivity
            field_simp
            ring
          calc a b₀ * ((N.factorial : ℝ) * ∏ b, P b (k' b))
              = (N.factorial : ℝ) * (a b₀ * ∏ b, P b (k' b)) := by ring
            _ = (N.factorial : ℝ) * ((k b₀ : ℝ) * ∏ b, P b (k b)) := by rw [hP_rel]
            _ = (k b₀ : ℝ) * ((N.factorial : ℝ) * ∏ b, P b (k b)) := by ring
      simp_rw [hinner]
      rw [← sum_mul]
      have hcast_sum : (∑ b₀ : B, (k b₀ : ℝ)) = ((N + 1 : ℕ) : ℝ) := by
        exact_mod_cast hsum
      rw [hcast_sum, Nat.factorial_succ]
      push_cast
      ring
    · rw [if_neg hsum]
      refine sum_eq_zero fun w _ => if_neg ?_
      intro hw
      apply hsum
      rw [← hw, sum_hist]

/-- At `N = ∑ b, k b`, the Poissonized histogram weight equals `prodPMF (θ * a) k`. -/
lemma poisson_hist_at_sum {B : Type*} [Fintype B] [DecidableEq B]
    {θ : ℝ} (hθ : 0 ≤ θ) (a : B → ℝ) (ha0 : ∀ b, 0 ≤ a b) (ha1 : ∑ b, a b = 1)
    (k : B → ℕ) :
    poissonPMF θ (∑ b, k b) *
      (∑ w : Fin (∑ b, k b) → B, if hist w = k then ∏ i, a (w i) else 0) =
      prodPMF (fun b => θ * a b) k := by
  set N := ∑ b, k b
  rw [weighted_hist_sum a N k, if_pos rfl]
  unfold poissonPMF prodPMF
  rw [max_eq_left hθ]
  have hexp : Real.exp (-θ) = ∏ b, Real.exp (-(θ * a b)) := by
    rw [← Real.exp_sum, sum_neg_distrib]
    congr 1
    calc -θ = -(θ * 1) := by ring
      _ = -(θ * ∑ b, a b) := by rw [ha1]
      _ = -∑ b, θ * a b := by rw [mul_sum]
  have hpow : θ ^ N = ∏ b, θ ^ k b := by
    dsimp [N]
    exact (prod_pow_eq_pow_sum univ k θ).symm
  have hNf : (N.factorial : ℝ) ≠ 0 := by positivity
  calc Real.exp (-θ) * θ ^ N / (N.factorial : ℝ) *
          ((N.factorial : ℝ) * ∏ b, a b ^ k b / ((k b).factorial : ℝ))
      = Real.exp (-θ) * θ ^ N * ∏ b, (a b ^ k b / ((k b).factorial : ℝ)) := by
        field_simp
    _ = (∏ b, Real.exp (-(θ * a b))) * (∏ b, θ ^ k b) * ∏ b, (a b ^ k b / ((k b).factorial : ℝ)) := by
        rw [hexp, hpow]
    _ = ∏ b, (Real.exp (-(θ * a b)) * (θ ^ k b * (a b ^ k b / ((k b).factorial : ℝ)))) := by
        rw [← prod_mul_distrib, ← prod_mul_distrib]
        refine prod_congr rfl fun b _ => by ring
    _ = ∏ b, Real.exp (-max (θ * a b) 0) * max (θ * a b) 0 ^ k b / ((k b).factorial : ℝ) := by
        refine prod_congr rfl fun b _ => ?_
        rw [max_eq_left (mul_nonneg hθ (ha0 b)), mul_pow]
        ring

/-- Finite slice `{k : B → ℕ | ∑ b, k b = N}`. -/
def histSlice (B : Type*) [Fintype B] [DecidableEq B] (N : ℕ) : Finset (B → ℕ) :=
  (Fintype.piFinset fun _ : B => range (N + 1)).filter fun k => ∑ b, k b = N

lemma mem_histSlice_iff {B : Type*} [Fintype B] [DecidableEq B] {N : ℕ} {k : B → ℕ} :
    k ∈ histSlice B N ↔ ∑ b, k b = N := by
  simp only [histSlice, mem_filter, Fintype.mem_piFinset, mem_range]
  refine ⟨fun h => h.2, fun h => ⟨fun b => ?_, h⟩⟩
  have : k b ≤ ∑ b', k b' := single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (mem_univ b)
  omega

/-- Poissonization of a nonnegative summable function of the histogram `hist w`. -/
theorem poisson_hist_tsum {B : Type*} [Fintype B] [DecidableEq B]
    {θ : ℝ} (hθ : 0 ≤ θ) (a : B → ℝ) (ha0 : ∀ b, 0 ≤ a b) (ha1 : ∑ b, a b = 1)
    (G : (B → ℕ) → ℝ) (hG0 : ∀ k, 0 ≤ G k)
    (hGs : Summable (fun k : B → ℕ => prodPMF (fun b => θ * a b) k * G k)) :
    (∑' N : ℕ, poissonPMF θ N * ∑ w : Fin N → B, (∏ i, a (w i)) * G (hist w)) =
      ∑' k : B → ℕ, prodPMF (fun b => θ * a b) k * G k := by
  set v : (B → ℕ) → ℝ := fun k => prodPMF (fun b => θ * a b) k * G k
  have hv0 : ∀ k, 0 ≤ v k := fun k => mul_nonneg (prodPMF_nonneg _ k) (hG0 k)
  set u : ℕ → ℝ := fun N => poissonPMF θ N * ∑ w : Fin N → B, (∏ i, a (w i)) * G (hist w)
  have hu0 : ∀ N, 0 ≤ u N := fun N => mul_nonneg (pmf_nonneg θ N)
    (sum_nonneg fun w _ => mul_nonneg (prod_nonneg fun i _ => ha0 _) (hG0 _))
  -- For each `N`, `u N` equals the sum of `v` over `histSlice B N`
  have hu_slice : ∀ N, u N = ∑ k ∈ histSlice B N, v k := by
    intro N
    dsimp [u]
    have hfib : (∑ w : Fin N → B, (∏ i, a (w i)) * G (hist w)) =
        ∑ k ∈ histSlice B N, (∑ w : Fin N → B, if hist w = k then ∏ i, a (w i) else 0) * G k := by
      rw [← sum_fiberwise_of_maps_to (g := hist) (t := histSlice B N)
        (fun w _ => mem_histSlice_iff.mpr (sum_hist w))]
      refine sum_congr rfl fun k _ => ?_
      rw [sum_mul, sum_filter]
      refine sum_congr rfl fun w _ => ?_
      split_ifs with h
      · rw [h]
      · ring
    rw [hfib, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hsum_k : ∑ b, k b = N := mem_histSlice_iff.mp hk
    subst hsum_k
    rw [← mul_assoc, poisson_hist_at_sum hθ a ha0 ha1 k]
  have hdisj : ∀ M : ℕ, Set.PairwiseDisjoint (↑(range M) : Set ℕ) (histSlice B) := by
    intro M N₁ _ N₂ _ hne
    refine disjoint_left.mpr fun k hk1 hk2 => hne ?_
    exact (mem_histSlice_iff.mp hk1).symm.trans (mem_histSlice_iff.mp hk2)
  have hrange_le : ∀ M : ℕ, ∑ N ∈ range M, u N ≤ ∑' k, v k := by
    intro M
    simp_rw [hu_slice]
    rw [← sum_biUnion (hdisj M)]
    exact hGs.sum_le_tsum _ fun k _ => hv0 k
  have hu_summ : Summable u := summable_of_sum_range_le hu0 hrange_le
  have hle1 : (∑' N, u N) ≤ ∑' k, v k := Real.tsum_le_of_sum_range_le hu0 hrange_le
  have hle2 : (∑' k, v k) ≤ ∑' N, u N := by
    refine Real.tsum_le_of_sum_le hv0 fun F => ?_
    set M := F.sup (fun k => ∑ b, k b) + 1
    have hsub : F ⊆ (range M).biUnion (histSlice B) := by
      intro k hk
      rw [mem_biUnion]
      refine ⟨∑ b, k b, mem_range.mpr ?_, mem_histSlice_iff.mpr rfl⟩
      have : ∑ b, k b ≤ F.sup (fun k' => ∑ b, k' b) := le_sup (f := fun k' => ∑ b, k' b) hk
      omega
    calc ∑ k ∈ F, v k
        ≤ ∑ k ∈ (range M).biUnion (histSlice B), v k :=
          sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hv0 k
      _ = ∑ N ∈ range M, ∑ k ∈ histSlice B N, v k := sum_biUnion (hdisj M)
      _ = ∑ N ∈ range M, u N := sum_congr rfl fun N _ => (hu_slice N).symm
      _ ≤ ∑' N, u N := hu_summ.sum_le_tsum (range M) fun N _ => hu0 N
  exact le_antisymm hle1 hle2

/-! ### 4. Product Poisson Convolution & Linear-Growth Summability -/

lemma prodPMF_linear_summable {n : ℕ} {μ : Fin n → ℝ} (hμ : ∀ j, 0 ≤ μ j)
    {F : (Fin n → ℕ) → ℝ} (hF0 : ∀ k, 0 ≤ F k) {A₀ B₀ : ℝ} (_hA₀ : 0 ≤ A₀) (_hB₀ : 0 ≤ B₀)
    (hFbnd : ∀ k, F k ≤ A₀ + B₀ * ∑ j, (k j : ℝ)) :
    Summable (fun k : Fin n → ℕ => prodPMF μ k * F k) := by
  have hdom : Summable (fun k : Fin n → ℕ =>
      A₀ * prodPMF μ k + ∑ j : Fin n, B₀ * (prodPMF μ k * (k j : ℝ))) :=
    ((prodPMF_summable μ).mul_left A₀).add
      (summable_sum fun j _ => (prodPMF_coord_hasSum1 hμ j).summable.mul_left B₀)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (prodPMF_nonneg μ k) (hF0 k))
    (fun k => ?_) hdom
  calc prodPMF μ k * F k
      ≤ prodPMF μ k * (A₀ + B₀ * ∑ j, (k j : ℝ)) :=
        mul_le_mul_of_nonneg_left (hFbnd k) (prodPMF_nonneg μ k)
    _ = A₀ * prodPMF μ k + ∑ j, B₀ * (prodPMF μ k * (k j : ℝ)) := by
        rw [mul_add, mul_sum, mul_sum]
        congr 1
        · ring
        · refine sum_congr rfl fun j _ => by ring

/-- Vector Poisson convolution on `Fin n → ℕ`. -/
lemma prodPMF_conv_vec {n : ℕ} {μ ν : Fin n → ℝ} (hμ : ∀ j, 0 ≤ μ j) (hν : ∀ j, 0 ≤ ν j)
    (k : Fin n → ℕ) :
    (∑ a ∈ Fintype.piFinset (fun j => range (k j + 1)),
      prodPMF μ a * prodPMF ν (k - a)) = prodPMF (fun j => μ j + ν j) k := by
  calc (∑ a ∈ Fintype.piFinset (fun j => range (k j + 1)), prodPMF μ a * prodPMF ν (k - a))
      = ∑ a ∈ Fintype.piFinset (fun j => range (k j + 1)),
          ∏ j, (poissonPMF (μ j) (a j) * poissonPMF (ν j) (k j - a j)) := by
        refine sum_congr rfl fun a _ => ?_
        simp [prodPMF, prod_mul_distrib]
    _ = ∏ j, ∑ m ∈ range (k j + 1), poissonPMF (μ j) m * poissonPMF (ν j) (k j - m) :=
        (prod_univ_sum (fun j => range (k j + 1))
          (fun j m => poissonPMF (μ j) m * poissonPMF (ν j) (k j - m))).symm
    _ = prodPMF (fun j => μ j + ν j) k := by
        unfold prodPMF
        refine prod_congr rfl fun j _ => pmf_conv (hμ j) (hν j) (k j)

/-- Infinite-sum convolution of two `prodPMF` distributions on `Fin n → ℕ`. -/
theorem prodPMF_conv_tsum {n : ℕ} {μ ν : Fin n → ℝ} (hμ : ∀ j, 0 ≤ μ j) (hν : ∀ j, 0 ≤ ν j)
    (F : (Fin n → ℕ) → ℝ) (hF0 : ∀ k, 0 ≤ F k)
    (hFs_k2 : ∀ k₁, Summable (fun k₂ => prodPMF ν k₂ * F (k₁ + k₂)))
    (hFs_tot : Summable (fun k => prodPMF (fun j => μ j + ν j) k * F k)) :
    (∑' k₁ : Fin n → ℕ, prodPMF μ k₁ * ∑' k₂ : Fin n → ℕ, prodPMF ν k₂ * F (k₁ + k₂)) =
      ∑' k : Fin n → ℕ, prodPMF (fun j => μ j + ν j) k * F k := by
  set RHS := ∑' k : Fin n → ℕ, prodPMF (fun j => μ j + ν j) k * F k
  set g₁ : (Fin n → ℕ) → ℝ := fun k₁ => prodPMF μ k₁ * ∑' k₂, prodPMF ν k₂ * F (k₁ + k₂)
  have hg₁0 : ∀ k₁, 0 ≤ g₁ k₁ := fun k₁ =>
    mul_nonneg (prodPMF_nonneg μ k₁)
      (tsum_nonneg fun k₂ => mul_nonneg (prodPMF_nonneg ν k₂) (hF0 _))
  let box : ℕ → Finset (Fin n → ℕ) := fun M => Fintype.piFinset fun _ => range M
  -- Any finite rectangle `S₁ × S₂` sums to at most `RHS`
  have hrect_le : ∀ S₁ S₂ : Finset (Fin n → ℕ),
      (∑ k₁ ∈ S₁, ∑ k₂ ∈ S₂, prodPMF μ k₁ * (prodPMF ν k₂ * F (k₁ + k₂))) ≤ RHS := by
    intro S₁ S₂
    set M := S₁.sup (fun k => univ.sup k) + S₂.sup (fun k => univ.sup k) + 1
    have hmaps : ∀ p ∈ S₁ ×ˢ S₂, p.1 + p.2 ∈ box M := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := mem_product.mp hp
      rw [Fintype.mem_piFinset]
      intro j
      rw [mem_range]
      have h1 : p.1 j ≤ S₁.sup (fun k => univ.sup k) :=
        le_trans (le_sup (f := p.1) (mem_univ j)) (le_sup (f := fun k => univ.sup k) hp1)
      have h2 : p.2 j ≤ S₂.sup (fun k => univ.sup k) :=
        le_trans (le_sup (f := p.2) (mem_univ j)) (le_sup (f := fun k => univ.sup k) hp2)
      simp only [Pi.add_apply]; omega
    rw [← sum_product']
    rw [← sum_fiberwise_of_maps_to hmaps]
    have hfib_le : ∀ k ∈ box M,
        (∑ p ∈ (S₁ ×ˢ S₂).filter (fun p => p.1 + p.2 = k),
          prodPMF μ p.1 * (prodPMF ν p.2 * F (p.1 + p.2))) ≤
          prodPMF (fun j => μ j + ν j) k * F k := by
      intro k _
      set subBox := Fintype.piFinset fun j => range (k j + 1)
      have himg : ((S₁ ×ˢ S₂).filter (fun p => p.1 + p.2 = k)).image Prod.fst ⊆ subBox := by
        intro a ha
        obtain ⟨⟨a', b'⟩, hmem, ha_eq⟩ := mem_image.mp ha
        dsimp at ha_eq
        subst ha_eq
        have hab : a' + b' = k := (mem_filter.mp hmem).2
        rw [Fintype.mem_piFinset]
        intro j
        rw [mem_range]
        have := congr_fun hab j
        simp only [Pi.add_apply] at this
        omega
      have hinj : Set.InjOn Prod.fst (((S₁ ×ˢ S₂).filter (fun p => p.1 + p.2 = k) :
          Finset ((Fin n → ℕ) × (Fin n → ℕ))) : Set ((Fin n → ℕ) × (Fin n → ℕ))) := by
        intro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 ha_eq
        dsimp at ha_eq
        subst ha_eq
        have h1' : (a₁, b₁) ∈ (S₁ ×ˢ S₂).filter (fun p => p.1 + p.2 = k) := h1
        have h2' : (a₁, b₂) ∈ (S₁ ×ˢ S₂).filter (fun p => p.1 + p.2 = k) := h2
        have heq1 : a₁ + b₁ = k := (mem_filter.mp h1').2
        have heq2 : a₁ + b₂ = k := (mem_filter.mp h2').2
        have hb_eq : b₁ = b₂ := by
          ext j
          have h1j := congr_fun heq1 j
          have h2j := congr_fun heq2 j
          simp only [Pi.add_apply] at h1j h2j
          omega
        subst hb_eq; rfl
      have hrew : (∑ p ∈ (S₁ ×ˢ S₂).filter (fun p => p.1 + p.2 = k),
          prodPMF μ p.1 * (prodPMF ν p.2 * F (p.1 + p.2))) =
          ∑ p ∈ (S₁ ×ˢ S₂).filter (fun p => p.1 + p.2 = k),
            (prodPMF μ p.1 * prodPMF ν (k - p.1)) * F k := by
        refine sum_congr rfl fun p hp => ?_
        have hab : p.1 + p.2 = k := (mem_filter.mp hp).2
        have hb : p.2 = k - p.1 := by
          ext j
          have hj := congr_fun hab j
          simp only [Pi.add_apply, Pi.sub_apply] at hj ⊢
          omega
        rw [hab, hb, mul_assoc]
      rw [hrew, ← sum_image (f := fun a => prodPMF μ a * prodPMF ν (k - a) * F k) hinj]
      calc (∑ a ∈ ((S₁ ×ˢ S₂).filter (fun p => p.1 + p.2 = k)).image Prod.fst,
              prodPMF μ a * prodPMF ν (k - a) * F k)
          ≤ ∑ a ∈ subBox, prodPMF μ a * prodPMF ν (k - a) * F k :=
            sum_le_sum_of_subset_of_nonneg himg fun a _ _ =>
              mul_nonneg (mul_nonneg (prodPMF_nonneg _ _) (prodPMF_nonneg _ _)) (hF0 k)
        _ = (∑ a ∈ subBox, prodPMF μ a * prodPMF ν (k - a)) * F k := (sum_mul _ _ _).symm
        _ = prodPMF (fun j => μ j + ν j) k * F k := by rw [prodPMF_conv_vec hμ hν k]
    exact le_trans (sum_le_sum hfib_le)
      (hFs_tot.sum_le_tsum (box M) fun k _ => mul_nonneg (prodPMF_nonneg _ _) (hF0 k))
  -- Lift from finite `S₂` to `tsum` over `k₂`
  have hS1_le : ∀ S₁ : Finset (Fin n → ℕ), ∑ k₁ ∈ S₁, g₁ k₁ ≤ RHS := by
    intro S₁
    have htend : Filter.Tendsto
        (fun S₂ : Finset (Fin n → ℕ) =>
          ∑ k₁ ∈ S₁, prodPMF μ k₁ * ∑ k₂ ∈ S₂, prodPMF ν k₂ * F (k₁ + k₂))
        Filter.atTop (nhds (∑ k₁ ∈ S₁, g₁ k₁)) :=
      tendsto_finsetSum S₁ fun k₁ _ => Filter.Tendsto.const_mul (prodPMF μ k₁) (hFs_k2 k₁).hasSum
    refine le_of_tendsto' htend fun S₂ => ?_
    simpa only [mul_sum] using hrect_le S₁ S₂
  have hg₁_summ : Summable g₁ := summable_of_sum_le hg₁0 hS1_le
  have hle1 : (∑' k₁, g₁ k₁) ≤ RHS := Real.tsum_le_of_sum_le hg₁0 hS1_le
  -- Reverse inequality `RHS ≤ ∑' k₁, g₁ k₁`
  have hle2 : RHS ≤ ∑' k₁, g₁ k₁ := by
    refine Real.tsum_le_of_sum_le (fun k => mul_nonneg (prodPMF_nonneg _ _) (hF0 k)) fun S => ?_
    set M := S.sup (fun k => univ.sup k) + 1
    -- Embed `Sigma subBox` over `k ∈ S` into `box M ×ˢ box M`
    let pairs : Finset ((Fin n → ℕ) × (Fin n → ℕ)) :=
      S.biUnion fun k =>
        (Fintype.piFinset fun j => range (k j + 1)).image (fun a => (a, k - a))
    have hpairs_sub : pairs ⊆ box M ×ˢ box M := by
      intro p hp
      obtain ⟨k, hkS, hp_img⟩ := mem_biUnion.mp hp
      obtain ⟨a, ha_sub, rfl⟩ := mem_image.mp hp_img
      dsimp [box]
      rw [mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · rw [mem_range]
        have h1 : a j < k j + 1 := mem_range.mp (Fintype.mem_piFinset.mp ha_sub j)
        have h2 : k j ≤ S.sup (fun k' => univ.sup k') :=
          le_trans (le_sup (f := k) (mem_univ j)) (le_sup (f := fun k' => univ.sup k') hkS)
        dsimp
        omega
      · rw [mem_range]
        have h2 : k j ≤ S.sup (fun k' => univ.sup k') :=
          le_trans (le_sup (f := k) (mem_univ j)) (le_sup (f := fun k' => univ.sup k') hkS)
        simp only [Pi.sub_apply]
        omega
    have hdisj_S : Set.PairwiseDisjoint (↑S : Set (Fin n → ℕ))
        (fun k => (Fintype.piFinset fun j => range (k j + 1)).image (fun a => (a, k - a))) := by
      intro k₁ _ k₂ _ hne
      refine disjoint_left.mpr fun p hp1 hp2 => hne ?_
      obtain ⟨a₁, ha₁, rfl⟩ := mem_image.mp hp1
      obtain ⟨a₂, ha₂, heq⟩ := mem_image.mp hp2
      obtain ⟨h1, h2⟩ := Prod.mk.injEq a₂ (k₂ - a₂) a₁ (k₁ - a₁) ▸ heq
      subst h1
      ext j
      have haj1 : a₂ j ≤ k₁ j := Nat.lt_succ_iff.mp (mem_range.mp (Fintype.mem_piFinset.mp ha₁ j))
      have haj2 : a₂ j ≤ k₂ j := Nat.lt_succ_iff.mp (mem_range.mp (Fintype.mem_piFinset.mp ha₂ j))
      have hj := congr_fun h2 j
      simp only [Pi.sub_apply] at hj
      omega
    calc ∑ k ∈ S, prodPMF (fun j => μ j + ν j) k * F k
        = ∑ k ∈ S, (∑ a ∈ Fintype.piFinset (fun j => range (k j + 1)),
            prodPMF μ a * prodPMF ν (k - a)) * F k := by
          refine sum_congr rfl fun k _ => by rw [prodPMF_conv_vec hμ hν k]
      _ = ∑ k ∈ S, ∑ p ∈ (Fintype.piFinset fun j => range (k j + 1)).image (fun a => (a, k - a)),
            prodPMF μ p.1 * (prodPMF ν p.2 * F (p.1 + p.2)) := by
          refine sum_congr rfl fun k _ => ?_
          rw [sum_mul]
          have hinj_a : Set.InjOn (fun a : Fin n → ℕ => (a, k - a))
              ↑(Fintype.piFinset fun j => range (k j + 1)) :=
            fun a₁ _ a₂ _ h => (Prod.mk.injEq _ _ _ _).mp h |>.1
          rw [sum_image hinj_a]
          refine sum_congr rfl fun a ha => ?_
          have hak : a + (k - a) = k := by
            ext j
            have haj : a j ≤ k j := Nat.lt_succ_iff.mp (mem_range.mp (Fintype.mem_piFinset.mp ha j))
            simp only [Pi.add_apply, Pi.sub_apply]; omega
          rw [hak, mul_assoc]
      _ = ∑ p ∈ pairs, prodPMF μ p.1 * (prodPMF ν p.2 * F (p.1 + p.2)) := (sum_biUnion hdisj_S).symm
      _ ≤ ∑ p ∈ box M ×ˢ box M, prodPMF μ p.1 * (prodPMF ν p.2 * F (p.1 + p.2)) :=
          sum_le_sum_of_subset_of_nonneg hpairs_sub fun p _ _ =>
            mul_nonneg (prodPMF_nonneg _ _) (mul_nonneg (prodPMF_nonneg _ _) (hF0 _))
      _ = ∑ k₁ ∈ box M, prodPMF μ k₁ * ∑ k₂ ∈ box M, prodPMF ν k₂ * F (k₁ + k₂) := by
          rw [sum_product]
          refine sum_congr rfl fun k₁ _ => ?_
          dsimp only
          exact (mul_sum _ _ _).symm
      _ ≤ ∑ k₁ ∈ box M, g₁ k₁ := by
          refine sum_le_sum fun k₁ _ => mul_le_mul_of_nonneg_left ?_ (prodPMF_nonneg _ _)
          exact (hFs_k2 k₁).sum_le_tsum (box M) fun k₂ _ => mul_nonneg (prodPMF_nonneg _ _) (hF0 _)
      _ ≤ ∑' k₁, g₁ k₁ := hg₁_summ.sum_le_tsum (box M) fun k₁ _ => hg₁0 k₁
  exact le_antisymm hle1 hle2

/-! ### 5. First-Window Weights, Thinning, and Superposition+Convolution -/

noncomputable def wt1 {n : ℕ} (lam p : Fin n → ℝ) (N : ℕ)
    (cls : Fin N → Fin n) (coin : Fin N → Bool) : ℝ :=
  ∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))

lemma wt1_nonneg {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (N : ℕ)
    (cls : Fin N → Fin n) (coin : Fin N → Bool) :
    0 ≤ wt1 lam p N cls coin := by
  unfold wt1
  refine prod_nonneg fun i _ => ?_
  have hΛ : 0 ≤ ∑ j, lam j := sum_nonneg fun j _ => (hlam j).le
  have h1 : 0 ≤ lam (cls i) / ∑ j, lam j := div_nonneg (hlam _).le hΛ
  have h2 : 0 ≤ (if coin i then p (cls i) else 1 - p (cls i)) := by
    split_ifs
    · exact hp0 _
    · linarith [hp1 (cls i)]
  exact mul_nonneg h1 h2

lemma wt1_sum_coin {n : ℕ} (lam p : Fin n → ℝ) (N : ℕ) (cls : Fin N → Fin n) :
    (∑ coin : Fin N → Bool, wt1 lam p N cls coin) = ∏ i, (lam (cls i) / ∑ j, lam j) := by
  unfold wt1
  rw [← Fintype.prod_sum (fun i (b : Bool) => (lam (cls i) / ∑ j, lam j) *
    (if b = true then p (cls i) else 1 - p (cls i)))]
  refine prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

lemma wt1_sum_eq_one {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (hn : 0 < n) (N : ℕ) :
    (∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool, wt1 lam p N cls coin) = 1 := by
  simp_rw [wt1_sum_coin]
  rw [← Fintype.prod_sum (fun _ (j : Fin n) => lam j / ∑ j', lam j'), prod_const]
  have hΛ : 0 < ∑ j, lam j := by
    have : lam ⟨0, hn⟩ ≤ ∑ j, lam j :=
      single_le_sum (f := lam) (fun j _ => (hlam j).le) (mem_univ _)
    linarith [hlam ⟨0, hn⟩]
  rw [← sum_div, div_self hΛ.ne', one_pow]

/-- Count of coin-positive arrivals of class `j` in `(cls, coin)`. -/
def markedCount {n N : ℕ} (cls : Fin N → Fin n) (coin : Fin N → Bool) (j : Fin n) : ℕ :=
  (univ.filter fun i : Fin N => cls i = j ∧ coin i = true).card

/-- Thinning marginal of `markedCount cls coin j₀` is `Poisson(lam j₀ * p j₀ * ℓ)`. -/
theorem wt1_thin_tsum {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (hn : 0 < n)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (j₀ : Fin n) (g : ℕ → ℝ) (hg0 : ∀ m, 0 ≤ g m)
    (hgs : Summable (fun m => poissonPMF (lam j₀ * p j₀ * ℓ) m * g m)) :
    (∑' N : ℕ, poissonPMF ((∑ j, lam j) * ℓ) N *
      ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
        wt1 lam p N cls coin * g (markedCount cls coin j₀)) =
      ∑' m : ℕ, poissonPMF (lam j₀ * p j₀ * ℓ) m * g m := by
  set Λ : ℝ := ∑ j, lam j
  have hΛ : 0 < Λ := by
    have : lam ⟨0, hn⟩ ≤ Λ := single_le_sum (f := lam) (fun j _ => (hlam j).le) (mem_univ _)
    linarith [hlam ⟨0, hn⟩]
  let a : Fin n × Bool → ℝ := fun q =>
    (lam q.1 / Λ) * (if q.2 = true then p q.1 else 1 - p q.1)
  have ha0 : ∀ q, 0 ≤ a q := by
    intro ⟨j, b⟩
    dsimp [a]
    refine mul_nonneg (div_nonneg (hlam j).le hΛ.le) ?_
    cases b
    · simp; linarith [hp1 j]
    · simp [hp0 j]
  have ha1 : ∑ q : Fin n × Bool, a q = 1 := by
    rw [Fintype.sum_prod_type]
    have hbool : ∀ j : Fin n, ∑ b : Bool, a (j, b) = lam j / Λ := by
      intro j
      rw [Fintype.sum_bool]
      dsimp [a]
      ring
    simp_rw [hbool, ← sum_div]
    exact div_self hΛ.ne'
  have hθ : 0 ≤ Λ * ℓ := mul_nonneg hΛ.le hℓ
  have hμ_j0 : (Λ * ℓ) * a (j₀, true) = lam j₀ * p j₀ * ℓ := by
    dsimp [a]
    have := hΛ.ne'
    field_simp
  have hgs' : Summable (fun m => poissonPMF ((Λ * ℓ) * a (j₀, true)) m * g m) := by
    rwa [hμ_j0]
  have hmarg := prodPMF_marginal_one (fun q : Fin n × Bool => (Λ * ℓ) * a q) (j₀, true) g hg0 hgs'
  have hhist := poisson_hist_tsum hθ a ha0 ha1 (fun k => g (k (j₀, true)))
    (fun k => hg0 _) hmarg.summable
  rw [hmarg.tsum_eq, hμ_j0] at hhist
  rw [← hhist]
  congr 1; ext N
  congr 1
  -- Explicit equivalence `(Fin N → Fin n) × (Fin N → Bool) ≃ (Fin N → Fin n × Bool)`
  let ev : ((Fin N → Fin n) × (Fin N → Bool)) ≃ (Fin N → Fin n × Bool) :=
    { toFun := fun pair i => (pair.1 i, pair.2 i)
      invFun := fun w => (fun i => (w i).1, fun i => (w i).2)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.sum_prod_type']
  rw [← Equiv.sum_comp ev]
  refine sum_congr rfl fun pair _ => ?_
  obtain ⟨cls, coin⟩ := pair
  have hwt : wt1 lam p N cls coin = ∏ i, a (ev (cls, coin) i) := rfl
  have hcnt : markedCount cls coin j₀ = hist (ev (cls, coin)) (j₀, true) := by
    unfold markedCount hist
    congr 1; ext i
    simp [ev, Prod.ext_iff]
  rw [hwt, hcnt]

/-- Superposition + convolution identity for `F (hist cls + k₂)`. -/
theorem wt1_superpos_conv_tsum {n : ℕ} (lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (hn : 0 < n)
    {ℓ τ₁ : ℝ} (hℓ : 0 ≤ ℓ) (hτ₁ : 0 ≤ τ₁)
    (F : (Fin n → ℕ) → ℝ) (hF0 : ∀ k, 0 ≤ F k) {A₀ B₀ : ℝ} (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (hFbnd : ∀ k, F k ≤ A₀ + B₀ * ∑ j, (k j : ℝ)) :
    (∑' N : ℕ, poissonPMF ((∑ j, lam j) * ℓ) N *
      ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
        wt1 lam p N cls coin *
          ∑' k₂ : Fin n → ℕ, prodPMF (fun j => lam j * τ₁) k₂ * F (hist cls + k₂)) =
      ∑' k : Fin n → ℕ, prodPMF (fun j => lam j * (ℓ + τ₁)) k * F k := by
  set Λ : ℝ := ∑ j, lam j
  have hΛ : 0 < Λ := by
    have : lam ⟨0, hn⟩ ≤ Λ := single_le_sum (f := lam) (fun j _ => (hlam j).le) (mem_univ _)
    linarith [hlam ⟨0, hn⟩]
  let a : Fin n → ℝ := fun j => lam j / Λ
  have ha0 : ∀ j, 0 ≤ a j := fun j => div_nonneg (hlam j).le hΛ.le
  have ha1 : ∑ j, a j = 1 := by dsimp [a]; rw [← sum_div, div_self hΛ.ne']
  have hθ : 0 ≤ Λ * ℓ := mul_nonneg hΛ.le hℓ
  have hμ₁ : ∀ j, 0 ≤ lam j * ℓ := fun j => mul_nonneg (hlam j).le hℓ
  have hμ₂ : ∀ j, 0 ≤ lam j * τ₁ := fun j => mul_nonneg (hlam j).le hτ₁
  have hθa : (fun j => (Λ * ℓ) * a j) = fun j => lam j * ℓ := by
    ext j; dsimp [a]; have := hΛ.ne'; field_simp
  -- Summability of `k₂` inner sum and total `k` sum
  have hk2_summ : ∀ k₁ : Fin n → ℕ,
      Summable (fun k₂ => prodPMF (fun j => lam j * τ₁) k₂ * F (k₁ + k₂)) := by
    intro k₁
    refine prodPMF_linear_summable hμ₂ (fun k₂ => hF0 (k₁ + k₂))
      (A₀ := A₀ + B₀ * ∑ j : Fin n, (k₁ j : ℝ)) (B₀ := B₀)
      (add_nonneg hA₀ (mul_nonneg hB₀ (sum_nonneg fun j _ => Nat.cast_nonneg _))) hB₀ fun k₂ => ?_
    calc F (k₁ + k₂) ≤ A₀ + B₀ * ∑ j, (((k₁ + k₂) j : ℕ) : ℝ) := hFbnd (k₁ + k₂)
      _ = (A₀ + B₀ * ∑ j, (k₁ j : ℝ)) + B₀ * ∑ j, (k₂ j : ℝ) := by
          simp only [Pi.add_apply, Nat.cast_add, sum_add_distrib]
          ring
  have htot_summ : Summable (fun k => prodPMF (fun j => lam j * ℓ + lam j * τ₁) k * F k) :=
    prodPMF_linear_summable (fun j => add_nonneg (hμ₁ j) (hμ₂ j)) hF0 hA₀ hB₀ hFbnd
  -- Summability of `k₁` outer sum
  have hk1_summ : Summable (fun k₁ => prodPMF (fun j => (Λ * ℓ) * a j) k₁ *
      ∑' k₂, prodPMF (fun j => lam j * τ₁) k₂ * F (k₁ + k₂)) := by
    rw [hθa]
    -- Bound the inner tsum linearly in `k₁`
    have hinner_bnd : ∀ k₁ : Fin n → ℕ,
        (∑' k₂, prodPMF (fun j => lam j * τ₁) k₂ * F (k₁ + k₂)) ≤
          (A₀ + B₀ * ∑ j, lam j * τ₁) + B₀ * ∑ j, (k₁ j : ℝ) := by
      intro k₁
      set C₁ : ℝ := A₀ + B₀ * ∑ j, (k₁ j : ℝ)
      have hdom_hs : HasSum (fun k₂ : Fin n → ℕ =>
          C₁ * prodPMF (fun j => lam j * τ₁) k₂ +
            ∑ j, B₀ * (prodPMF (fun j => lam j * τ₁) k₂ * (k₂ j : ℝ)))
          (C₁ * 1 + ∑ j, B₀ * (lam j * τ₁)) :=
        ((prodPMF_hasSum0 _).mul_left C₁).add
          (hasSum_sum fun j _ => (prodPMF_coord_hasSum1 hμ₂ j).mul_left B₀)
      calc (∑' k₂, prodPMF (fun j => lam j * τ₁) k₂ * F (k₁ + k₂))
          ≤ ∑' k₂, (C₁ * prodPMF (fun j => lam j * τ₁) k₂ +
              ∑ j, B₀ * (prodPMF (fun j => lam j * τ₁) k₂ * (k₂ j : ℝ))) := by
            refine Summable.tsum_le_tsum (fun k₂ => ?_) (hk2_summ k₁) hdom_hs.summable
            calc prodPMF (fun j => lam j * τ₁) k₂ * F (k₁ + k₂)
                ≤ prodPMF (fun j => lam j * τ₁) k₂ * (C₁ + B₀ * ∑ j, (k₂ j : ℝ)) := by
                  refine mul_le_mul_of_nonneg_left ?_ (prodPMF_nonneg _ _)
                  calc F (k₁ + k₂) ≤ A₀ + B₀ * ∑ j, (((k₁ + k₂) j : ℕ) : ℝ) := hFbnd (k₁ + k₂)
                    _ = C₁ + B₀ * ∑ j, (k₂ j : ℝ) := by
                        dsimp [C₁]; simp only [Nat.cast_add, sum_add_distrib]; ring
              _ = C₁ * prodPMF (fun j => lam j * τ₁) k₂ +
                    ∑ j, B₀ * (prodPMF (fun j => lam j * τ₁) k₂ * (k₂ j : ℝ)) := by
                  rw [mul_add, mul_sum, mul_sum]; congr 1
                  · ring
                  · refine sum_congr rfl fun j _ => by ring
        _ = C₁ * 1 + ∑ j, B₀ * (lam j * τ₁) := hdom_hs.tsum_eq
        _ = (A₀ + B₀ * ∑ j, lam j * τ₁) + B₀ * ∑ j, (k₁ j : ℝ) := by
            dsimp [C₁]; rw [← mul_sum]; ring
    exact prodPMF_linear_summable hμ₁
      (fun k₁ => tsum_nonneg fun k₂ => mul_nonneg (prodPMF_nonneg _ _) (hF0 _))
      (add_nonneg hA₀ (mul_nonneg hB₀ (sum_nonneg fun j _ => hμ₂ j))) hB₀ hinner_bnd
  -- Sum over `coin` first, then apply `poisson_hist_tsum` and `prodPMF_conv_tsum`
  have hcoin_pull : ∀ (N : ℕ) (cls : Fin N → Fin n),
      (∑ coin : Fin N → Bool, wt1 lam p N cls coin *
          ∑' k₂ : Fin n → ℕ, prodPMF (fun j => lam j * τ₁) k₂ * F (hist cls + k₂)) =
        (∏ i, a (cls i)) *
          ∑' k₂ : Fin n → ℕ, prodPMF (fun j => lam j * τ₁) k₂ * F (hist cls + k₂) := by
    intro N cls
    rw [← sum_mul, wt1_sum_coin]
  simp_rw [hcoin_pull]
  rw [poisson_hist_tsum hθ a ha0 ha1
    (fun k₁ => ∑' k₂, prodPMF (fun j => lam j * τ₁) k₂ * F (k₁ + k₂))
    (fun k₁ => tsum_nonneg fun k₂ => mul_nonneg (prodPMF_nonneg _ _) (hF0 _)) hk1_summ]
  rw [hθa]
  rw [prodPMF_conv_tsum hμ₁ hμ₂ F hF0 hk2_summ htot_summ]
  congr 1; ext k
  congr 1; unfold prodPMF
  refine prod_congr rfl fun j _ => by dsimp only; rw [mul_add]

end ResolvingNRM.IRT.Part2

open ResolvingNRM.IRT.Part1 ResolvingNRM.IRT.Part2

namespace ResolvingNRM.IRT.Part3

/-! ### 1. `runWindow` Exactness and Bounds -/

def listMarkedCount {n : ℕ} (L : List (Fin n × Bool)) (j : Fin n) : ℕ :=
  (L.map fun q => if q.1 = j ∧ q.2 = true then 1 else 0).sum

lemma listMarkedCount_cons {n : ℕ} (j₀ : Fin n) (b₀ : Bool) (rest : List (Fin n × Bool))
    (j : Fin n) :
    listMarkedCount ((j₀, b₀) :: rest) j =
      (if j₀ = j ∧ b₀ = true then 1 else 0) + listMarkedCount rest j := by
  simp [listMarkedCount]

lemma listMarkedCount_ofFn {n N : ℕ} (cls : Fin N → Fin n) (coin : Fin N → Bool) (j : Fin n) :
    listMarkedCount (List.ofFn fun i => (cls i, coin i)) j = markedCount cls coin j := by
  unfold listMarkedCount markedCount
  rw [card_filter, List.map_ofFn, List.sum_ofFn]
  rfl

lemma runWindow_when_fits {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hA : ∀ l j, 0 ≤ A l j) (L : List (Fin n × Bool)) :
    ∀ c : Fin m → ℝ, (∀ l, ∑ j, A l j * (listMarkedCount L j : ℝ) ≤ c l) →
      runWindow A r L c =
        (∑ j, r j * (listMarkedCount L j : ℝ),
          fun l => c l - ∑ j, A l j * (listMarkedCount L j : ℝ)) := by
  induction L with
  | nil =>
    intro c _
    simp [runWindow, listMarkedCount]
  | cons hd rest ih =>
    obtain ⟨j₀, b₀⟩ := hd
    intro c hc
    cases b₀ with
    | false =>
      have hcnt : ∀ j, listMarkedCount ((j₀, false) :: rest) j = listMarkedCount rest j := by
        intro j; simp [listMarkedCount_cons]
      have hcond : ¬ (false = true ∧ ∀ l, A l j₀ ≤ c l) := by simp
      simp only [runWindow, if_neg hcond, hcnt] at hc ⊢
      exact ih c hc
    | true =>
      have hcnt_sum : ∀ (f : Fin n → ℝ),
          ∑ j, f j * (listMarkedCount ((j₀, true) :: rest) j : ℝ) =
            f j₀ + ∑ j, f j * (listMarkedCount rest j : ℝ) := by
        intro f
        have hpt : ∀ j, f j * (listMarkedCount ((j₀, true) :: rest) j : ℝ) =
            (if j₀ = j then f j else 0) + f j * (listMarkedCount rest j : ℝ) := by
          intro j
          rw [listMarkedCount_cons]
          by_cases hj : j₀ = j
          · subst hj; simp; ring
          · simp [hj]
        simp_rw [hpt, sum_add_distrib, sum_ite_eq, mem_univ, if_true]
      have hfit0 : ∀ l, A l j₀ ≤ c l := by
        intro l
        have hcl := hc l
        rw [hcnt_sum (fun j => A l j)] at hcl
        have hrest0 : 0 ≤ ∑ j, A l j * (listMarkedCount rest j : ℝ) :=
          sum_nonneg fun j _ => mul_nonneg (hA l j) (Nat.cast_nonneg _)
        linarith
      have hcond : true = true ∧ ∀ l, A l j₀ ≤ c l := ⟨rfl, hfit0⟩
      have hc' : ∀ l, ∑ j, A l j * (listMarkedCount rest j : ℝ) ≤ c l - A l j₀ := by
        intro l
        have hcl := hc l
        rw [hcnt_sum (fun j => A l j)] at hcl
        linarith
      rw [runWindow, if_pos hcond, ih (fun l => c l - A l j₀) hc']
      ext
      · dsimp only
        rw [hcnt_sum r]
      · rename_i l
        dsimp only
        rw [hcnt_sum (fun j => A l j)]
        ring

lemma runWindow_bounds {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (L : List (Fin n × Bool)) :
    ∀ c : Fin m → ℝ, 0 ≤ c →
      0 ≤ (runWindow A r L c).1 ∧ (runWindow A r L c).1 ≤ L.length * ∑ j, r j ∧
        0 ≤ (runWindow A r L c).2 := by
  induction L with
  | nil => intro c hc; simp [runWindow, hc]
  | cons a rest ih =>
    intro c hc
    obtain ⟨j, b⟩ := a
    have hrj : r j ≤ ∑ j', r j' := single_le_sum (f := r) (fun j' _ => hr j') (mem_univ j)
    by_cases h : b = true ∧ ∀ l, A l j ≤ c l
    · have hc' : 0 ≤ (fun l => c l - A l j) := fun l => by
        have := h.2 l; simp only [Pi.zero_apply]; linarith
      obtain ⟨h1, h2, h3⟩ := ih _ hc'
      simp only [runWindow, if_pos h, List.length_cons]
      refine ⟨by linarith [hr j], ?_, h3⟩
      push_cast
      linarith
    · obtain ⟨h1, h2, h3⟩ := ih c hc
      simp only [runWindow, if_neg h, List.length_cons]
      refine ⟨h1, ?_, h3⟩
      push_cast
      have : 0 ≤ ∑ j', r j' := sum_nonneg fun j' _ => hr j'
      linarith

/-! ### 2. `piValue` Bounds, DLP Scaling, and Support Lemmas -/

lemma piValue_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (C : Fin m → ℝ) (hC : 0 ≤ C) (u : Fin n → ℝ) (hu : 0 ≤ u) :
    0 ≤ piValue A r C u := by
  simpa using le_piValue A r hr C u 0 (by simpa using hC) le_rfl hu

lemma piValue_le_dot {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (C : Fin m → ℝ) (hC : 0 ≤ C) (u : Fin n → ℝ) (hu : 0 ≤ u) :
    piValue A r C u ≤ r ⬝ᵥ u := by
  obtain ⟨z, _, _, hzu, hzopt⟩ := piValue_attained A r C hC u hu
  rw [hzopt]
  exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hzu j) (hr j)

lemma piValue_le_R_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (C : Fin m → ℝ) (hC : 0 ≤ C) (u : Fin n → ℝ) (hu : 0 ≤ u) :
    piValue A r C u ≤ (∑ j, r j) * ∑ j, u j := by
  refine le_trans (piValue_le_dot A r hr C hC u hu) ?_
  calc r ⬝ᵥ u = ∑ j, r j * u j := rfl
    _ ≤ ∑ j, (∑ k, r k) * u j := sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (single_le_sum (f := r) (fun k _ => hr k) (mem_univ j)) (hu j)
    _ = (∑ k, r k) * ∑ j, u j := (mul_sum _ _ _).symm

lemma dlp_scaled_opt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j)
    {sel : (Fin m → ℝ) → (Fin n → ℝ)} (hsel : IsDLPSelector A r lam sel)
    {T : ℝ} (hT : 0 < T) {C : Fin m → ℝ} (hC : 0 ≤ C) :
    let x := sel (fun l => C l / T)
    A *ᵥ (T • x) ≤ C ∧ 0 ≤ T • x ∧ (T • x ≤ fun j => lam j * T) ∧
      r ⬝ᵥ (T • x) = piValue A r C (fun j => lam j * T) := by
  intro x
  have hb : 0 ≤ (fun l => C l / T) := fun l => div_nonneg (hC l) hT.le
  obtain ⟨⟨hxC, hx0, hxlam⟩, hxopt⟩ := hsel _ hb
  have h1 : A *ᵥ (T • x) ≤ C := by
    intro l
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact (le_div_iff₀' hT).mp (hxC l)
  have h2 : 0 ≤ T • x := fun j => mul_nonneg hT.le (hx0 j)
  have h3 : T • x ≤ fun j => lam j * T := fun j => by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hxlam j) hT.le
  refine ⟨h1, h2, h3, le_antisymm (le_piValue A r hr C _ (T • x) h1 h2 h3) ?_⟩
  obtain ⟨z, hzC, hz0, hzu, hzV⟩ :=
    piValue_attained A r C hC (fun j => lam j * T) (fun j => mul_nonneg (hlam j).le hT.le)
  rw [hzV]
  have hzT_C : A *ᵥ (T⁻¹ • z) ≤ fun l => C l / T := by
    intro l
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    dsimp only
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hzC l) (inv_nonneg.mpr hT.le)
  have hzT_0 : 0 ≤ T⁻¹ • z := fun j => mul_nonneg (inv_nonneg.mpr hT.le) (hz0 j)
  have hzT_lam : T⁻¹ • z ≤ lam := fun j => by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_le_iff₀ hT]
    linarith [hzu j]
  have hopt_z := hxopt (T⁻¹ • z) hzT_C hzT_0 hzT_lam
  rw [dotProduct_smul, smul_eq_mul] at hopt_z
  rw [dotProduct_smul, smul_eq_mul]
  have hmul := mul_le_mul_of_nonneg_left hopt_z hT.le
  rwa [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul] at hmul

lemma thresholdProbs_mem {n : ℕ} (lam : Fin n → ℝ) (τ : ℝ) (x : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hx0 : 0 ≤ x) (hx1 : x ≤ lam) (j : Fin n) :
    0 ≤ thresholdProbs lam τ x j ∧ thresholdProbs lam τ x j ≤ 1 := by
  unfold thresholdProbs
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨div_nonneg (hx0 j) (hlam j).le, (div_le_one (hlam j)).mpr (hx1 j)⟩

lemma wt1_pos_imp_zero {n N : ℕ} {lam p : Fin n → ℝ} {cls : Fin N → Fin n}
    {coin : Fin N → Bool} (hw : 0 < wt1 lam p N cls coin) {j : Fin n} (hpj : p j = 0) :
    markedCount cls coin j = 0 := by
  unfold markedCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro i _ ⟨hcls, hcoin⟩
  have hzero : wt1 lam p N cls coin = 0 := by
    unfold wt1
    refine prod_eq_zero (mem_univ i) ?_
    simp [hcls, hcoin, hpj]
  linarith

lemma wt1_pos_imp_hist {n N : ℕ} {lam p : Fin n → ℝ} {cls : Fin N → Fin n}
    {coin : Fin N → Bool} (hw : 0 < wt1 lam p N cls coin) {j : Fin n} (hpj : p j = 1) :
    markedCount cls coin j = hist cls j := by
  unfold markedCount hist
  congr 1; ext i
  simp only [mem_filter, mem_univ, true_and]
  refine ⟨fun h => h.1, fun hcls => ⟨hcls, ?_⟩⟩
  by_contra hcoin
  have hfalse : coin i = false := Bool.eq_false_iff.mpr hcoin
  have hzero : wt1 lam p N cls coin = 0 := by
    unfold wt1
    refine prod_eq_zero (mem_univ i) ?_
    simp [hcls, hfalse, hpj]
  linarith

/-! ### 3. `hoValue` Nonnegativity and Trivial Regimes -/

lemma hoValue_one_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j)
    {sel : (Fin m → ℝ) → (Fin n → ℝ)} (hsel : IsDLPSelector A r lam sel)
    {T : ℝ} (hT : 1 ≤ T) {C : Fin m → ℝ} (hC : 0 ≤ C) :
    0 ≤ hoValue A r lam sel 1 T C := by
  have htau0 : 0 < tau T 0 := by simp [tau]; linarith
  have hb : 0 ≤ (fun l => C l / tau T 0) := fun l => div_nonneg (hC l) htau0.le
  obtain ⟨⟨_, hx0, hx1⟩, _⟩ := hsel _ hb
  set p := thresholdProbs lam (tau T 0) (sel fun l => C l / tau T 0)
  have hp0 : ∀ j, 0 ≤ p j := fun j => (thresholdProbs_mem lam _ _ hlam hx0 hx1 j).1
  have hp1 : ∀ j, p j ≤ 1 := fun j => (thresholdProbs_mem lam _ _ hlam hx0 hx1 j).2
  have hho_cont_nonneg : ∀ c' : Fin m → ℝ, 0 ≤ c' → 0 ≤ hindsightValue A r lam (tau T 1) c' := by
    intro c' hc'
    unfold hindsightValue
    refine tsum_nonneg fun k => mul_nonneg (prod_nonneg fun j _ => pmf_nonneg _ _) ?_
    exact piValue_nonneg A r hr c' hc' _ fun j => Nat.cast_nonneg _
  simp only [hoValue, hoAux, zero_add, windowValue]
  refine tsum_nonneg fun N => mul_nonneg (pmf_nonneg _ _) ?_
  refine sum_nonneg fun cls _ => sum_nonneg fun coin _ => ?_
  have hw0 := wt1_nonneg lam p hlam hp0 hp1 N cls coin
  obtain ⟨hr1, _, hc2⟩ := runWindow_bounds A r hr (List.ofFn fun i => (cls i, coin i)) C hC
  exact mul_nonneg hw0 (add_nonneg hr1 (hho_cont_nonneg _ hc2))

lemma hindsight_le_T_rho {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j)
    {T : ℝ} (hT : 0 < T) {C : Fin m → ℝ} (hC : 0 ≤ C) :
    hindsightValue A r lam T C ≤ T * (r ⬝ᵥ lam) := by
  refine le_trans (hindsight_le_dlp A r lam hlam hr hA T hT C hC) ?_
  unfold dlpValue
  exact mul_le_mul_of_nonneg_left
    (piValue_le_dot A r hr (fun l => C l / T) (fun l => div_nonneg (hC l) hT.le) lam
      (fun j => (hlam j).le)) hT.le

/-! ### 4. Fractional Power Identities (`q = T ^ (1/12)`) -/

lemma rpow_identities {T : ℝ} (hT8 : (8 : ℝ) ^ (12 : ℕ) ≤ T) :
    let q := T ^ (1 / 12 : ℝ)
    8 ≤ q ∧ q ^ (12 : ℕ) = T ∧ tau T 0 = T ∧ tau T 1 = q ^ (10 : ℕ) ∧
      T ^ (1 / 6 : ℝ) = q ^ (2 : ℕ) ∧ T ^ (-(1 / 4 : ℝ)) = (q ^ (3 : ℕ))⁻¹ := by
  intro q
  have h8_pos : (0 : ℝ) < (8 : ℝ) ^ (12 : ℕ) := by positivity
  have hT0 : 0 ≤ T := le_trans h8_pos.le hT8
  have hq8 : 8 ≤ q := by
    have hle : ((8 : ℝ) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) ≤ T ^ (1 / 12 : ℝ) :=
      Real.rpow_le_rpow h8_pos.le hT8 (by norm_num)
    have h8eq : ((8 : ℝ) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) = 8 := by
      rw [← Real.rpow_natCast 8 12, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [h8eq] at hle
  have hq12 : q ^ (12 : ℕ) = T := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0]
    norm_num
  have htau0 : tau T 0 = T := by simp [tau]
  have htau1 : tau T 1 = q ^ (10 : ℕ) := by
    dsimp [q, tau]
    rw [pow_one, ← Real.rpow_natCast, ← Real.rpow_mul hT0]
    norm_num
  have hT16 : T ^ (1 / 6 : ℝ) = q ^ (2 : ℕ) := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0]
    norm_num
  have hT14 : T ^ (-(1 / 4 : ℝ)) = (q ^ (3 : ℕ))⁻¹ := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0, ← Real.rpow_neg hT0]
    norm_num
  exact ⟨hq8, hq12, htau0, htau1, hT16, hT14⟩

lemma q_pow_le {q : ℝ} (hq1 : 1 ≤ q) {a b : ℕ} (hab : a ≤ b) : q ^ a ≤ q ^ b :=
  pow_le_pow_right₀ hq1 hab

/-! ### 5. Good-Event Pathwise Comparison (Zero `nlinarith`) -/

lemma good_event_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hstab : ∀ (C : Fin m → ℝ), 0 ≤ C → ∀ (u u' : Fin n → ℝ), 0 ≤ u → 0 ≤ u' →
      ∀ y : Fin n → ℝ, A *ᵥ y ≤ C → 0 ≤ y → y ≤ u → r ⬝ᵥ y = piValue A r C u →
        ∃ z : Fin n → ℝ, A *ᵥ z ≤ C ∧ 0 ≤ z ∧ z ≤ u' ∧ r ⬝ᵥ z = piValue A r C u' ∧
          ∀ j, |z j - y j| ≤ α * ∑ k, |u' k - u k|)
    {lam_min : ℝ} (hlam_min_le : ∀ j, lam_min ≤ lam j) (hlam_min_pos : 0 < lam_min)
    {sel : (Fin m → ℝ) → (Fin n → ℝ)} (hsel : IsDLPSelector A r lam sel)
    {T : ℝ} (hT8 : (8 : ℝ) ^ (12 : ℕ) ≤ T) {C : Fin m → ℝ} (hC : 0 ≤ C)
    (N : ℕ) (cls : Fin N → Fin n) (coin : Fin N → Bool) (k₂ : Fin n → ℕ)
    (hwt_pos : 0 < wt1 lam (thresholdProbs lam (tau T 0) (sel fun l => C l / tau T 0)) N cls coin)
    (hG1 : ∀ j, |(((hist cls j + k₂ j : ℕ) : ℝ)) - lam j * T| ≤
      (lam_min / 4 * (T ^ (1 / 12 : ℝ)) ^ (7 : ℕ)) / (1 + α * (n : ℝ)))
    (hG2 : ∀ j, |(k₂ j : ℝ) - lam j * tau T 1| ≤
      lam_min / 4 * (T ^ (1 / 12 : ℝ)) ^ (7 : ℕ))
    (hG3 : ∀ j, |(markedCount cls coin j : ℝ) -
        (tau T 0 - tau T 1) * lam j *
          thresholdProbs lam (tau T 0) (sel fun l => C l / tau T 0) j| ≤
      lam_min / 4 * (T ^ (1 / 12 : ℝ)) ^ (7 : ℕ)) :
    piValue A r C (fun j => ((hist cls j + k₂ j : ℕ) : ℝ)) ≤
      (runWindow A r (List.ofFn fun i => (cls i, coin i)) C).1 +
        piValue A r (runWindow A r (List.ofFn fun i => (cls i, coin i)) C).2
          (fun j => (k₂ j : ℝ)) := by
  let q : ℝ := T ^ (1 / 12 : ℝ)
  let d : ℝ := q ^ (7 : ℕ)
  let h : ℝ := lam_min / 4 * d
  let B : ℝ := 1 + α * (n : ℝ)
  let τ₁ : ℝ := tau T 1
  let ℓ : ℝ := tau T 0 - tau T 1
  let ε : ℝ := T ^ (-(1 / 4 : ℝ))
  obtain ⟨hq8, hq12, htau0, htau1, _, hT14⟩ := rpow_identities hT8
  change 8 ≤ q at hq8
  change q ^ (12 : ℕ) = T at hq12
  change tau T 1 = q ^ (10 : ℕ) at htau1
  change T ^ (-(1 / 4 : ℝ)) = (q ^ (3 : ℕ))⁻¹ at hT14
  have hT_pos : 0 < T := lt_of_lt_of_le (by positivity) hT8
  have hq1 : 1 ≤ q := by linarith
  have hq_pos : 0 < q := by linarith
  have hB_pos : 0 < B := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hα0 (Nat.cast_nonneg n))
  have hd_pos : 0 < d := pow_pos hq_pos 7
  have hh_pos : 0 < h := mul_pos (div_pos hlam_min_pos (by norm_num)) hd_pos
  have hτ_ε : τ₁ * ε = d := by
    change tau T 1 * T ^ (-(1 / 4 : ℝ)) = q ^ (7 : ℕ)
    rw [htau1, hT14]
    have hq3_ne : q ^ (3 : ℕ) ≠ 0 := (pow_pos hq_pos 3).ne'
    field_simp
  have hT_ε : T * ε = q ^ (9 : ℕ) := by
    change T * T ^ (-(1 / 4 : ℝ)) = q ^ (9 : ℕ)
    rw [hT14, ← hq12]
    have hq3_ne : q ^ (3 : ℕ) ≠ 0 := (pow_pos hq_pos 3).ne'
    field_simp
  have hτ_sub_Tε : (7 / 8 : ℝ) * d ≤ τ₁ - T * ε := by
    change (7 / 8 : ℝ) * d ≤ tau T 1 - T * ε
    rw [htau1, hT_ε]
    have h1 : (7 : ℝ) * q ^ (9 : ℕ) ≤ q ^ (10 : ℕ) - q ^ (9 : ℕ) := by
      have heq : q ^ (10 : ℕ) - q ^ (9 : ℕ) = (q - 1) * q ^ (9 : ℕ) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hq_pos.le 9)
    have h2 : d ≤ q ^ (9 : ℕ) := q_pow_le hq1 (by norm_num)
    linarith
  -- DLP solution and stability
  let x : Fin n → ℝ := sel (fun l => C l / T)
  let p : Fin n → ℝ := thresholdProbs lam T x
  have hp_eq : thresholdProbs lam (tau T 0) (sel fun l => C l / tau T 0) = p := by
    dsimp [p, x]; rw [htau0]
  rw [hp_eq] at hwt_pos hG3
  obtain ⟨hxC_T, hx0_T, hxlam_T, hxopt_T⟩ := dlp_scaled_opt A r lam hlam hr hsel hT_pos hC
  let K : Fin n → ℝ := fun j => ((hist cls j + k₂ j : ℕ) : ℝ)
  let Z : Fin n → ℝ := fun j => (markedCount cls coin j : ℝ)
  change ∀ j, |K j - lam j * T| ≤ h / B at hG1
  change ∀ j, |(k₂ j : ℝ) - lam j * τ₁| ≤ h at hG2
  change ∀ j, |Z j - ℓ * lam j * p j| ≤ h at hG3
  obtain ⟨zbar, hzC, hz0, hzK, hzopt, hz_dist⟩ := hstab C hC
    (fun j => lam j * T) K (fun j => mul_nonneg (hlam j).le hT_pos.le)
    (fun j => Nat.cast_nonneg _) (T • x) hxC_T hx0_T hxlam_T hxopt_T
  have hGamma_le : α * ∑ k, |K k - lam k * T| ≤ h := by
    have hsum : ∑ k, |K k - lam k * T| ≤ (n : ℝ) * (h / B) := by
      calc ∑ k, |K k - lam k * T| ≤ ∑ _k : Fin n, (h / B) := sum_le_sum fun k _ => hG1 k
        _ = (n : ℝ) * (h / B) := by simp
    calc α * ∑ k, |K k - lam k * T| ≤ α * ((n : ℝ) * (h / B)) :=
          mul_le_mul_of_nonneg_left hsum hα0
      _ = (α * (n : ℝ) / B) * h := by ring
      _ ≤ 1 * h := by
          refine mul_le_mul_of_nonneg_right ?_ hh_pos.le
          rw [div_le_one hB_pos]
          dsimp [B]; linarith
      _ = h := one_mul h
  have hzbar_near : ∀ j, |zbar j - T * x j| ≤ h := fun j =>
    le_trans (by simpa [Pi.smul_apply, smul_eq_mul] using hz_dist j) hGamma_le
  have hZ_bounds : ∀ j, Z j ≤ zbar j ∧ zbar j ≤ Z j + (k₂ j : ℝ) := by
    intro j
    have hlamj_d : 4 * h ≤ lam j * d := by
      calc 4 * h = lam_min * d := by dsimp [h]; ring
        _ ≤ lam j * d := mul_le_mul_of_nonneg_right (hlam_min_le j) hd_pos.le
    have hzbar_lo : T * x j - h ≤ zbar j := by linarith [(abs_le.mp (hzbar_near j)).1]
    have hzbar_hi : zbar j ≤ T * x j + h := by linarith [(abs_le.mp (hzbar_near j)).2]
    have hℓ_def : ℓ = T - τ₁ := by dsimp [ℓ, τ₁]; rw [htau0]
    have hdiff_j : (7 / 2 : ℝ) * h ≤ lam j * (τ₁ - T * ε) := by
      have h1 : lam j * ((7 / 8 : ℝ) * d) ≤ lam j * (τ₁ - T * ε) :=
        mul_le_mul_of_nonneg_left hτ_sub_Tε (hlam j).le
      have h2 : lam j * ((7 / 8 : ℝ) * d) = (7 / 8 : ℝ) * (lam j * d) := by ring
      linarith
    by_cases hlow : x j < lam j * ε
    · have hpj0 : p j = 0 := by unfold p thresholdProbs; exact if_pos hlow
      have hZj0 : Z j = 0 := by
        dsimp [Z]; rw [wt1_pos_imp_zero hwt_pos hpj0]; simp
      refine ⟨by rw [hZj0]; exact hz0 j, ?_⟩
      have hk2_lo : lam j * τ₁ - h ≤ (k₂ j : ℝ) := by linarith [(abs_le.mp (hG2 j)).1]
      have hTx_lt : T * x j < lam j * (T * ε) := by
        have hm := mul_lt_mul_of_pos_left hlow hT_pos
        have hrw : T * (lam j * ε) = lam j * (T * ε) := by ring
        linarith
      have hlin_eq : lam j * (τ₁ - T * ε) = lam j * τ₁ - lam j * (T * ε) := by ring
      linarith [hZj0]
    · have hlow' : lam j * ε ≤ x j := le_of_not_gt hlow
      by_cases hhigh : x j > lam j * (1 - ε)
      · have hpj1 : p j = 1 := by
          unfold p thresholdProbs
          rw [if_neg hlow, if_pos hhigh]
        have hZj_hist : markedCount cls coin j = hist cls j := wt1_pos_imp_hist hwt_pos hpj1
        have hZK : Z j + (k₂ j : ℝ) = K j := by
          dsimp [Z, K]; rw [hZj_hist]; push_cast; rfl
        refine ⟨?_, by rw [hZK]; exact hzK j⟩
        have hZ_hi : Z j ≤ ℓ * lam j + h := by
          have := (abs_le.mp (hG3 j)).2
          rw [hpj1, mul_one] at this
          linarith
        have hTx_gt : lam j * (T - T * ε) < T * x j := by
          have hm := mul_lt_mul_of_pos_left hhigh hT_pos
          have hrw : T * (lam j * (1 - ε)) = lam j * (T - T * ε) := by ring
          linarith
        have hℓ_lam : ℓ * lam j = lam j * T - lam j * τ₁ := by rw [hℓ_def]; ring
        have hlin_eq : lam j * (T - T * ε) = lam j * T - lam j * (T * ε) := by ring
        have hlin_eq2 : lam j * (τ₁ - T * ε) = lam j * τ₁ - lam j * (T * ε) := by ring
        linarith
      · have hhigh' : x j ≤ lam j * (1 - ε) := le_of_not_gt hhigh
        have hpj_mid : p j = x j / lam j := by
          unfold p thresholdProbs
          rw [if_neg hlow, if_neg hhigh]
        have hℓ_p : ℓ * lam j * p j = ℓ * x j := by
          rw [hpj_mid]
          have := (hlam j).ne'
          field_simp
        have hZ_lo : ℓ * x j - h ≤ Z j := by
          have := (abs_le.mp (hG3 j)).1
          rw [hℓ_p] at this
          linarith
        have hZ_hi : Z j ≤ ℓ * x j + h := by
          have := (abs_le.mp (hG3 j)).2
          rw [hℓ_p] at this
          linarith
        have hτ_pos : 0 ≤ τ₁ := by change 0 ≤ tau T 1; rw [htau1]; exact pow_nonneg hq_pos.le 10
        have hτx_lo : 4 * h ≤ τ₁ * x j := by
          have hm : τ₁ * (lam j * ε) ≤ τ₁ * x j := mul_le_mul_of_nonneg_left hlow' hτ_pos
          have heq : τ₁ * (lam j * ε) = lam j * d := by rw [← hτ_ε]; ring
          linarith
        have hτ_compl_lo : 4 * h ≤ τ₁ * (lam j - x j) := by
          have hsub_ge : lam j * ε ≤ lam j - x j := by linarith
          have hm : τ₁ * (lam j * ε) ≤ τ₁ * (lam j - x j) := mul_le_mul_of_nonneg_left hsub_ge hτ_pos
          have heq : τ₁ * (lam j * ε) = lam j * d := by rw [← hτ_ε]; ring
          linarith
        have hTx_split : T * x j = ℓ * x j + τ₁ * x j := by rw [hℓ_def]; ring
        have hk2_lo : lam j * τ₁ - h ≤ (k₂ j : ℝ) := by linarith [(abs_le.mp (hG2 j)).1]
        refine ⟨by linarith, ?_⟩
        have hcompl_eq : τ₁ * (lam j - x j) = lam j * τ₁ - τ₁ * x j := by ring
        linarith
  have hAZ_le_C : ∀ l, ∑ j, A l j * (listMarkedCount (List.ofFn fun i => (cls i, coin i)) j : ℝ) ≤ C l := by
    intro l
    simp_rw [listMarkedCount_ofFn]
    calc ∑ j, A l j * Z j ≤ ∑ j, A l j * zbar j :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hZ_bounds j).1 (hA l j)
      _ = (A *ᵥ zbar) l := rfl
      _ ≤ C l := hzC l
  rw [runWindow_when_fits A r hA _ C hAZ_le_C]
  simp only [listMarkedCount_ofFn]
  let w : Fin n → ℝ := fun j => zbar j - Z j
  have hw0 : 0 ≤ w := fun j => sub_nonneg.mpr (hZ_bounds j).1
  have hwk2 : w ≤ fun j => (k₂ j : ℝ) := fun j => sub_le_iff_le_add'.mpr (hZ_bounds j).2
  have hwC : A *ᵥ w ≤ fun l => C l - ∑ j, A l j * Z j := by
    intro l
    calc (A *ᵥ w) l = ∑ j, A l j * (zbar j - Z j) := rfl
      _ = (A *ᵥ zbar) l - ∑ j, A l j * Z j := by simp [mulVec, dotProduct, mul_sub, sum_sub_distrib]
      _ ≤ C l - ∑ j, A l j * Z j := sub_le_sub_right (hzC l) _
  have hw_val : r ⬝ᵥ w ≤ piValue A r (fun l => C l - ∑ j, A l j * Z j) (fun j => (k₂ j : ℝ)) :=
    le_piValue A r hr _ _ w hwC hw0 hwk2
  rw [← hzopt]
  have hr_split : r ⬝ᵥ zbar = (∑ j, r j * Z j) + r ⬝ᵥ w := by
    simp [dotProduct, w, mul_sub, sum_sub_distrib]
  linarith

/-! ### 6. Tail Probability Bound Helper and Sum Bound -/

lemma tail_strict_le {μ x β_exp : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hxμ : x ≤ μ)
    (hβ : β_exp ≤ x ^ 2 / (3 * μ)) :
    (∑' m : ℕ, poissonPMF μ m * (if x < |(m : ℝ) - μ| then (1 : ℝ) else 0)) ≤
      2 * Real.exp (-β_exp) := by
  have hpt : ∀ m : ℕ, poissonPMF μ m * (if x < |(m : ℝ) - μ| then (1 : ℝ) else 0) ≤
      if x ≤ |(m : ℝ) - μ| then poissonPMF μ m else 0 := by
    intro m
    split_ifs with h1 h2
    · rw [mul_one]
    · exact False.elim (h2 h1.le)
    · rw [mul_zero]; exact pmf_nonneg μ m
    · rw [mul_zero]
  have hs1 : Summable (fun m : ℕ => poissonPMF μ m * (if x < |(m : ℝ) - μ| then (1 : ℝ) else 0)) := by
    refine Summable.of_nonneg_of_le
      (fun m => mul_nonneg (pmf_nonneg μ m) (by split_ifs <;> norm_num))
      (fun m => ?_) (pmf_summable μ)
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]; exact pmf_nonneg μ m
  have hs2 : Summable (fun m : ℕ => if x ≤ |(m : ℝ) - μ| then poissonPMF μ m else 0) := by
    refine Summable.of_nonneg_of_le
      (fun m => by split_ifs; exact pmf_nonneg μ m; exact le_rfl)
      (fun m => by split_ifs; exact le_rfl; exact pmf_nonneg μ m) (pmf_summable μ)
  calc (∑' m : ℕ, poissonPMF μ m * (if x < |(m : ℝ) - μ| then (1 : ℝ) else 0))
      ≤ ∑' m : ℕ, if x ≤ |(m : ℝ) - μ| then poissonPMF μ m else 0 :=
        Summable.tsum_le_tsum hpt hs1 hs2
    _ ≤ 2 * Real.exp (-(x ^ 2) / (3 * μ)) := poisson_tail_bound μ x hμ hx hxμ
    _ ≤ 2 * Real.exp (-β_exp) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        rw [neg_div]
        linarith

lemma tail_sum_bound {n : ℕ} (lam x : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hx0 : 0 ≤ x) (hx1 : x ≤ lam)
    {lam_min lam_max : ℝ} (hlam_min_pos : 0 < lam_min) (hlam_max_pos : 0 < lam_max)
    (hlam_min_le : ∀ j, lam_min ≤ lam j) (hlam_max_ge : ∀ j, lam j ≤ lam_max)
    {B : ℝ} (hB_ge1 : 1 ≤ B) {T : ℝ} (hT8 : (8 : ℝ) ^ (12 : ℕ) ≤ T) :
    ∑ j : Fin n, (
      (∑' m : ℕ, poissonPMF (lam j * T) m *
        (if (lam_min / 4 * (T ^ (1 / 12 : ℝ)) ^ (7 : ℕ)) / B < |(m : ℝ) - lam j * T|
          then (1 : ℝ) else 0)) +
      (∑' m : ℕ, poissonPMF (lam j * tau T 1) m *
        (if lam_min / 4 * (T ^ (1 / 12 : ℝ)) ^ (7 : ℕ) < |(m : ℝ) - lam j * tau T 1|
          then (1 : ℝ) else 0)) +
      (∑' m : ℕ, poissonPMF (lam j * thresholdProbs lam (tau T 0) x j * (tau T 0 - tau T 1)) m *
        (if lam_min / 4 * (T ^ (1 / 12 : ℝ)) ^ (7 : ℕ) <
            |(m : ℝ) - (tau T 0 - tau T 1) * lam j * thresholdProbs lam (tau T 0) x j|
          then (1 : ℝ) else 0))) ≤
      6 * (n : ℝ) * Real.exp (-(lam_min ^ 2 / (48 * lam_max * B ^ 2)) * T ^ (1 / 6 : ℝ)) := by
  let q := T ^ (1 / 12 : ℝ)
  let h := lam_min / 4 * q ^ (7 : ℕ)
  let β := lam_min ^ 2 / (48 * lam_max * B ^ 2)
  let τ₁ := tau T 1
  let ℓ := tau T 0 - tau T 1
  let p := thresholdProbs lam (tau T 0) x
  change ∑ j : Fin n, (
      (∑' m : ℕ, poissonPMF (lam j * T) m * (if h / B < |(m : ℝ) - lam j * T| then (1 : ℝ) else 0)) +
      (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
      (∑' m : ℕ, poissonPMF (lam j * p j * ℓ) m * (if h < |(m : ℝ) - ℓ * lam j * p j| then (1 : ℝ) else 0))) ≤
      6 * (n : ℝ) * Real.exp (-β * T ^ (1 / 6 : ℝ))
  obtain ⟨hq8, hq12, htau0, htau1, hT16, hT14⟩ := rpow_identities hT8
  change 8 ≤ q at hq8
  change q ^ (12 : ℕ) = T at hq12
  change tau T 1 = q ^ (10 : ℕ) at htau1
  change T ^ (1 / 6 : ℝ) = q ^ (2 : ℕ) at hT16
  change T ^ (-(1 / 4 : ℝ)) = (q ^ (3 : ℕ))⁻¹ at hT14
  have hT_pos : 0 < T := lt_of_lt_of_le (by positivity) hT8
  have hq1 : 1 ≤ q := by linarith
  have hq_pos : 0 < q := by linarith
  have hB_pos : 0 < B := by linarith
  have hd_pos : 0 < q ^ (7 : ℕ) := pow_pos hq_pos 7
  have hh_pos : 0 < h := mul_pos (div_pos hlam_min_pos (by norm_num)) hd_pos
  have hhB_pos : 0 < h / B := div_pos hh_pos hB_pos
  have hhB_le_h : h / B ≤ h := div_le_self hh_pos.le hB_ge1
  have hτ₁_pos : 0 < τ₁ := by change 0 < tau T 1; rw [htau1]; exact pow_pos hq_pos 10
  have hτ₁_le_T : τ₁ ≤ T := by
    change tau T 1 ≤ T
    rw [htau1, ← hq12]
    exact q_pow_le hq1 (by norm_num)
  have hℓ_nonneg : 0 ≤ ℓ := by change 0 ≤ tau T 0 - τ₁; rw [htau0]; linarith
  have hℓ_le_T : ℓ ≤ T := by change tau T 0 - τ₁ ≤ T; rw [htau0]; linarith
  have hℓ_ge_half : T / 2 ≤ ℓ := by
    change T / 2 ≤ tau T 0 - tau T 1
    rw [htau0, htau1, ← hq12]
    have hq2 : 2 ≤ q ^ (2 : ℕ) := by
      calc (2 : ℝ) ≤ q ^ (1 : ℕ) := by rw [pow_one]; linarith
        _ ≤ q ^ (2 : ℕ) := q_pow_le hq1 (by norm_num)
    have hprod : 0 ≤ q ^ (10 : ℕ) * (q ^ (2 : ℕ) - 2) :=
      mul_nonneg (pow_nonneg hq_pos.le 10) (by linarith)
    have hident : 2 * (q ^ (12 : ℕ) - q ^ (10 : ℕ)) - q ^ (12 : ℕ) =
        q ^ (10 : ℕ) * (q ^ (2 : ℕ) - 2) := by ring
    linarith
  have hd_le_T : q ^ (7 : ℕ) ≤ T := by rw [← hq12]; exact q_pow_le hq1 (by norm_num)
  have hd_le_τ₁ : q ^ (7 : ℕ) ≤ τ₁ := by change q ^ (7 : ℕ) ≤ tau T 1; rw [htau1]; exact q_pow_le hq1 (by norm_num)
  have hexp_bound : ∀ {μ x_thr : ℝ}, 0 < μ → μ ≤ lam_max * T → h / B ≤ x_thr →
      β * T ^ (1 / 6 : ℝ) ≤ x_thr ^ 2 / (3 * μ) := by
    intro μ x_thr hμ0 hμ_max hx_ge
    rw [hT16]
    rw [← hq12] at hμ_max
    have hnum : (h / B) ^ 2 ≤ x_thr ^ 2 := sq_le_sq' (by linarith) hx_ge
    have hden : 3 * μ ≤ 3 * (lam_max * q ^ (12 : ℕ)) := by linarith
    have heq : β * q ^ (2 : ℕ) = (h / B) ^ 2 / (3 * (lam_max * q ^ (12 : ℕ))) := by
      dsimp [β, h]
      have hq12_ne : q ^ (12 : ℕ) ≠ 0 := (pow_pos hq_pos 12).ne'
      have hlmax_ne : lam_max ≠ 0 := hlam_max_pos.ne'
      have hB_ne : B ≠ 0 := hB_pos.ne'
      field_simp
      ring
    rw [heq]
    exact div_le_div₀ (sq_nonneg x_thr) hnum (by positivity) hden
  have hneg_β : -(β * T ^ (1 / 6 : ℝ)) = -β * T ^ (1 / 6 : ℝ) := by ring
  have hj_le : ∀ j : Fin n,
      (∑' m : ℕ, poissonPMF (lam j * T) m * (if h / B < |(m : ℝ) - lam j * T| then (1 : ℝ) else 0)) +
      (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
      (∑' m : ℕ, poissonPMF (lam j * p j * ℓ) m * (if h < |(m : ℝ) - ℓ * lam j * p j| then (1 : ℝ) else 0)) ≤
        6 * Real.exp (-β * T ^ (1 / 6 : ℝ)) := by
    intro j
    have hx1_le_μ1 : h / B ≤ lam j * T := by
      have hm : lam_min * q ^ (7 : ℕ) ≤ lam j * T :=
        mul_le_mul (hlam_min_le j) hd_le_T hd_pos.le (hlam j).le
      have hh_le : h ≤ lam_min * q ^ (7 : ℕ) := by dsimp [h]; linarith [mul_pos hlam_min_pos hd_pos]
      linarith
    have ht1 := tail_strict_le (mul_pos (hlam j) hT_pos) hhB_pos hx1_le_μ1
      (hexp_bound (mul_pos (hlam j) hT_pos)
        (mul_le_mul_of_nonneg_right (hlam_max_ge j) hT_pos.le) le_rfl)
    rw [hneg_β] at ht1
    have hx2_le_μ2 : h ≤ lam j * τ₁ := by
      have hm : lam_min * q ^ (7 : ℕ) ≤ lam j * τ₁ :=
        mul_le_mul (hlam_min_le j) hd_le_τ₁ hd_pos.le (hlam j).le
      have hh_le : h ≤ lam_min * q ^ (7 : ℕ) := by dsimp [h]; linarith [mul_pos hlam_min_pos hd_pos]
      linarith
    have ht2 := tail_strict_le (mul_pos (hlam j) hτ₁_pos) hh_pos hx2_le_μ2
      (hexp_bound (mul_pos (hlam j) hτ₁_pos)
        (le_trans (mul_le_mul_of_nonneg_left hτ₁_le_T (hlam j).le)
          (mul_le_mul_of_nonneg_right (hlam_max_ge j) hT_pos.le)) hhB_le_h)
    rw [hneg_β] at ht2
    obtain ⟨hp0_j, hp1_j⟩ := thresholdProbs_mem lam (tau T 0) x hlam hx0 hx1 j
    change 0 ≤ p j at hp0_j
    change p j ≤ 1 at hp1_j
    have ht3 : (∑' m : ℕ, poissonPMF (lam j * p j * ℓ) m *
        (if h < |(m : ℝ) - ℓ * lam j * p j| then (1 : ℝ) else 0)) ≤
          2 * Real.exp (-β * T ^ (1 / 6 : ℝ)) := by
      rcases eq_or_lt_of_le hp0_j with hpj0 | hpj_pos
      · have hzero_term : ∀ m : ℕ, poissonPMF (lam j * p j * ℓ) m *
            (if h < |(m : ℝ) - ℓ * lam j * p j| then (1 : ℝ) else 0) = 0 := by
          intro m
          rw [← hpj0, mul_zero, zero_mul, mul_zero, pmf_zero]
          rcases m with _ | m
          · simp [not_lt.mpr hh_pos.le]
          · simp
        simp_rw [hzero_term, tsum_zero]
        positivity
      · have hpj_ge_eps : (q ^ (3 : ℕ))⁻¹ ≤ p j := by
          have hp_def : p j = thresholdProbs lam (tau T 0) x j := rfl
          rw [hp_def] at hpj_pos ⊢
          unfold thresholdProbs at hpj_pos ⊢
          split_ifs at hpj_pos ⊢ with hc1 hc2
          · linarith
          · exact inv_le_one_of_one_le₀ (one_le_pow₀ hq1)
          · rw [htau0, hT14] at hc1
            rw [le_div_iff₀ (hlam j)]
            linarith [le_of_not_gt hc1]
        have hμ3_eq : lam j * p j * ℓ = ℓ * lam j * p j := by ring
        rw [hμ3_eq]
        have hx3_le_μ3 : h ≤ ℓ * lam j * p j := by
          have ha : T / 2 * lam_min ≤ ℓ * lam j :=
            mul_le_mul hℓ_ge_half (hlam_min_le j) hlam_min_pos.le hℓ_nonneg
          have h1 : (T / 2 * lam_min) * (q ^ (3 : ℕ))⁻¹ ≤ (ℓ * lam j) * p j :=
            mul_le_mul ha hpj_ge_eps (inv_nonneg.mpr (pow_nonneg hq_pos.le 3))
              (mul_nonneg hℓ_nonneg (hlam j).le)
          have h2 : (T / 2 * lam_min) * (q ^ (3 : ℕ))⁻¹ = (lam_min / 2) * q ^ (9 : ℕ) := by
            rw [← hq12]
            have hq3_ne : q ^ (3 : ℕ) ≠ 0 := (pow_pos hq_pos 3).ne'
            field_simp
          have h3 : h ≤ (lam_min / 2) * q ^ (9 : ℕ) := by
            have hq79 : q ^ (7 : ℕ) ≤ q ^ (9 : ℕ) := q_pow_le hq1 (by norm_num)
            have hm : (lam_min / 4) * q ^ (7 : ℕ) ≤ (lam_min / 4) * q ^ (9 : ℕ) :=
              mul_le_mul_of_nonneg_left hq79 (div_nonneg hlam_min_pos.le (by norm_num))
            have hm2 : (lam_min / 4) * q ^ (9 : ℕ) ≤ (lam_min / 2) * q ^ (9 : ℕ) :=
              mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hq_pos.le 9)
            dsimp [h]; linarith
          linarith
        have hμ3_pos : 0 < ℓ * lam j * p j := lt_of_lt_of_le hh_pos hx3_le_μ3
        have hμ3_max : ℓ * lam j * p j ≤ lam_max * T := by
          calc ℓ * lam j * p j ≤ ℓ * lam j * 1 :=
                mul_le_mul_of_nonneg_left hp1_j (mul_nonneg hℓ_nonneg (hlam j).le)
            _ = lam j * ℓ := by ring
            _ ≤ lam_max * T := mul_le_mul (hlam_max_ge j) hℓ_le_T hℓ_nonneg hlam_max_pos.le
        have hraw := tail_strict_le hμ3_pos hh_pos hx3_le_μ3 (hexp_bound hμ3_pos hμ3_max hhB_le_h)
        rwa [hneg_β] at hraw
    linarith
  calc _ ≤ ∑ _j : Fin n, 6 * Real.exp (-β * T ^ (1 / 6 : ℝ)) := sum_le_sum fun j _ => hj_le j
    _ = 6 * (n : ℝ) * Real.exp (-β * T ^ (1 / 6 : ℝ)) := by simp; ring

/-! ### 7. Joint Expectation Series Bound (Modularized) -/

lemma sq_add_sum_le {n : ℕ} (a : ℝ) (v : Fin n → ℝ) :
    (a + ∑ j, v j) ^ 2 ≤ 2 * a ^ 2 + 2 * (n : ℝ) * ∑ j, v j ^ 2 := by
  have h1 : (a + ∑ j, v j) ^ 2 ≤ 2 * a ^ 2 + 2 * (∑ j, v j) ^ 2 := by
    nlinarith [sq_nonneg (a - ∑ j, v j)]
  have h2 : (∑ j, v j) ^ 2 ≤ (n : ℝ) * ∑ j, v j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := v)
    simpa using this
  linarith

noncomputable def Fhi {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (C : Fin m → ℝ)
    (k : Fin n → ℕ) : ℝ :=
  piValue A r C (fun j => (k j : ℝ))

noncomputable def Vpt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (C : Fin m → ℝ)
    (N : ℕ) (cls : Fin N → Fin n) (coin : Fin N → Bool) (k₂ : Fin n → ℕ) : ℝ :=
  (runWindow A r (List.ofFn fun i => (cls i, coin i)) C).1 +
    piValue A r (runWindow A r (List.ofFn fun i => (cls i, coin i)) C).2 (fun j => (k₂ j : ℝ))

noncomputable def badInd1 {n : ℕ} (lam : Fin n → ℝ) (T hB : ℝ)
    (j : Fin n) (N : ℕ) (cls : Fin N → Fin n) (k₂ : Fin n → ℕ) : ℝ :=
  if hB < |(((hist cls j + k₂ j : ℕ) : ℝ)) - lam j * T| then 1 else 0

noncomputable def badInd2 {n : ℕ} (lam : Fin n → ℝ) (τ₁ h : ℝ)
    (j : Fin n) (k₂ : Fin n → ℕ) : ℝ :=
  if h < |(k₂ j : ℝ) - lam j * τ₁| then 1 else 0

noncomputable def badInd3 {n : ℕ} (lam p : Fin n → ℝ) (ℓ h : ℝ)
    (j : Fin n) (N : ℕ) (cls : Fin N → Fin n) (coin : Fin N → Bool) : ℝ :=
  if h < |(markedCount cls coin j : ℝ) - ℓ * lam j * p j| then 1 else 0

noncomputable def rhsK2 {n : ℕ} (r lam p : Fin n → ℝ) (T ℓ τ₁ a_par h hB : ℝ)
    (N : ℕ) (cls : Fin N → Fin n) (coin : Fin N → Bool) : ℝ :=
  ((∑ j, r j) / (2 * a_par)) *
      (2 * (N : ℝ) ^ 2 + 2 * (n : ℝ) * ∑ j, ((lam j * τ₁) ^ 2 + lam j * τ₁)) +
    ((∑ j, r j) * a_par / 2) * ∑ j, (
      (∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂) +
      (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
      badInd3 lam p ℓ h j N cls coin)

lemma hindsight_joint_eq_and_summable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam p : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hn : 0 < n) (hr : ∀ j, 0 ≤ r j)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    {T ℓ τ₁ : ℝ} (hℓ : 0 ≤ ℓ) (hτ₁ : 0 < τ₁) (hsum_T : ℓ + τ₁ = T)
    {C : Fin m → ℝ} (hC : 0 ≤ C) :
    hindsightValue A r lam T C =
      (∑' N : ℕ, poissonPMF ((∑ j, lam j) * ℓ) N *
        ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
          wt1 lam p N cls coin *
            ∑' k₂ : Fin n → ℕ, prodPMF (fun j => lam j * τ₁) k₂ * Fhi A r C (hist cls + k₂)) ∧
    Summable (fun N : ℕ => poissonPMF ((∑ j, lam j) * ℓ) N *
      ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
        wt1 lam p N cls coin *
          ∑' k₂ : Fin n → ℕ, prodPMF (fun j => lam j * τ₁) k₂ * Fhi A r C (hist cls + k₂)) := by
  let R : ℝ := ∑ j, r j
  have hR0 : 0 ≤ R := sum_nonneg fun j _ => hr j
  let Λ : ℝ := ∑ j, lam j
  have hΛ_pos : 0 < Λ := by
    have : lam ⟨0, hn⟩ ≤ Λ := single_le_sum (f := lam) (fun j _ => (hlam j).le) (mem_univ _)
    linarith [hlam ⟨0, hn⟩]
  have hθ : 0 ≤ Λ * ℓ := mul_nonneg hΛ_pos.le hℓ
  have hμ₂ : ∀ j, 0 ≤ lam j * τ₁ := fun j => (mul_pos (hlam j) hτ₁).le
  have hF_hi0 : ∀ k, 0 ≤ Fhi A r C k := fun k => piValue_nonneg A r hr C hC _ fun j => Nat.cast_nonneg _
  have hF_hi_bnd : ∀ k, Fhi A r C k ≤ 0 + R * ∑ j, (k j : ℝ) := fun k => by
    rw [zero_add]; exact piValue_le_R_sum A r hr C hC _ fun j => Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · have hsup := wt1_superpos_conv_tsum lam p hlam hn hℓ hτ₁.le (Fhi A r C) hF_hi0 le_rfl hR0 hF_hi_bnd
    rw [hsum_T] at hsup
    unfold hindsightValue
    unfold prodPMF Fhi at hsup
    exact hsup.symm
  · have hdom : Summable (fun N : ℕ =>
        R * (poissonPMF (Λ * ℓ) N * (N : ℝ)) + (R * (Λ * τ₁)) * poissonPMF (Λ * ℓ) N) :=
      ((pmf_hasSum1 hθ).summable.mul_left R).add ((pmf_summable (Λ * ℓ)).mul_left (R * (Λ * τ₁)))
    refine Summable.of_nonneg_of_le (fun N => mul_nonneg (pmf_nonneg _ _)
      (sum_nonneg fun cls _ => sum_nonneg fun coin _ =>
        mul_nonneg (wt1_nonneg lam p hlam hp0 hp1 N cls coin)
          (tsum_nonneg fun k₂ => mul_nonneg (prodPMF_nonneg _ _) (hF_hi0 _)))) (fun N => ?_) hdom
    have hinner_le : ∀ (cls : Fin N → Fin n),
        (∑' k₂ : Fin n → ℕ, prodPMF (fun j => lam j * τ₁) k₂ * Fhi A r C (hist cls + k₂)) ≤
          R * (N : ℝ) + R * (Λ * τ₁) := by
      intro cls
      have hsh : ∑ j, (hist cls j : ℝ) = (N : ℝ) := by exact_mod_cast sum_hist cls
      have hs_k2 := prodPMF_linear_summable hμ₂ (fun k₂ => hF_hi0 (hist cls + k₂))
        (A₀ := R * (N : ℝ)) (B₀ := R) (mul_nonneg hR0 (Nat.cast_nonneg N)) hR0 (fun k₂ => by
          have := hF_hi_bnd (hist cls + k₂)
          simp only [zero_add, Pi.add_apply, Nat.cast_add, sum_add_distrib, hsh] at this
          linarith)
      have hdom_k2 : HasSum (fun k₂ : Fin n → ℕ =>
          (R * (N : ℝ)) * prodPMF (fun j => lam j * τ₁) k₂ +
            ∑ j, R * (prodPMF (fun j => lam j * τ₁) k₂ * (k₂ j : ℝ)))
          ((R * (N : ℝ)) * 1 + ∑ j, R * (lam j * τ₁)) :=
        ((prodPMF_hasSum0 _).mul_left _).add
          (hasSum_sum fun j _ => (prodPMF_coord_hasSum1 hμ₂ j).mul_left R)
      calc (∑' k₂, prodPMF (fun j => lam j * τ₁) k₂ * Fhi A r C (hist cls + k₂))
          ≤ ∑' k₂, ((R * (N : ℝ)) * prodPMF (fun j => lam j * τ₁) k₂ +
              ∑ j, R * (prodPMF (fun j => lam j * τ₁) k₂ * (k₂ j : ℝ))) := by
            refine Summable.tsum_le_tsum (fun k₂ => ?_) hs_k2 hdom_k2.summable
            calc prodPMF (fun j => lam j * τ₁) k₂ * Fhi A r C (hist cls + k₂)
                ≤ prodPMF (fun j => lam j * τ₁) k₂ * (R * (N : ℝ) + R * ∑ j, (k₂ j : ℝ)) := by
                  refine mul_le_mul_of_nonneg_left ?_ (prodPMF_nonneg _ _)
                  have := hF_hi_bnd (hist cls + k₂)
                  simp only [zero_add, Pi.add_apply, Nat.cast_add, sum_add_distrib, hsh] at this
                  linarith
              _ = _ := by
                  rw [mul_add, mul_sum, mul_sum]; congr 1
                  · ring
                  · exact sum_congr rfl fun j _ => by ring
        _ = (R * (N : ℝ)) * 1 + ∑ j, R * (lam j * τ₁) := hdom_k2.tsum_eq
        _ = R * (N : ℝ) + R * (Λ * τ₁) := by dsimp [Λ]; rw [← mul_sum, ← sum_mul]; ring
    calc poissonPMF (Λ * ℓ) N * ∑ cls, ∑ coin, wt1 lam p N cls coin *
            ∑' k₂, prodPMF (fun j => lam j * τ₁) k₂ * Fhi A r C (hist cls + k₂)
        ≤ poissonPMF (Λ * ℓ) N * ∑ cls, ∑ coin, wt1 lam p N cls coin * (R * (N : ℝ) + R * (Λ * τ₁)) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun cls _ => sum_le_sum fun coin _ => ?_) (pmf_nonneg _ _)
          exact mul_le_mul_of_nonneg_left (hinner_le cls) (wt1_nonneg lam p hlam hp0 hp1 N cls coin)
      _ = poissonPMF (Λ * ℓ) N * (R * (N : ℝ) + R * (Λ * τ₁)) := by
          simp_rw [← sum_mul, wt1_sum_eq_one lam p hlam hn N, one_mul]
      _ = R * (poissonPMF (Λ * ℓ) N * (N : ℝ)) + (R * (Λ * τ₁)) * poissonPMF (Λ * ℓ) N := by ring

lemma window_ho_eq_and_summable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam p : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hn : 0 < n) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    {ℓ τ₁ : ℝ} (hℓ : 0 ≤ ℓ) (hτ₁ : 0 < τ₁) {C : Fin m → ℝ} (hC : 0 ≤ C) :
    (∀ (N : ℕ) (cls : Fin N → Fin n) (coin : Fin N → Bool),
      HasSum (fun k₂ : Fin n → ℕ => prodPMF (fun j => lam j * τ₁) k₂ * Vpt A r C N cls coin k₂)
        ((runWindow A r (List.ofFn fun i => (cls i, coin i)) C).1 +
          hindsightValue A r lam τ₁ (runWindow A r (List.ofFn fun i => (cls i, coin i)) C).2)) ∧
    windowValue A r lam ℓ p C (hindsightValue A r lam τ₁) =
      (∑' N : ℕ, poissonPMF ((∑ j, lam j) * ℓ) N *
        ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
          wt1 lam p N cls coin *
            ∑' k₂ : Fin n → ℕ, prodPMF (fun j => lam j * τ₁) k₂ * Vpt A r C N cls coin k₂) ∧
    Summable (fun N : ℕ => poissonPMF ((∑ j, lam j) * ℓ) N *
      ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
        wt1 lam p N cls coin *
          ∑' k₂ : Fin n → ℕ, prodPMF (fun j => lam j * τ₁) k₂ * Vpt A r C N cls coin k₂) := by
  let R : ℝ := ∑ j, r j
  have hR0 : 0 ≤ R := sum_nonneg fun j _ => hr j
  let Λ : ℝ := ∑ j, lam j
  have hΛ_pos : 0 < Λ := by
    have : lam ⟨0, hn⟩ ≤ Λ := single_le_sum (f := lam) (fun j _ => (hlam j).le) (mem_univ _)
    linarith [hlam ⟨0, hn⟩]
  have hθ : 0 ≤ Λ * ℓ := mul_nonneg hΛ_pos.le hℓ
  have hμ₂ : ∀ j, 0 ≤ lam j * τ₁ := fun j => (mul_pos (hlam j) hτ₁).le
  have hk2_V_hasSum : ∀ (N : ℕ) (cls : Fin N → Fin n) (coin : Fin N → Bool),
      HasSum (fun k₂ : Fin n → ℕ => prodPMF (fun j => lam j * τ₁) k₂ * Vpt A r C N cls coin k₂)
        ((runWindow A r (List.ofFn fun i => (cls i, coin i)) C).1 +
          hindsightValue A r lam τ₁ (runWindow A r (List.ofFn fun i => (cls i, coin i)) C).2) := by
    intro N cls coin
    let rw_res := runWindow A r (List.ofFn fun i => (cls i, coin i)) C
    obtain ⟨_, _, hc_end⟩ := runWindow_bounds A r hr (List.ofFn fun i => (cls i, coin i)) C hC
    have hs_cont : Summable (fun k₂ : Fin n → ℕ =>
        prodPMF (fun j => lam j * τ₁) k₂ * piValue A r rw_res.2 (fun j => (k₂ j : ℝ))) :=
      prodPMF_linear_summable hμ₂
        (fun k₂ => piValue_nonneg A r hr rw_res.2 hc_end _ fun j => Nat.cast_nonneg _)
        le_rfl hR0 (fun k₂ => by
          rw [zero_add]; exact piValue_le_R_sum A r hr rw_res.2 hc_end _ fun j => Nat.cast_nonneg _)
    have hs1 := (prodPMF_hasSum0 (fun j => lam j * τ₁)).mul_right rw_res.1
    rw [one_mul] at hs1
    exact (hs1.add hs_cont.hasSum).congr_fun fun k₂ => by dsimp [Vpt, rw_res]; ring
  refine ⟨hk2_V_hasSum, ?_, ?_⟩
  · unfold windowValue
    congr 1; ext N
    congr 1; refine sum_congr rfl fun cls _ => sum_congr rfl fun coin _ => ?_
    rw [(hk2_V_hasSum N cls coin).tsum_eq]
    rfl
  · have hdom : Summable (fun N : ℕ =>
        R * (poissonPMF (Λ * ℓ) N * (N : ℝ)) + (τ₁ * (r ⬝ᵥ lam)) * poissonPMF (Λ * ℓ) N) :=
      ((pmf_hasSum1 hθ).summable.mul_left R).add ((pmf_summable (Λ * ℓ)).mul_left (τ₁ * (r ⬝ᵥ lam)))
    refine Summable.of_nonneg_of_le (fun N => mul_nonneg (pmf_nonneg _ _)
      (sum_nonneg fun cls _ => sum_nonneg fun coin _ => by
        rw [(hk2_V_hasSum N cls coin).tsum_eq]
        obtain ⟨hr1, _, hc2⟩ := runWindow_bounds A r hr (List.ofFn fun i => (cls i, coin i)) C hC
        refine mul_nonneg (wt1_nonneg lam p hlam hp0 hp1 N cls coin) (add_nonneg hr1 ?_)
        exact tsum_nonneg fun k => mul_nonneg (prod_nonneg fun j _ => pmf_nonneg _ _)
          (piValue_nonneg A r hr _ hc2 _ fun j => Nat.cast_nonneg _))) (fun N => ?_) hdom
    calc poissonPMF (Λ * ℓ) N * ∑ cls, ∑ coin, wt1 lam p N cls coin *
            ∑' k₂, prodPMF (fun j => lam j * τ₁) k₂ * Vpt A r C N cls coin k₂
        ≤ poissonPMF (Λ * ℓ) N * ∑ cls, ∑ coin, wt1 lam p N cls coin * (R * (N : ℝ) + τ₁ * (r ⬝ᵥ lam)) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun cls _ => sum_le_sum fun coin _ => ?_) (pmf_nonneg _ _)
          rw [(hk2_V_hasSum N cls coin).tsum_eq]
          obtain ⟨_, hr2, hc2⟩ := runWindow_bounds A r hr (List.ofFn fun i => (cls i, coin i)) C hC
          rw [List.length_ofFn] at hr2
          have hhi_c2 := hindsight_le_T_rho A r lam hlam hr hA hτ₁ hc2
          exact mul_le_mul_of_nonneg_left (by dsimp [R]; linarith) (wt1_nonneg lam p hlam hp0 hp1 N cls coin)
      _ = poissonPMF (Λ * ℓ) N * (R * (N : ℝ) + τ₁ * (r ⬝ᵥ lam)) := by
          simp_rw [← sum_mul, wt1_sum_eq_one lam p hlam hn N, one_mul]
      _ = R * (poissonPMF (Λ * ℓ) N * (N : ℝ)) + (τ₁ * (r ⬝ᵥ lam)) * poissonPMF (Λ * ℓ) N := by ring

lemma pointwise_amgm_dom {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam p : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    {T ℓ τ₁ a_par h hB : ℝ} (ha_pos : 0 < a_par) {C : Fin m → ℝ} (hC : 0 ≤ C)
    (hgood : ∀ (N : ℕ) (cls : Fin N → Fin n) (coin : Fin N → Bool) (k₂ : Fin n → ℕ),
      0 < wt1 lam p N cls coin →
      (∀ j, |(((hist cls j + k₂ j : ℕ) : ℝ)) - lam j * T| ≤ hB) →
      (∀ j, |(k₂ j : ℝ) - lam j * τ₁| ≤ h) →
      (∀ j, |(markedCount cls coin j : ℝ) - ℓ * lam j * p j| ≤ h) →
      Fhi A r C (hist cls + k₂) ≤ Vpt A r C N cls coin k₂)
    (N : ℕ) (cls : Fin N → Fin n) (coin : Fin N → Bool) (k₂ : Fin n → ℕ) :
    wt1 lam p N cls coin * (Fhi A r C (hist cls + k₂) - Vpt A r C N cls coin k₂) ≤
      wt1 lam p N cls coin * (
        ((∑ j, r j) / (2 * a_par)) * (2 * (N : ℝ) ^ 2 + 2 * (n : ℝ) * ∑ j, (k₂ j : ℝ) ^ 2) +
        ((∑ j, r j) * a_par / 2) * ∑ j,
          (badInd1 lam T hB j N cls k₂ + badInd2 lam τ₁ h j k₂ + badInd3 lam p ℓ h j N cls coin)) := by
  let R : ℝ := ∑ j, r j
  have hR0 : 0 ≤ R := sum_nonneg fun j _ => hr j
  have hw0 := wt1_nonneg lam p hlam hp0 hp1 N cls coin
  have hbad_nonneg : 0 ≤ ∑ j, (badInd1 lam T hB j N cls k₂ + badInd2 lam τ₁ h j k₂ + badInd3 lam p ℓ h j N cls coin) :=
    sum_nonneg fun j _ => by dsimp [badInd1, badInd2, badInd3]; split_ifs <;> norm_num
  have hsq_nonneg : 0 ≤ 2 * (N : ℝ) ^ 2 + 2 * (n : ℝ) * ∑ j, (k₂ j : ℝ) ^ 2 := by
    have : 0 ≤ ∑ j, (k₂ j : ℝ) ^ 2 := sum_nonneg fun j _ => sq_nonneg _
    positivity
  rcases eq_or_lt_of_le hw0 with hw_zero | hw_pos
  · rw [← hw_zero, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left ?_ hw_pos.le
    by_cases hG : (∀ j, |(((hist cls j + k₂ j : ℕ) : ℝ)) - lam j * T| ≤ hB) ∧
        (∀ j, |(k₂ j : ℝ) - lam j * τ₁| ≤ h) ∧
        (∀ j, |(markedCount cls coin j : ℝ) - ℓ * lam j * p j| ≤ h)
    · have hle0 := hgood N cls coin k₂ hw_pos hG.1 hG.2.1 hG.2.2
      have hrhs0 : 0 ≤ (R / (2 * a_par)) * (2 * (N : ℝ) ^ 2 + 2 * (n : ℝ) * ∑ j, (k₂ j : ℝ) ^ 2) +
          (R * a_par / 2) * ∑ j,
            (badInd1 lam T hB j N cls k₂ + badInd2 lam τ₁ h j k₂ + badInd3 lam p ℓ h j N cls coin) := by
        positivity
      dsimp [R] at hrhs0
      linarith
    · have hbad_ge1 : 1 ≤ ∑ j,
          (badInd1 lam T hB j N cls k₂ + badInd2 lam τ₁ h j k₂ + badInd3 lam p ℓ h j N cls coin) := by
        have hex : (∃ j, hB < |(((hist cls j + k₂ j : ℕ) : ℝ)) - lam j * T|) ∨
            (∃ j, h < |(k₂ j : ℝ) - lam j * τ₁|) ∨
            (∃ j, h < |(markedCount cls coin j : ℝ) - ℓ * lam j * p j|) := by
          by_contra hnone
          apply hG
          refine ⟨fun j => le_of_not_gt fun hj => hnone (Or.inl ⟨j, hj⟩),
            fun j => le_of_not_gt fun hj => hnone (Or.inr (Or.inl ⟨j, hj⟩)),
            fun j => le_of_not_gt fun hj => hnone (Or.inr (Or.inr ⟨j, hj⟩))⟩
        have hterm0 : ∀ j, 0 ≤ badInd1 lam T hB j N cls k₂ + badInd2 lam τ₁ h j k₂ + badInd3 lam p ℓ h j N cls coin := by
          intro j; dsimp [badInd1, badInd2, badInd3]; split_ifs <;> norm_num
        rcases hex with ⟨j₀, hj₀⟩ | ⟨j₀, hj₀⟩ | ⟨j₀, hj₀⟩
        · refine le_trans ?_ (single_le_sum (fun j _ => hterm0 j) (mem_univ j₀))
          have hb1 : badInd1 lam T hB j₀ N cls k₂ = 1 := if_pos hj₀
          have hb2 : 0 ≤ badInd2 lam τ₁ h j₀ k₂ := by dsimp [badInd2]; split_ifs <;> norm_num
          have hb3 : 0 ≤ badInd3 lam p ℓ h j₀ N cls coin := by dsimp [badInd3]; split_ifs <;> norm_num
          linarith
        · refine le_trans ?_ (single_le_sum (fun j _ => hterm0 j) (mem_univ j₀))
          have hb1 : 0 ≤ badInd1 lam T hB j₀ N cls k₂ := by dsimp [badInd1]; split_ifs <;> norm_num
          have hb2 : badInd2 lam τ₁ h j₀ k₂ = 1 := if_pos hj₀
          have hb3 : 0 ≤ badInd3 lam p ℓ h j₀ N cls coin := by dsimp [badInd3]; split_ifs <;> norm_num
          linarith
        · refine le_trans ?_ (single_le_sum (fun j _ => hterm0 j) (mem_univ j₀))
          have hb1 : 0 ≤ badInd1 lam T hB j₀ N cls k₂ := by dsimp [badInd1]; split_ifs <;> norm_num
          have hb2 : 0 ≤ badInd2 lam τ₁ h j₀ k₂ := by dsimp [badInd2]; split_ifs <;> norm_num
          have hb3 : badInd3 lam p ℓ h j₀ N cls coin = 1 := if_pos hj₀
          linarith
      obtain ⟨hr1, _, hc2⟩ := runWindow_bounds A r hr (List.ofFn fun i => (cls i, coin i)) C hC
      have hV0 : 0 ≤ Vpt A r C N cls coin k₂ :=
        add_nonneg hr1 (piValue_nonneg A r hr _ hc2 _ fun j => Nat.cast_nonneg _)
      have hF_le : Fhi A r C (hist cls + k₂) ≤ R * ((N : ℝ) + ∑ j, (k₂ j : ℝ)) := by
        have hsh : ∑ j, (hist cls j : ℝ) = (N : ℝ) := by exact_mod_cast sum_hist cls
        calc Fhi A r C (hist cls + k₂)
            ≤ (∑ j, r j) * ∑ j, (((hist cls + k₂) j : ℕ) : ℝ) :=
              piValue_le_R_sum A r hr C hC _ fun j => Nat.cast_nonneg _
          _ = R * ((N : ℝ) + ∑ j, (k₂ j : ℝ)) := by
              dsimp [R]; simp only [Nat.cast_add, sum_add_distrib, hsh]
      let S_val : ℝ := (N : ℝ) + ∑ j, (k₂ j : ℝ)
      have hquad : S_val ≤ S_val ^ 2 / (2 * a_par) + a_par / 2 := by
        rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (S_val - a_par)]
      have hS_sq : S_val ^ 2 ≤ 2 * (N : ℝ) ^ 2 + 2 * (n : ℝ) * ∑ j, (k₂ j : ℝ) ^ 2 :=
        sq_add_sum_le (N : ℝ) (fun j => (k₂ j : ℝ))
      calc Fhi A r C (hist cls + k₂) - Vpt A r C N cls coin k₂
          ≤ R * S_val := by dsimp [S_val]; linarith
        _ ≤ R * (S_val ^ 2 / (2 * a_par) + a_par / 2) := mul_le_mul_of_nonneg_left hquad hR0
        _ = (R / (2 * a_par)) * S_val ^ 2 + (R * a_par / 2) * 1 := by ring
        _ ≤ (R / (2 * a_par)) * (2 * (N : ℝ) ^ 2 + 2 * (n : ℝ) * ∑ j, (k₂ j : ℝ) ^ 2) +
              (R * a_par / 2) * ∑ j,
                (badInd1 lam T hB j N cls k₂ + badInd2 lam τ₁ h j k₂ + badInd3 lam p ℓ h j N cls coin) :=
            add_le_add (mul_le_mul_of_nonneg_left hS_sq (by positivity))
              (mul_le_mul_of_nonneg_left hbad_ge1 (by positivity))

lemma rhs_k2_hasSum {n : ℕ} (r lam p : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    {T ℓ τ₁ a_par h hB : ℝ} (hτ₁ : 0 < τ₁)
    (N : ℕ) (cls : Fin N → Fin n) (coin : Fin N → Bool) :
    HasSum (fun k₂ : Fin n → ℕ => prodPMF (fun j => lam j * τ₁) k₂ * (
      ((∑ j, r j) / (2 * a_par)) * (2 * (N : ℝ) ^ 2 + 2 * (n : ℝ) * ∑ j, (k₂ j : ℝ) ^ 2) +
      ((∑ j, r j) * a_par / 2) * ∑ j,
        (badInd1 lam T hB j N cls k₂ + badInd2 lam τ₁ h j k₂ + badInd3 lam p ℓ h j N cls coin)))
      (rhsK2 r lam p T ℓ τ₁ a_par h hB N cls coin) := by
  have hμ₂ : ∀ j, 0 ≤ lam j * τ₁ := fun j => (mul_pos (hlam j) hτ₁).le
  have hsq_hs : HasSum (fun k₂ : Fin n → ℕ => prodPMF (fun j => lam j * τ₁) k₂ *
      (2 * (N : ℝ) ^ 2 + 2 * (n : ℝ) * ∑ j, (k₂ j : ℝ) ^ 2))
      (2 * (N : ℝ) ^ 2 + 2 * (n : ℝ) * ∑ j, ((lam j * τ₁) ^ 2 + lam j * τ₁)) := by
    have h1 := (prodPMF_hasSum0 (fun j => lam j * τ₁)).mul_left (2 * (N : ℝ) ^ 2)
    rw [mul_one] at h1
    have h2 := (hasSum_sum fun j (_ : j ∈ univ) => prodPMF_coord_hasSum2 hμ₂ j).mul_left (2 * (n : ℝ))
    refine (h1.add h2).congr_fun fun k₂ => ?_
    rw [mul_add]
    congr 1
    · ring
    · rw [mul_sum, mul_sum, mul_sum]
      exact sum_congr rfl fun j _ => by ring
  have hbad_hs : ∀ j ∈ (univ : Finset (Fin n)),
      HasSum (fun k₂ : Fin n → ℕ => prodPMF (fun j' => lam j' * τ₁) k₂ *
        (badInd1 lam T hB j N cls k₂ + badInd2 lam τ₁ h j k₂ + badInd3 lam p ℓ h j N cls coin))
        ((∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂) +
         (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
         badInd3 lam p ℓ h j N cls coin) := by
    intro j _
    have hb1_s : Summable (fun k₂ => prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂) := by
      refine Summable.of_nonneg_of_le
        (fun k₂ => mul_nonneg (prodPMF_nonneg _ _) (by dsimp [badInd1]; split_ifs <;> norm_num))
        (fun k₂ => ?_) (prodPMF_summable (fun j' => lam j' * τ₁))
      dsimp [badInd1]; split_ifs
      · rw [mul_one]
      · rw [mul_zero]; exact prodPMF_nonneg _ _
    have hb2_m_s : Summable (fun m : ℕ => poissonPMF (lam j * τ₁) m *
        (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) := by
      refine Summable.of_nonneg_of_le
        (fun m => mul_nonneg (pmf_nonneg _ _) (by split_ifs <;> norm_num))
        (fun m => ?_) (pmf_summable (lam j * τ₁))
      split_ifs
      · rw [mul_one]
      · rw [mul_zero]; exact pmf_nonneg _ _
    have hb2_hs := prodPMF_marginal_one (fun j' => lam j' * τ₁) j
      (fun m => if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)
      (fun m => by split_ifs <;> norm_num) hb2_m_s
    have hb3_hs := (prodPMF_hasSum0 (fun j' => lam j' * τ₁)).mul_right (badInd3 lam p ℓ h j N cls coin)
    rw [one_mul] at hb3_hs
    refine ((hb1_s.hasSum.add hb2_hs).add hb3_hs).congr_fun fun k₂ => ?_
    dsimp only [badInd2]
    ring
  unfold rhsK2
  refine ((hsq_hs.mul_left ((∑ j, r j) / (2 * a_par))).add
    ((hasSum_sum hbad_hs).mul_left ((∑ j, r j) * a_par / 2))).congr_fun fun k₂ => ?_
  rw [mul_add]
  congr 1
  · ring
  · rw [mul_sum, mul_sum, mul_sum]
    exact sum_congr rfl fun j _ => by ring

lemma rhs_N_hasSum {n : ℕ} (r lam p : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hn : 0 < n) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    {T ℓ τ₁ a_par h hB : ℝ} (hℓ : 0 ≤ ℓ) (hτ₁ : 0 < τ₁) (hsum_T : ℓ + τ₁ = T) :
    HasSum (fun N : ℕ => poissonPMF ((∑ j, lam j) * ℓ) N *
      ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
        wt1 lam p N cls coin * rhsK2 r lam p T ℓ τ₁ a_par h hB N cls coin)
      (((∑ j, r j) / (2 * a_par)) *
          (2 * (((∑ j, lam j) * ℓ) ^ 2 + (∑ j, lam j) * ℓ) +
            2 * (n : ℝ) * ∑ j, ((lam j * τ₁) ^ 2 + lam j * τ₁)) +
        ((∑ j, r j) * a_par / 2) * ∑ j : Fin n, (
          (∑' m : ℕ, poissonPMF (lam j * T) m * (if hB < |(m : ℝ) - lam j * T| then (1 : ℝ) else 0)) +
          (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
          (∑' m : ℕ, poissonPMF (lam j * p j * ℓ) m * (if h < |(m : ℝ) - ℓ * lam j * p j| then (1 : ℝ) else 0)))) := by
  let R : ℝ := ∑ j, r j
  let Λ : ℝ := ∑ j, lam j
  have hΛ_pos : 0 < Λ := by
    have : lam ⟨0, hn⟩ ≤ Λ := single_le_sum (f := lam) (fun j _ => (hlam j).le) (mem_univ _)
    linarith [hlam ⟨0, hn⟩]
  have hθ : 0 ≤ Λ * ℓ := mul_nonneg hΛ_pos.le hℓ
  have hbad1_tsum : ∀ j : Fin n,
      HasSum (fun N : ℕ => poissonPMF (Λ * ℓ) N *
        ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
          wt1 lam p N cls coin * ∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂)
        (∑' m : ℕ, poissonPMF (lam j * T) m * (if hB < |(m : ℝ) - lam j * T| then (1 : ℝ) else 0)) := by
    intro j
    let g1 : ℕ → ℝ := fun m => if hB < |(m : ℝ) - lam j * T| then 1 else 0
    have hg1_s : Summable (fun m => poissonPMF (lam j * T) m * g1 m) := by
      refine Summable.of_nonneg_of_le (fun m => mul_nonneg (pmf_nonneg _ _) (by dsimp [g1]; split_ifs <;> norm_num))
        (fun m => ?_) (pmf_summable (lam j * T))
      dsimp [g1]; split_ifs
      · rw [mul_one]
      · rw [mul_zero]; exact pmf_nonneg _ _
    have hsup := wt1_superpos_conv_tsum lam p hlam hn hℓ hτ₁.le
      (fun k => g1 (k j)) (fun k => by dsimp [g1]; split_ifs <;> norm_num)
      zero_le_one le_rfl (fun k => by dsimp [g1]; split_ifs <;> norm_num)
    rw [hsum_T] at hsup
    have hmarg := prodPMF_marginal_one (fun j' => lam j' * T) j g1
      (fun m => by dsimp [g1]; split_ifs <;> norm_num) hg1_s
    rw [hmarg.tsum_eq] at hsup
    have hsumm_N : Summable (fun N : ℕ => poissonPMF (Λ * ℓ) N *
        ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
          wt1 lam p N cls coin * ∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂) := by
      refine Summable.of_nonneg_of_le (fun N => mul_nonneg (pmf_nonneg _ _)
        (sum_nonneg fun cls _ => sum_nonneg fun coin _ => mul_nonneg (wt1_nonneg lam p hlam hp0 hp1 N cls coin)
          (tsum_nonneg fun k₂ => mul_nonneg (prodPMF_nonneg _ _) (by dsimp [badInd1]; split_ifs <;> norm_num))))
        (fun N => ?_) (pmf_summable (Λ * ℓ))
      have hk2_le1 : ∀ cls : Fin N → Fin n,
          (∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂) ≤ 1 := by
        intro cls
        have hbs : Summable (fun k₂ => prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂) := by
          refine Summable.of_nonneg_of_le
            (fun k₂ => mul_nonneg (prodPMF_nonneg _ _) (by dsimp [badInd1]; split_ifs <;> norm_num))
            (fun k₂ => ?_) (prodPMF_summable (fun j' => lam j' * τ₁))
          dsimp [badInd1]; split_ifs
          · rw [mul_one]
          · rw [mul_zero]; exact prodPMF_nonneg _ _
        calc (∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂)
            ≤ ∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ :=
              Summable.tsum_le_tsum (fun k₂ => by
                dsimp [badInd1]; split_ifs
                · rw [mul_one]
                · rw [mul_zero]; exact prodPMF_nonneg _ _) hbs (prodPMF_summable _)
          _ = 1 := prodPMF_tsum_eq_one _
      calc poissonPMF (Λ * ℓ) N * ∑ cls, ∑ coin, wt1 lam p N cls coin * _
          ≤ poissonPMF (Λ * ℓ) N * ∑ cls, ∑ coin, wt1 lam p N cls coin * 1 :=
            mul_le_mul_of_nonneg_left (sum_le_sum fun cls _ => sum_le_sum fun coin _ =>
              mul_le_mul_of_nonneg_left (hk2_le1 cls) (wt1_nonneg lam p hlam hp0 hp1 N cls coin)) (pmf_nonneg _ _)
        _ = poissonPMF (Λ * ℓ) N := by simp_rw [mul_one, wt1_sum_eq_one lam p hlam hn N, mul_one]
    rw [← hsup]
    exact hsumm_N.hasSum
  have hbad3_tsum : ∀ j : Fin n,
      HasSum (fun N : ℕ => poissonPMF (Λ * ℓ) N *
        ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
          wt1 lam p N cls coin * badInd3 lam p ℓ h j N cls coin)
        (∑' m : ℕ, poissonPMF (lam j * p j * ℓ) m * (if h < |(m : ℝ) - ℓ * lam j * p j| then (1 : ℝ) else 0)) := by
    intro j
    let g3 : ℕ → ℝ := fun m => if h < |(m : ℝ) - ℓ * lam j * p j| then 1 else 0
    have hg3_s : Summable (fun m => poissonPMF (lam j * p j * ℓ) m * g3 m) := by
      refine Summable.of_nonneg_of_le (fun m => mul_nonneg (pmf_nonneg _ _) (by dsimp [g3]; split_ifs <;> norm_num))
        (fun m => ?_) (pmf_summable (lam j * p j * ℓ))
      dsimp [g3]; split_ifs
      · rw [mul_one]
      · rw [mul_zero]; exact pmf_nonneg _ _
    have hthin := wt1_thin_tsum lam p hlam hn hp0 hp1 hℓ j g3
      (fun m => by dsimp [g3]; split_ifs <;> norm_num) hg3_s
    have hsumm_N : Summable (fun N : ℕ => poissonPMF (Λ * ℓ) N *
        ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
          wt1 lam p N cls coin * badInd3 lam p ℓ h j N cls coin) := by
      refine Summable.of_nonneg_of_le (fun N => mul_nonneg (pmf_nonneg _ _)
        (sum_nonneg fun cls _ => sum_nonneg fun coin _ =>
          mul_nonneg (wt1_nonneg lam p hlam hp0 hp1 N cls coin) (by dsimp [badInd3]; split_ifs <;> norm_num)))
        (fun N => ?_) (pmf_summable (Λ * ℓ))
      calc poissonPMF (Λ * ℓ) N * ∑ cls, ∑ coin, wt1 lam p N cls coin * badInd3 lam p ℓ h j N cls coin
          ≤ poissonPMF (Λ * ℓ) N * ∑ cls, ∑ coin, wt1 lam p N cls coin * 1 :=
            mul_le_mul_of_nonneg_left (sum_le_sum fun cls _ => sum_le_sum fun coin _ =>
              mul_le_mul_of_nonneg_left (by dsimp [badInd3]; split_ifs <;> norm_num)
                (wt1_nonneg lam p hlam hp0 hp1 N cls coin)) (pmf_nonneg _ _)
        _ = poissonPMF (Λ * ℓ) N := by simp_rw [mul_one, wt1_sum_eq_one lam p hlam hn N, mul_one]
    rw [← hthin]
    exact hsumm_N.hasSum
  have hsq_N_wt_hs : HasSum (fun N : ℕ => poissonPMF (Λ * ℓ) N *
      ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
        wt1 lam p N cls coin * (2 * (N : ℝ) ^ 2 + 2 * (n : ℝ) * ∑ j, ((lam j * τ₁) ^ 2 + lam j * τ₁)))
      (2 * ((Λ * ℓ) ^ 2 + Λ * ℓ) + 2 * (n : ℝ) * ∑ j, ((lam j * τ₁) ^ 2 + lam j * τ₁)) := by
    have h1 := (pmf_hasSum2 hθ).mul_left 2
    have h2 := (pmf_hasSum0 hθ).mul_left (2 * (n : ℝ) * ∑ j, ((lam j * τ₁) ^ 2 + lam j * τ₁))
    rw [mul_one] at h2
    refine (h1.add h2).congr_fun fun N => ?_
    simp_rw [← sum_mul, wt1_sum_eq_one lam p hlam hn N, one_mul]
    ring
  have htail_j_hs : ∀ j ∈ (univ : Finset (Fin n)),
      HasSum (fun N : ℕ => poissonPMF (Λ * ℓ) N *
        ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool, wt1 lam p N cls coin * (
          (∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂) +
          (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
          badInd3 lam p ℓ h j N cls coin))
        ((∑' m : ℕ, poissonPMF (lam j * T) m * (if hB < |(m : ℝ) - lam j * T| then (1 : ℝ) else 0)) +
         (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
         (∑' m : ℕ, poissonPMF (lam j * p j * ℓ) m * (if h < |(m : ℝ) - ℓ * lam j * p j| then (1 : ℝ) else 0))) := by
    intro j _
    let c2 := ∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)
    have hc2_hs : HasSum (fun N : ℕ => poissonPMF (Λ * ℓ) N *
        ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool, wt1 lam p N cls coin * c2) c2 := by
      have h0 := (pmf_hasSum0 hθ).mul_right c2
      rw [one_mul] at h0
      refine h0.congr_fun fun N => ?_
      simp_rw [← sum_mul, wt1_sum_eq_one lam p hlam hn N, one_mul]
    refine (((hbad1_tsum j).add hc2_hs).add (hbad3_tsum j)).congr_fun fun N => ?_
    dsimp only [c2]
    simp_rw [mul_add, sum_add_distrib, mul_add]
  refine ((hsq_N_wt_hs.mul_left (R / (2 * a_par))).add
    ((hasSum_sum htail_j_hs).mul_left (R * a_par / 2))).congr_fun fun N => ?_
  unfold rhsK2
  dsimp only [R, Λ]
  have hlhs : ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
      wt1 lam p N cls coin * (
        ((∑ j, r j) / (2 * a_par)) *
          (2 * (N : ℝ) ^ 2 + 2 * (n : ℝ) * ∑ j, ((lam j * τ₁) ^ 2 + lam j * τ₁)) +
        ((∑ j, r j) * a_par / 2) * ∑ j, (
          (∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂) +
          (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
          badInd3 lam p ℓ h j N cls coin)) =
      (∑ cls, ∑ coin, wt1 lam p N cls coin *
        (((∑ j, r j) / (2 * a_par)) *
          (2 * (N : ℝ) ^ 2 + 2 * (n : ℝ) * ∑ j, ((lam j * τ₁) ^ 2 + lam j * τ₁)))) +
      (∑ cls, ∑ coin, wt1 lam p N cls coin *
        (((∑ j, r j) * a_par / 2) * ∑ j, (
          (∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂) +
          (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
          badInd3 lam p ℓ h j N cls coin))) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun cls _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun coin _ => mul_add _ _ _
  rw [hlhs, mul_add]
  congr 1
  · simp_rw [mul_left_comm (wt1 lam p N _ _) ((∑ j, r j) / (2 * a_par)), ← mul_sum]
    ring
  · simp_rw [mul_left_comm (wt1 lam p N _ _) ((∑ j, r j) * a_par / 2), ← mul_sum]
    rw [mul_left_comm (poissonPMF _ N) ((∑ j, r j) * a_par / 2)]
    congr 1
    congr 1
    calc ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool, wt1 lam p N cls coin * ∑ j,
            ((∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂) +
             (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
             badInd3 lam p ℓ h j N cls coin)
        = ∑ cls, ∑ coin, ∑ j, wt1 lam p N cls coin *
            ((∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂) +
             (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
             badInd3 lam p ℓ h j N cls coin) := by simp_rw [mul_sum]
      _ = ∑ cls, ∑ j, ∑ coin, wt1 lam p N cls coin *
            ((∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂) +
             (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
             badInd3 lam p ℓ h j N cls coin) := sum_congr rfl fun cls _ => sum_comm
      _ = ∑ j, ∑ cls, ∑ coin, wt1 lam p N cls coin *
            ((∑' k₂, prodPMF (fun j' => lam j' * τ₁) k₂ * badInd1 lam T hB j N cls k₂) +
             (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
             badInd3 lam p ℓ h j N cls coin) := sum_comm

lemma joint_expectation_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam p : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hn : 0 < n) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    {T ℓ τ₁ : ℝ} (hℓ : 0 ≤ ℓ) (hτ₁ : 0 < τ₁) (hsum_T : ℓ + τ₁ = T)
    {C : Fin m → ℝ} (hC : 0 ≤ C) {a_par h hB : ℝ} (ha_pos : 0 < a_par)
    (hgood : ∀ (N : ℕ) (cls : Fin N → Fin n) (coin : Fin N → Bool) (k₂ : Fin n → ℕ),
      0 < wt1 lam p N cls coin →
      (∀ j, |(((hist cls j + k₂ j : ℕ) : ℝ)) - lam j * T| ≤ hB) →
      (∀ j, |(k₂ j : ℝ) - lam j * τ₁| ≤ h) →
      (∀ j, |(markedCount cls coin j : ℝ) - ℓ * lam j * p j| ≤ h) →
      piValue A r C (fun j => ((hist cls j + k₂ j : ℕ) : ℝ)) ≤
        (runWindow A r (List.ofFn fun i => (cls i, coin i)) C).1 +
          piValue A r (runWindow A r (List.ofFn fun i => (cls i, coin i)) C).2 (fun j => (k₂ j : ℝ))) :
    hindsightValue A r lam T C - windowValue A r lam ℓ p C (hindsightValue A r lam τ₁) ≤
      ((∑ j, r j) / (2 * a_par)) *
          (2 * (((∑ j, lam j) * ℓ) ^ 2 + (∑ j, lam j) * ℓ) +
            2 * (n : ℝ) * ∑ j, ((lam j * τ₁) ^ 2 + lam j * τ₁)) +
        ((∑ j, r j) * a_par / 2) * ∑ j : Fin n, (
          (∑' m : ℕ, poissonPMF (lam j * T) m * (if hB < |(m : ℝ) - lam j * T| then (1 : ℝ) else 0)) +
          (∑' m : ℕ, poissonPMF (lam j * τ₁) m * (if h < |(m : ℝ) - lam j * τ₁| then (1 : ℝ) else 0)) +
          (∑' m : ℕ, poissonPMF (lam j * p j * ℓ) m * (if h < |(m : ℝ) - ℓ * lam j * p j| then (1 : ℝ) else 0))) := by
  obtain ⟨hhi_eq, hhi_N_summ⟩ := hindsight_joint_eq_and_summable A r lam p hlam hn hr hp0 hp1 hℓ hτ₁ hsum_T hC
  obtain ⟨hk2_V_hasSum, hho_eq, hho_N_summ⟩ := window_ho_eq_and_summable A r lam p hlam hn hr hA hp0 hp1 hℓ hτ₁ hC
  have hrhs_N := rhs_N_hasSum r lam p hlam hn hp0 hp1 (a_par := a_par) (h := h) (hB := hB) hℓ hτ₁ hsum_T
  rw [hhi_eq, hho_eq, ← Summable.tsum_sub hhi_N_summ hho_N_summ, ← hrhs_N.tsum_eq]
  refine Summable.tsum_le_tsum (fun N => ?_) (hhi_N_summ.sub hho_N_summ) hrhs_N.summable
  rw [← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ (pmf_nonneg _ _)
  rw [← sum_sub_distrib]
  refine sum_le_sum fun cls _ => ?_
  rw [← sum_sub_distrib]
  refine sum_le_sum fun coin _ => ?_
  rcases eq_or_lt_of_le (wt1_nonneg lam p hlam hp0 hp1 N cls coin) with hw_zero | hw_pos
  · rw [← hw_zero, zero_mul, zero_mul, sub_self, zero_mul]
  · rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ hw_pos.le
    have hμ₂ : ∀ j, 0 ≤ lam j * τ₁ := fun j => (mul_pos (hlam j) hτ₁).le
    have hR0 : 0 ≤ ∑ j, r j := sum_nonneg fun j _ => hr j
    have hs_F : Summable (fun k₂ => prodPMF (fun j => lam j * τ₁) k₂ * Fhi A r C (hist cls + k₂)) := by
      have hsh : ∑ j, (hist cls j : ℝ) = (N : ℝ) := by exact_mod_cast sum_hist cls
      exact prodPMF_linear_summable hμ₂
        (fun k₂ => piValue_nonneg A r hr C hC _ fun j => Nat.cast_nonneg _)
        (A₀ := (∑ j, r j) * (N : ℝ)) (B₀ := ∑ j, r j)
        (mul_nonneg hR0 (Nat.cast_nonneg N)) hR0 (fun k₂ => by
          calc Fhi A r C (hist cls + k₂)
              ≤ (∑ j, r j) * ∑ j, (((hist cls + k₂) j : ℕ) : ℝ) :=
                piValue_le_R_sum A r hr C hC _ fun j => Nat.cast_nonneg _
            _ = (∑ j, r j) * (N : ℝ) + (∑ j, r j) * ∑ j, (k₂ j : ℝ) := by
                simp only [Pi.add_apply, Nat.cast_add, sum_add_distrib, hsh, mul_add])
    have hs_V := (hk2_V_hasSum N cls coin).summable
    have hrhs_k2 := rhs_k2_hasSum r lam p hlam (T := T) (ℓ := ℓ) (a_par := a_par) (h := h) (hB := hB) hτ₁ N cls coin
    rw [← Summable.tsum_sub hs_F hs_V, ← hrhs_k2.tsum_eq]
    refine Summable.tsum_le_tsum (fun k₂ => ?_) (hs_F.sub hs_V) hrhs_k2.summable
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ (prodPMF_nonneg (fun j => lam j * τ₁) k₂)
    have hpt := pointwise_amgm_dom A r lam p hlam hr hp0 hp1 (T := T) (ℓ := ℓ) (τ₁ := τ₁)
      (h := h) (hB := hB) ha_pos hC hgood N cls coin k₂
    exact (mul_le_mul_iff_of_pos_left hw_pos).mp hpt

/-! ### 8. Main Assembly of `prop1_part1_ho_one_resolve` -/

theorem main_proof {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ M : ℝ, ∀ sel : (Fin m → ℝ) → (Fin n → ℝ), IsDLPSelector A r lam sel →
      ∀ T : ℝ, 1 ≤ T → ∀ C : Fin m → ℝ, 0 ≤ C →
        hindsightValue A r lam T C - hoValue A r lam sel 1 T C ≤
          M * T * Real.exp (-κ * T ^ (1 / 6 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, zero_lt_one, 0, fun sel hsel T hT C hC => ?_⟩
    have hT0 : 0 < T := by linarith
    have hho0 := hoValue_one_nonneg A r lam hlam hr hsel hT hC
    have hhi0 := hindsight_le_T_rho A r lam hlam hr hA hT0 hC
    have hrl0 : r ⬝ᵥ lam = 0 := by simp [dotProduct]
    rw [hrl0, mul_zero] at hhi0
    simp only [zero_mul]
    linarith
  have huniv_ne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  let lam_min : ℝ := univ.inf' huniv_ne lam
  let lam_max : ℝ := univ.sup' huniv_ne lam
  have hlam_min_pos : 0 < lam_min := (lt_inf'_iff huniv_ne).mpr fun j _ => hlam j
  have hlam_min_le : ∀ j, lam_min ≤ lam j := fun j => inf'_le lam (mem_univ j)
  have hlam_max_ge : ∀ j, lam j ≤ lam_max := fun j => le_sup' lam (mem_univ j)
  have hlam_max_pos : 0 < lam_max := lt_of_lt_of_le (hlam ⟨0, hn⟩) (hlam_max_ge ⟨0, hn⟩)
  obtain ⟨α, hα0, hstab⟩ := optimal_face_stability A r hr hA
  let B : ℝ := 1 + α * (n : ℝ)
  have hB_ge1 : 1 ≤ B := by
    have : 0 ≤ α * (n : ℝ) := mul_nonneg hα0 (Nat.cast_nonneg n)
    dsimp [B]; linarith
  have hB_pos : 0 < B := by linarith
  let β : ℝ := lam_min ^ 2 / (48 * lam_max * B ^ 2)
  have hβ_pos : 0 < β := by positivity
  let κ : ℝ := β / 2
  have hκ_pos : 0 < κ := by positivity
  let Λ : ℝ := ∑ j, lam j
  have hΛ_pos : 0 < Λ := by
    have : lam ⟨0, hn⟩ ≤ Λ := single_le_sum (f := lam) (fun j _ => (hlam j).le) (mem_univ _)
    linarith [hlam ⟨0, hn⟩]
  let R : ℝ := ∑ j, r j
  have hR0 : 0 ≤ R := sum_nonneg fun j _ => hr j
  let ρ : ℝ := r ⬝ᵥ lam
  have hρ0 : 0 ≤ ρ := sum_nonneg fun j _ => mul_nonneg (hr j) (hlam j).le
  let M_sq : ℝ := 2 * (Λ ^ 2 + Λ) + 2 * (n : ℝ) * ∑ j, (lam j ^ 2 + lam j)
  have hM_sq0 : 0 ≤ M_sq := by
    dsimp [M_sq]
    have : 0 ≤ ∑ j, (lam j ^ 2 + lam j) := sum_nonneg fun j _ => by linarith [sq_nonneg (lam j), hlam j]
    positivity
  let M_large : ℝ := R * M_sq / 2 + 3 * R * (n : ℝ)
  let M : ℝ := M_large + ρ * Real.exp (64 * κ)
  refine ⟨κ, hκ_pos, M, fun sel hsel T hT C hC => ?_⟩
  by_cases hT8 : (8 : ℝ) ^ (12 : ℕ) ≤ T
  · let q : ℝ := T ^ (1 / 12 : ℝ)
    let h : ℝ := lam_min / 4 * q ^ (7 : ℕ)
    let τ₁ : ℝ := tau T 1
    let ℓ : ℝ := tau T 0 - tau T 1
    obtain ⟨hq8, hq12, htau0, htau1, _, _⟩ := rpow_identities hT8
    change 8 ≤ q at hq8
    change q ^ (12 : ℕ) = T at hq12
    change tau T 1 = q ^ (10 : ℕ) at htau1
    have hT_pos : 0 < T := by linarith
    have hq1 : 1 ≤ q := by linarith
    have hq_pos : 0 < q := by linarith
    have hτ₁_pos : 0 < τ₁ := by change 0 < tau T 1; rw [htau1]; exact pow_pos hq_pos 10
    have hτ₁_le_T : τ₁ ≤ T := by change tau T 1 ≤ T; rw [htau1, ← hq12]; exact q_pow_le hq1 (by norm_num)
    have hℓ_nonneg : 0 ≤ ℓ := by change 0 ≤ tau T 0 - τ₁; rw [htau0]; linarith
    have hℓ_le_T : ℓ ≤ T := by change tau T 0 - τ₁ ≤ T; rw [htau0]; linarith
    have hℓ_add_τ₁ : ℓ + τ₁ = T := by change tau T 0 - tau T 1 + tau T 1 = T; rw [htau0]; ring
    have hb_dlp : 0 ≤ (fun l => C l / tau T 0) := fun l => div_nonneg (hC l) (by rw [htau0]; linarith)
    obtain ⟨⟨_, hx0, hx1⟩, _⟩ := hsel _ hb_dlp
    let p : Fin n → ℝ := thresholdProbs lam (tau T 0) (sel fun l => C l / tau T 0)
    have hp0 : ∀ j, 0 ≤ p j := fun j => (thresholdProbs_mem lam _ _ hlam hx0 hx1 j).1
    have hp1 : ∀ j, p j ≤ 1 := fun j => (thresholdProbs_mem lam _ _ hlam hx0 hx1 j).2
    let a_par : ℝ := T * Real.exp (κ * T ^ (1 / 6 : ℝ))
    have ha_pos : 0 < a_par := by positivity
    have hho_def : hoValue A r lam sel 1 T C = windowValue A r lam ℓ p C (hindsightValue A r lam τ₁) := by
      simp [hoValue, hoAux, ℓ, p, τ₁]
    rw [hho_def]
    have hdiff := joint_expectation_bound A r lam p hlam hn hr hA hp0 hp1 hℓ_nonneg hτ₁_pos hℓ_add_τ₁ hC
      (h := h) (hB := h / B) ha_pos
      (fun N cls coin k₂ hwt h1 h2 h3 =>
        good_event_le A r lam hlam hr hA hα0 hstab hlam_min_le hlam_min_pos hsel hT8 hC N cls coin k₂ hwt h1 h2 h3)
    have htail := tail_sum_bound lam (sel fun l => C l / tau T 0) hlam hx0 hx1
      hlam_min_pos hlam_max_pos hlam_min_le hlam_max_ge hB_ge1 hT8
    have hT_le_T2 : T ≤ T ^ 2 := by
      calc T = T * 1 := (mul_one T).symm
        _ ≤ T * T := mul_le_mul_of_nonneg_left hT hT_pos.le
        _ = T ^ 2 := (sq T).symm
    have hsq_tot_le : 2 * ((Λ * ℓ) ^ 2 + Λ * ℓ) + 2 * (n : ℝ) * ∑ j, ((lam j * τ₁) ^ 2 + lam j * τ₁) ≤
        M_sq * T ^ 2 := by
      have hℓ2 : ℓ ^ 2 ≤ T ^ 2 := sq_le_sq' (by linarith) hℓ_le_T
      have hℓ_T2 : ℓ ≤ T ^ 2 := le_trans hℓ_le_T hT_le_T2
      have h1 : (Λ * ℓ) ^ 2 + Λ * ℓ ≤ (Λ ^ 2 + Λ) * T ^ 2 := by
        have ha : (Λ * ℓ) ^ 2 ≤ Λ ^ 2 * T ^ 2 := by
          rw [mul_pow]; exact mul_le_mul_of_nonneg_left hℓ2 (sq_nonneg Λ)
        have hb : Λ * ℓ ≤ Λ * T ^ 2 := mul_le_mul_of_nonneg_left hℓ_T2 hΛ_pos.le
        linarith [show (Λ ^ 2 + Λ) * T ^ 2 = Λ ^ 2 * T ^ 2 + Λ * T ^ 2 by ring]
      have hτ2 : τ₁ ^ 2 ≤ T ^ 2 := sq_le_sq' (by linarith) hτ₁_le_T
      have hτ_T2 : τ₁ ≤ T ^ 2 := le_trans hτ₁_le_T hT_le_T2
      have h2 : ∑ j, ((lam j * τ₁) ^ 2 + lam j * τ₁) ≤ (∑ j, (lam j ^ 2 + lam j)) * T ^ 2 := by
        rw [sum_mul]
        refine sum_le_sum fun j _ => ?_
        have ha : (lam j * τ₁) ^ 2 ≤ lam j ^ 2 * T ^ 2 := by
          rw [mul_pow]; exact mul_le_mul_of_nonneg_left hτ2 (sq_nonneg (lam j))
        have hb : lam j * τ₁ ≤ lam j * T ^ 2 := mul_le_mul_of_nonneg_left hτ_T2 (hlam j).le
        linarith [show (lam j ^ 2 + lam j) * T ^ 2 = lam j ^ 2 * T ^ 2 + lam j * T ^ 2 by ring]
      have h2m : 2 * (n : ℝ) * ∑ j, ((lam j * τ₁) ^ 2 + lam j * τ₁) ≤
          2 * (n : ℝ) * ((∑ j, (lam j ^ 2 + lam j)) * T ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      dsimp [M_sq]
      linarith [show (2 * (Λ ^ 2 + Λ) + 2 * (n : ℝ) * ∑ j, (lam j ^ 2 + lam j)) * T ^ 2 =
        2 * ((Λ ^ 2 + Λ) * T ^ 2) + 2 * (n : ℝ) * ((∑ j, (lam j ^ 2 + lam j)) * T ^ 2) by ring]
    have halg1 : (R / (2 * a_par)) * (M_sq * T ^ 2) =
        (R * M_sq / 2) * T * Real.exp (-κ * T ^ (1 / 6 : ℝ)) := by
      dsimp [a_par]
      rw [neg_mul, Real.exp_neg]
      have hT_ne : T ≠ 0 := hT_pos.ne'
      have hexp_ne : Real.exp (κ * T ^ (1 / 6 : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
      field_simp
    have halg2 : (R * a_par / 2) * (6 * (n : ℝ) * Real.exp (-β * T ^ (1 / 6 : ℝ))) =
        (3 * R * (n : ℝ)) * T * Real.exp (-κ * T ^ (1 / 6 : ℝ)) := by
      dsimp [a_par, κ]
      have hexp_prod : Real.exp (β / 2 * T ^ (1 / 6 : ℝ)) * Real.exp (-β * T ^ (1 / 6 : ℝ)) =
          Real.exp (-(β / 2) * T ^ (1 / 6 : ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc (R * (T * Real.exp (β / 2 * T ^ (1 / 6 : ℝ))) / 2) *
              (6 * (n : ℝ) * Real.exp (-β * T ^ (1 / 6 : ℝ)))
          = (3 * R * (n : ℝ)) * T *
              (Real.exp (β / 2 * T ^ (1 / 6 : ℝ)) * Real.exp (-β * T ^ (1 / 6 : ℝ))) := by ring
        _ = (3 * R * (n : ℝ)) * T * Real.exp (-(β / 2) * T ^ (1 / 6 : ℝ)) := by rw [hexp_prod]
    have hM_ge : M_large ≤ M := by
      dsimp [M]
      have : 0 ≤ ρ * Real.exp (64 * κ) := mul_nonneg hρ0 (Real.exp_pos _).le
      linarith
    calc hindsightValue A r lam T C - windowValue A r lam ℓ p C (hindsightValue A r lam τ₁)
        ≤ _ := hdiff
      _ ≤ (R / (2 * a_par)) * (M_sq * T ^ 2) +
            (R * a_par / 2) * (6 * (n : ℝ) * Real.exp (-β * T ^ (1 / 6 : ℝ))) :=
          add_le_add (mul_le_mul_of_nonneg_left hsq_tot_le (by positivity))
            (mul_le_mul_of_nonneg_left htail (by positivity))
      _ = M_large * (T * Real.exp (-κ * T ^ (1 / 6 : ℝ))) := by
          rw [halg1, halg2]; dsimp [M_large]; ring
      _ ≤ M * (T * Real.exp (-κ * T ^ (1 / 6 : ℝ))) :=
          mul_le_mul_of_nonneg_right hM_ge (by positivity)
      _ = M * T * Real.exp (-κ * T ^ (1 / 6 : ℝ)) := (mul_assoc _ _ _).symm
  · have hT8' : T < (8 : ℝ) ^ (12 : ℕ) := lt_of_not_ge hT8
    have hT0 : 0 < T := by linarith
    have hho0 := hoValue_one_nonneg A r lam hlam hr hsel hT hC
    have hhi_le := hindsight_le_T_rho A r lam hlam hr hA hT0 hC
    have hT16_le_64 : T ^ (1 / 6 : ℝ) ≤ 64 := by
      have hle : T ^ (1 / 6 : ℝ) ≤ ((8 : ℝ) ^ (12 : ℕ)) ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow hT0.le hT8'.le (by norm_num)
      have h64 : ((8 : ℝ) ^ (12 : ℕ)) ^ (1 / 6 : ℝ) = 64 := by
        rw [← Real.rpow_natCast 8 12, ← Real.rpow_mul (by norm_num)]
        norm_num
      rwa [h64] at hle
    have hexp_ge1 : 1 ≤ Real.exp (64 * κ) * Real.exp (-κ * T ^ (1 / 6 : ℝ)) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      have : κ * T ^ (1 / 6 : ℝ) ≤ κ * 64 := mul_le_mul_of_nonneg_left hT16_le_64 hκ_pos.le
      linarith
    have hM_large0 : 0 ≤ M_large := by dsimp [M_large]; positivity
    calc hindsightValue A r lam T C - hoValue A r lam sel 1 T C
        ≤ T * ρ := by dsimp [ρ]; linarith
      _ ≤ T * ρ * (Real.exp (64 * κ) * Real.exp (-κ * T ^ (1 / 6 : ℝ))) :=
          le_mul_of_one_le_right (mul_nonneg hT0.le hρ0) hexp_ge1
      _ = (ρ * Real.exp (64 * κ)) * (T * Real.exp (-κ * T ^ (1 / 6 : ℝ))) := by ring
      _ ≤ M * (T * Real.exp (-κ * T ^ (1 / 6 : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          dsimp [M]; linarith
      _ = M * T * Real.exp (-κ * T ^ (1 / 6 : ℝ)) := (mul_assoc _ _ _).symm

end ResolvingNRM.IRT.Part3

open ResolvingNRM.IRT.Part1 ResolvingNRM.IRT.Part2 ResolvingNRM.IRT.Part3

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ M : ℝ, ∀ sel : (Fin m → ℝ) → (Fin n → ℝ), IsDLPSelector A r lam sel →
      ∀ T : ℝ, 1 ≤ T → ∀ C : Fin m → ℝ, 0 ≤ C →
        hindsightValue A r lam T C - hoValue A r lam sel 1 T C ≤
          M * T * Real.exp (-κ * T ^ (1 / 6 : ℝ)) :=
  main_proof A r lam hlam hr hA

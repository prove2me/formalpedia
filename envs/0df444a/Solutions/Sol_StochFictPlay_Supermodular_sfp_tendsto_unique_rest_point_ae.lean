-- Prove2me | solution 1 for StochFictPlay.Supermodular.sfp_tendsto_unique_rest_point_ae
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T17:14:10.260066+00:00
-- url     : https://prove2.me/submissions/ff6bda05-e165-446f-9ad2-b92b5c2c0557

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel
import Definitions.Def_StochFictPlay_Supermodular_Game
import Definitions.Def_StochFictPlay_Supermodular_Dynamics
import Definitions.Def_StochFictPlay_Supermodular_SFP
import Definitions.Def_StochFictPlay_Supermodular_StochOrder

set_option autoImplicit false

/- Complete checked body: ArgmaxBasics -/
section

open scoped BigOperators
open MeasureTheory
open StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

def IsLeastMax {k : ℕ} (v : Fin k → ℝ) (i : Fin k) : Prop :=
  (∀ j, v j ≤ v i) ∧ ∀ j, j < i → v j < v i

theorem exists_leastMax {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) : ∃ i, IsLeastMax v i := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ v ⟨⟨0,hk⟩, Finset.mem_univ _⟩
  let s := Finset.univ.filter (fun i => ∀ j, v j ≤ v i)
  have hs : s.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => hi j (Finset.mem_univ _)⟩⟩
  let a := s.min' hs
  have ha : a ∈ s := Finset.min'_mem s hs
  have hamax : ∀ j, v j ≤ v a := (Finset.mem_filter.mp ha).2
  refine ⟨a, hamax, ?_⟩
  intro j hj
  apply lt_of_le_of_ne (hamax j)
  intro he
  have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun b => by rw [he]; exact hamax b⟩
  have haj : a ≤ j := Finset.min'_le s j hjs
  exact (not_lt_of_ge haj) hj

noncomputable def argmaxIndex {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) : Fin k :=
  Classical.choose (exists_leastMax hk v)

theorem argmaxIndex_spec {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) :
    IsLeastMax v (argmaxIndex hk v) := Classical.choose_spec (exists_leastMax hk v)

theorem leastMax_unique {k : ℕ} {v : Fin k → ℝ} {i j : Fin k}
    (hi : IsLeastMax v i) (hj : IsLeastMax v j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim ((not_lt_of_ge (hi.1 j)) (hj.2 i hij))
  · exact hij
  · exact False.elim ((not_lt_of_ge (hj.1 i)) (hi.2 j hij))

theorem argmaxIndex_eq_iff {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) (i : Fin k) :
    argmaxIndex hk v = i ↔ IsLeastMax v i := by
  constructor
  · intro h
    rw [← h]
    exact argmaxIndex_spec hk v
  · intro hi
    exact leastMax_unique (argmaxIndex_spec hk v) hi

theorem argmaxVec_eq_single {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) :
    argmaxVec v = Pi.single (argmaxIndex hk v) (1:ℝ) := by
  classical
  funext i
  rw [argmaxVec]
  have he : ((∀ j, v j ≤ v i) ∧ ∀ j, j < i → v j < v i) ↔ argmaxIndex hk v = i :=
    (argmaxIndex_eq_iff hk v i).symm
  simp only [he]
  by_cases hi : argmaxIndex hk v = i
  · subst i
    simp
  · simp [hi, Ne.symm hi]

theorem argmaxVec_simplex {k : ℕ} (hk : 0 < k) (v : Fin k → ℝ) :
    argmaxVec v ∈ stdSimplex ℝ (Fin k) := by
  rw [argmaxVec_eq_single hk v]
  constructor
  · intro i
    classical
    by_cases hi : i = argmaxIndex hk v <;> simp [hi]
  · simp

theorem measurable_leastMax {k : ℕ} (i : Fin k) :
    MeasurableSet {v : Fin k → ℝ | IsLeastMax v i} := by
  have h1 : MeasurableSet {v : Fin k → ℝ | ∀ j, v j ≤ v i} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i)
  have h2 : MeasurableSet {v : Fin k → ℝ | ∀ j, j < i → v j < v i} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)
  exact h1.inter h2

theorem measurable_argmaxIndex {k : ℕ} (hk : 0 < k) : Measurable (argmaxIndex hk) := by
  apply measurable_to_countable'
  intro i
  simpa only [Set.preimage, Set.mem_singleton_iff, argmaxIndex_eq_iff] using measurable_leastMax i

theorem measurable_argmaxVec {k : ℕ} (hk : 0 < k) : Measurable (argmaxVec (k := k)) := by
  have he : argmaxVec (k := k) = (fun i => Pi.single i (1:ℝ)) ∘ argmaxIndex hk :=
    funext (argmaxVec_eq_single hk)
  rw [he]
  exact (measurable_of_countable _).comp (measurable_argmaxIndex hk)


end StochFictPlay.SupermodularProof
end

/- Complete checked body: ArgmaxOrder -/
section

open scoped BigOperators
open StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

theorem argmaxIndex_mono_differences {k : ℕ} (hk : 0 < k) (v w : Fin k → ℝ)
    (h : ∀ i j : Fin k, j < i → v i-v j ≤ w i-w j) :
    argmaxIndex hk v ≤ argmaxIndex hk w := by
  by_contra hn
  have hij : argmaxIndex hk w < argmaxIndex hk v := lt_of_not_ge hn
  have hv := (argmaxIndex_spec hk v).2 (argmaxIndex hk w) hij
  have hw := (argmaxIndex_spec hk w).1 (argmaxIndex hk v)
  have hd := h (argmaxIndex hk v) (argmaxIndex hk w) hij
  linarith

lemma Tco_single {m : ℕ} (a : Fin m) (i : Fin (m-1)) :
    Tco (Pi.single a (1 : ℝ)) i = if i.val < a.val then 1 else 0 := by
  classical
  unfold Tco
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [Pi.single_eq_of_ne hba]
  · simp

theorem argmaxVec_tail_mono {k : ℕ} (hk : 0 < k) (v w e : Fin k → ℝ)
    (h : ∀ i j : Fin k, j < i → v i-v j ≤ w i-w j) :
    Tco (argmaxVec (v+e)) ≤ Tco (argmaxVec (w+e)) := by
  have hm : argmaxIndex hk (v+e) ≤ argmaxIndex hk (w+e) := by
    apply argmaxIndex_mono_differences hk
    intro i j hij
    have hh := h i j hij
    simp only [Pi.add_apply]
    linarith
  rw [argmaxVec_eq_single hk, argmaxVec_eq_single hk]
  intro i
  rw [Tco_single, Tco_single]
  have hh : (argmaxIndex hk (v+e)).val ≤ (argmaxIndex hk (w+e)).val := hm
  by_cases hi : i.val < (argmaxIndex hk (v+e)).val
  · have hiw : i.val < (argmaxIndex hk (w+e)).val := hi.trans_le hh
    simp [hi, hiw]
  · simp only [if_neg hi]
    split_ifs <;> norm_num

end StochFictPlay.SupermodularProof

end

/- Complete checked body: AttributedOrder -/
section

namespace StochFictPlay.SupermodularProof.AttributedWeightedSum
-- Prove2me | solution 1 for StochFictPlay.Supermodular.lemmaA2_weighted_sum_pos
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:33:09.829226+00:00
-- url     : https://prove2.me/submissions/4f2298cb-79ab-48ac-b56e-6d271885f064

open scoped BigOperators

private theorem prefix_extend {n : ℕ} (c : Fin n → ℝ) (j : ℕ) (hj : j ≤ n) :
    (∑ i ∈ Finset.range j, (if h : i < n then c ⟨i,h⟩ else 0)) =
      ∑ k : Fin n, if k.val < j then c k else 0 := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  calc
    _ = ∑ i ∈ Finset.range j, if h : i < n then (if i < j then c ⟨i,h⟩ else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono hj)
      intro i hi hin
      simp only [Finset.mem_range] at hi hin
      simp [hin]

theorem checked_lemmaA2_weighted_sum_pos (n : ℕ) (b c : Fin n → ℝ) (hb : StrictMono b)
    (hc_le : ∀ j : ℕ, j ≤ n → ∑ k : Fin n, (if k.val < j then c k else 0) ≤ 0)
    (hc_lt : ∃ j : ℕ, j ≤ n ∧ ∑ k : Fin n, (if k.val < j then c k else 0) < 0)
    (hc_eq : ∑ k : Fin n, c k = 0) :
    0 < ∑ k : Fin n, b k * c k := by
  classical
  let B : ℕ → ℝ := fun i => if h : i < n then b ⟨i,h⟩ else 0
  let C : ℕ → ℝ := fun i => if h : i < n then c ⟨i,h⟩ else 0
  have hC (j : ℕ) (hj : j ≤ n) : (∑ i ∈ Finset.range j, C i) = ∑ k : Fin n, if k.val < j then c k else 0 := prefix_extend c j hj
  have hCn : ∑ i ∈ Finset.range n, C i = 0 := by simpa only [hC n le_rfl,Fin.is_lt,if_true] using hc_eq
  have hS : (∑ k : Fin n, b k*c k) = ∑ i ∈ Finset.range n, B i * C i := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [B,C,Finset.mem_range.mp hi]
  have hB (i : ℕ) (hi : i < n-1) : 0 < B (i+1)-B i := by
    have hi0 : i < n := by omega
    have hi1 : i+1 < n := by omega
    simp only [B,dif_pos hi0,dif_pos hi1]
    exact sub_pos.mpr (hb (show (⟨i,hi0⟩ : Fin n) < ⟨i+1,hi1⟩ from by simp))
  obtain ⟨j,hjn,hj⟩ := hc_lt
  have hj0 : 0 < j := by
    by_contra h
    have hz : j=0 := by omega
    simp [hz] at hj
  have hjn' : j < n := by
    by_contra h
    have : j=n := by omega
    simp only [this,Fin.is_lt,if_true,hc_eq] at hj
    linarith
  have hneg : (∑ i ∈ Finset.range (n-1), (B (i+1)-B i) * ∑ k ∈ Finset.range (i+1), C k) < 0 := by
    apply Finset.sum_neg'
    · intro i hi
      have hi' := Finset.mem_range.mp hi
      exact mul_nonpos_of_nonneg_of_nonpos (hB i hi').le (by rw [hC]; exact hc_le _ (by omega); omega)
    · refine ⟨j-1,Finset.mem_range.mpr (by omega),?_⟩
      have hj1 : j-1+1=j := by omega
      have hpre : (∑ k ∈ Finset.range (j-1+1), C k) < 0 := by rw [hj1,hC j hjn]; exact hj
      exact mul_neg_of_pos_of_neg (hB (j-1) (by omega)) hpre
  rw [hS]
  have hid := Finset.sum_range_by_parts B C n
  simp only [smul_eq_mul,hCn,mul_zero,zero_sub] at hid
  rw [hid]
  exact neg_pos.mpr hneg

end StochFictPlay.SupermodularProof.AttributedWeightedSum

namespace StochFictPlay.SupermodularProof.AttributedPartialSums
-- Prove2me | solution 1 for StochFictPlay.Supermodular.obs14_Tco_le_iff_partial_sums
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:35:37.169998+00:00
-- url     : https://prove2.me/submissions/58b3abde-6609-44b6-bd9d-fbea5b2ceeec

open scoped BigOperators
open StochFictPlay.Supermodular

private theorem prefix_tail {m : ℕ} (x y : Fin m → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin m)) (hy : y ∈ stdSimplex ℝ (Fin m))
    (i : Fin (m-1)) :
    (∑ j : Fin m, if j.val < i.val+1 then y j-x j else 0) = Tco x i-Tco y i := by
  have hid : (∑ j : Fin m, if j.val < i.val+1 then y j-x j else 0) + (Tco y i-Tco x i) =
      (∑ j : Fin m, y j) - ∑ j : Fin m, x j := by
    simp only [Tco,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i.val < j.val
    · have hji : ¬j.val < i.val+1 := by omega
      simp [hij,hji]
    · have hji : j.val < i.val+1 := by omega
      simp [hij,hji]
  rw [hx.2,hy.2] at hid
  linarith

theorem checked_obs14_Tco_le_iff_partial_sums (m : ℕ) (x y : Fin m → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin m)) (hy : y ∈ stdSimplex ℝ (Fin m)) :
    Tco x ≤ Tco y ↔
      ∀ k : ℕ, k < m → ∑ i : Fin m, (if i.val < k then y i - x i else 0) ≤ 0 := by
  constructor
  · intro h k hk
    by_cases hk0 : k=0
    · simp [hk0]
    · let i : Fin (m-1) := ⟨k-1,by omega⟩
      have hik : i.val+1=k := by dsimp [i]; omega
      have hh := prefix_tail x y hx hy i
      rw [hik] at hh
      rw [hh]
      exact sub_nonpos.mpr (h i)
  · intro h i
    have hi : i.val+1 < m := by have := i.isLt; omega
    have hh := h (i.val+1) hi
    rw [prefix_tail x y hx hy i] at hh
    exact sub_nonpos.mp hh

end StochFictPlay.SupermodularProof.AttributedPartialSums

namespace StochFictPlay.SupermodularProof.AttributedIncreasingDifferences
-- Prove2me | solution 1 for StochFictPlay.Supermodular.lemmaA3_mixed_increasing_differences
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:36:19.551973+00:00
-- url     : https://prove2.me/submissions/74ce9f77-f2cc-4585-8e57-952277713084

open scoped BigOperators

private theorem prefix_extend {n : ℕ} (c : Fin n → ℝ) (j : ℕ) (hj : j ≤ n) :
    (∑ i ∈ Finset.range j, (if h : i < n then c ⟨i,h⟩ else 0)) =
      ∑ k : Fin n, if k.val < j then c k else 0 := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  calc
    _ = ∑ i ∈ Finset.range j, if h : i < n then (if i < j then c ⟨i,h⟩ else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono hj)
      intro i hi hin
      simp only [Finset.mem_range] at hi hin
      simp [hin]

private theorem weighted_pos (n : ℕ) (b c : Fin n → ℝ) (hb : StrictMono b)
    (hc_le : ∀ j : ℕ, j ≤ n → ∑ k : Fin n, (if k.val < j then c k else 0) ≤ 0)
    (hc_lt : ∃ j : ℕ, j ≤ n ∧ ∑ k : Fin n, (if k.val < j then c k else 0) < 0)
    (hc_eq : ∑ k : Fin n, c k = 0) :
    0 < ∑ k : Fin n, b k * c k := by
  classical
  let B : ℕ → ℝ := fun i => if h : i < n then b ⟨i,h⟩ else 0
  let C : ℕ → ℝ := fun i => if h : i < n then c ⟨i,h⟩ else 0
  have hC (j : ℕ) (hj : j ≤ n) : (∑ i ∈ Finset.range j, C i) = ∑ k : Fin n, if k.val < j then c k else 0 := prefix_extend c j hj
  have hCn : ∑ i ∈ Finset.range n, C i = 0 := by simpa only [hC n le_rfl,Fin.is_lt,if_true] using hc_eq
  have hS : (∑ k : Fin n, b k*c k) = ∑ i ∈ Finset.range n, B i * C i := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [B,C,Finset.mem_range.mp hi]
  have hB (i : ℕ) (hi : i < n-1) : 0 < B (i+1)-B i := by
    have hi0 : i < n := by omega
    have hi1 : i+1 < n := by omega
    simp only [B,dif_pos hi0,dif_pos hi1]
    exact sub_pos.mpr (hb (show (⟨i,hi0⟩ : Fin n) < ⟨i+1,hi1⟩ from by simp))
  obtain ⟨j,hjn,hj⟩ := hc_lt
  have hj0 : 0 < j := by
    by_contra h
    have hz : j=0 := by omega
    simp [hz] at hj
  have hjn' : j < n := by
    by_contra h
    have : j=n := by omega
    simp only [this,Fin.is_lt,if_true,hc_eq] at hj
    linarith
  have hneg : (∑ i ∈ Finset.range (n-1), (B (i+1)-B i) * ∑ k ∈ Finset.range (i+1), C k) < 0 := by
    apply Finset.sum_neg'
    · intro i hi
      have hi' := Finset.mem_range.mp hi
      exact mul_nonpos_of_nonneg_of_nonpos (hB i hi').le (by rw [hC]; exact hc_le _ (by omega); omega)
    · refine ⟨j-1,Finset.mem_range.mpr (by omega),?_⟩
      have hj1 : j-1+1=j := by omega
      have hpre : (∑ k ∈ Finset.range (j-1+1), C k) < 0 := by rw [hj1,hC j hjn]; exact hj
      exact mul_neg_of_pos_of_neg (hB (j-1) (by omega)) hpre
  rw [hS]
  have hid := Finset.sum_range_by_parts B C n
  simp only [smul_eq_mul,hCn,mul_zero,zero_sub] at hid
  rw [hid]
  exact neg_pos.mpr hneg

open StochFictPlay.Supermodular
private theorem prefix_tail {m : ℕ} (x y : Fin m → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin m)) (hy : y ∈ stdSimplex ℝ (Fin m))
    (i : Fin (m-1)) :
    (∑ j : Fin m, if j.val < i.val+1 then y j-x j else 0) = Tco x i-Tco y i := by
  have hid : (∑ j : Fin m, if j.val < i.val+1 then y j-x j else 0) + (Tco y i-Tco x i) =
      (∑ j : Fin m, y j) - ∑ j : Fin m, x j := by
    simp only [Tco,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i.val < j.val
    · have hji : ¬j.val < i.val+1 := by omega
      simp [hij,hji]
    · have hji : j.val < i.val+1 := by omega
      simp [hij,hji]
  rw [hx.2,hy.2] at hid
  linarith

private theorem order_iff (m : ℕ) (x y : Fin m → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin m)) (hy : y ∈ stdSimplex ℝ (Fin m)) :
    Tco x ≤ Tco y ↔
      ∀ k : ℕ, k < m → ∑ i : Fin m, (if i.val < k then y i - x i else 0) ≤ 0 := by
  constructor
  · intro h k hk
    by_cases hk0 : k=0
    · simp [hk0]
    · let i : Fin (m-1) := ⟨k-1,by omega⟩
      have hik : i.val+1=k := by dsimp [i]; omega
      have hh := prefix_tail x y hx hy i
      rw [hik] at hh
      rw [hh]
      exact sub_nonpos.mpr (h i)
  · intro h i
    have hi : i.val+1 < m := by have := i.isLt; omega
    have hh := h (i.val+1) hi
    rw [prefix_tail x y hx hy i] at hh
    exact sub_nonpos.mp hh

private theorem prefix_step {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    (∑ k : Fin n, if k.val < j.val+1 then c k else 0) =
      (∑ k : Fin n, if k.val < j.val then c k else 0) + c j := by
  classical
  calc
    _ = ∑ k : Fin n, ((if k.val < j.val then c k else 0) + (if k=j then c k else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkj : k.val < j.val
      · have h1 : k.val < j.val+1 := by omega
        have hne : k ≠ j := by intro h; subst h; omega
        simp [hkj,h1,hne]
      · by_cases he : k=j
        · subst k; simp
        · have hv : k.val ≠ j.val := by intro h; exact he (Fin.ext h)
          have h1 : ¬k.val < j.val+1 := by omega
          simp [hkj,h1,he]
    _ = _ := by simp [Finset.sum_add_distrib]

theorem checked_lemmaA3_mixed_increasing_differences {n₁ n₂ : ℕ} (A : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hA : ∀ i j : Fin n₁, i < j → StrictMono (fun k : Fin n₂ => A j k - A i k))
    (x y : Fin n₂ → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n₂)) (hy : y ∈ stdSimplex ℝ (Fin n₂))
    (hT : Tco x ≤ Tco y) (hne : y ≠ x) :
    StrictMono (fun i : Fin n₁ => Matrix.mulVec A y i - Matrix.mulVec A x i) := by
  have heq : ∑ k : Fin n₂, (y k-x k) = 0 := by rw [Finset.sum_sub_distrib,hx.2,hy.2,sub_self]
  have hle (j : ℕ) (hj : j ≤ n₂) : (∑ k : Fin n₂, if k.val < j then y k-x k else 0) ≤ 0 := by
    rcases lt_or_eq_of_le hj with hj|rfl
    · exact (order_iff n₂ x y hx hy).mp hT j hj
    · simpa only [Fin.is_lt,if_true,heq] using (le_refl (0:ℝ))
  have hlt : ∃ j : ℕ, j ≤ n₂ ∧ (∑ k : Fin n₂, if k.val < j then y k-x k else 0) < 0 := by
    by_contra h
    push Not at h
    have hz (j : ℕ) (hj : j ≤ n₂) : (∑ k : Fin n₂, if k.val < j then y k-x k else 0) = 0 := le_antisymm (hle j hj) (h j hj)
    apply hne
    funext j
    have hh := prefix_step (fun k => y k-x k) j
    rw [hz _ (by omega),hz _ (by omega)] at hh
    linarith
  intro i j hij
  have hw := weighted_pos n₂ (fun k => A j k-A i k) (fun k => y k-x k) (hA i j hij) hle hlt heq
  have hid : (∑ k : Fin n₂, (A j k-A i k)*(y k-x k)) =
      (Matrix.mulVec A y j-Matrix.mulVec A x j) - (Matrix.mulVec A y i-Matrix.mulVec A x i) := by
    simp only [Matrix.mulVec,dotProduct,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hid] at hw
  exact sub_pos.mp hw

end StochFictPlay.SupermodularProof.AttributedIncreasingDifferences

end

/- Complete checked body: StochasticOrderMean -/
section

open scoped BigOperators
open StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

/- The finite summation-by-parts normalization follows the complete ryanshin
   order sources preserved in AttributedOrder; this version proves the weak inequality. -/
lemma prefix_extend_weak {m : ℕ} (c : Fin m → ℝ) (j : ℕ) (hj : j ≤ m) :
    (∑ i ∈ Finset.range j, (if h : i < m then c ⟨i,h⟩ else 0)) =
      ∑ k : Fin m, if k.val < j then c k else 0 := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  calc
    _ = ∑ i ∈ Finset.range j, if h : i < m then (if i < j then c ⟨i,h⟩ else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono hj)
      intro i _ hin
      simp only [Finset.mem_range] at hin
      simp [hin]

theorem stochastic_order_mean {m : ℕ} (x y b : Fin m → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin m)) (hy : y ∈ stdSimplex ℝ (Fin m))
    (hxy : Tco x ≤ Tco y) (hb : Monotone b) :
    ∑ k, x k * b k ≤ ∑ k, y k * b k := by
  classical
  let c : Fin m → ℝ := fun k => y k-x k
  let B : ℕ → ℝ := fun i => if h : i < m then b ⟨i,h⟩ else 0
  let C : ℕ → ℝ := fun i => if h : i < m then c ⟨i,h⟩ else 0
  have hc : ∑ k, c k = 0 := by simp [c, Finset.sum_sub_distrib, hx.2, hy.2]
  have hp : ∀ j : ℕ, j ≤ m → (∑ k : Fin m, if k.val < j then c k else 0) ≤ 0 := by
    intro j hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact (AttributedPartialSums.checked_obs14_Tco_le_iff_partial_sums m x y hx hy).mp hxy j hj
    · simpa only [Fin.is_lt, if_true, hc] using (le_rfl : (0 : ℝ) ≤ 0)
  have hC : ∀ j, j ≤ m → (∑ i ∈ Finset.range j, C i) =
      ∑ k : Fin m, if k.val < j then c k else 0 :=
    fun j hj => prefix_extend_weak c j hj
  have hCm : ∑ i ∈ Finset.range m, C i = 0 := by
    simpa only [hC m le_rfl, Fin.is_lt, if_true] using hc
  have hB : ∀ i, i < m-1 → 0 ≤ B (i+1)-B i := by
    intro i hi
    have hi0 : i < m := by omega
    have hi1 : i+1 < m := by omega
    simp only [B, dif_pos hi0, dif_pos hi1]
    exact sub_nonneg.mpr (hb (show (⟨i,hi0⟩ : Fin m) ≤ ⟨i+1,hi1⟩ from by simp))
  have hn : (∑ i ∈ Finset.range (m-1), (B (i+1)-B i) *
      ∑ k ∈ Finset.range (i+1), C k) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    apply mul_nonpos_of_nonneg_of_nonpos (hB i (Finset.mem_range.mp hi))
    rw [hC _ (by have := Finset.mem_range.mp hi; omega)]
    exact hp _ (by have := Finset.mem_range.mp hi; omega)
  have hid := Finset.sum_range_by_parts B C m
  simp only [smul_eq_mul, hCm, mul_zero, zero_sub] at hid
  have hs : 0 ≤ ∑ k : Fin m, b k*c k := by
    calc
      0 ≤ -(∑ i ∈ Finset.range (m-1), (B (i+1)-B i) * ∑ k ∈ Finset.range (i+1), C k) := by linarith
      _ = ∑ i ∈ Finset.range m, B i * C i := hid.symm
      _ = ∑ k : Fin m, b k*c k := by
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i hi
        simp [B, C, Finset.mem_range.mp hi]
  have he : (∑ k, b k*c k) = (∑ k, y k*b k) - ∑ k, x k*b k := by
    simp only [c, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  linarith

end StochFictPlay.SupermodularProof

end

/- Complete checked body: ProductExpectation -/
section

open scoped BigOperators
open StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

abbrev OtherProfile {p : ℕ} (n : Fin p → ℕ) (α : Fin p) :=
  (β : {β : Fin p // β ≠ α}) → Fin (n β.1)

def joinProfile {p : ℕ} {n : Fin p → ℕ} (α : Fin p) (i : Fin (n α))
    (s : OtherProfile n α) : Profile n := (Equiv.piSplitAt α (fun β => Fin (n β))).symm (i,s)

lemma joinProfile_self {p : ℕ} {n : Fin p → ℕ} (α : Fin p) (i : Fin (n α))
    (s : OtherProfile n α) : joinProfile α i s α = i := by
  simp [joinProfile, Equiv.piSplitAt]

lemma joinProfile_other {p : ℕ} {n : Fin p → ℕ} (α : Fin p) (i : Fin (n α))
    (s : OtherProfile n α) (β : {β : Fin p // β ≠ α}) : joinProfile α i s β.1 = s β := by
  simp [joinProfile, Equiv.piSplitAt, β.property]

lemma joinProfile_update {p : ℕ} {n : Fin p → ℕ} (α : Fin p) (i j : Fin (n α))
    (s : OtherProfile n α) : Function.update (joinProfile α i s) α j = joinProfile α j s := by
  funext β
  by_cases h : β = α
  · subst β
    simp [joinProfile_self]
  · simp [joinProfile, Equiv.piSplitAt, h]

noncomputable def otherWeight {p : ℕ} {n : Fin p → ℕ} (x : Mixed n) (α : Fin p)
    (s : OtherProfile n α) : ℝ := ∏ β : {β : Fin p // β ≠ α}, x β.1 (s β)

noncomputable def productExpectation {p : ℕ} {n : Fin p → ℕ}
    (x : Mixed n) (f : Profile n → ℝ) : ℝ := ∑ s : Profile n, f s * ∏ β, x β (s β)

lemma profile_weight_split {p : ℕ} {n : Fin p → ℕ} (x : Mixed n) (α : Fin p)
    (i : Fin (n α)) (s : OtherProfile n α) :
    (∏ β, x β (joinProfile α i s β)) = x α i * otherWeight x α s := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ α]
  simp only [joinProfile_self, joinProfile_other, otherWeight]

lemma otherWeight_update {p : ℕ} {n : Fin p → ℕ} (x : Mixed n) (α : Fin p)
    (q : Fin (n α) → ℝ) (s : OtherProfile n α) :
    otherWeight (Function.update x α q) α s = otherWeight x α s := by
  unfold otherWeight
  apply Finset.prod_congr rfl
  intro β _
  rw [Function.update_of_ne β.property]

lemma productExpectation_split {p : ℕ} {n : Fin p → ℕ}
    (x : Mixed n) (f : Profile n → ℝ) (α : Fin p) :
    productExpectation x f = ∑ i : Fin (n α), x α i *
      ∑ s : OtherProfile n α, f (joinProfile α i s) * otherWeight x α s := by
  classical
  unfold productExpectation
  rw [← (Equiv.piSplitAt α (fun β => Fin (n β))).symm.sum_comp
    (fun s => f s * ∏ β, x β (s β)), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  change f (joinProfile α i s) * (∏ β, x β (joinProfile α i s β)) = _
  rw [profile_weight_split]
  ring

lemma productExpectation_update_mono {p : ℕ} {n : Fin p → ℕ}
    (x : Mixed n) (hx : x ∈ mixedProfiles n) (f : Profile n → ℝ) (α : Fin p)
    (q : Fin (n α) → ℝ) (hq : q ∈ stdSimplex ℝ (Fin (n α)))
    (horder : Tco (x α) ≤ Tco q)
    (hf : ∀ s : Profile n, Monotone (fun i => f (Function.update s α i))) :
    productExpectation x f ≤ productExpectation (Function.update x α q) f := by
  classical
  rw [productExpectation_split x f α, productExpectation_split _ f α]
  simp only [Function.update_self, otherWeight_update]
  apply stochastic_order_mean (x α) q _ (hx α) hq horder
  intro i j hij
  apply Finset.sum_le_sum
  intro s _
  have hh := hf (joinProfile α i s) hij
  dsimp only at hh
  rw [joinProfile_update, joinProfile_update] at hh
  apply mul_le_mul_of_nonneg_right hh
  exact Finset.prod_nonneg (fun β _ => (hx β.1).1 (s β))

theorem productExpectation_mono {p : ℕ} {n : Fin p → ℕ}
    (x y : Mixed n) (hx : x ∈ mixedProfiles n) (hy : y ∈ mixedProfiles n)
    (hxy : ∀ α, Tco (x α) ≤ Tco (y α)) (f : Profile n → ℝ)
    (hf : ∀ α (s : Profile n), Monotone (fun i => f (Function.update s α i))) :
    productExpectation x f ≤ productExpectation y f := by
  classical
  let mix := fun (s : Finset (Fin p)) (α : Fin p) => if α ∈ s then y α else x α
  have hmem : ∀ s, mix s ∈ mixedProfiles n := by
    intro s α
    dsimp [mix]
    split_ifs <;> first | exact hy α | exact hx α
  have hh : ∀ s, productExpectation x f ≤ productExpectation (mix s) f := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert α s hα ih =>
      have hstep := productExpectation_update_mono (mix s) (hmem s) f α (y α) (hy α)
        (by simpa [mix, hα] using hxy α) (hf α)
      have he : Function.update (mix s) α (y α) = mix (insert α s) := by
        funext β
        by_cases hb : β = α
        · subst β; simp [mix]
        · simp [mix, hb]
      rw [he] at hstep
      exact ih.trans hstep
  simpa [mix] using hh Finset.univ

lemma productExpectation_sub {p : ℕ} {n : Fin p → ℕ} (x : Mixed n)
    (f g : Profile n → ℝ) :
    productExpectation x (fun s => f s-g s) = productExpectation x f-productExpectation x g := by
  simp only [productExpectation, sub_mul, Finset.sum_sub_distrib]

lemma payoffVec_as_expectation {p : ℕ} {n : Fin p → ℕ} (x : Mixed n)
    (hx : x ∈ mixedProfiles n) (u : (α : Fin p) → Profile n → ℝ)
    (α : Fin p) (i : Fin (n α)) :
    payoffVec u x α i = productExpectation x (fun s => u α (Function.update s α i)) := by
  classical
  have he : payoffVec u x α i =
      ∑ s : OtherProfile n α, u α (joinProfile α i s) * otherWeight x α s := by
    unfold payoffVec
    rw [← (Equiv.piSplitAt α (fun β => Fin (n β))).symm.sum_comp
      (fun s => if s α = i then u α s * ∏ β ∈ Finset.univ.erase α, x β (s β) else 0),
      Fintype.sum_prod_type]
    change (∑ k : Fin (n α), ∑ s : OtherProfile n α,
      if joinProfile α k s α = i then u α (joinProfile α k s) *
        ∏ β ∈ Finset.univ.erase α, x β (joinProfile α k s β) else 0) = _
    simp only [joinProfile_self]
    rw [Finset.sum_eq_single i]
    · simp only [if_true]
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      rw [Finset.prod_subtype (F := inferInstance) (p := fun β : Fin p => β ≠ α) (Finset.univ.erase α) (by simp)]
      simp only [joinProfile_other, otherWeight]
    · intro k _ hki
      simp [hki]
    · simp
  rw [he, productExpectation_split _ _ α]
  simp only [joinProfile_update]
  rw [← Finset.sum_mul, (hx α).2, one_mul]

end StochFictPlay.SupermodularProof

end

/- Complete checked body: DensityTies -/
section

open scoped ENNReal
open MeasureTheory
open StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

theorem density_probability {k : ℕ} (f : (Fin k → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) :
    IsProbabilityMeasure (volume.withDensity f) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hf.2.2.2.1

theorem volume_tie_zero {k : ℕ} (π : Fin k → ℝ) (i j : Fin k) (hij : i ≠ j) :
    volume {e : Fin k → ℝ | π i+e i = π j+e j} = 0 := by
  let L : (Fin k → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i - LinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j
  have hL : L ≠ 0 := by
    intro h
    have he := congrArg (fun q : (Fin k → ℝ) →ₗ[ℝ] ℝ => q (Pi.single i 1)) h
    simp [L, Ne.symm hij] at he
  have hker : LinearMap.ker L ≠ ⊤ := by
    intro h
    apply hL
    exact LinearMap.ker_eq_top.mp h
  have hz := Measure.addHaar_submodule (volume : Measure (Fin k → ℝ)) (LinearMap.ker L) hker
  have he : {e : Fin k → ℝ | π i+e i = π j+e j} =
      (fun e => π+e) ⁻¹' (LinearMap.ker L : Set (Fin k → ℝ)) := by
    ext e
    simp [L, sub_eq_zero]
  rw [he, measure_preimage_add]
  exact hz

theorem density_tie_zero {k : ℕ} (f : (Fin k → ℝ) → ℝ≥0∞)
    (π : Fin k → ℝ) (i j : Fin k) (hij : i ≠ j) :
    volume.withDensity f {e : Fin k → ℝ | π i+e i = π j+e j} = 0 :=
  withDensity_absolutelyContinuous volume f (volume_tie_zero π i j hij)

theorem ae_no_ties {k : ℕ} (f : (Fin k → ℝ) → ℝ≥0∞) (π : Fin k → ℝ) :
    ∀ᵐ e ∂volume.withDensity f, ∀ i j : Fin k, i ≠ j → π i+e i ≠ π j+e j := by
  simp only [ae_all_iff]
  intro i j hij
  rw [ae_iff]
  simpa only [not_not] using density_tie_zero f π i j hij


end StochFictPlay.SupermodularProof
end

/- Complete checked body: ChoiceLaw -/
section

open scoped BigOperators ENNReal
open MeasureTheory StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

theorem measurable_strictWinner {k : ℕ} (π : Fin k → ℝ) (i : Fin k) :
    MeasurableSet {e : Fin k → ℝ | ∀ j, j ≠ i → π j+e j < π i+e i} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt (measurable_const.add (measurable_pi_apply j))
    (measurable_const.add (measurable_pi_apply i))

theorem argmax_indicator_ae {k : ℕ} (f : (Fin k → ℝ) → ℝ≥0∞)
    (π : Fin k → ℝ) (i : Fin k) :
    (fun e => argmaxVec (π+e) i) =ᵐ[volume.withDensity f]
      {e : Fin k → ℝ | ∀ j, j ≠ i → π j+e j < π i+e i}.indicator (fun _ => (1:ℝ)) := by
  classical
  filter_upwards [ae_no_ties f π] with e he
  have hi : IsLeastMax (π+e) i ↔ ∀ j, j ≠ i → π j+e j < π i+e i := by
    constructor
    · intro h j hji
      exact lt_of_le_of_ne (h.1 j) (he j i hji)
    · intro h
      constructor
      · intro j
        by_cases hji : j=i
        · subst j; exact le_rfl
        · exact (h j hji).le
      · intro j hj
        exact h j (ne_of_lt hj)
  have hi' : ((∀ j, (π+e) j ≤ (π+e) i) ∧ ∀ j, j < i → (π+e) j < (π+e) i) ↔
      ∀ j, j ≠ i → π j+e j < π i+e i := hi
  simp only [argmaxVec, hi', Set.indicator_apply, Set.mem_ofPred_eq]

theorem argmax_integrable {k : ℕ} (hk : 0 < k) (f : (Fin k → ℝ) → ℝ≥0∞)
    (hf : IsRegularDensity f) (π : Fin k → ℝ) (i : Fin k) :
    Integrable (fun e => argmaxVec (π+e) i) (volume.withDensity f) := by
  let : IsProbabilityMeasure (volume.withDensity f) := density_probability f hf
  have hm : Measurable (fun e => argmaxVec (π+e) i) :=
    (measurable_pi_apply i).comp ((measurable_argmaxVec hk).comp (measurable_const.add measurable_id))
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [] with e
  unfold argmaxVec
  split_ifs <;> norm_num

theorem choiceProb_eq_integral {k : ℕ} (f : (Fin k → ℝ) → ℝ≥0∞)
    (π : Fin k → ℝ) (i : Fin k) :
    choiceProb f π i = ∫ e, argmaxVec (π+e) i ∂volume.withDensity f := by
  rw [integral_congr_ae (argmax_indicator_ae f π i)]
  change (volume.withDensity f).real {e : Fin k → ℝ | ∀ j, j ≠ i → π j+e j < π i+e i} =
    ∫ e, {e : Fin k → ℝ | ∀ j, j ≠ i → π j+e j < π i+e i}.indicator 1 e ∂volume.withDensity f
  exact (integral_indicator_one (measurable_strictWinner π i)).symm

theorem choiceProb_simplex {k : ℕ} (hk : 0 < k) (f : (Fin k → ℝ) → ℝ≥0∞)
    (hf : IsRegularDensity f) (π : Fin k → ℝ) :
    choiceProb f π ∈ stdSimplex ℝ (Fin k) := by
  let : IsProbabilityMeasure (volume.withDensity f) := density_probability f hf
  constructor
  · intro i
    exact ENNReal.toReal_nonneg
  · simp_rw [choiceProb_eq_integral]
    rw [← integral_finsetSum _ (fun i _ => argmax_integrable hk f hf π i)]
    have he : (fun e : Fin k → ℝ => ∑ i, argmaxVec (π+e) i) = fun _ => (1:ℝ) := by
      funext e
      exact (argmaxVec_simplex hk (π+e)).2
    rw [he]
    simp

theorem continuous_payoffVec {p : ℕ} {n : Fin p → ℕ}
    (u : (α : Fin p) → Profile n → ℝ) : Continuous (payoffVec u) := by
  unfold payoffVec
  apply continuous_pi
  intro α
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro s _
  by_cases hs : s α=i
  · simp only [if_pos hs]
    fun_prop
  · simp only [if_neg hs]
    exact continuous_const

theorem continuous_pbr {p : ℕ} {n : Fin p → ℕ}
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) : Continuous (pbr f u) := by
  apply continuous_pi
  intro α
  exact (hf α).2.2.2.2.continuous.comp ((continuous_apply α).comp (continuous_payoffVec u))

theorem pbr_mem_mixed {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) (x : Mixed n) : pbr f u x ∈ mixedProfiles n := by
  intro α
  exact choiceProb_simplex (hn α) (f α) (hf α) (payoffVec u x α)


end StochFictPlay.SupermodularProof
end

/- Complete checked body: TailCoordinates -/
section

open scoped BigOperators
open StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

lemma tailMass_zero {m : ℕ} (v : Fin (m-1) → ℝ) : tailMass v 0 = 1 := by
  simp [tailMass]

lemma tailMass_end {m : ℕ} (hm : 0 < m) (v : Fin (m-1) → ℝ) : tailMass v m = 0 := by
  simp [tailMass, hm.ne']

lemma tailMass_index {m : ℕ} (v : Fin (m-1) → ℝ) (i : Fin (m-1)) :
    tailMass v (i.val+1) = v i := by
  simp [tailMass, i.isLt]

lemma Tinv_sum {m : ℕ} (hm : 0 < m) (v : Fin (m-1) → ℝ) :
    ∑ j : Fin m, Tinv v j = 1 := by
  classical
  calc
    _ = ∑ j ∈ Finset.range m, (tailMass v j - tailMass v (j+1)) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [dif_pos (Finset.mem_range.mp hj), Tinv]
    _ = tailMass v 0 - tailMass v m := Finset.sum_range_sub' _ _
    _ = 1 := by rw [tailMass_zero, tailMass_end hm]; ring

lemma Tco_Tinv {m : ℕ} (v : Fin (m-1) → ℝ) : Tco (Tinv v) = v := by
  classical
  funext i
  let F : ℕ → ℝ := fun j => tailMass v (max (i.val+1) j)
  have hf : ∀ j : ℕ, (if i.val < j then tailMass v j-tailMass v (j+1) else 0) =
      F j - F (j+1) := by
    intro j
    by_cases hj : i.val < j
    · have h2 : i.val+1 ≤ j+1 := by omega
      simp [hj, F, max_eq_right h2]
    · have h1 : j ≤ i.val+1 := by omega
      have h2 : j+1 ≤ i.val+1 := by omega
      simp [hj, F, max_eq_left h1, max_eq_left h2]
  have hm : 0 < m := by have hi := i.isLt; omega
  have him : i.val+1 ≤ m := by have hi := i.isLt; omega
  calc
    Tco (Tinv v) i = ∑ j ∈ Finset.range m,
        (if i.val < j then tailMass v j-tailMass v (j+1) else 0) := by
      rw [Tco, Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [dif_pos (Finset.mem_range.mp hj), Tinv]
    _ = ∑ j ∈ Finset.range m, (F j-F (j+1)) :=
      Finset.sum_congr rfl (fun j _ => hf j)
    _ = F 0 - F m := Finset.sum_range_sub' _ _
    _ = v i := by simp [F, max_eq_right him, tailMass_end hm, tailMass_index]

lemma tailMass_Tco {m : ℕ} (x : Fin m → ℝ) (hx : ∑ j, x j = 1) (k : ℕ) :
    tailMass (Tco x) k = ∑ j : Fin m, if k ≤ j.val then x j else 0 := by
  classical
  by_cases hk : k = 0
  · subst k
    simp [tailMass, hx]
  · by_cases hm : k-1 < m-1
    · simp only [tailMass, hk, if_false, dif_pos hm, Tco]
      apply Finset.sum_congr rfl
      intro j _
      have he : k-1 < j.val ↔ k ≤ j.val := by omega
      simp only [he]
    · simp only [tailMass, hk, if_false, dif_neg hm]
      symm
      apply Finset.sum_eq_zero
      intro j _
      have hj := j.isLt
      have hkj : ¬k ≤ j.val := by omega
      simp [hkj]

lemma Tinv_Tco {m : ℕ} (x : Fin m → ℝ) (hx : ∑ j, x j = 1) : Tinv (Tco x) = x := by
  classical
  funext i
  simp only [Tinv, tailMass_Tco x hx, ← Finset.sum_sub_distrib]
  calc
    (∑ j : Fin m, ((if i.val ≤ j.val then x j else 0) -
      (if i.val+1 ≤ j.val then x j else 0))) =
        ∑ j : Fin m, if j = i then x j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j; simp
      · have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
        by_cases hle : i.val ≤ j.val
        · have hlt : i.val+1 ≤ j.val := by omega
          simp [hji, hle, hlt]
        · have hlt : ¬i.val+1 ≤ j.val := by omega
          simp [hji, hle, hlt]
    _ = x i := by simp

lemma tailMass_bounds {m : ℕ} (v : Fin (m-1) → ℝ)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (k : ℕ) : 0 ≤ tailMass v k ∧ tailMass v k ≤ 1 := by
  unfold tailMass
  split_ifs <;> first | exact hv _ | constructor <;> norm_num

lemma tailMass_antitone {m : ℕ} (v : Fin (m-1) → ℝ)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (ha : Antitone v) : Antitone (tailMass v) := by
  intro a b hab
  by_cases ha0 : a = 0
  · subst a
    rw [tailMass_zero]
    exact (tailMass_bounds v hv b).2
  by_cases hb0 : b = 0
  · omega
  by_cases ham : a-1 < m-1
  · by_cases hbm : b-1 < m-1
    · simp only [tailMass, ha0, hb0, if_false, dif_pos ham, dif_pos hbm]
      exact ha (show (⟨a-1, ham⟩ : Fin (m-1)) ≤ ⟨b-1, hbm⟩ from Nat.sub_le_sub_right hab 1)
    · simp only [tailMass, ha0, hb0, if_false, dif_pos ham, dif_neg hbm]
      exact (hv _).1
  · have hbm : ¬b-1 < m-1 := by omega
    simp [tailMass, ha0, hb0, ham, hbm]

lemma Tinv_simplex {m : ℕ} (hm : 0 < m) (v : Fin (m-1) → ℝ)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (ha : Antitone v) :
    Tinv v ∈ stdSimplex ℝ (Fin m) := by
  constructor
  · intro i
    exact sub_nonneg.mpr (tailMass_antitone v hv ha (Nat.le_succ i.val))
  · exact Tinv_sum hm v

lemma Tco_bounds {m : ℕ} (x : Fin m → ℝ) (hx : x ∈ stdSimplex ℝ (Fin m)) :
    ∀ i, 0 ≤ Tco x i ∧ Tco x i ≤ 1 := by
  intro i
  constructor
  · exact Finset.sum_nonneg (fun j _ => by split_ifs; exact hx.1 j; rfl)
  · calc
      Tco x i ≤ ∑ j, x j := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs <;> first | exact le_rfl | exact hx.1 j
      _ = 1 := hx.2

lemma Tco_antitone {m : ℕ} (x : Fin m → ℝ) (hx : ∀ j, 0 ≤ x j) : Antitone (Tco x) := by
  intro i j hij
  apply Finset.sum_le_sum
  intro k _
  change (if j.val < k.val then x k else 0) ≤ (if i.val < k.val then x k else 0)
  have hv : i.val ≤ j.val := hij
  split_ifs <;> first | exact le_rfl | exact hx k | omega

end StochFictPlay.SupermodularProof

end

/- Complete checked body: TailSpace -/
section

open scoped BigOperators Topology
open Set StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

abbrev TailIndex {p : ℕ} (n : Fin p → ℕ) := Σ α : Fin p, Fin (n α - 1)

def tailLinear {p : ℕ} (n : Fin p → ℕ) : Mixed n →ₗ[ℝ] (TailIndex n → ℝ) where
  toFun x a := Tco (x a.1) a.2
  map_add' x y := by
    classical
    funext a
    simp only [Tco, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  map_smul' c x := by
    classical
    funext a
    simp only [Tco, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp

def fromTails {p : ℕ} (n : Fin p → ℕ) (v : TailIndex n → ℝ) : Mixed n :=
  TinvMap (fun α i => v ⟨α,i⟩)

def TailSet {p : ℕ} (n : Fin p → ℕ) : Set (TailIndex n → ℝ) :=
  {v | (fun α i => v ⟨α,i⟩) ∈ TSigma n}

lemma tailLinear_fromTails {p : ℕ} (n : Fin p → ℕ) (v : TailIndex n → ℝ) :
    tailLinear n (fromTails n v) = v := by
  funext a
  exact congrFun (Tco_Tinv (fun i => v ⟨a.1,i⟩)) a.2

lemma fromTails_tailLinear {p : ℕ} {n : Fin p → ℕ} (x : Mixed n)
    (hx : x ∈ mixedProfiles n) : fromTails n (tailLinear n x) = x := by
  funext α
  exact Tinv_Tco (x α) (hx α).2

lemma tailLinear_mem {p : ℕ} {n : Fin p → ℕ} (x : Mixed n)
    (hx : x ∈ mixedProfiles n) : tailLinear n x ∈ TailSet n := by
  intro α
  refine ⟨fun i => ⟨(Tco_bounds (x α) (hx α) i).2, (Tco_bounds (x α) (hx α) i).1⟩, ?_⟩
  exact Tco_antitone (x α) (hx α).1

lemma fromTails_mem {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (v : TailIndex n → ℝ) (hv : v ∈ TailSet n) : fromTails n v ∈ mixedProfiles n := by
  intro α
  exact Tinv_simplex (hn α) (fun i => v ⟨α,i⟩)
    (fun i => ⟨((hv α).1 i).2, ((hv α).1 i).1⟩) (hv α).2

lemma continuous_tailLinear {p : ℕ} (n : Fin p → ℕ) : Continuous (tailLinear n) :=
  (tailLinear n).continuous_of_finiteDimensional

lemma continuous_fromTails {p : ℕ} (n : Fin p → ℕ) : Continuous (fromTails n) := by
  classical
  apply continuous_pi
  intro α
  apply continuous_pi
  intro j
  change Continuous (fun v : TailIndex n → ℝ =>
    tailMass (fun i => v ⟨α,i⟩) j.val - tailMass (fun i => v ⟨α,i⟩) (j.val+1))
  apply Continuous.sub
  · unfold tailMass
    split_ifs <;> fun_prop
  · unfold tailMass
    split_ifs <;> fun_prop

lemma TailSet_zero {p : ℕ} (n : Fin p → ℕ) : (fun _ => 0) ∈ TailSet n := by
  intro α
  exact ⟨fun _ => ⟨by norm_num, le_rfl⟩, fun _ _ _ => le_rfl⟩

lemma TailSet_one {p : ℕ} (n : Fin p → ℕ) : (fun _ => 1) ∈ TailSet n := by
  intro α
  exact ⟨fun _ => ⟨le_rfl, by norm_num⟩, fun _ _ _ => le_rfl⟩

lemma TailSet_bounds {p : ℕ} {n : Fin p → ℕ} (v : TailIndex n → ℝ) (hv : v ∈ TailSet n) :
    (fun _ => 0) ≤ v ∧ v ≤ (fun _ => 1) :=
  ⟨fun a => ((hv a.1).1 a.2).2, fun a => ((hv a.1).1 a.2).1⟩

lemma TailSet_closed {p : ℕ} (n : Fin p → ℕ) : IsClosed (TailSet n) := by
  change IsClosed {v : TailIndex n → ℝ | ∀ α,
    (∀ i, v ⟨α,i⟩ ≤ 1 ∧ 0 ≤ v ⟨α,i⟩) ∧ Antitone (fun i => v ⟨α,i⟩)}
  simp only [Set.ofPred_forall, Set.ofPred_and, Antitone]
  apply isClosed_iInter
  intro α
  apply IsClosed.inter
  · apply isClosed_iInter
    intro i
    exact (isClosed_le (continuous_apply (⟨α,i⟩ : TailIndex n)) continuous_const).inter
      (isClosed_le continuous_const (continuous_apply (⟨α,i⟩ : TailIndex n)))
  · apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro _
    exact isClosed_le (continuous_apply (⟨α,j⟩ : TailIndex n)) (continuous_apply (⟨α,i⟩ : TailIndex n))

lemma TailSet_inf {p : ℕ} {n : Fin p → ℕ} (v w : TailIndex n → ℝ)
    (hv : v ∈ TailSet n) (hw : w ∈ TailSet n) : v ⊓ w ∈ TailSet n := by
  intro α
  constructor
  · intro i
    exact ⟨(min_le_left _ _).trans ((hv α).1 i).1,
      le_min ((hv α).1 i).2 ((hw α).1 i).2⟩
  · intro i j hij
    exact min_le_min ((hv α).2 hij) ((hw α).2 hij)

lemma TailSet_sup {p : ℕ} {n : Fin p → ℕ} (v w : TailIndex n → ℝ)
    (hv : v ∈ TailSet n) (hw : w ∈ TailSet n) : v ⊔ w ∈ TailSet n := by
  intro α
  constructor
  · intro i
    exact ⟨max_le ((hv α).1 i).1 ((hw α).1 i).1,
      ((hv α).1 i).2.trans (le_max_left _ _)⟩
  · intro i j hij
    exact max_le_max ((hv α).2 hij) ((hw α).2 hij)

end StochFictPlay.SupermodularProof

end

/- Complete checked body: ResponseOrder -/
section

open scoped BigOperators ENNReal
open MeasureTheory Set StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

theorem payoff_differences_mono {p : ℕ} {n : Fin p → ℕ}
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (x y : Mixed n) (hx : x ∈ mixedProfiles n) (hy : y ∈ mixedProfiles n)
    (hxy : ∀ α, Tco (x α) ≤ Tco (y α)) (α : Fin p) (i j : Fin (n α)) (hji : j < i) :
    payoffVec u x α i-payoffVec u x α j ≤ payoffVec u y α i-payoffVec u y α j := by
  classical
  let g := fun s : Profile n => u α (Function.update s α i)-u α (Function.update s α j)
  have hg : ∀ β (s : Profile n), Monotone (fun k => g (Function.update s β k)) := by
    intro β s
    by_cases hba : β = α
    · subst β
      intro k l _
      simp only [g, Function.update_idem]
      exact le_rfl
    · have hh := (hu α β (Ne.symm hba) s i j hji).monotone
      simpa only [g, Function.update_comm hba] using hh
  have hh := productExpectation_mono x y hx hy hxy g hg
  dsimp [g] at hh
  rw [productExpectation_sub, productExpectation_sub,
    ← payoffVec_as_expectation x hx u α i, ← payoffVec_as_expectation x hx u α j,
    ← payoffVec_as_expectation y hy u α i, ← payoffVec_as_expectation y hy u α j] at hh
  exact hh

lemma argmax_tail_integrable {m : ℕ} (hm : 0 < m)
    (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π : Fin m → ℝ)
    (i : Fin (m-1)) :
    Integrable (fun e => Tco (argmaxVec (π+e)) i) (volume.withDensity f) := by
  classical
  apply integrable_finsetSum
  intro j _
  by_cases hij : i.val < j.val
  · simpa only [if_pos hij] using argmax_integrable hm f hf π j
  · simp only [if_neg hij]
    exact integrable_zero _ _ _

lemma Tco_choiceProb_integral {m : ℕ} (hm : 0 < m)
    (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (π : Fin m → ℝ)
    (i : Fin (m-1)) :
    Tco (choiceProb f π) i = ∫ e, Tco (argmaxVec (π+e)) i ∂volume.withDensity f := by
  classical
  unfold Tco
  calc
    _ = ∑ j : Fin m, ∫ e, (if i.val < j.val then argmaxVec (π+e) j else 0) ∂volume.withDensity f := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i.val < j.val
      · simp only [if_pos hij, choiceProb_eq_integral]
      · simp [hij]
    _ = _ := by
      rw [integral_finsetSum _ (fun j _ => ?_)]
      by_cases hij : i.val < j.val
      · simpa only [if_pos hij] using argmax_integrable hm f hf π j
      · simp only [if_neg hij]
        exact integrable_zero _ _ _

theorem choiceProb_tail_mono {m : ℕ} (hm : 0 < m)
    (f : (Fin m → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f) (v w : Fin m → ℝ)
    (hvw : ∀ i j : Fin m, j < i → v i-v j ≤ w i-w j) :
    Tco (choiceProb f v) ≤ Tco (choiceProb f w) := by
  intro i
  rw [Tco_choiceProb_integral hm f hf v, Tco_choiceProb_integral hm f hf w]
  exact integral_mono (argmax_tail_integrable hm f hf v i)
    (argmax_tail_integrable hm f hf w i) (fun e => argmaxVec_tail_mono hm v w e hvw i)

theorem pbr_tail_mono {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (x y : Mixed n) (hx : x ∈ mixedProfiles n) (hy : y ∈ mixedProfiles n)
    (hxy : ∀ α, Tco (x α) ≤ Tco (y α)) :
    ∀ α, Tco (pbr f u x α) ≤ Tco (pbr f u y α) := by
  intro α
  exact choiceProb_tail_mono (hn α) (f α) (hf α) (payoffVec u x α) (payoffVec u y α)
    (fun i j hji => payoff_differences_mono u hu x y hx hy hxy α i j hji)

noncomputable def tailResponse {p : ℕ} (n : Fin p → ℕ)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞)
    (u : (α : Fin p) → Profile n → ℝ) (v : TailIndex n → ℝ) : TailIndex n → ℝ :=
  tailLinear n (pbr f u (fromTails n v))

theorem tailResponse_mem {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) : MapsTo (tailResponse n f u) (TailSet n) (TailSet n) := by
  intro v _
  exact tailLinear_mem _ (pbr_mem_mixed hn f hf u _)

theorem tailResponse_continuous {p : ℕ} (n : Fin p → ℕ)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) : Continuous (tailResponse n f u) :=
  (continuous_tailLinear n).comp ((continuous_pbr f hf u).comp (continuous_fromTails n))

theorem tailResponse_mono {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u) :
    MonotoneOn (tailResponse n f u) (TailSet n) := by
  intro v hv w hw hvw
  have hh := pbr_tail_mono hn f hf u hu (fromTails n v) (fromTails n w)
    (fromTails_mem hn v hv) (fromTails_mem hn w hw) (by
      intro α i
      have h1 := congrFun (tailLinear_fromTails n v) ⟨α,i⟩
      have h2 := congrFun (tailLinear_fromTails n w) ⟨α,i⟩
      change Tco (fromTails n v α) i = v ⟨α,i⟩ at h1
      change Tco (fromTails n w α) i = w ⟨α,i⟩ at h2
      rw [h1, h2]
      exact hvw ⟨α,i⟩)
  intro a
  exact hh a.1 a.2

end StochFictPlay.SupermodularProof

end

/- Complete checked body: LatticeIteration -/
section

open scoped Topology
open Filter Set

namespace StochFictPlay.SupermodularProof

def responseIterate {E : Type*} (B : E → E) (a : E) : ℕ → E
  | 0 => a
  | r+1 => B (responseIterate B a r)

lemma responseIterate_mem {E : Type*} {K : Set E} (B : E → E)
    (hB : MapsTo B K K) {a : E} (ha : a ∈ K) (r : ℕ) : responseIterate B a r ∈ K := by
  induction r with
  | zero => exact ha
  | succ r ih => exact hB ih

lemma responseIterate_mono {ι : Type*} {K : Set (ι → ℝ)} (B : (ι → ℝ) → ι → ℝ)
    (hB : MapsTo B K K) (hm : MonotoneOn B K) {a : ι → ℝ} (ha : a ∈ K)
    (hle : a ≤ B a) : Monotone (responseIterate B a) := by
  apply monotone_nat_of_le_succ
  intro r
  induction r with
  | zero => exact hle
  | succ r ih =>
    exact hm (responseIterate_mem B hB ha r) (responseIterate_mem B hB ha (r+1)) ih

lemma responseIterate_anti {ι : Type*} {K : Set (ι → ℝ)} (B : (ι → ℝ) → ι → ℝ)
    (hB : MapsTo B K K) (hm : MonotoneOn B K) {a : ι → ℝ} (ha : a ∈ K)
    (hle : B a ≤ a) : Antitone (responseIterate B a) := by
  apply antitone_nat_of_succ_le
  intro r
  induction r with
  | zero => exact hle
  | succ r ih =>
    exact hm (responseIterate_mem B hB ha (r+1)) (responseIterate_mem B hB ha r) ih

theorem lower_iterates_tendsto {ι : Type*} {K : Set (ι → ℝ)} (hK : IsClosed K)
    (hbound : ∀ v ∈ K, v ≤ (fun _ => 1)) (B : (ι → ℝ) → ι → ℝ)
    (hB : MapsTo B K K) (hm : MonotoneOn B K) (hc : ContinuousOn B K)
    (c : ι → ℝ) (hu : ∀ v ∈ K, B v = v → v = c)
    (a : ι → ℝ) (ha : a ∈ K) (hle : a ≤ B a) :
    Tendsto (responseIterate B a) atTop (𝓝 c) := by
  let l : ι → ℝ := fun i => ⨆ r, responseIterate B a r i
  have hmono := responseIterate_mono B hB hm ha hle
  have ht : Tendsto (responseIterate B a) atTop (𝓝 l) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_atTop_ciSup (fun r s hrs => hmono hrs i)
    exact ⟨1, by rintro y ⟨r, rfl⟩; exact hbound _ (responseIterate_mem B hB ha r) i⟩
  have hl : l ∈ K := hK.mem_of_tendsto ht
    (Eventually.of_forall (responseIterate_mem B hB ha))
  have htK : Tendsto (responseIterate B a) atTop (𝓝[K] l) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (responseIterate_mem B hB ha)⟩
  have hb : Tendsto (fun r => B (responseIterate B a r)) atTop (𝓝 (B l)) := Filter.Tendsto.comp (hc l hl) htK
  have hs : Tendsto (fun r => responseIterate B a (r+1)) atTop (𝓝 l) :=
    (tendsto_add_atTop_iff_nat 1).2 ht
  have he : B l = l := tendsto_nhds_unique hb hs
  rwa [hu l hl he] at ht

theorem upper_iterates_tendsto {ι : Type*} {K : Set (ι → ℝ)} (hK : IsClosed K)
    (hbound : ∀ v ∈ K, (fun _ => 0) ≤ v) (B : (ι → ℝ) → ι → ℝ)
    (hB : MapsTo B K K) (hm : MonotoneOn B K) (hc : ContinuousOn B K)
    (c : ι → ℝ) (hu : ∀ v ∈ K, B v = v → v = c)
    (a : ι → ℝ) (ha : a ∈ K) (hle : B a ≤ a) :
    Tendsto (responseIterate B a) atTop (𝓝 c) := by
  let l : ι → ℝ := fun i => ⨅ r, responseIterate B a r i
  have hanti := responseIterate_anti B hB hm ha hle
  have ht : Tendsto (responseIterate B a) atTop (𝓝 l) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_atTop_ciInf (fun r s hrs => hanti hrs i)
    exact ⟨0, by rintro y ⟨r, rfl⟩; exact hbound _ (responseIterate_mem B hB ha r) i⟩
  have hl : l ∈ K := hK.mem_of_tendsto ht
    (Eventually.of_forall (responseIterate_mem B hB ha))
  have htK : Tendsto (responseIterate B a) atTop (𝓝[K] l) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (responseIterate_mem B hB ha)⟩
  have hb : Tendsto (fun r => B (responseIterate B a r)) atTop (𝓝 (B l)) := Filter.Tendsto.comp (hc l hl) htK
  have hs : Tendsto (fun r => responseIterate B a (r+1)) atTop (𝓝 l) :=
    (tendsto_add_atTop_iff_nat 1).2 ht
  have he : B l = l := tendsto_nhds_unique hb hs
  rwa [hu l hl he] at ht

end StochFictPlay.SupermodularProof

end

/- Complete checked body: CesaroLattice -/
section

open scoped BigOperators Topology
open Filter Set

namespace StochFictPlay.SupermodularProof

noncomputable def vectorAverage {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (z : ℕ → E) (t : ℕ) : E :=
  (t : ℝ)⁻¹ • ∑ s ∈ Finset.range t, z s

lemma vectorAverage_mono {ι : Type*} {x y : ℕ → ι → ℝ} (h : ∀ t, x t ≤ y t) (t : ℕ) :
    vectorAverage x t ≤ vectorAverage y t := by
  intro i
  simp only [vectorAverage, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun s _ => h s i)

lemma lower_clamp_step {ι : Type*} [Fintype ι] {K : Set (ι → ℝ)}
    (B : (ι → ℝ) → ι → ℝ) (hm : MonotoneOn B K) (hc : ContinuousOn B K)
    (hmeet : ∀ x ∈ K, ∀ y ∈ K, x ⊓ y ∈ K)
    (z : ℕ → ι → ℝ) (hz : ∀ t, z t ∈ K) (a : ι → ℝ) (ha : a ∈ K)
    (ht : Tendsto (fun t => z t ⊓ a) atTop (𝓝 a))
    (he : Tendsto (fun t => z t - vectorAverage (fun s => B (z s)) t) atTop (𝓝 0)) :
    Tendsto (fun t => z t ⊓ B a) atTop (𝓝 (B a)) := by
  have hb : Tendsto (fun t => B (z t ⊓ a)) atTop (𝓝 (B a)) :=
    Filter.Tendsto.comp (hc a ha) (tendsto_nhdsWithin_iff.mpr
      ⟨ht, Eventually.of_forall (fun t => hmeet _ (hz t) a ha)⟩)
  have hv : Tendsto (fun t => vectorAverage (fun s => B (z s ⊓ a)) t) atTop (𝓝 (B a)) :=
    hb.cesaro_smul
  let l := fun t => z t - vectorAverage (fun s => B (z s)) t +
    vectorAverage (fun s => B (z s ⊓ a)) t
  have hl : Tendsto l atTop (𝓝 (B a)) := by simpa [l] using he.add hv
  have hle : ∀ t, l t ≤ z t := by
    intro t
    have hh := vectorAverage_mono (fun s => hm (hmeet _ (hz s) a ha) (hz s) inf_le_left) t
    intro i
    have hi := hh i
    dsimp [l]
    change z t i - vectorAverage (fun s => B (z s)) t i +
      vectorAverage (fun s => B (z s ⊓ a)) t i ≤ z t i
    linarith
  apply tendsto_pi_nhds.2
  intro i
  have ht' : Tendsto (fun t => min (l t i) (B a i)) atTop (𝓝 (B a i)) := by
    simpa using (tendsto_pi_nhds.1 hl i).min (tendsto_const_nhds : Tendsto (fun _ : ℕ => B a i) atTop (𝓝 (B a i)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le ht' tendsto_const_nhds
    (fun t => min_le_min_right _ (hle t i)) (fun t => min_le_right _ _)

lemma upper_clamp_step {ι : Type*} [Fintype ι] {K : Set (ι → ℝ)}
    (B : (ι → ℝ) → ι → ℝ) (hm : MonotoneOn B K) (hc : ContinuousOn B K)
    (hjoin : ∀ x ∈ K, ∀ y ∈ K, x ⊔ y ∈ K)
    (z : ℕ → ι → ℝ) (hz : ∀ t, z t ∈ K) (a : ι → ℝ) (ha : a ∈ K)
    (ht : Tendsto (fun t => z t ⊔ a) atTop (𝓝 a))
    (he : Tendsto (fun t => z t - vectorAverage (fun s => B (z s)) t) atTop (𝓝 0)) :
    Tendsto (fun t => z t ⊔ B a) atTop (𝓝 (B a)) := by
  have hb : Tendsto (fun t => B (z t ⊔ a)) atTop (𝓝 (B a)) :=
    Filter.Tendsto.comp (hc a ha) (tendsto_nhdsWithin_iff.mpr
      ⟨ht, Eventually.of_forall (fun t => hjoin _ (hz t) a ha)⟩)
  have hv : Tendsto (fun t => vectorAverage (fun s => B (z s ⊔ a)) t) atTop (𝓝 (B a)) :=
    hb.cesaro_smul
  let l := fun t => z t - vectorAverage (fun s => B (z s)) t +
    vectorAverage (fun s => B (z s ⊔ a)) t
  have hl : Tendsto l atTop (𝓝 (B a)) := by simpa [l] using he.add hv
  have hle : ∀ t, z t ≤ l t := by
    intro t
    have hh := vectorAverage_mono (fun s => hm (hz s) (hjoin _ (hz s) a ha) le_sup_left) t
    intro i
    have hi := hh i
    dsimp [l]
    change z t i ≤ z t i - vectorAverage (fun s => B (z s)) t i +
      vectorAverage (fun s => B (z s ⊔ a)) t i
    linarith
  apply tendsto_pi_nhds.2
  intro i
  have ht' : Tendsto (fun t => max (l t i) (B a i)) atTop (𝓝 (B a i)) := by
    simpa using (tendsto_pi_nhds.1 hl i).max (tendsto_const_nhds : Tendsto (fun _ : ℕ => B a i) atTop (𝓝 (B a i)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht'
    (fun t => le_max_right _ _) (fun t => max_le_max_right _ (hle t i))

theorem converge_of_cesaro_noise {ι : Type*} [Fintype ι] {K : Set (ι → ℝ)}
    (hK : IsClosed K) (h0 : (fun _ => 0) ∈ K) (h1 : (fun _ => 1) ∈ K)
    (hbound : ∀ x ∈ K, (fun _ => 0) ≤ x ∧ x ≤ (fun _ => 1))
    (hmeet : ∀ x ∈ K, ∀ y ∈ K, x ⊓ y ∈ K)
    (hjoin : ∀ x ∈ K, ∀ y ∈ K, x ⊔ y ∈ K)
    (B : (ι → ℝ) → ι → ℝ) (hB : MapsTo B K K)
    (hm : MonotoneOn B K) (hc : ContinuousOn B K)
    (c : ι → ℝ) (hu : ∀ v ∈ K, B v = v → v = c)
    (z : ℕ → ι → ℝ) (hz : ∀ t, z t ∈ K)
    (he : Tendsto (fun t => z t - vectorAverage (fun s => B (z s)) t) atTop (𝓝 0)) :
    Tendsto z atTop (𝓝 c) := by
  have ha : Tendsto (responseIterate B (fun _ => 0)) atTop (𝓝 c) :=
    lower_iterates_tendsto hK (fun x hx => (hbound x hx).2) B hB hm hc c hu _ h0
      (hbound _ (hB h0)).1
  have hb : Tendsto (responseIterate B (fun _ => 1)) atTop (𝓝 c) :=
    upper_iterates_tendsto hK (fun x hx => (hbound x hx).1) B hB hm hc c hu _ h1
      (hbound _ (hB h1)).2
  have hlow : ∀ r, Tendsto (fun t => z t ⊓ responseIterate B (fun _ => 0) r)
      atTop (𝓝 (responseIterate B (fun _ => 0) r)) := by
    intro r
    induction r with
    | zero =>
      have hh : (fun t => z t ⊓ (fun _ => 0)) = (fun _ : ℕ => (fun _ => (0 : ℝ))) :=
        funext (fun t => inf_eq_right.mpr (hbound _ (hz t)).1)
      simpa only [responseIterate, hh] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (fun _ : ι => (0 : ℝ))) atTop (𝓝 _))
    | succ r ih =>
      exact lower_clamp_step B hm hc hmeet z hz _ (responseIterate_mem B hB h0 r) ih he
  have hupp : ∀ r, Tendsto (fun t => z t ⊔ responseIterate B (fun _ => 1) r)
      atTop (𝓝 (responseIterate B (fun _ => 1) r)) := by
    intro r
    induction r with
    | zero =>
      have hh : (fun t => z t ⊔ (fun _ => 1)) = (fun _ : ℕ => (fun _ => (1 : ℝ))) :=
        funext (fun t => sup_eq_right.mpr (hbound _ (hz t)).2)
      simpa only [responseIterate, hh] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (fun _ : ι => (1 : ℝ))) atTop (𝓝 _))
    | succ r ih =>
      exact upper_clamp_step B hm hc hjoin z hz _ (responseIterate_mem B hB h1 r) ih he
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_order.2
  constructor
  · intro d hd
    obtain ⟨r, hr⟩ := ((tendsto_pi_nhds.1 ha i).eventually (lt_mem_nhds hd)).exists
    filter_upwards [(tendsto_pi_nhds.1 (hlow r) i).eventually (lt_mem_nhds hr)] with t ht
    exact ht.trans_le (min_le_left _ _)
  · intro d hd
    obtain ⟨r, hr⟩ := ((tendsto_pi_nhds.1 hb i).eventually (gt_mem_nhds hd)).exists
    filter_upwards [(tendsto_pi_nhds.1 (hupp r) i).eventually (gt_mem_nhds hr)] with t ht
    exact lt_of_le_of_lt (le_max_left _ _) ht

end StochFictPlay.SupermodularProof

end

/- Complete checked body: TailConvergence -/
section

open scoped BigOperators ENNReal Topology
open Filter Set StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

theorem tailResponse_unique {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) (xs : Mixed n)
    (hRP : restPoints (pField f u) (mixedProfiles n) = {xs})
    (v : TailIndex n → ℝ) (hv : v ∈ TailSet n) (hfix : tailResponse n f u v = v) :
    v = tailLinear n xs := by
  let x := fromTails n v
  have hx : x ∈ mixedProfiles n := fromTails_mem hn v hv
  have hp : pbr f u x = x := by
    calc
      pbr f u x = fromTails n (tailLinear n (pbr f u x)) :=
        (fromTails_tailLinear _ (pbr_mem_mixed hn f hf u x)).symm
      _ = fromTails n v := congrArg (fromTails n) hfix
      _ = x := rfl
  have hr : x ∈ restPoints (pField f u) (mixedProfiles n) := by
    refine ⟨hx, ?_⟩
    funext α
    change pbr f u x α-x α = 0
    rw [hp]
    exact sub_self _
  rw [hRP, Set.mem_singleton_iff] at hr
  calc
    v = tailLinear n x := (tailLinear_fromTails n v).symm
    _ = tailLinear n xs := congrArg (tailLinear n) hr

theorem mixed_converges_of_noise {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (xs : Mixed n) (hRP : restPoints (pField f u) (mixedProfiles n) = {xs})
    (x : ℕ → Mixed n) (hx0 : x 0 = 0) (hx : ∀ t, 0 < t → x t ∈ mixedProfiles n)
    (he : Tendsto (fun t => x t - vectorAverage (fun s => pbr f u (x s)) t) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 xs) := by
  let z := fun t => tailLinear n (x t)
  let B := tailResponse n f u
  let C := fun t => tailLinear n (pbr f u (x t))
  have hz : ∀ t, z t ∈ TailSet n := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · have hz0 : z 0 = (fun _ : TailIndex n => 0) := by
        change tailLinear n (x 0) = _
        rw [hx0, map_zero]
        rfl
      rw [hz0]
      exact TailSet_zero n
    · exact tailLinear_mem _ (hx t ht)
  have he1 : Tendsto (fun t => z t-vectorAverage C t) atTop (𝓝 0) := by
    have hh := (continuous_tailLinear n).tendsto (0 : Mixed n) |>.comp he
    simpa only [Function.comp_def, map_zero, map_sub, vectorAverage, map_smul, map_sum, z, C] using hh
  have hdiff : (fun t => C t-B (z t)) =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    dsimp [C, B, z, tailResponse]
    rw [fromTails_tailLinear _ (hx t ht)]
    exact sub_self _
  have he2 : Tendsto (fun t => vectorAverage C t-vectorAverage (fun s => B (z s)) t)
      atTop (𝓝 0) := by
    have hh : Tendsto (fun t => C t-B (z t)) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' hdiff.symm
    simpa only [vectorAverage, Finset.sum_sub_distrib, smul_sub] using hh.cesaro_smul
  have hez : Tendsto (fun t => z t-vectorAverage (fun s => B (z s)) t) atTop (𝓝 0) := by
    have hh := he1.add he2
    simpa only [sub_add_sub_cancel, add_zero] using hh
  have ht : Tendsto z atTop (𝓝 (tailLinear n xs)) :=
    converge_of_cesaro_noise (TailSet_closed n) (TailSet_zero n) (TailSet_one n)
      (fun v hv => TailSet_bounds v hv)
      (fun v hv w hw => TailSet_inf v w hv hw)
      (fun v hv w hw => TailSet_sup v w hv hw)
      B (tailResponse_mem hn f hf u) (tailResponse_mono hn f hf u hu)
      (tailResponse_continuous n f hf u).continuousOn (tailLinear n xs)
      (tailResponse_unique hn f hf u xs hRP) z hz hez
  have hxs : xs ∈ mixedProfiles n := by
    have hh : xs ∈ restPoints (pField f u) (mixedProfiles n) := by rw [hRP]; simp
    exact hh.1
  have hfz : Tendsto (fun t => fromTails n (z t)) atTop (𝓝 xs) := by
    have hh := (continuous_fromTails n).tendsto (tailLinear n xs) |>.comp ht
    rwa [fromTails_tailLinear xs hxs] at hh
  apply hfz.congr'
  filter_upwards [eventually_ge_atTop 1] with t ht
  exact fromTails_tailLinear (x t) (hx t ht)

end StochFictPlay.SupermodularProof

end

/- Complete checked body: ShockPast -/
section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

noncomputable abbrev shockHistory {Ω : Type*} {p : ℕ} {n : Fin p → ℕ}
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) : MeasurableSpace Ω :=
  ⨆ i ∈ {i : ℕ × Fin p | i.1 < t},
    (inferInstance : MeasurableSpace (Fin (n i.2) → ℝ)).comap (ε i.1 i.2)

theorem shockHistory_mono {Ω : Type*} {p : ℕ} {n : Fin p → ℕ}
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) {s t : ℕ} (hst : s ≤ t) :
    shockHistory ε s ≤ shockHistory ε t := by
  apply iSup₂_le
  intro i hi
  exact le_iSup₂_of_le i (lt_of_lt_of_le hi hst) le_rfl

theorem shockHistory_le {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} {n : Fin p → ℕ}
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : ∀ t α, Measurable (ε t α))
    (t : ℕ) : shockHistory ε t ≤ ‹MeasurableSpace Ω› := by
  exact iSup₂_le (fun i _ => (hε i.1 i.2).comap_le)

theorem measurable_shock_past {Ω : Type*} {p : ℕ} {n : Fin p → ℕ}
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) {s t : ℕ} (hst : s < t)
    (α : Fin p) : Measurable[shockHistory ε t] (ε s α) := by
  apply Measurable.of_comap_le
  exact le_iSup₂_of_le (s,α) hst le_rfl

theorem past_indep_shock {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {p : ℕ} {n : Fin p → ℕ}
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : IsShockFamily P f ε)
    {Y : Type*} [MeasurableSpace Y] (t : ℕ) (Z : Ω → Y)
    (hZ : Measurable[shockHistory ε t] Z) (α : Fin p) : IndepFun Z (ε t α) P := by
  have hI := indep_iSup_of_disjoint
    (m := fun i : ℕ × Fin p =>
      (inferInstance : MeasurableSpace (Fin (n i.2) → ℝ)).comap (ε i.1 i.2))
    (fun i => (hε.1 i.1 i.2).comap_le) hε.2.2.iIndep
    (S := {i : ℕ × Fin p | i.1 < t}) (T := {(t,α)})
    (Set.disjoint_singleton_right.mpr (by simp))
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hI hZ.comap_le)
    (le_iSup₂_of_le (t,α) (Set.mem_singleton _) le_rfl)

theorem integral_past_shock {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p : ℕ} {n : Fin p → ℕ}
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : IsShockFamily P f ε)
    {Y : Type*} [MeasurableSpace Y] (t : ℕ) (Z : Ω → Y)
    (hZ : Measurable[shockHistory ε t] Z) (α : Fin p)
    (G : Y × (Fin (n α) → ℝ) → ℝ) (hG : Measurable G)
    (C : ℝ) (hC : ∀ z, ‖G z‖ ≤ C) :
    (∫ ω, G (Z ω, ε t α ω) ∂P) =
      ∫ ω, (∫ e, G (Z ω,e) ∂volume.withDensity (f α)) ∂P := by
  have hZm : Measurable Z := hZ.mono (shockHistory_le ε hε.1 t) le_rfl
  let : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZm.aemeasurable
  let : IsProbabilityMeasure (volume.withDensity (f α)) := density_probability (f α) (hf α)
  have hmap : P.map (fun ω => (Z ω, ε t α ω)) =
      (P.map Z).prod (volume.withDensity (f α)) := by
    rw [← hε.2.1 t α]
    exact (indepFun_iff_map_prod_eq_prod_map_map hZm.aemeasurable
      (hε.1 t α).aemeasurable).mp (past_indep_shock P f ε hε t Z hZ α)
  have hGi : Integrable G ((P.map Z).prod (volume.withDensity (f α))) :=
    Integrable.of_bound hG.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  rw [← integral_map (hZm.prodMk (hε.1 t α)).aemeasurable hG.aestronglyMeasurable,
    hmap, integral_prod _ hGi,
    integral_map hZm.aemeasurable hG.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable]


end StochFictPlay.SupermodularProof
end

/- Complete checked body: RunBasics -/
section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

noncomputable def choiceUpdate {p : ℕ} {n : Fin p → ℕ}
    (u : (α : Fin p) → Profile n → ℝ) (z : Mixed n × Mixed n) : Mixed n :=
  fun α => argmaxVec (payoffVec u z.1 α + z.2 α)

theorem measurable_choiceUpdate {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) : Measurable (choiceUpdate u) := by
  apply measurable_pi_lambda
  intro α
  have hfst : Measurable (fun z : Mixed n × Mixed n => z.1) := measurable_fst
  have hsnd : Measurable (fun z : Mixed n × Mixed n => z.2) := measurable_snd
  have hπ := ((measurable_pi_apply α).comp (continuous_payoffVec u).measurable).comp hfst
  have he := (measurable_pi_apply α).comp hsnd
  exact (measurable_argmaxVec (hn α)).comp (hπ.add he)

theorem sfpCum_measurable_past {Ω : Type*} {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) :
    Measurable[shockHistory ε t] (sfpCum u s₁ ε t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    cases t with
    | zero => exact measurable_const
    | succ t =>
      let : MeasurableSpace Ω := shockHistory ε (t+2)
      have hm : Measurable[shockHistory ε (t+2)] (sfpCum u s₁ ε (t+1)) :=
        ih.mono (shockHistory_mono ε (Nat.le_succ (t+1))) le_rfl
      have hx : Measurable[shockHistory ε (t+2)]
          (fun ω => (1/((t+1:ℕ):ℝ)) • sfpCum u s₁ ε (t+1) ω) := by
        have hc : Measurable[shockHistory ε (t+2)] (fun _ : Ω => (1/((t+1:ℕ):ℝ))) := measurable_const
        exact hc.smul hm
      have he : Measurable[shockHistory ε (t+2)]
          (fun ω α => ε (t+1) α ω) := measurable_pi_lambda _ (fun α =>
            measurable_shock_past ε (Nat.lt_succ_self (t+1)) α)
      have hpair := hx.prodMk he
      have hchoice := (measurable_choiceUpdate hn u).comp hpair
      have htotal := hm.add hchoice
      change Measurable[shockHistory ε (t+2)] (sfpCum u s₁ ε (t+2)) at htotal
      exact htotal

theorem sfpBelief_measurable_past {Ω : Type*} {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) :
    Measurable[shockHistory ε t] (sfpBelief u s₁ ε t) := by
  have hc : Measurable[shockHistory ε t] (fun _ : Ω => (1/(t:ℝ))) := measurable_const
  exact hc.smul (sfpCum_measurable_past hn u s₁ ε t)

theorem pureVec_simplex {p : ℕ} {n : Fin p → ℕ} (s : Profile n) (α : Fin p) :
    pureVec s α ∈ stdSimplex ℝ (Fin (n α)) := by
  classical
  constructor
  · intro i
    by_cases hi : i=s α <;> simp [pureVec,hi]
  · simp [pureVec]

theorem sfpCum_nonneg_sum {Ω : Type*} {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) (ω : Ω) (α : Fin p) :
    (∀ i, 0 ≤ sfpCum u s₁ ε t ω α i) ∧ ∑ i, sfpCum u s₁ ε t ω α i = (t:ℝ) := by
  induction t with
  | zero => simp [sfpCum]
  | succ t ih =>
    cases t with
    | zero => simpa only [sfpCum, stdSimplex, Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_zero,
        Nat.cast_one, zero_add] using pureVec_simplex s₁ α
    | succ t =>
      have ha := argmaxVec_simplex (hn α)
        (fun i => payoffVec u ((1/((t+1:ℕ):ℝ)) • sfpCum u s₁ ε (t+1) ω) α i + ε (t+1) α ω i)
      constructor
      · intro i
        exact add_nonneg (ih.1 i) (ha.1 i)
      · have hs : (∑ i, sfpChoice u ((1/((t+1:ℕ):ℝ)) • sfpCum u s₁ ε (t+1) ω)
            (ε (t+1)) ω α i) = 1 := ha.2
        simp only [sfpCum, Pi.add_apply, Finset.sum_add_distrib]
        rw [ih.2, hs]
        push_cast
        ring

theorem sfpCum_coordinate_bounds {Ω : Type*} {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) (ω : Ω)
    (α : Fin p) (i : Fin (n α)) :
    0 ≤ sfpCum u s₁ ε t ω α i ∧ sfpCum u s₁ ε t ω α i ≤ (t:ℝ) := by
  have h := sfpCum_nonneg_sum hn u s₁ ε t ω α
  refine ⟨h.1 i, ?_⟩
  rw [← h.2]
  exact Finset.single_le_sum (fun j _ => h.1 j) (Finset.mem_univ i)

theorem sfpBelief_mem_mixed {Ω : Type*} {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) (ht : 0 < t) (ω : Ω) :
    sfpBelief u s₁ ε t ω ∈ mixedProfiles n := by
  intro α
  have h := sfpCum_nonneg_sum hn u s₁ ε t ω α
  have htR : (t:ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  constructor
  · intro i
    exact mul_nonneg (by positivity) (h.1 i)
  · change (∑ i, (1/(t:ℝ))*sfpCum u s₁ ε t ω α i) = 1
    rw [← Finset.mul_sum, h.2]
    field_simp

noncomputable def responseSum {Ω : Type*} {p : ℕ} {n : Fin p → ℕ}
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞)
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) (ω : Ω) : Mixed n :=
  ∑ s ∈ Finset.range t, pbr f u (sfpBelief u s₁ ε s ω)

noncomputable def centeredCum {Ω : Type*} {p : ℕ} {n : Fin p → ℕ}
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞)
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) (ω : Ω) : Mixed n :=
  sfpCum u s₁ ε t ω - responseSum f u s₁ ε t ω

theorem centeredCum_measurable_past {Ω : Type*} {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) :
    Measurable[shockHistory ε t] (centeredCum f u s₁ ε t) := by
  apply (sfpCum_measurable_past hn u s₁ ε t).sub
  apply Finset.measurable_sum
  intro s hs
  have hst : s ≤ t := (Finset.mem_range.mp hs).le
  exact (continuous_pbr f hf u).measurable.comp
    ((sfpBelief_measurable_past hn u s₁ ε s).mono (shockHistory_mono ε hst) le_rfl)


end StochFictPlay.SupermodularProof
end

/- Complete checked body: CenteredChoice -/
section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

noncomputable def centeredChoice {k : ℕ} (f : (Fin k → ℝ) → ℝ≥0∞)
    (π e : Fin k → ℝ) (i : Fin k) : ℝ := argmaxVec (π+e) i-choiceProb f π i

theorem simplex_coordinate_bounds {k : ℕ} {x : Fin k → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin k)) (i : Fin k) : 0 ≤ x i ∧ x i ≤ 1 := by
  refine ⟨hx.1 i, ?_⟩
  rw [← hx.2]
  exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)

theorem centeredChoice_bound {k : ℕ} (hk : 0 < k) (f : (Fin k → ℝ) → ℝ≥0∞)
    (hf : IsRegularDensity f) (π e : Fin k → ℝ) (i : Fin k) :
    |centeredChoice f π e i| ≤ 1 := by
  have hx := simplex_coordinate_bounds (argmaxVec_simplex hk (π+e)) i
  have hy := simplex_coordinate_bounds (choiceProb_simplex hk f hf π) i
  unfold centeredChoice
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem centeredChoice_mean_zero {k : ℕ} (hk : 0 < k) (f : (Fin k → ℝ) → ℝ≥0∞)
    (hf : IsRegularDensity f) (π : Fin k → ℝ) (i : Fin k) :
    (∫ e, centeredChoice f π e i ∂volume.withDensity f) = 0 := by
  let : IsProbabilityMeasure (volume.withDensity f) := density_probability f hf
  unfold centeredChoice
  rw [integral_sub (argmax_integrable hk f hf π i) (integrable_const _),
    ← choiceProb_eq_integral]
  simp

theorem measurable_centeredChoice {k : ℕ} (hk : 0 < k) (f : (Fin k → ℝ) → ℝ≥0∞)
    (hf : IsRegularDensity f) (i : Fin k) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => centeredChoice f z.1 z.2 i) := by
  have ha := ((measurable_pi_apply i).comp (measurable_argmaxVec hk)).comp
    (measurable_fst.add measurable_snd)
  have hfst : Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => z.1) := measurable_fst
  have hb := ((measurable_pi_apply i).comp hf.2.2.2.2.continuous.measurable).comp hfst
  exact ha.sub hb

theorem past_centered_product_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : IsShockFamily P f ε)
    (t : ℕ) (α : Fin p) (i : Fin (n α)) (π : Ω → (Fin (n α) → ℝ)) (r : Ω → ℝ)
    (hπ : Measurable[shockHistory ε t] π) (hr : Measurable[shockHistory ε t] r)
    (C : ℝ) (hC : 0 ≤ C) (hrC : ∀ ω, |r ω| ≤ C) :
    (∫ ω, r ω * centeredChoice (f α) (π ω) (ε t α ω) i ∂P) = 0 := by
  let clip : ℝ → ℝ := fun x => max (-C) (min C x)
  have hc : ∀ x, ‖clip x‖ ≤ C := by
    intro x
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have heq : ∀ ω, clip (r ω) = r ω := by
    intro ω
    have h := abs_le.mp (hrC ω)
    dsimp [clip]
    rw [min_eq_right h.2, max_eq_right h.1]
  let G : ((Fin (n α) → ℝ) × ℝ) × (Fin (n α) → ℝ) → ℝ :=
    fun z => clip z.1.2 * centeredChoice (f α) z.1.1 z.2 i
  have hg : Measurable G := by
    have hc' : Measurable (fun z : ((Fin (n α) → ℝ) × ℝ) × (Fin (n α) → ℝ) => clip z.1.2) := by
      dsimp [clip]
      fun_prop
    exact hc'.mul ((measurable_centeredChoice (hn α) (f α) (hf α) i).comp
      (measurable_fst.fst.prodMk measurable_snd))
  have hb : ∀ z, ‖G z‖ ≤ C := by
    intro z
    change ‖clip z.1.2 * centeredChoice (f α) z.1.1 z.2 i‖ ≤ C
    rw [norm_mul]
    calc
      _ ≤ ‖clip z.1.2‖ * 1 := mul_le_mul_of_nonneg_left
        (centeredChoice_bound (hn α) (f α) (hf α) z.1.1 z.2 i) (norm_nonneg _)
      _ ≤ C := by simpa only [mul_one] using hc z.1.2
  have ht := integral_past_shock P f hf ε hε t (fun ω => (π ω,r ω)) (hπ.prodMk hr) α G hg C hb
  have hz : ∀ z, (∫ e, G (z,e) ∂volume.withDensity (f α)) = 0 := by
    intro z
    dsimp [G]
    rw [integral_const_mul, centeredChoice_mean_zero (hn α) (f α) (hf α), mul_zero]
  simp_rw [hz, integral_zero] at ht
  calc
    _ = ∫ ω, G ((π ω,r ω),ε t α ω) ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by dsimp [G]; rw [heq])
    _ = 0 := ht


end StochFictPlay.SupermodularProof
end

/- Complete checked body: BoundedMoments -/
section

open MeasureTheory

namespace StochFictPlay.SupermodularProof

theorem bounded_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Ω → ℝ) (hS : Measurable S) (C : ℝ)
    (hC : ∀ ω, |S ω| ≤ C) : Integrable S P :=
  Integrable.of_bound hS.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem bounded_sq_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Ω → ℝ) (hS : Measurable S) (C : ℝ)
    (hC : ∀ ω, |S ω| ≤ C) : Integrable (fun ω => (S ω)^2) P := by
  apply bounded_integrable P _ (hS.pow_const 2) (C^2)
  intro ω
  rw [abs_of_nonneg (sq_nonneg _)]
  have h := hC ω
  nlinarith [sq_abs (S ω), abs_nonneg (S ω)]

theorem bounded_integral_sq_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Ω → ℝ) (hS : Measurable S) (C : ℝ)
    (hC : ∀ ω, |S ω| ≤ C) : (∫ ω, (S ω)^2 ∂P) ≤ C^2 := by
  calc
    _ ≤ ∫ _ω : Ω, C^2 ∂P := integral_mono (bounded_sq_integrable P S hS C hC)
      (integrable_const _) (fun ω => by
        have h := hC ω
        nlinarith [sq_abs (S ω), abs_nonneg (S ω)])
    _ = _ := by simp

theorem mean_square_add_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S D : Ω → ℝ) (hS : Measurable S) (hD : Measurable D)
    (C : ℝ) (hC : 0 ≤ C) (hSbound : ∀ ω, |S ω| ≤ C) (hDbound : ∀ ω, |D ω| ≤ 1)
    (hzero : (∫ ω, S ω*D ω ∂P) = 0) :
    (∫ ω, (S ω+D ω)^2 ∂P) ≤ (∫ ω, (S ω)^2 ∂P)+1 := by
  have hprod : Integrable (fun ω => S ω*D ω) P := by
    apply bounded_integrable P _ (hS.mul hD) C
    intro ω
    change |S ω*D ω| ≤ C
    rw [abs_mul]
    calc
      _ ≤ C*1 := mul_le_mul (hSbound ω) (hDbound ω) (abs_nonneg _) hC
      _ = C := mul_one _
  have hsqS := bounded_sq_integrable P S hS C hSbound
  have hsqD := bounded_sq_integrable P D hD 1 hDbound
  have he : (fun ω => (S ω+D ω)^2) = fun ω => (S ω)^2 + 2*(S ω*D ω)+(D ω)^2 := by
    funext ω; ring
  have hsum : Integrable (fun ω => (S ω)^2+2*(S ω*D ω)) P := hsqS.add (hprod.const_mul 2)
  have he1 : (∫ ω, (S ω)^2+2*(S ω*D ω)+(D ω)^2 ∂P) =
      (∫ ω, (S ω)^2+2*(S ω*D ω) ∂P)+(∫ ω, (D ω)^2 ∂P) := integral_add hsum hsqD
  have he2 : (∫ ω, (S ω)^2+2*(S ω*D ω) ∂P) =
      (∫ ω, (S ω)^2 ∂P)+(∫ ω, 2*(S ω*D ω) ∂P) := integral_add hsqS (hprod.const_mul 2)
  rw [he, he1, he2, integral_const_mul, hzero]
  have hd := bounded_integral_sq_le P D hD 1 hDbound
  norm_num at hd ⊢
  linarith


end StochFictPlay.SupermodularProof
end

/- Complete checked body: SquareStrongLaw -/
section

open scoped ENNReal Topology
open MeasureTheory Filter

namespace StochFictPlay.SupermodularProof

theorem ae_summable_of_integral_norm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Integrable (F n) P)
    (hs : Summable (fun n => ∫ ω, ‖F n ω‖ ∂P)) :
    ∀ᵐ ω ∂P, Summable (fun n => ‖F n ω‖) := by
  have he : ∀ n, ∫⁻ ω, ‖F n ω‖ₑ ∂P = ‖∫ ω, ‖F n ω‖ ∂P‖ₑ := by
    intro n
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF n).norm, ENNReal.coe_nnreal_eq, coe_nnnorm]
    change ENNReal.ofReal (∫ ω, |F n ω| ∂P) = ENNReal.ofReal |∫ ω, |F n ω| ∂P|
    rw [abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg (F n ω))) ]
  have ht : ∑' n, ∫⁻ ω, ‖F n ω‖ₑ ∂P ≠ ∞ := by
    simp_rw [he]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  have hm : ∀ n, AEMeasurable (fun ω => ‖F n ω‖ₑ) P := fun n => (hF n).1.enorm
  rw [← lintegral_tsum hm] at ht
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) ht] with ω hω
  change Summable (fun n => (‖F n ω‖₊ : ℝ))
  rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
  exact hω.ne

def squareTimes (k : ℕ) : ℕ := (k+1)^2

theorem squareTimes_pos (k : ℕ) : 0 < squareTimes k := by unfold squareTimes; positivity

theorem squareTimes_tendsto : Tendsto squareTimes atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop N] with k hk
  unfold squareTimes
  nlinarith

theorem squareTimes_ratio (a : ℝ) (ha : 1 < a) :
    ∀ᶠ k : ℕ in atTop, (squareTimes (k+1):ℝ) ≤ a * squareTimes k := by
  obtain ⟨N,hN⟩ := exists_nat_ge (3/(a-1))
  filter_upwards [eventually_ge_atTop N] with k hk
  have hkr : (N:ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 < a-1 := by linarith
  have hb : 3 ≤ ((k:ℝ)+1)*(a-1) := (div_le_iff₀ hp).mp (by linarith)
  have hm := mul_le_mul_of_nonneg_right hb (show 0 ≤ (k:ℝ)+1 by positivity)
  simp only [squareTimes, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem tendsto_average_of_square_subsequence (S : ℕ → ℝ)
    (hstep : ∀ k, |S (k+1)-S k| ≤ 1)
    (hs : Tendsto (fun k => S (squareTimes k)/(squareTimes k:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun t => S t/(t:ℝ)) atTop (𝓝 0) := by
  let u : ℕ → ℝ := fun t => S t+t
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro t
    have hl := (abs_le.mp (hstep t)).1
    dsimp [u]
    push_cast
    linarith
  have hsub : Tendsto (fun k => u (squareTimes k)/(squareTimes k:ℝ)) atTop (𝓝 1) := by
    have he : ∀ k, u (squareTimes k)/(squareTimes k:ℝ) =
        S (squareTimes k)/(squareTimes k:ℝ)+1 := by
      intro k
      have hn : (squareTimes k:ℝ) ≠ 0 := by exact_mod_cast (squareTimes_pos k).ne'
      simp [u, add_div, hn]
    simp_rw [he]
    simpa using hs.add_const 1
  have hall : Tendsto (fun t => u t/(t:ℝ)) atTop (𝓝 1) :=
    tendsto_div_of_monotone_of_exists_subseq_tendsto_div u 1 hu
      (fun a ha => ⟨squareTimes, squareTimes_ratio a ha, squareTimes_tendsto, hsub⟩)
  have hz : Tendsto (fun t => u t/(t:ℝ)-1) atTop (𝓝 0) := by
    simpa using hall.sub_const 1
  apply hz.congr'
  filter_upwards [eventually_ge_atTop 1] with t ht
  have htR : (t:ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  simp [u, add_div, htR]

theorem ae_average_tendsto_zero_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : ℕ → Ω → ℝ)
    (hint : ∀ t, Integrable (fun ω => (S t ω)^2) P)
    (hsecond : ∀ t, ∫ ω, (S t ω)^2 ∂P ≤ (t:ℝ))
    (hstep : ∀ t ω, |S (t+1) ω-S t ω| ≤ 1) :
    ∀ᵐ ω ∂P, Tendsto (fun t => S t ω/(t:ℝ)) atTop (𝓝 0) := by
  let F : ℕ → Ω → ℝ := fun k ω => (S (squareTimes k) ω/(squareTimes k:ℝ))^2
  have hF : ∀ k, Integrable (F k) P := by
    intro k
    simpa only [F, div_pow] using (hint (squareTimes k)).div_const ((squareTimes k:ℝ)^2)
  have hb : ∀ k, ∫ ω, ‖F k ω‖ ∂P ≤ 1/((k:ℝ)+1)^2 := by
    intro k
    have hn : 0 < (squareTimes k:ℝ) := by exact_mod_cast squareTimes_pos k
    have hnorm : (fun ω => ‖F k ω‖) = fun ω => (S (squareTimes k) ω)^2/(squareTimes k:ℝ)^2 := by
      funext ω
      change |(S (squareTimes k) ω/(squareTimes k:ℝ))^2| = _
      rw [abs_of_nonneg (sq_nonneg _), div_pow]
    rw [hnorm, integral_div]
    calc
      _ ≤ (squareTimes k:ℝ)/(squareTimes k:ℝ)^2 :=
        div_le_div_of_nonneg_right (hsecond _) (sq_nonneg _)
      _ = _ := by simp only [squareTimes, Nat.cast_pow, Nat.cast_add, Nat.cast_one]; field_simp
  have hs : Summable (fun k : ℕ => 1/((k:ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ)))
  have hsF : Summable (fun k => ∫ ω, ‖F k ω‖ ∂P) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg (fun ω => norm_nonneg _)) hb hs
  filter_upwards [ae_summable_of_integral_norm F hF hsF] with ω hω
  apply tendsto_average_of_square_subsequence (fun t => S t ω) (fun t => hstep t ω)
  have hz := hω.tendsto_atTop_zero
  have he : (fun k => ‖F k ω‖) = fun k => (S (squareTimes k) ω/(squareTimes k:ℝ))^2 := by
    funext k
    exact Real.norm_of_nonneg (sq_nonneg _)
  rw [he] at hz
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hz


end StochFictPlay.SupermodularProof
end

/- Complete checked body: RunDeviation -/
section

open scoped BigOperators ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open StochFictPlay.Supermodular

namespace StochFictPlay.SupermodularProof

theorem responseSum_coordinate_bounds {Ω : Type*} {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) (ω : Ω)
    (α : Fin p) (i : Fin (n α)) :
    0 ≤ responseSum f u s₁ ε t ω α i ∧ responseSum f u s₁ ε t ω α i ≤ (t:ℝ) := by
  have hb : ∀ s, 0 ≤ pbr f u (sfpBelief u s₁ ε s ω) α i ∧
      pbr f u (sfpBelief u s₁ ε s ω) α i ≤ 1 :=
    fun s => simplex_coordinate_bounds (pbr_mem_mixed hn f hf u _ α) i
  simp only [responseSum, Finset.sum_apply]
  constructor
  · exact Finset.sum_nonneg (fun s _ => (hb s).1)
  · calc
      _ ≤ ∑ _s ∈ Finset.range t, (1:ℝ) := Finset.sum_le_sum (fun s _ => (hb s).2)
      _ = t := by simp

theorem centeredCum_bound {Ω : Type*} {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) (ω : Ω)
    (α : Fin p) (i : Fin (n α)) : |centeredCum f u s₁ ε t ω α i| ≤ (t:ℝ) := by
  have hc := sfpCum_coordinate_bounds hn u s₁ ε t ω α i
  have hr := responseSum_coordinate_bounds hn f hf u s₁ ε t ω α i
  change |sfpCum u s₁ ε t ω α i-responseSum f u s₁ ε t ω α i| ≤ _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem centeredCum_step {Ω : Type*} {p : ℕ} {n : Fin p → ℕ}
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞)
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) (ht : 0 < t) (ω : Ω)
    (α : Fin p) (i : Fin (n α)) :
    centeredCum f u s₁ ε (t+1) ω α i = centeredCum f u s₁ ε t ω α i +
      centeredChoice (f α) (payoffVec u (sfpBelief u s₁ ε t ω) α) (ε t α ω) i := by
  cases t with
  | zero => omega
  | succ t =>
    simp only [centeredCum, responseSum, Finset.sum_range_succ, sfpCum, sfpChoice,
      centeredChoice, sfpBelief, pbr, Pi.add_def, Pi.sub_apply, Finset.sum_apply]
    ring

theorem centeredCum_increment_bound {Ω : Type*} {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) (ω : Ω)
    (α : Fin p) (i : Fin (n α)) :
    |centeredCum f u s₁ ε (t+1) ω α i-centeredCum f u s₁ ε t ω α i| ≤ 1 := by
  cases t with
  | zero =>
    have hb := centeredCum_bound hn f hf u s₁ ε 1 ω α i
    simpa [centeredCum, responseSum, sfpCum] using hb
  | succ t =>
    rw [centeredCum_step f u s₁ ε (t+1) (by omega)]
    simpa using centeredChoice_bound (hn α) (f α) (hf α)
      (payoffVec u (sfpBelief u s₁ ε (t+1) ω) α) (ε (t+1) α ω) i

theorem centeredCum_second_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : IsShockFamily P f ε)
    (α : Fin p) (i : Fin (n α)) (t : ℕ) :
    (∫ ω, (centeredCum f u s₁ ε t ω α i)^2 ∂P) ≤ (t:ℝ) := by
  let M : ℕ → Ω → ℝ := fun t ω => centeredCum f u s₁ ε t ω α i
  have hM : ∀ t, Measurable[shockHistory ε t] (M t) := fun t =>
    (measurable_pi_apply i).comp ((measurable_pi_apply α).comp
      (centeredCum_measurable_past hn f hf u s₁ ε t))
  have hMm : ∀ t, Measurable (M t) := fun t => (hM t).mono (shockHistory_le ε hε.1 t) le_rfl
  have hMb : ∀ t ω, |M t ω| ≤ (t:ℝ) := fun t ω => centeredCum_bound hn f hf u s₁ ε t ω α i
  change (∫ ω, (M t ω)^2 ∂P) ≤ _
  induction t with
  | zero => simp [M,centeredCum,responseSum,sfpCum]
  | succ t ih =>
    by_cases ht : t=0
    · subst t
      simpa using bounded_integral_sq_le P (M 1) (hMm 1) 1 (by simpa only [Nat.cast_one] using hMb 1)
    · have htpos : 0 < t := Nat.pos_of_ne_zero ht
      let π : Ω → (Fin (n α) → ℝ) := fun ω => payoffVec u (sfpBelief u s₁ ε t ω) α
      let D : Ω → ℝ := fun ω => centeredChoice (f α) (π ω) (ε t α ω) i
      have hπ : Measurable[shockHistory ε t] π :=
        ((measurable_pi_apply α).comp (continuous_payoffVec u).measurable).comp
          (sfpBelief_measurable_past hn u s₁ ε t)
      have hπm : Measurable π := hπ.mono (shockHistory_le ε hε.1 t) le_rfl
      have hD : Measurable D := (measurable_centeredChoice (hn α) (f α) (hf α) i).comp
        (hπm.prodMk (hε.1 t α))
      have hDb : ∀ ω, |D ω| ≤ 1 := fun ω =>
        centeredChoice_bound (hn α) (f α) (hf α) (π ω) (ε t α ω) i
      have hzero : (∫ ω, M t ω*D ω ∂P)=0 :=
        past_centered_product_zero P hn f hf ε hε t α i π (M t) hπ (hM t) t
          (by positivity) (hMb t)
      have he : M (t+1) = fun ω => M t ω+D ω := by
        funext ω
        exact centeredCum_step f u s₁ ε t htpos ω α i
      rw [he]
      calc
        _ ≤ (∫ ω, (M t ω)^2 ∂P)+1 :=
          mean_square_add_le P (M t) D (hMm t) hD t (by positivity) (hMb t) hDb hzero
        _ ≤ ((t+1:ℕ):ℝ) := by push_cast; linarith

theorem sfp_centered_average_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p : ℕ} {n : Fin p → ℕ} (hn : ∀ α, 1 ≤ n α)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : IsShockFamily P f ε) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℕ => sfpBelief u s₁ ε t ω -
      (1/(t:ℝ)) • ∑ s ∈ Finset.range t, pbr f u (sfpBelief u s₁ ε s ω)) atTop (𝓝 0) := by
  have ha : ∀ᵐ ω ∂P, ∀ α : Fin p, ∀ i : Fin (n α),
      Tendsto (fun t => centeredCum f u s₁ ε t ω α i/(t:ℝ)) atTop (𝓝 0) := by
    simp only [ae_all_iff]
    intro α i
    apply ae_average_tendsto_zero_of_second_moment P
      (fun t ω => centeredCum f u s₁ ε t ω α i)
    · intro t
      have hm := ((measurable_pi_apply i).comp ((measurable_pi_apply α).comp
        (centeredCum_measurable_past hn f hf u s₁ ε t))).mono (shockHistory_le ε hε.1 t) le_rfl
      exact bounded_sq_integrable P _ hm t (fun ω => centeredCum_bound hn f hf u s₁ ε t ω α i)
    · exact centeredCum_second_moment P hn f hf u s₁ ε hε α i
    · exact fun t ω => centeredCum_increment_bound hn f hf u s₁ ε t ω α i
  filter_upwards [ha] with ω hω
  apply tendsto_pi_nhds.2
  intro α
  apply tendsto_pi_nhds.2
  intro i
  convert hω α i using 1
  · funext t
    simp only [sfpBelief, centeredCum, responseSum, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    ring
  · rfl


end StochFictPlay.SupermodularProof
end

/- Complete checked body: FictitiousRoot -/
section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- Theorem 6.1(iv), unique rest point clause (Hofbauer–Sandholm 2002, manuscript p. 24). Let `G`
be a strictly supermodular game with `p ≥ 2` players, and let each player's shock density `f α`
meet the conditions of Theorem 2.1. If the perturbed best response dynamic `(P)` has exactly one
rest point `x*` in `Σ`, then standard stochastic fictitious play converges to `x*` almost
surely: on every probability space, for every family of shocks `ε_t^α` with densities `f α`,
independent over time and across players, and every initial pure profile, the beliefs
`Z_t = (1/t) ∑_{u ≤ t} ζ_u` satisfy `P(lim_{t→∞} Z_t = x*) = 1`. -/
theorem sfp_tendsto_unique_rest_point_ae {p : ℕ} (n : Fin p → ℕ) (_hp : 2 ≤ p)
    (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (xs : Mixed n) (hRP : restPoints (pField f u) (mixedProfiles n) = {xs})
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : IsShockFamily P f ε)
    (s₁ : Profile n) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℕ => sfpBelief u s₁ ε t ω) atTop (𝓝 xs) := by
  filter_upwards [StochFictPlay.SupermodularProof.sfp_centered_average_ae P hn f hf u s₁ ε hε]
    with ω hω
  apply StochFictPlay.SupermodularProof.mixed_converges_of_noise hn f hf u hu xs hRP
    (fun t => sfpBelief u s₁ ε t ω)
  · simp [sfpBelief, sfpCum]
  · intro t ht
    exact StochFictPlay.SupermodularProof.sfpBelief_mem_mixed hn u s₁ ε t ht ω
  · simpa only [StochFictPlay.SupermodularProof.vectorAverage, one_div] using hω

end StochFictPlay.Supermodular

end

open StochFictPlay StochFictPlay.Supermodular
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal


theorem solution {p : ℕ} (n : Fin p → ℕ) (hp : 2 ≤ p)
    (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (xs : Mixed n) (hRP : restPoints (pField f u) (mixedProfiles n) = {xs})
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (hε : IsShockFamily P f ε)
    (s₁ : Profile n) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℕ => sfpBelief u s₁ ε t ω) atTop (𝓝 xs) := by
  exact StochFictPlay.Supermodular.sfp_tendsto_unique_rest_point_ae n hp hn u hu f hf xs hRP P ε hε s₁

#print axioms StochFictPlay.Supermodular.sfp_tendsto_unique_rest_point_ae
#print axioms solution

-- Prove2me | solution 1 for SupportVectorMachines.Regression.theorem_A_8_3_kahane_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:13:04.36061+00:00
-- url     : https://prove2.me/submissions/8e4b979b-c1fa-41ba-9ab6-780adc5a6f4d

import Mathlib
import Definitions.Def_SupportVectorMachines_Regression_IsRademacherSequence

open MeasureTheory ProbabilityTheory

namespace SupportVectorMachines.Regression


lemma aux_kh_even_sum (h : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m + 1), (if Even j then h (j / 2) else 0) =
      ∑ k ∈ Finset.range (m + 1), h k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => h k) (m + 1)]
    have h1 : ¬ Even (2 * m + 1) := by simp [Nat.even_add_one]
    have h2 : Even (2 * m + 1 + 1) := by simp [Nat.even_add_one]
    have h3 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    simp [h1, h2, h3]

lemma aux_kh_two_point (m : ℕ) (hm : 1 ≤ m) (a b : ℝ) :
    (a + b / (2 * m)) ^ (2 * m) + (a - b / (2 * m)) ^ (2 * m) ≤ 2 * (a ^ 2 + b ^ 2) ^ m := by
  set c := b / (2 * m) with hc
  have hm0 : (0 : ℝ) < 2 * m := by positivity
  have e1 : (a + c) ^ (2 * m) + (a - c) ^ (2 * m) =
      ∑ j ∈ Finset.range (2 * m + 1), (c ^ j + (-c) ^ j) * a ^ (2 * m - j) *
        ((2 * m).choose j : ℝ) := by
    rw [add_comm a c, sub_eq_neg_add, add_pow, add_pow, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  have e2 : 2 * (a ^ 2 + b ^ 2) ^ m =
      ∑ j ∈ Finset.range (2 * m + 1), (if Even j then
        2 * ((b ^ 2) ^ (j / 2) * (a ^ 2) ^ (m - j / 2) * (m.choose (j / 2) : ℝ)) else 0) := by
    rw [aux_kh_even_sum (fun k => 2 * ((b ^ 2) ^ k * (a ^ 2) ^ (m - k) * (m.choose k : ℝ))),
      ← Finset.mul_sum, add_comm (a ^ 2), add_pow]
  rw [e1, e2]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have hjle : j ≤ 2 * m := by simpa [Nat.lt_succ_iff] using hj
  split_ifs with hev
  · obtain ⟨k, rfl⟩ := hev
    have hk2 : (k + k) / 2 = k := by omega
    rw [hk2]
    have hkm : k ≤ m := by omega
    have hpow : c ^ (k + k) + (-c) ^ (k + k) = 2 * (b ^ 2) ^ k / ((2 * m : ℝ) ^ 2) ^ k := by
      rw [show k + k = 2 * k by ring, pow_mul, pow_mul, neg_sq, hc, div_pow, div_pow]
      ring
    have ha : a ^ (2 * m - (k + k)) = (a ^ 2) ^ (m - k) := by
      rw [← pow_mul]; congr 1; omega
    rw [hpow, ha]
    have hch : ((2 * m).choose (k + k) : ℝ) ≤ ((2 * m : ℝ) ^ 2) ^ k := by
      have := Nat.choose_le_pow (2 * m) (k + k)
      calc ((2 * m).choose (k + k) : ℝ) ≤ ((2 * m : ℕ) : ℝ) ^ (k + k) := by exact_mod_cast this
        _ = ((2 * m : ℝ) ^ 2) ^ k := by push_cast; rw [← pow_mul]; ring_nf
    have hch2 : (1 : ℝ) ≤ (m.choose k : ℝ) := by
      exact_mod_cast Nat.choose_pos hkm
    have hB : 0 ≤ (b ^ 2) ^ k := by positivity
    have hA : 0 ≤ (a ^ 2) ^ (m - k) := by positivity
    have hD : 0 < ((2 * m : ℝ) ^ 2) ^ k := by positivity
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hD]
    have : 2 * (b ^ 2) ^ k * (a ^ 2) ^ (m - k) * ((2 * m).choose (k + k) : ℝ) ≤
        2 * (b ^ 2) ^ k * (a ^ 2) ^ (m - k) * ((2 * m : ℝ) ^ 2) ^ k :=
      mul_le_mul_of_nonneg_left hch (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hB hA) hD.le]
  · have hodd : Odd j := Nat.not_even_iff_odd.mp hev
    rw [hodd.neg_pow]
    simp

lemma aux_kh_vec_two_point {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (hm : 1 ≤ m) (u x : E) :
    ‖u + (1 / (2 * m : ℝ)) • x‖ ^ (2 * m) + ‖u - (1 / (2 * m : ℝ)) • x‖ ^ (2 * m) ≤
      2 * ((‖u + x‖ ^ 2 + ‖u - x‖ ^ 2) / 2) ^ m := by
  set ρ : ℝ := 1 / (2 * m : ℝ) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set P := ‖u + x‖
  set Q := ‖u - x‖
  have hP : 0 ≤ P := norm_nonneg _
  have hQ : 0 ≤ Q := norm_nonneg _
  have h1 : ‖u + ρ • x‖ ≤ ((1 + ρ) / 2) * P + ((1 - ρ) / 2) * Q := by
    have : u + ρ • x = ((1 + ρ) / 2) • (u + x) + ((1 - ρ) / 2) • (u - x) := by
      simp only [smul_add, smul_sub]; module
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
      Real.norm_of_nonneg (by linarith)]
  have h2 : ‖u - ρ • x‖ ≤ ((1 - ρ) / 2) * P + ((1 + ρ) / 2) * Q := by
    have : u - ρ • x = ((1 - ρ) / 2) • (u + x) + ((1 + ρ) / 2) • (u - x) := by
      simp only [smul_add, smul_sub]; module
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
      Real.norm_of_nonneg (by linarith)]
  have key := aux_kh_two_point m hm ((P + Q) / 2) ((P - Q) / 2)
  have e1 : (P + Q) / 2 + (P - Q) / 2 / (2 * m) = ((1 + ρ) / 2) * P + ((1 - ρ) / 2) * Q := by
    rw [hρ]; ring
  have e2 : (P + Q) / 2 - (P - Q) / 2 / (2 * m) = ((1 - ρ) / 2) * P + ((1 + ρ) / 2) * Q := by
    rw [hρ]; ring
  have e3 : ((P + Q) / 2) ^ 2 + ((P - Q) / 2) ^ 2 = (P ^ 2 + Q ^ 2) / 2 := by ring
  rw [e1, e2, e3] at key
  refine le_trans (add_le_add ?_ ?_) key
  · exact pow_le_pow_left₀ (norm_nonneg _) h1 _
  · exact pow_le_pow_left₀ (norm_nonneg _) h2 _



lemma aux_kh_mink2 (m : ℕ) (hm : 1 ≤ m) {A B a b G g : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hG : 0 ≤ G) (hg : 0 ≤ g)
    (h1 : A ^ m + B ^ m ≤ 2 * G ^ m) (h2 : a ^ m + b ^ m ≤ 2 * g ^ m) :
    (A + a) ^ m + (B + b) ^ m ≤ 2 * (G + g) ^ m := by
  have hm0 : m ≠ 0 := by omega
  have hp : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hL := Real.Lp_add_le (Finset.univ : Finset (Fin 2)) ![A, B] ![a, b] hp
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    abs_of_nonneg hA, abs_of_nonneg hB, abs_of_nonneg ha, abs_of_nonneg hb, Pi.add_apply,
    abs_of_nonneg (add_nonneg hA ha), abs_of_nonneg (add_nonneg hB hb), Real.rpow_natCast,
    one_div] at hL
  have hmono : ∀ {X Y W : ℝ}, 0 ≤ X → 0 ≤ Y → 0 ≤ W → X ^ m + Y ^ m ≤ 2 * W ^ m →
      (X ^ m + Y ^ m) ^ ((m : ℝ)⁻¹) ≤ (2 : ℝ) ^ ((m : ℝ)⁻¹) * W := by
    intro X Y W hX hY hW h
    calc (X ^ m + Y ^ m) ^ ((m : ℝ)⁻¹) ≤ (2 * W ^ m) ^ ((m : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) h (by positivity)
      _ = (2 : ℝ) ^ ((m : ℝ)⁻¹) * W := by
          rw [Real.mul_rpow (by norm_num) (by positivity), Real.pow_rpow_inv_natCast hW hm0]
  have h3 := hL.trans (add_le_add (hmono hA hB hG h1) (hmono ha hb hg h2))
  rw [← mul_add] at h3
  have h4 := pow_le_pow_left₀ (by positivity) h3 m
  rw [Real.rpow_inv_natCast_pow (by positivity) hm0, mul_pow,
    Real.rpow_inv_natCast_pow (by norm_num) hm0] at h4
  exact h4

lemma aux_kh_mink (m : ℕ) (hm : 1 ≤ m) {ι : Type*} (s : Finset ι) (h₁ h₂ g : ι → ℝ)
    (hh₁ : ∀ i, 0 ≤ h₁ i) (hh₂ : ∀ i, 0 ≤ h₂ i) (hg : ∀ i, 0 ≤ g i)
    (h : ∀ i, h₁ i ^ m + h₂ i ^ m ≤ 2 * g i ^ m) :
    (∑ i ∈ s, h₁ i) ^ m + (∑ i ∈ s, h₂ i) ^ m ≤ 2 * (∑ i ∈ s, g i) ^ m := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hm0 : m ≠ 0 := by omega
    simp [zero_pow hm0]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    exact aux_kh_mink2 m hm (hh₁ i) (hh₂ i) (Finset.sum_nonneg fun j _ => hh₁ j)
      (Finset.sum_nonneg fun j _ => hh₂ j) (hg i) (Finset.sum_nonneg fun j _ => hg j) (h i) ih

/-- The sign attached to a boolean. -/
def aux_kh_sg (β : Bool) : ℝ := if β then 1 else -1

lemma aux_kh_sum_cons {n : ℕ} (F : (Fin (n + 1) → Bool) → ℝ) :
    ∑ b, F b = ∑ β : Bool, ∑ b' : Fin n → Bool, F (Fin.cons β b') := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma aux_kh_hyper (m : ℕ) (hm : 1 ≤ m) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ (n : ℕ) (y : E) (x : Fin n → E),
      (∑ b : Fin n → Bool, ‖y + (1 / (2 * m : ℝ)) • ∑ i, aux_kh_sg (b i) • x i‖ ^ (2 * m)) /
          2 ^ n ≤
        ((∑ b : Fin n → Bool, ‖y + ∑ i, aux_kh_sg (b i) • x i‖ ^ 2) / 2 ^ n) ^ m := by
  set ρ : ℝ := 1 / (2 * m : ℝ) with hρ
  intro n
  induction n with
  | zero =>
    intro y x
    simp [pow_mul]
  | succ n ih =>
    intro y x
    rw [aux_kh_sum_cons, aux_kh_sum_cons]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fintype.sum_bool, aux_kh_sg,
      if_true, Bool.false_eq_true, if_false, one_smul, neg_smul]
    set T : (Fin n → Bool) → E := fun b' => ∑ i : Fin n, aux_kh_sg (b' i) • x i.succ with hT
    have hT' : ∀ b' : Fin n → Bool,
        ∑ i : Fin n, (if b' i = true then (1 : ℝ) else -1) • x i.succ = T b' := by
      intro b'; rfl
    simp only [hT']
    have ihp : (∑ b' : Fin n → Bool, ‖(y + ρ • x 0) + ρ • T b'‖ ^ (2 * m)) / 2 ^ n ≤
        ((∑ b' : Fin n → Bool, ‖(y + ρ • x 0) + T b'‖ ^ 2) / 2 ^ n) ^ m :=
      ih (y + ρ • x 0) (fun i => x i.succ)
    have ihm : (∑ b' : Fin n → Bool, ‖(y - ρ • x 0) + ρ • T b'‖ ^ (2 * m)) / 2 ^ n ≤
        ((∑ b' : Fin n → Bool, ‖(y - ρ • x 0) + T b'‖ ^ 2) / 2 ^ n) ^ m :=
      ih (y - ρ • x 0) (fun i => x i.succ)
    have hmink := aux_kh_mink m hm Finset.univ
      (fun b' => ‖(y + T b') + ρ • x 0‖ ^ 2) (fun b' => ‖(y + T b') - ρ • x 0‖ ^ 2)
      (fun b' => (‖(y + T b') + x 0‖ ^ 2 + ‖(y + T b') - x 0‖ ^ 2) / 2)
      (fun _ => by positivity) (fun _ => by positivity) (fun _ => by positivity)
      (fun b' => by
        have := aux_kh_vec_two_point m hm (y + T b') (x 0)
        simp only [← pow_mul]
        exact this)
    have ep : ∀ b', y + ρ • (x 0 + T b') = (y + ρ • x 0) + ρ • T b' := by
      intro b'; rw [smul_add]; abel
    have em : ∀ b', y + ρ • (-x 0 + T b') = (y - ρ • x 0) + ρ • T b' := by
      intro b'; rw [smul_add, smul_neg]; abel
    have fp : ∀ b', (y + ρ • x 0) + T b' = (y + T b') + ρ • x 0 := by intro b'; abel
    have fm : ∀ b', (y - ρ • x 0) + T b' = (y + T b') - ρ • x 0 := by intro b'; abel
    have gp : ∀ b', y + (x 0 + T b') = (y + T b') + x 0 := by intro b'; abel
    have gm : ∀ b', y + (-x 0 + T b') = (y + T b') - x 0 := by intro b'; abel
    simp only [ep, em, gp, gm]
    simp only [fp, fm] at ihp ihm
    set Lp := ∑ b' : Fin n → Bool, ‖y + ρ • x 0 + ρ • T b'‖ ^ (2 * m)
    set Lm := ∑ b' : Fin n → Bool, ‖y - ρ • x 0 + ρ • T b'‖ ^ (2 * m)
    set Hp := ∑ b' : Fin n → Bool, ‖(y + T b') + ρ • x 0‖ ^ 2
    set Hm := ∑ b' : Fin n → Bool, ‖(y + T b') - ρ • x 0‖ ^ 2
    set Gp := ∑ b' : Fin n → Bool, ‖(y + T b') + x 0‖ ^ 2
    set Gm := ∑ b' : Fin n → Bool, ‖(y + T b') - x 0‖ ^ 2
    have hG : ∑ b' : Fin n → Bool, (‖(y + T b') + x 0‖ ^ 2 + ‖(y + T b') - x 0‖ ^ 2) / 2 =
        (Gp + Gm) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [hG] at hmink
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hHp : 0 ≤ Hp := Finset.sum_nonneg fun _ _ => by positivity
    have hHm : 0 ≤ Hm := Finset.sum_nonneg fun _ _ => by positivity
    calc (Lp + Lm) / 2 ^ (n + 1) = (Lp / 2 ^ n + Lm / 2 ^ n) / 2 := by
          rw [pow_succ]; field_simp
      _ ≤ ((Hp / 2 ^ n) ^ m + (Hm / 2 ^ n) ^ m) / 2 := by gcongr
      _ = (Hp ^ m + Hm ^ m) / (2 * (2 ^ n) ^ m) := by
          rw [div_pow, div_pow]; field_simp
      _ ≤ (2 * ((Gp + Gm) / 2) ^ m) / (2 * (2 ^ n) ^ m) := by gcongr
      _ = ((Gp + Gm) / 2 ^ (n + 1)) ^ m := by
          rw [pow_succ, div_pow, div_pow, mul_pow]; field_simp

lemma aux_kh_coin {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
    (e : Θ → ℝ) (he : Measurable e) (h1 : ν {θ | e θ = 1} = 1 / 2)
    (h2 : ν {θ | e θ = -1} = 1 / 2) (A : Set ℝ) (hA : MeasurableSet A) :
    ν.map e A = (2 : ENNReal)⁻¹ * ∑ β : Bool, A.indicator 1 (aux_kh_sg β) := by
  rw [Measure.map_apply he hA]
  have hm1 : MeasurableSet {θ | e θ = 1} := he (measurableSet_singleton 1)
  have hm2 : MeasurableSet {θ | e θ = -1} := he (measurableSet_singleton (-1))
  have hdisj : Disjoint {θ | e θ = 1} {θ | e θ = -1} := by
    rw [Set.disjoint_left]; intro θ h h'; simp only [Set.mem_setOf_eq] at h h'; linarith
  have hU : ν ({θ | e θ = 1} ∪ {θ | e θ = -1}) = 1 := by
    rw [measure_union hdisj hm2, h1, h2]; exact ENNReal.add_halves 1
  have hUc : ν ({θ | e θ = 1} ∪ {θ | e θ = -1})ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff (hm1.union hm2)]; exact hU
  rw [← measure_inter_conull hUc, Set.inter_union_distrib_left,
    measure_union (hdisj.mono Set.inter_subset_right Set.inter_subset_right)
      ((he hA).inter hm2)]
  simp only [Fintype.sum_bool, aux_kh_sg, if_true, Bool.false_eq_true, if_false]
  have key : ∀ c : ℝ, ν (e ⁻¹' A ∩ {θ | e θ = c}) = A.indicator 1 c * ν {θ | e θ = c} := by
    intro c
    by_cases hc : c ∈ A
    · have : e ⁻¹' A ∩ {θ | e θ = c} = {θ | e θ = c} := by
        ext θ
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨h ▸ hc, h⟩
      rw [this, Set.indicator_of_mem hc]; simp
    · have : e ⁻¹' A ∩ {θ | e θ = c} = ∅ := by
        ext θ
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro h h'; exact hc (h' ▸ h)
      rw [this, Set.indicator_of_notMem hc]; simp
  rw [key, key, h1, h2, one_div]
  ring

lemma aux_kh_reduce {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
    {n : ℕ} (ε : Fin n → Θ → ℝ) (hε : IsRademacherSequence ε ν) (F : (Fin n → ℝ) → ℝ)
    (hF : Continuous F) :
    ∫ θ, F (fun i => ε i θ) ∂ν = (∑ b : Fin n → Bool, F (fun i => aux_kh_sg (b i))) / 2 ^ n := by
  obtain ⟨hmeas, hind, hval⟩ := hε
  have hX : Measurable (fun θ i => ε i θ) := measurable_pi_lambda _ hmeas
  have hmap : ν.map (fun θ i => ε i θ) = Measure.pi (fun i => ν.map (ε i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hmeas i).aemeasurable)).1 hind
  set μ' : Measure (Fin n → ℝ) := ((2 : ENNReal) ^ n)⁻¹ •
    ∑ b : Fin n → Bool, Measure.dirac (fun i => aux_kh_sg (b i)) with hμ'
  have hpi : Measure.pi (fun i => ν.map (ε i)) = μ' := by
    refine Measure.pi_eq (fun s hs => ?_)
    rw [Finset.prod_congr rfl (fun i _ => aux_kh_coin ν (ε i) (hmeas i) (hval i).1 (hval i).2
      (s i) (hs i))]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_univ_sum]
    simp only [hμ', Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      Measure.dirac_apply' _ (MeasurableSet.univ_pi hs), smul_eq_mul]
    rw [ENNReal.inv_pow, Fintype.piFinset_univ]
    congr 1
    refine Finset.sum_congr rfl (fun b _ => ?_)
    classical
    by_cases hb : ∀ i, aux_kh_sg (b i) ∈ s i
    · rw [Set.indicator_of_mem (Set.mem_univ_pi.2 hb)]
      rw [Finset.prod_eq_one (fun i _ => Set.indicator_of_mem (hb i) _)]
      rfl
    · obtain ⟨i, hi⟩ := not_forall.1 hb
      rw [Set.indicator_of_notMem (fun h => hi (Set.mem_univ_pi.1 h i))]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)]
  calc ∫ θ, F (fun i => ε i θ) ∂ν = ∫ s, F s ∂(ν.map (fun θ i => ε i θ)) :=
        (integral_map hX.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ s, F s ∂μ' := by rw [hmap, hpi]
    _ = (∑ b : Fin n → Bool, F (fun i => aux_kh_sg (b i))) / 2 ^ n := by
      rw [hμ', integral_smul_measure,
        integral_finsetSum_measure (fun b _ => integrable_dirac enorm_lt_top)]
      simp only [integral_dirac, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
        ENNReal.toReal_ofNat]
      rw [inv_mul_eq_div]



lemma aux_kh_mono {ι : Type*} [Fintype ι] (N : ℝ) (hN : (Fintype.card ι : ℝ) = N)
    (hNpos : 0 < N) (Z : ι → ℝ) (hZ : ∀ i, 0 ≤ Z i) {r r' : ℝ} (hr : 0 < r) (hrr : r ≤ r') :
    ((∑ i, Z i ^ r) / N) ^ (1 / r) ≤ ((∑ i, Z i ^ r') / N) ^ (1 / r') := by
  have hr' : 0 < r' := hr.trans_le hrr
  have hw : ∑ _i : ι, (1 / N) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]; field_simp
  have h := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ (fun _ => 1 / N)
    (fun i => Z i ^ r) (fun _ _ => by positivity) hw (fun i _ => Real.rpow_nonneg (hZ i) _)
    (p := r' / r) (by rw [le_div_iff₀ hr]; linarith)
  simp only [← Finset.mul_sum] at h
  have e1 : ∀ i, (Z i ^ r) ^ (r' / r) = Z i ^ r' := by
    intro i; rw [← Real.rpow_mul (hZ i)]; congr 1; field_simp
  simp only [e1] at h
  rw [one_div_mul_eq_div, one_div_mul_eq_div] at h
  have hA : 0 ≤ (∑ i, Z i ^ r) / N :=
    div_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hZ i) _) hNpos.le
  calc ((∑ i, Z i ^ r) / N) ^ (1 / r) = (((∑ i, Z i ^ r) / N) ^ (r' / r)) ^ (1 / r') := by
        rw [← Real.rpow_mul hA]; congr 1; field_simp
    _ ≤ ((∑ i, Z i ^ r') / N) ^ (1 / r') :=
        Real.rpow_le_rpow (Real.rpow_nonneg hA _) h (by positivity)

lemma aux_kh_interp {T2 Tq T4 q : ℝ} (hq : 0 < q) (hq2 : q < 2) (h2 : 0 < T2) (hTq : 0 ≤ Tq)
    (h4 : 0 ≤ T4) (hH : T2 ≤ Tq ^ (2 / (4 - q)) * T4 ^ ((2 - q) / (4 - q)))
    (hT4 : T4 ≤ 256 * T2 ^ 2) :
    T2 ^ (1 / 2 : ℝ) ≤ (256 : ℝ) ^ ((2 - q) / (2 * q)) * Tq ^ (1 / q) := by
  set α : ℝ := 2 / (4 - q) with hα
  set β : ℝ := (2 - q) / (4 - q) with hβ
  have h4q : 0 < 4 - q := by linarith
  have hβ0 : 0 ≤ β := div_nonneg (by linarith) h4q.le
  have hT4' : T4 ^ β ≤ (256 : ℝ) ^ β * T2 ^ (2 * β) := by
    calc T4 ^ β ≤ (256 * T2 ^ 2) ^ β := Real.rpow_le_rpow h4 hT4 hβ0
      _ = (256 : ℝ) ^ β * T2 ^ (2 * β) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_mul h2.le]
        norm_cast
  have h1 : T2 ≤ Tq ^ α * ((256 : ℝ) ^ β * T2 ^ (2 * β)) :=
    hH.trans (mul_le_mul_of_nonneg_left hT4' (Real.rpow_nonneg hTq _))
  have hpos : 0 < T2 ^ (2 * β) := Real.rpow_pos_of_pos h2 _
  have h2' : T2 ^ (1 - 2 * β) ≤ Tq ^ α * (256 : ℝ) ^ β := by
    rw [Real.rpow_sub h2, Real.rpow_one, div_le_iff₀ hpos]
    linarith [h1]
  set e : ℝ := (4 - q) / (2 * q) with he
  have he0 : 0 ≤ e := div_nonneg h4q.le (by linarith)
  have h3 := Real.rpow_le_rpow (Real.rpow_nonneg h2.le _) h2' he0
  rw [← Real.rpow_mul h2.le, Real.mul_rpow (Real.rpow_nonneg hTq _) (by positivity),
    ← Real.rpow_mul hTq, ← Real.rpow_mul (by norm_num)] at h3
  have x1 : (1 - 2 * β) * e = 1 / 2 := by
    rw [hβ, he]; field_simp; ring
  have x2 : α * e = 1 / q := by
    rw [hα, he]; field_simp
  have x3 : β * e = (2 - q) / (2 * q) := by
    rw [hβ, he]; field_simp
  rw [x1, x2, x3] at h3
  linarith [h3]


lemma aux_kh_holder {ι : Type*} [Fintype ι] (N : ℝ) (hN : 0 < N) (Z : ι → ℝ)
    (hZ : ∀ i, 0 ≤ Z i) {q : ℝ} (hq : 0 < q) (hq2 : q < 2) :
    (∑ i, Z i ^ (2 : ℝ)) / N ≤
      ((∑ i, Z i ^ q) / N) ^ (2 / (4 - q)) * ((∑ i, Z i ^ (4 : ℝ)) / N) ^ ((2 - q) / (4 - q)) := by
  set α : ℝ := 2 / (4 - q) with hα
  set β : ℝ := (2 - q) / (4 - q) with hβ
  have h4q : 0 < 4 - q := by linarith
  have hα0 : 0 < α := div_pos (by norm_num) h4q
  have hβ0 : 0 < β := div_pos (by linarith) h4q
  have hαβ : α + β = 1 := by rw [hα, hβ]; field_simp; ring
  have hconj : α⁻¹.HolderConjugate β⁻¹ := Real.HolderConjugate.inv_inv hα0 hβ0 hαβ
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hconj
    (f := fun i => Z i ^ (q * α)) (g := fun i => Z i ^ (4 * β))
    (fun i _ => Real.rpow_nonneg (hZ i) _) (fun i _ => Real.rpow_nonneg (hZ i) _)
  have e1 : ∀ i, Z i ^ (q * α) * Z i ^ (4 * β) = Z i ^ (2 : ℝ) := by
    intro i
    have hs : q * α + 4 * β = 2 := by rw [hα, hβ]; field_simp; ring
    rw [← Real.rpow_add' (hZ i) (by rw [hs]; norm_num), hs]
  have e2 : ∀ i, (Z i ^ (q * α)) ^ α⁻¹ = Z i ^ q := by
    intro i; rw [← Real.rpow_mul (hZ i)]; congr 1; field_simp
  have e3 : ∀ i, (Z i ^ (4 * β)) ^ β⁻¹ = Z i ^ (4 : ℝ) := by
    intro i; rw [← Real.rpow_mul (hZ i)]; congr 1; field_simp
  simp only [e1, e2, e3, one_div, inv_inv] at h
  have hA : 0 ≤ ∑ i, Z i ^ q := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hZ i) _
  have hB : 0 ≤ ∑ i, Z i ^ (4 : ℝ) := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hZ i) _
  rw [Real.div_rpow hA hN.le, Real.div_rpow hB hN.le, div_mul_div_comm,
    ← Real.rpow_add hN, hαβ, Real.rpow_one]
  exact div_le_div_of_nonneg_right h hN.le

lemma aux_kh_moment (m : ℕ) (hm : 1 ≤ m) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (x : Fin n → E) :
    (∑ b : Fin n → Bool, ‖∑ i, aux_kh_sg (b i) • x i‖ ^ (2 * m)) / 2 ^ n ≤
      (2 * m : ℝ) ^ (2 * m) *
        ((∑ b : Fin n → Bool, ‖∑ i, aux_kh_sg (b i) • x i‖ ^ 2) / 2 ^ n) ^ m := by
  have h := aux_kh_hyper m hm n 0 x
  simp only [zero_add, norm_smul, mul_pow, ← Finset.mul_sum] at h
  have hc : ‖(1 / (2 * m : ℝ))‖ ^ (2 * m) = 1 / (2 * m : ℝ) ^ (2 * m) := by
    rw [Real.norm_of_nonneg (by positivity), div_pow, one_pow]
  rw [hc, mul_div_assoc] at h
  have hpos : (0 : ℝ) < (2 * m : ℝ) ^ (2 * m) := by positivity
  rw [one_div, inv_mul_le_iff₀ hpos] at h
  exact h

lemma aux_kh_fin (p q : ℝ) (hp : 0 < p) (hq : 0 < q) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ) (x : Fin n → E) :
    ((∑ b : Fin n → Bool, ‖∑ i, aux_kh_sg (b i) • x i‖ ^ p) / 2 ^ n) ^ (1 / p) ≤
      (2 * ((⌈p / 2⌉₊ + 1 : ℕ) : ℝ) * (256 : ℝ) ^ (1 / q)) *
        ((∑ b : Fin n → Bool, ‖∑ i, aux_kh_sg (b i) • x i‖ ^ q) / 2 ^ n) ^ (1 / q) := by
  set Z : (Fin n → Bool) → ℝ := fun b => ‖∑ i, aux_kh_sg (b i) • x i‖ with hZdef
  have hZ : ∀ b, 0 ≤ Z b := fun b => norm_nonneg _
  set m : ℕ := ⌈p / 2⌉₊ + 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hN : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by
    simp [Fintype.card_fun]
  have hNpos : (0 : ℝ) < 2 ^ n := by positivity
  have hpm : p ≤ ((2 * m : ℕ) : ℝ) := by
    have := Nat.le_ceil (p / 2)
    push_cast [hmdef]
    linarith
  -- step 1
  have s1 := aux_kh_mono (2 ^ n) hN hNpos Z hZ hp hpm
  -- step 2
  have s2 : ((∑ b, Z b ^ (((2 * m : ℕ) : ℝ))) / 2 ^ n) ^ (1 / (((2 * m : ℕ) : ℝ))) ≤
      (2 * m : ℝ) * ((∑ b, Z b ^ (2 : ℝ)) / 2 ^ n) ^ (1 / (2 : ℝ)) := by
    have hmom := aux_kh_moment m hm1 n x
    simp only [Real.rpow_natCast, Real.rpow_two]
    set B := (∑ b, Z b ^ 2) / 2 ^ n with hB
    have hB0 : 0 ≤ B := div_nonneg (Finset.sum_nonneg fun b _ => by positivity) hNpos.le
    have hA0 : 0 ≤ (∑ b, Z b ^ (2 * m)) / 2 ^ n :=
      div_nonneg (Finset.sum_nonneg fun b _ => by positivity) hNpos.le
    have hsq : B ^ (1 / (2 : ℝ)) = Real.sqrt B := by rw [Real.sqrt_eq_rpow]
    rw [hsq]
    have hm0 : 2 * m ≠ 0 := by omega
    have key : (2 * m : ℝ) ^ (2 * m) * B ^ m = ((2 * m : ℝ) * Real.sqrt B) ^ (2 * m) := by
      rw [mul_pow _ (Real.sqrt B), pow_mul (Real.sqrt B), Real.sq_sqrt hB0]
    rw [key] at hmom
    calc ((∑ b, Z b ^ (2 * m)) / 2 ^ n) ^ (1 / (((2 * m : ℕ) : ℝ)))
        ≤ (((2 * m : ℝ) * Real.sqrt B) ^ (2 * m)) ^ (1 / (((2 * m : ℕ) : ℝ))) :=
          Real.rpow_le_rpow hA0 hmom (by positivity)
      _ = (2 * m : ℝ) * Real.sqrt B := by
          rw [one_div, Real.pow_rpow_inv_natCast (by positivity) hm0]
  -- step 3
  have s3 : ((∑ b, Z b ^ (2 : ℝ)) / 2 ^ n) ^ (1 / (2 : ℝ)) ≤
      (256 : ℝ) ^ (1 / q) * ((∑ b, Z b ^ q) / 2 ^ n) ^ (1 / q) := by
    have hMq : 0 ≤ ((∑ b, Z b ^ q) / 2 ^ n) ^ (1 / q) :=
      Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (hZ b) _)
        hNpos.le) _
    have h256 : (1 : ℝ) ≤ (256 : ℝ) ^ (1 / q) := Real.one_le_rpow (by norm_num) (by positivity)
    by_cases hq2 : 2 ≤ q
    · have := aux_kh_mono (2 ^ n) hN hNpos Z hZ (by norm_num : (0 : ℝ) < 2) hq2
      nlinarith
    · replace hq2 : q < 2 := not_le.1 hq2
      set T2 := (∑ b, Z b ^ (2 : ℝ)) / 2 ^ n with hT2
      have hT20 : 0 ≤ T2 :=
        div_nonneg (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (hZ b) _) hNpos.le
      rcases hT20.eq_or_lt with h0 | hpos
      · rw [← h0, Real.zero_rpow (by norm_num)]
        positivity
      · have hH := aux_kh_holder (2 ^ n) hNpos Z hZ hq hq2
        have hmom := aux_kh_moment 2 (by norm_num) n x
        have hT4 : (∑ b, Z b ^ (4 : ℝ)) / 2 ^ n ≤ 256 * T2 ^ 2 := by
          have e4 : ∀ b, Z b ^ (4 : ℝ) = Z b ^ (2 * 2) := by
            intro b; rw [← Real.rpow_natCast]; norm_num
          simp only [e4, hT2, Real.rpow_two]
          convert hmom using 2
          norm_num
        have hi := aux_kh_interp hq hq2 hpos
          (div_nonneg (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (hZ b) _) hNpos.le)
          (div_nonneg (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (hZ b) _) hNpos.le)
          hH hT4
        have hexp : (256 : ℝ) ^ ((2 - q) / (2 * q)) ≤ (256 : ℝ) ^ (1 / q) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          rw [div_le_div_iff₀ (by positivity) hq]
          nlinarith
        calc T2 ^ (1 / (2 : ℝ)) ≤ (256 : ℝ) ^ ((2 - q) / (2 * q)) * _ := hi
          _ ≤ (256 : ℝ) ^ (1 / q) * _ := mul_le_mul_of_nonneg_right hexp hMq
  calc ((∑ b, Z b ^ p) / 2 ^ n) ^ (1 / p)
      ≤ ((∑ b, Z b ^ (((2 * m : ℕ) : ℝ))) / 2 ^ n) ^ (1 / (((2 * m : ℕ) : ℝ))) := s1
    _ ≤ (2 * m : ℝ) * ((∑ b, Z b ^ (2 : ℝ)) / 2 ^ n) ^ (1 / (2 : ℝ)) := s2
    _ ≤ (2 * m : ℝ) * ((256 : ℝ) ^ (1 / q) * ((∑ b, Z b ^ q) / 2 ^ n) ^ (1 / q)) :=
        mul_le_mul_of_nonneg_left s3 (by positivity)
    _ = _ := by push_cast [hmdef]; ring

end SupportVectorMachines.Regression

open SupportVectorMachines.Regression
open MeasureTheory ProbabilityTheory

theorem solution
    {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ) (ε : Fin n → Θ → ℝ), IsRademacherSequence ε ν →
        ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
          [MeasurableSpace E] [BorelSpace E] (x : Fin n → E),
          (∫ θ, ‖∑ i, ε i θ • x i‖ ^ p ∂ν) ^ (1 / p) ≤
            K * (∫ θ, ‖∑ i, ε i θ • x i‖ ^ q ∂ν) ^ (1 / q) := by
  refine ⟨2 * ((⌈p / 2⌉₊ + 1 : ℕ) : ℝ) * (256 : ℝ) ^ (1 / q), by positivity, ?_⟩
  intro n ε hε E _ _ _ _ _ x
  have hred : ∀ r : ℝ, 0 < r → ∫ θ, ‖∑ i, ε i θ • x i‖ ^ r ∂ν =
      (∑ b : Fin n → Bool, ‖∑ i, aux_kh_sg (b i) • x i‖ ^ r) / 2 ^ n := by
    intro r hr
    have hc : Continuous (fun s : Fin n → ℝ => ‖∑ i, s i • x i‖ ^ r) := by
      refine Continuous.rpow_const ?_ (fun _ => Or.inr hr.le)
      fun_prop
    exact aux_kh_reduce ν ε hε (fun s : Fin n → ℝ => ‖∑ i, s i • x i‖ ^ r) hc
  rw [hred p hp, hred q hq]
  exact aux_kh_fin p q hp hq n x

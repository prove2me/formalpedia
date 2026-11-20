-- Prove2me | solution 1 for UniversalSubmod.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:47:06.968173+00:00
-- url     : https://prove2.me/submissions/0cdeeb55-e2ef-4be5-9141-8095c9261d7a

import Mathlib

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Lemma25

open Finset

/-- sign of a boolean -/
noncomputable def sg (b : Bool) : ℝ := if b then 1 else -1

lemma sg_sq (b : Bool) : sg b ^ 2 = 1 := by
  cases b <;> simp [sg]

lemma mgf_sum (k : ℕ) (c : Fin k → ℝ) (t : ℝ) :
    ∑ z : Fin k → Bool, Real.exp (t * ∑ l, c l * sg (z l)) =
      ∏ l, (Real.exp (t * c l) + Real.exp (-(t * c l))) := by
  have h1 : ∀ z : Fin k → Bool, Real.exp (t * ∑ l, c l * sg (z l)) =
      ∏ l, Real.exp (t * (c l * sg (z l))) := by
    intro z
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  have := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset Bool))
    (fun l b => Real.exp (t * (c l * sg b)))
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  apply Finset.prod_congr rfl
  intro l _
  simp [sg, mul_comm]

lemma one_sided (k : ℕ) (c : Fin k → ℝ) (hc : ∀ l, |c l| ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    (((Finset.univ.filter (fun z : Fin k → Bool => ε * k ≤ ∑ l, c l * sg (z l))).card : ℕ) : ℝ)
      ≤ 2 ^ k * Real.exp (-(ε ^ 2 * k / 2)) := by
  set A := Finset.univ.filter (fun z : Fin k → Bool => ε * k ≤ ∑ l, c l * sg (z l)) with hA
  have h1 : (A.card : ℝ) * Real.exp (ε * (ε * k)) ≤
      ∑ z : Fin k → Bool, Real.exp (ε * ∑ l, c l * sg (z l)) := by
    calc (A.card : ℝ) * Real.exp (ε * (ε * k)) = ∑ z ∈ A, Real.exp (ε * (ε * k)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ A, Real.exp (ε * ∑ l, c l * sg (z l)) := by
          apply Finset.sum_le_sum
          intro z hz
          have : ε * k ≤ ∑ l, c l * sg (z l) := (Finset.mem_filter.mp hz).2
          exact Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => (Real.exp_pos _).le)
  rw [mgf_sum] at h1
  have h2 : ∀ l : Fin k, Real.exp (ε * c l) + Real.exp (-(ε * c l)) ≤ 2 * Real.exp (ε ^ 2 / 2) := by
    intro l
    have := Real.cosh_le_exp_half_sq (ε * c l)
    rw [Real.cosh_eq] at this
    have h3 : (ε * c l) ^ 2 ≤ ε ^ 2 := by
      have : (c l) ^ 2 ≤ 1 := by
        have := hc l
        nlinarith [abs_nonneg (c l), sq_abs (c l)]
      nlinarith [sq_nonneg ε]
    have : Real.exp ((ε * c l) ^ 2 / 2) ≤ Real.exp (ε ^ 2 / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have h3 : ∏ l, (Real.exp (ε * c l) + Real.exp (-(ε * c l))) ≤ (2 * Real.exp (ε ^ 2 / 2)) ^ k := by
    calc _ ≤ ∏ _l : Fin k, (2 * Real.exp (ε ^ 2 / 2)) :=
          Finset.prod_le_prod (fun l _ => by positivity) (fun l _ => h2 l)
      _ = _ := by simp
  have h4 : (A.card : ℝ) * Real.exp (ε * (ε * k)) ≤ (2 * Real.exp (ε ^ 2 / 2)) ^ k :=
    h1.trans h3
  have h5 : (2 * Real.exp (ε ^ 2 / 2)) ^ k = 2 ^ k * Real.exp (ε ^ 2 * k / 2) := by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
  rw [h5] at h4
  have h6 : Real.exp (ε * (ε * k)) = Real.exp (ε ^ 2 * k / 2) * Real.exp (ε ^ 2 * k / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos : 0 < Real.exp (ε ^ 2 * k / 2) := Real.exp_pos _
  rw [Real.exp_neg]
  rw [h6] at h4
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  nlinarith

lemma tail (k : ℕ) (c : Fin k → ℝ) (hc : ∀ l, |c l| ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    (((Finset.univ.filter (fun z : Fin k → Bool => ε * k < |∑ l, c l * sg (z l)|)).card : ℕ) : ℝ)
      ≤ 2 * (2 ^ k * Real.exp (-(ε ^ 2 * k / 2))) := by
  have hA := one_sided k c hc ε hε
  have hB := one_sided k (fun l => - c l) (fun l => by simpa using hc l) ε hε
  have hsub : Finset.univ.filter (fun z : Fin k → Bool => ε * k < |∑ l, c l * sg (z l)|) ⊆
      Finset.univ.filter (fun z : Fin k → Bool => ε * k ≤ ∑ l, c l * sg (z l)) ∪
      Finset.univ.filter (fun z : Fin k → Bool => ε * k ≤ ∑ l, (fun l => - c l) l * sg (z l)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hz ⊢
    simp only [neg_mul, Finset.sum_neg_distrib]
    rcases le_abs'.mp hz.le with h | h
    · right; linarith
    · left; linarith
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 : (_ : ℝ) ≤ _ := Nat.cast_le.mpr this
  push_cast at h2
  linarith

lemma exists_seq (n k : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (hkn : 4 / ε ^ 2 * Real.log n ≤ (k : ℝ)) :
    ∀ m, m ≤ n → ∃ x : ℕ → (Fin k → Bool), ∀ i j, i < j → j < m →
      |∑ l, sg (x i l) * sg (x j l)| ≤ ε * k := by
  intro m
  induction m with
  | zero => intro _; exact ⟨fun _ => fun _ => true, fun i j _ h => absurd h (by omega)⟩
  | succ m ih =>
    intro hm
    obtain ⟨x, hx⟩ := ih (by omega)
    -- bad set
    let bad : Finset (Fin k → Bool) := (Finset.range m).biUnion (fun i =>
      Finset.univ.filter (fun z : Fin k → Bool => ε * k < |∑ l, sg (x i l) * sg (z l)|))
    have hcard : (bad.card : ℝ) < 2 ^ k := by
      have h1 : (bad.card : ℝ) ≤ ∑ i ∈ Finset.range m, (((Finset.univ.filter
          (fun z : Fin k → Bool => ε * k < |∑ l, sg (x i l) * sg (z l)|)).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      have h2 : ∀ i ∈ Finset.range m, (((Finset.univ.filter
          (fun z : Fin k → Bool => ε * k < |∑ l, sg (x i l) * sg (z l)|)).card : ℕ) : ℝ) ≤
          2 * (2 ^ k * Real.exp (-(ε ^ 2 * k / 2))) := by
        intro i _
        apply tail k _ _ ε hε
        intro l
        have := sg_sq (x i l)
        have h : |sg (x i l)| ^ 2 = 1 := by rw [sq_abs]; exact this
        nlinarith [abs_nonneg (sg (x i l))]
      have h3 := h1.trans (Finset.sum_le_sum h2)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hexp : Real.exp (-(ε ^ 2 * k / 2)) ≤ 1 / (n : ℝ) ^ 2 := by
        have hlog : 2 * Real.log n ≤ ε ^ 2 * k / 2 := by
          have : 4 / ε ^ 2 * Real.log n * ε ^ 2 ≤ k * ε ^ 2 := by gcongr
          have e : 4 / ε ^ 2 * Real.log n * ε ^ 2 = 4 * Real.log n := by field_simp
          nlinarith
        calc Real.exp (-(ε ^ 2 * k / 2)) ≤ Real.exp (-(2 * Real.log n)) :=
              Real.exp_le_exp.mpr (by linarith)
          _ = 1 / (n : ℝ) ^ 2 := by
              rw [Real.exp_neg, show 2 * Real.log n = ((2:ℕ):ℝ) * Real.log n by norm_num,
                Real.exp_nat_mul, Real.exp_log (by linarith)]
              simp
      have hm' : (m : ℝ) ≤ n - 1 := by
        have : m + 1 ≤ n := hm
        have : ((m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
        push_cast at this; linarith
      have h2k : (0 : ℝ) < 2 ^ k := by positivity
      have hnpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      calc (bad.card : ℝ) ≤ m * (2 * (2 ^ k * Real.exp (-(ε ^ 2 * k / 2)))) := h3
        _ ≤ (n - 1) * (2 * (2 ^ k * (1 / (n : ℝ) ^ 2))) := by
            have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
            gcongr
        _ < 2 ^ k := by
            have : (n - 1) * (2 * (2 ^ k * (1 / (n : ℝ) ^ 2))) = 2 ^ k * (2 * (n - 1) / n ^ 2) := by
              field_simp
            rw [this]
            have : 2 * ((n : ℝ) - 1) / n ^ 2 < 1 := by
              rw [div_lt_one hnpos]; nlinarith [sq_nonneg ((n : ℝ) - 1)]
            nlinarith
    have hex : ∃ z : Fin k → Bool, z ∉ bad := by
      by_contra h
      push_neg at h
      have : bad = Finset.univ := Finset.eq_univ_of_forall h
      rw [this, Finset.card_univ] at hcard
      simp at hcard
    obtain ⟨z, hz⟩ := hex
    refine ⟨Function.update x m z, ?_⟩
    intro i j hij hj
    by_cases hjm : j = m
    · subst hjm
      have him : i ∈ Finset.range j := Finset.mem_range.mpr hij
      have : ¬ (j > 0 ∧ False) := by simp
      simp only [bad, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        not_exists, not_lt] at hz
      have := not_lt.mp (fun h => hz i ⟨him, h⟩)
      rw [Function.update_of_ne (by omega), Function.update_self]
      simpa using this
    · have hi' : i ≠ m := by omega
      rw [Function.update_of_ne hi', Function.update_of_ne hjm]
      exact hx i j hij (by omega)

end UniversalSubmod.Dev.Lemma25

namespace UniversalSubmod

open scoped RealInnerProductSpace

theorem chk_lemma_2_5 (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 0 < k)
    (hkn : 4 / ε ^ 2 * Real.log n ≤ (k : ℝ)) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin k),
      (∀ i, ‖v i‖ = 1) ∧ ∀ i j, i ≠ j → |⟪v i, v j⟫| ≤ ε := by
  obtain ⟨x, hx⟩ := Dev.Lemma25.exists_seq n k hn ε hε hkn n le_rfl
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨fun i => WithLp.toLp 2 (fun l => (1 / Real.sqrt k) * Dev.Lemma25.sg (x i l)), ?_, ?_⟩
  · intro i
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp only [Real.norm_eq_abs, sq_abs, mul_pow, Dev.Lemma25.sg_sq, mul_one, one_div, inv_pow]
    rw [Real.sq_sqrt hkpos.le]
    simp [Finset.sum_const, Finset.card_univ]
    field_simp
  · intro i j hij
    have hinner : ⟪(WithLp.toLp 2 (fun l => (1 / Real.sqrt k) * Dev.Lemma25.sg (x i l)) :
        EuclideanSpace ℝ (Fin k)), WithLp.toLp 2 (fun l => (1 / Real.sqrt k) *
        Dev.Lemma25.sg (x j l))⟫ = (1 / k) * ∑ l, Dev.Lemma25.sg (x i l) * Dev.Lemma25.sg (x j l) := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      have : (1 / Real.sqrt k) * (1 / Real.sqrt k) = 1 / k := by
        have hs : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hkpos.le
        have hs0 : Real.sqrt k ≠ 0 := (Real.sqrt_pos.mpr hkpos).ne'
        field_simp
        linarith
      rw [← this]; ring
    rw [hinner, abs_mul, abs_of_pos (by positivity)]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · have := hx i j h j.2
      calc 1 / (k : ℝ) * |_| ≤ 1 / k * (ε * k) := by gcongr
        _ = ε := by field_simp
    · have := hx j i h i.2
      calc 1 / (k : ℝ) * |_| ≤ 1 / k * (ε * k) := by
            gcongr
            simpa [mul_comm] using this
        _ = ε := by field_simp

end UniversalSubmod
end

theorem solution : type_of% @UniversalSubmod.chk_lemma_2_5 := @UniversalSubmod.chk_lemma_2_5

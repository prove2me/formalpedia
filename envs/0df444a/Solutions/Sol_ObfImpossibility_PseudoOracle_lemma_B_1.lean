-- Prove2me | solution 1 for ObfImpossibility.PseudoOracle.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T08:02:44.942079+00:00
-- url     : https://prove2.me/submissions/a95cccc5-e28b-46c6-a48b-7e4bc1bc3dea

import Mathlib
import Definitions.Def_ObfImpossibility_PseudoOracle_Setting

set_option autoImplicit false

namespace ObfImpossibility.PseudoOracle
namespace QTree
variable {K L : ℕ}

/-- The set of oracle points queried by the run of `t` against `G`. -/
def qset : QTree K L → (Fin K → Fin L) → Finset (Fin K)
  | out _, _ => ∅
  | query z k, G => insert z ((k (G z)).qset G)

theorem card_qset_le (t : QTree K L) (G : Fin K → Fin L) : (t.qset G).card ≤ t.depth := by
  induction t with
  | out b => simp [qset, depth]
  | query z k ih =>
    simp only [qset, depth]
    have h1 := Finset.card_insert_le z ((k (G z)).qset G)
    have h2 := ih (G z)
    have h3 := Finset.le_sup (f := fun y => (k y).depth) (Finset.mem_univ (G z))
    omega

theorem hits_eq_true_iff (t : QTree K L) (G : Fin K → Fin L) (A : Finset (Fin K)) :
    t.hits G A = true ↔ ∃ z ∈ t.qset G, z ∈ A := by
  induction t with
  | out b => simp [hits, qset]
  | query z k ih =>
    simp only [hits, qset, Bool.or_eq_true, decide_eq_true_eq, ih, Finset.mem_insert]
    constructor
    · rintro (h | ⟨w, hw, hwA⟩)
      · exact ⟨z, Or.inl rfl, h⟩
      · exact ⟨w, Or.inr hw, hwA⟩
    · rintro ⟨w, (rfl | hw), hwA⟩
      · exact Or.inl hwA
      · exact Or.inr ⟨w, hw, hwA⟩

theorem run_congr (t : QTree K L) (G G' : Fin K → Fin L)
    (h : ∀ z ∈ t.qset G, G' z = G z) : t.run G' = t.run G := by
  induction t with
  | out b => simp [run]
  | query z k ih =>
    simp only [run]
    have hz : G' z = G z := h z (by simp [qset])
    rw [hz]
    exact ih (G z) (fun w hw => h w (by simp [qset, hw]))

end QTree

/-- Bool to real indicator. -/
noncomputable def b2r (b : Bool) : ℝ := if b then 1 else 0

lemma b2r_nonneg (b : Bool) : 0 ≤ b2r b := by cases b <;> simp [b2r]
lemma b2r_le_one (b : Bool) : b2r b ≤ 1 := by cases b <;> simp [b2r]
lemma b2r_not (b : Bool) : b2r (!b) = 1 - b2r b := by cases b <;> simp [b2r]

lemma avg_eq {α : Type} (s : Finset α) (f : α → Bool) :
    avg s f = (∑ a ∈ s, b2r (f a)) / s.card := by
  unfold avg
  congr 1
  rw [Finset.card_filter]
  push_cast
  rfl

lemma avg_nonneg {α : Type} (s : Finset α) (f : α → Bool) : 0 ≤ avg s f := by
  unfold avg; positivity

lemma avg_le_one {α : Type} (s : Finset α) (f : α → Bool) : avg s f ≤ 1 := by
  unfold avg
  rcases Nat.eq_zero_or_pos s.card with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finset.card_filter_le _ _

lemma exp_le_quad (x : ℝ) (hx : |x| ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le hx
  have := (abs_le.mp this).2
  linarith

/-- Chernoff bound, counting form, for sampling with replacement from a finset `U`. -/
theorem chernoff_up {α : Type} [DecidableEq α] (U : Finset α) (hU : U.Nonempty) (f : α → Bool)
    (m : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        (avg U f + η) * m ≤ ∑ i, b2r (f (φ i))).card : ℝ) ≤
      Real.exp (-(m * η ^ 2 / 4)) * (U.card : ℝ) ^ m := by
  set P := Fintype.piFinset fun _ : Fin m => U with hP
  set lam := η / 2 with hlam
  set p := avg U f with hp
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hp0 : 0 ≤ p := avg_nonneg _ _
  have hp1 : p ≤ 1 := avg_le_one _ _
  have hlam0 : 0 < lam := by positivity
  have hW : ∑ u ∈ U, Real.exp (lam * b2r (f u)) = U.card * (1 + p * (Real.exp lam - 1)) := by
    have key : ∀ u, Real.exp (lam * b2r (f u)) = 1 + b2r (f u) * (Real.exp lam - 1) := by
      intro u; cases f u <;> simp [b2r]
    simp_rw [key, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hp, avg_eq]
    field_simp
    simp
  have hprod : ∑ φ ∈ P, Real.exp (lam * ∑ i, b2r (f (φ i))) =
      (∑ u ∈ U, Real.exp (lam * b2r (f u))) ^ m := by
    rw [← Fin.prod_const, Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro φ _
    rw [Finset.mul_sum, Real.exp_sum]
  have hmark : (((P.filter fun φ => (p + η) * m ≤ ∑ i, b2r (f (φ i))).card : ℝ)) *
      Real.exp (lam * ((p + η) * m)) ≤ ∑ φ ∈ P, Real.exp (lam * ∑ i, b2r (f (φ i))) := by
    calc _ = ∑ φ ∈ P.filter (fun φ => (p + η) * m ≤ ∑ i, b2r (f (φ i))),
          Real.exp (lam * ((p + η) * m)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ φ ∈ P.filter (fun φ => (p + η) * m ≤ ∑ i, b2r (f (φ i))),
          Real.exp (lam * ∑ i, b2r (f (φ i))) := by
          apply Finset.sum_le_sum
          intro φ hφ
          exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hφ).2 hlam0.le)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => (Real.exp_pos _).le)
  have h1 : 1 + p * (Real.exp lam - 1) ≤ Real.exp (p * (lam + lam ^ 2)) := by
    have hq := exp_le_quad lam (by rw [abs_le]; constructor <;> linarith)
    calc 1 + p * (Real.exp lam - 1) ≤ 1 + p * (lam + lam ^ 2) := by nlinarith
      _ ≤ _ := by linarith [Real.add_one_le_exp (p * (lam + lam ^ 2))]
  have hbase0 : 0 ≤ 1 + p * (Real.exp lam - 1) := by
    have : 1 ≤ Real.exp lam := Real.one_le_exp hlam0.le
    nlinarith
  have h2 : (1 + p * (Real.exp lam - 1)) ^ m ≤ Real.exp (m * (p * (lam + lam ^ 2))) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hbase0 h1 m
  have hE : 0 < Real.exp (lam * ((p + η) * m)) := Real.exp_pos _
  rw [hprod, hW, mul_pow] at hmark
  have h3 : (((P.filter fun φ => (p + η) * m ≤ ∑ i, b2r (f (φ i))).card : ℝ)) ≤
      (U.card : ℝ) ^ m * Real.exp (m * (p * (lam + lam ^ 2))) / Real.exp (lam * ((p + η) * m)) := by
    rw [le_div_iff₀ hE]
    calc _ ≤ (U.card : ℝ) ^ m * (1 + p * (Real.exp lam - 1)) ^ m := hmark
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  refine h3.trans ?_
  rw [mul_div_assoc, ← Real.exp_sub, mul_comm (Real.exp _)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [hlam]
  nlinarith [mul_nonneg hm (mul_nonneg (sub_nonneg.mpr hp1) (sq_nonneg (η / 2)))]


/-- Lower tail, from the upper tail applied to the negated function. -/
theorem chernoff_down {α : Type} [DecidableEq α] (U : Finset α) (hU : U.Nonempty) (f : α → Bool)
    (m : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        ∑ i, b2r (f (φ i)) ≤ (avg U f - η) * m).card : ℝ) ≤
      Real.exp (-(m * η ^ 2 / 4)) * (U.card : ℝ) ^ m := by
  have h := chernoff_up U hU (fun a => !f a) m η hη0 hη1
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have havg : avg U (fun a => !f a) = 1 - avg U f := by
    rw [avg_eq, avg_eq]
    simp_rw [b2r_not, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    field_simp
  refine le_trans (le_of_eq ?_) h
  congr 2
  ext φ
  simp only [Finset.mem_filter, havg, b2r_not, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> nlinarith

/-- Two-sided Chernoff. -/
theorem chernoff_two {α : Type} [DecidableEq α] (U : Finset α) (hU : U.Nonempty) (f : α → Bool)
    (m : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        η * m ≤ |∑ i, b2r (f (φ i)) - avg U f * m|).card : ℝ) ≤
      2 * Real.exp (-(m * η ^ 2 / 4)) * (U.card : ℝ) ^ m := by
  have h1 := chernoff_up U hU f m η hη0 hη1
  have h2 := chernoff_down U hU f m η hη0 hη1
  have hsub : ((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        η * m ≤ |∑ i, b2r (f (φ i)) - avg U f * m|) ⊆
      ((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        (avg U f + η) * m ≤ ∑ i, b2r (f (φ i))) ∪
      ((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        ∑ i, b2r (f (φ i)) ≤ (avg U f - η) * m) := by
    intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_union] at hφ ⊢
    rcases le_abs'.mp hφ.2 with h | h
    · right; exact ⟨hφ.1, by nlinarith⟩
    · left; exact ⟨hφ.1, by nlinarith⟩
  calc _ ≤ ((((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        (avg U f + η) * m ≤ ∑ i, b2r (f (φ i))) ∪
      ((Fintype.piFinset fun _ : Fin m => U).filter fun φ =>
        ∑ i, b2r (f (φ i)) ≤ (avg U f - η) * m)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := by
        refine le_trans (Nat.cast_le.mpr (Finset.card_union_le _ _)) ?_
        push_cast
        linarith

/-- Two Boolean functions agreeing on `A` off `E` have averages over `A` within `|E|/|A|`. -/
lemma avg_diff_le {α : Type} [DecidableEq α] (A E : Finset α) (f g : α → Bool)
    (h : ∀ a ∈ A, a ∉ E → f a = g a) :
    |avg A f - avg A g| ≤ (E.card : ℝ) / A.card := by
  rcases Nat.eq_zero_or_pos A.card with h0 | h0
  · simp [avg, h0]
  have hA : (0 : ℝ) < A.card := by exact_mod_cast h0
  rw [avg_eq, avg_eq, ← sub_div, abs_div, abs_of_pos hA]
  apply div_le_div_of_nonneg_right _ hA.le
  rw [← Finset.sum_sub_distrib]
  calc |∑ a ∈ A, (b2r (f a) - b2r (g a))| ≤ ∑ a ∈ A, |b2r (f a) - b2r (g a)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ A, (if a ∈ E then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases hE : a ∈ E
        · simp only [hE, if_true]
          rw [abs_le]; constructor <;>
            linarith [b2r_nonneg (f a), b2r_le_one (f a), b2r_nonneg (g a), b2r_le_one (g a)]
        · simp [hE, h a ha hE]
    _ = ((A.filter (· ∈ E)).card : ℝ) := by
        rw [Finset.card_filter]; push_cast; rfl
    _ ≤ E.card := by
        exact_mod_cast Finset.card_le_card (fun a ha => (Finset.mem_filter.mp ha).2)

/-- Average over a large subset is close to the average over the whole set. -/
lemma avg_subset_le {α : Type} [DecidableEq α] (A U : Finset α) (f : α → Bool) (hAU : A ⊆ U)
    (hA : A.Nonempty) : |avg A f - avg U f| ≤ ((U \ A).card : ℝ) / U.card := by
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast (hA.mono hAU).card_pos
  have hcard : ((U \ A).card : ℝ) = U.card - A.card := by
    rw [Finset.card_sdiff_of_subset hAU, Nat.cast_sub (Finset.card_le_card hAU)]
  have hsplit : ∑ a ∈ U, b2r (f a) = ∑ a ∈ A, b2r (f a) + ∑ a ∈ U \ A, b2r (f a) := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hAU]
  set SA := ∑ a ∈ A, b2r (f a)
  set SR := ∑ a ∈ U \ A, b2r (f a)
  have hSA0 : 0 ≤ SA := Finset.sum_nonneg (fun _ _ => b2r_nonneg _)
  have hSA1 : SA ≤ A.card := by
    calc SA ≤ ∑ a ∈ A, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => b2r_le_one _)
      _ = A.card := by simp
  have hSR0 : 0 ≤ SR := Finset.sum_nonneg (fun _ _ => b2r_nonneg _)
  have hSR1 : SR ≤ (U \ A).card := by
    calc SR ≤ ∑ a ∈ U \ A, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => b2r_le_one _)
      _ = (U \ A).card := by simp
  rw [avg_eq, avg_eq, hsplit, hcard]
  rw [hcard] at hSR1
  have hau : (A.card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card hAU
  set a : ℝ := (A.card : ℝ)
  set u : ℝ := (U.card : ℝ)
  have key : SA / a - (SA + SR) / u = (SA * (u - a) - a * SR) / (a * u) := by
    field_simp; ring
  rw [key, abs_div, abs_of_pos (mul_pos hAc hUc), div_le_div_iff₀ (mul_pos hAc hUc) hUc]
  have hN : |SA * (u - a) - a * SR| ≤ a * (u - a) := by
    rw [abs_le]; constructor <;>
      nlinarith [mul_le_mul_of_nonneg_left hSR1 hAc.le,
        mul_le_mul_of_nonneg_right hSA1 (sub_nonneg.mpr hau), mul_nonneg hAc.le hSR0,
        mul_nonneg hSA0 (sub_nonneg.mpr hau)]
  nlinarith [mul_le_mul_of_nonneg_right hN hUc.le]

/-- Markov counting. -/
lemma markov_count {β : Type} (P : Finset β) (X : β → ℕ) (t : ℝ) (ht : 0 < t) :
    ((P.filter fun s => t < (X s : ℝ)).card : ℝ) ≤ (∑ s ∈ P, (X s : ℝ)) / t := by
  rw [le_div_iff₀ ht]
  calc ((P.filter fun s => t < (X s : ℝ)).card : ℝ) * t
        = ∑ s ∈ P.filter (fun s => t < (X s : ℝ)), t := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ s ∈ P.filter (fun s => t < (X s : ℝ)), (X s : ℝ) :=
        Finset.sum_le_sum (fun s hs => (Finset.mem_filter.mp hs).2.le)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.cast_nonneg _)

/-- Counting functions `s` with `s j ∈ A s`, where `A s` does not depend on `s j`. -/
lemma count_coord {m K : ℕ} (j : Fin m) (A : (Fin m → Fin K) → Finset (Fin K)) (q : ℕ)
    (hA : ∀ s s' : Fin m → Fin K, (∀ k, k ≠ j → s k = s' k) → A s = A s')
    (hq : ∀ s, (A s).card ≤ q) :
    (Finset.univ.filter fun s : Fin m → Fin K => s j ∈ A s).card ≤ q * K ^ (m - 1) := by
  classical
  let e := Equiv.funSplitAt j (Fin K)
  have h1 : (Finset.univ.filter fun s : Fin m → Fin K => s j ∈ A s).card =
      (Finset.univ.filter fun p : Fin K × ({k // k ≠ j} → Fin K) => p.1 ∈ A (e.symm p)).card := by
    apply Finset.card_bij (fun s _ => e s)
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [e.symm_apply_apply]
      exact hs
    · intro a _ b _ h; exact e.injective h
    · intro p hp
      refine ⟨e.symm p, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have : (e.symm p) j = p.1 := by simp [e]
      rw [this]; exact hp
  rw [h1]
  have hsplit : (Finset.univ.filter fun p : Fin K × ({k // k ≠ j} → Fin K) => p.1 ∈ A (e.symm p)).card
      = ∑ t : ({k // k ≠ j} → Fin K),
          (Finset.univ.filter fun b : Fin K => b ∈ A (e.symm (b, t))).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.card_filter]
  rw [hsplit]
  have hbound : ∀ t : ({k // k ≠ j} → Fin K),
      (Finset.univ.filter fun b : Fin K => b ∈ A (e.symm (b, t))).card ≤ q := by
    intro t
    rcases Finset.eq_empty_or_nonempty
      (Finset.univ.filter fun b : Fin K => b ∈ A (e.symm (b, t))) with h | ⟨b1, hb1⟩
    · rw [h]; simp
    · refine le_trans (Finset.card_le_card ?_) (hq (e.symm (b1, t)))
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have : A (e.symm (b, t)) = A (e.symm (b1, t)) := by
        apply hA
        intro k hk
        simp [e, hk]
      rw [← this]; exact hb
  calc _ ≤ ∑ _t : ({k // k ≠ j} → Fin K), q := Finset.sum_le_sum (fun t _ => hbound t)
    _ = q * K ^ (m - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul,
          mul_comm]
        congr 2
        rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]

/-- `n^m ≤ 2 n^{(m)}` when `4 m^2 ≤ n`. -/
lemma pow_le_two_descFactorial (n m : ℕ) (h : 4 * m ^ 2 ≤ n) :
    (n : ℝ) ^ m ≤ 2 * (n.descFactorial m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  have hn : 0 < n := by nlinarith
  have hmn : m ≤ n := by nlinarith
  have h1 : ((n + 1 - m : ℕ) : ℝ) ^ m ≤ n.descFactorial m := by
    exact_mod_cast Nat.pow_sub_le_descFactorial n m
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : ((n : ℝ) - m) ≤ ((n + 1 - m : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  have h3 : (0 : ℝ) ≤ n - m := by
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hb := one_add_mul_le_pow (a := -((m : ℝ) / n)) (by
    have : (m : ℝ) / n ≤ 1 := by rw [div_le_one hnr]; exact_mod_cast hmn
    have : 0 ≤ (m : ℝ) / n := by positivity
    linarith) m
  have hmm : (4 : ℝ) * (m : ℝ) ^ 2 ≤ n := by exact_mod_cast h
  have h4 : (1 : ℝ) / 2 ≤ 1 + (m : ℝ) * -((m : ℝ) / n) := by
    rw [mul_neg, ← mul_div_assoc, ← sq]
    have : (m : ℝ) ^ 2 / n ≤ 1 / 4 := by
      rw [div_le_iff₀ hnr]; linarith
    linarith
  have h5 : (1 + -((m : ℝ) / n)) ^ m * (n : ℝ) ^ m = ((n : ℝ) - m) ^ m := by
    rw [← mul_pow]; congr 1; field_simp; ring
  have h6 : ((n : ℝ) - m) ^ m ≤ ((n + 1 - m : ℕ) : ℝ) ^ m := pow_le_pow_left₀ h3 h2 m
  have h7 : (1 / 2 : ℝ) * (n : ℝ) ^ m ≤ ((n : ℝ) - m) ^ m := by
    rw [← h5]
    exact mul_le_mul_of_nonneg_right (h4.trans hb) (by positivity)
  linarith

section Sim
variable {K L : ℕ}

/-- The simulator `M`: run `D y`, answering a query `z ∈ S` with `y` and `z ∉ S` with `g z`. -/
def sim (D : Fin L → QTree K L) (S : Finset (Fin K)) (g : Fin K → Fin L) (y : Fin L) : Bool :=
  (D y).run (fun z => if z ∈ S then y else g z)

/-- `L_G`-analogue: the complement of `g([K] \ S)`. -/
def LGf (S : Finset (Fin K)) (g : Fin K → Fin L) : Finset (Fin L) :=
  Finset.univ \ ((Finset.univ.filter fun x => x ∉ S).image g)

lemma sim_congr (D : Fin L → QTree K L) (S : Finset (Fin K)) (g g' : Fin K → Fin L)
    (h : ∀ z, z ∉ S → g z = g' z) : sim D S g = sim D S g' := by
  funext y
  unfold sim
  congr 1
  funext z
  split_ifs with hz
  · rfl
  · exact h z hz

lemma LGf_congr (S : Finset (Fin K)) (g g' : Fin K → Fin L)
    (h : ∀ z, z ∉ S → g z = g' z) : LGf S g = LGf S g' := by
  unfold LGf
  congr 1
  apply Finset.image_congr
  intro z hz
  exact h z (Finset.mem_filter.mp hz).2

lemma sim_eq_run_of_not_hits (D : Fin L → QTree K L) (S : Finset (Fin K)) (G : Fin K → Fin L)
    (y : Fin L) (h : (D y).hits G S = false) : sim D S G y = (D y).run G := by
  unfold sim
  apply QTree.run_congr
  intro z hz
  have hzS : z ∉ S := by
    intro hzS
    have := (QTree.hits_eq_true_iff _ _ _).mpr ⟨z, hz, hzS⟩
    rw [h] at this
    exact Bool.false_ne_true this
  simp [hzS]

lemma sim_eq_run_at (D : Fin L → QTree K L) (S : Finset (Fin K)) (G : Fin K ↪ Fin L)
    (x : Fin K) (h : (D (G x)).hits G (S.erase x) = false) :
    sim D S G (G x) = (D (G x)).run G := by
  unfold sim
  apply QTree.run_congr
  intro z hz
  by_cases hzS : z ∈ S
  · have hzx : z = x := by
      by_contra hne
      have := (QTree.hits_eq_true_iff _ _ _).mpr ⟨z, hz, Finset.mem_erase.mpr ⟨hne, hzS⟩⟩
      rw [h] at this
      exact Bool.false_ne_true this
    subst hzx
    simp [hzS]
  · simp [hzS]

/-- Positions whose run queries another sample point. -/
def badPos (D : Fin L → QTree K L) (G : Fin K → Fin L) {m : ℕ} (s : Fin m → Fin K) :
    Finset (Fin m) :=
  Finset.univ.filter fun i => (D (G (s i))).hits G ((Finset.univ.image s).erase (s i)) = true

/-- Inputs whose run queries a sample point. -/
def hitY (D : Fin L → QTree K L) (G : Fin K → Fin L) {m : ℕ} (s : Fin m → Fin K) :
    Finset (Fin L) :=
  Finset.univ.filter fun y => (D y).hits G (Finset.univ.image s) = true

lemma sum_badPos_le (D : Fin L → QTree K L) (q : ℕ) (hq : ∀ y, (D y).depth ≤ q)
    (G : Fin K → Fin L) (m : ℕ) :
    ∑ s : Fin m → Fin K, (badPos D G s).card ≤ m * (m * (q * K ^ (m - 1))) := by
  classical
  have h1 : ∑ s : Fin m → Fin K, (badPos D G s).card =
      ∑ i : Fin m, (Finset.univ.filter fun s : Fin m → Fin K =>
        (D (G (s i))).hits G ((Finset.univ.image s).erase (s i)) = true).card := by
    unfold badPos
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  rw [h1]
  calc _ ≤ ∑ _i : Fin m, m * (q * K ^ (m - 1)) := by
        apply Finset.sum_le_sum
        intro i _
        have hsub : (Finset.univ.filter fun s : Fin m → Fin K =>
            (D (G (s i))).hits G ((Finset.univ.image s).erase (s i)) = true) ⊆
            (Finset.univ.filter fun j : Fin m => j ≠ i).biUnion
              (fun j => Finset.univ.filter fun s : Fin m → Fin K =>
                s j ∈ (D (G (s i))).qset G) := by
          intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
          obtain ⟨z, hzq, hz⟩ := (QTree.hits_eq_true_iff _ _ _).mp hs
          obtain ⟨hzne, hzim⟩ := Finset.mem_erase.mp hz
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hzim
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨j, ?_, hzq⟩
          rintro rfl
          exact hzne rfl
        refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
        calc _ ≤ ∑ _j ∈ (Finset.univ.filter fun j : Fin m => j ≠ i), q * K ^ (m - 1) := by
              apply Finset.sum_le_sum
              intro j hj
              have hji : j ≠ i := (Finset.mem_filter.mp hj).2
              apply count_coord j (fun s => (D (G (s i))).qset G) q
              · intro s s' hss
                rw [hss i (Ne.symm hji)]
              · intro s
                exact (QTree.card_qset_le _ _).trans (hq _)
          _ ≤ _ := by
              rw [Finset.sum_const, smul_eq_mul]
              apply Nat.mul_le_mul_right
              exact (Finset.card_filter_le _ _).trans (by simp)
    _ = _ := by simp

lemma sum_hitY_le (D : Fin L → QTree K L) (q : ℕ) (hq : ∀ y, (D y).depth ≤ q)
    (G : Fin K → Fin L) (m : ℕ) :
    ∑ s : Fin m → Fin K, (hitY D G s).card ≤ L * (m * (q * K ^ (m - 1))) := by
  classical
  have h1 : ∑ s : Fin m → Fin K, (hitY D G s).card =
      ∑ y : Fin L, (Finset.univ.filter fun s : Fin m → Fin K =>
        (D y).hits G (Finset.univ.image s) = true).card := by
    unfold hitY
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  rw [h1]
  calc _ ≤ ∑ _y : Fin L, m * (q * K ^ (m - 1)) := by
        apply Finset.sum_le_sum
        intro y _
        have hsub : (Finset.univ.filter fun s : Fin m → Fin K =>
            (D y).hits G (Finset.univ.image s) = true) ⊆
            (Finset.univ : Finset (Fin m)).biUnion
              (fun j => Finset.univ.filter fun s : Fin m → Fin K => s j ∈ (D y).qset G) := by
          intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
          obtain ⟨z, hzq, hz⟩ := (QTree.hits_eq_true_iff _ _ _).mp hs
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨j, hzq⟩
        refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
        calc _ ≤ ∑ _j : Fin m, q * K ^ (m - 1) := by
              apply Finset.sum_le_sum
              intro j _
              apply count_coord j (fun _ => (D y).qset G) q
              · intro s s' _; rfl
              · intro s
                exact (QTree.card_qset_le _ _).trans (hq _)
          _ = _ := by simp
    _ = _ := by simp

lemma card_LGf (S : Finset (Fin K)) (g : Fin K → Fin L)
    (hg : Set.InjOn g ↑(Finset.univ.filter fun x => x ∉ S)) :
    (LGf S g).card = L - (K - S.card) := by
  unfold LGf
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_image_of_injOn hg]
  congr 1
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

/-- The encoding count for one sample embedding `s`. -/
lemma encode_count (D : Fin L → QTree K L) {m : ℕ} (s : Fin m ↪ Fin K) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η ≤ 1) (hKL : K < L) :
    ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
        η * m ≤ |∑ i, b2r (sim D (Finset.univ.image s) G (G (s i))) -
          avg (LGf (Finset.univ.image s) G) (sim D (Finset.univ.image s) G) * m|).card : ℝ) ≤
      2 * Real.exp (-(m * η ^ 2 / 4)) * ((L - K + m : ℕ) : ℝ) ^ m *
        (L.descFactorial (K - m) : ℝ) := by
  classical
  set S : Finset (Fin K) := Finset.univ.image s with hS
  have hScard : S.card = m := by
    rw [hS, Finset.card_image_of_injective _ s.injective]; simp
  have hmK : m ≤ K := by
    have := Finset.card_le_univ S
    rw [hScard, Fintype.card_fin] at this; exact this
  let T := {x : Fin K // x ∉ S}
  have y0 : Fin L := ⟨0, by omega⟩
  let ext : (T ↪ Fin L) → Fin K → Fin L := fun H x => if h : x ∈ S then y0 else H ⟨x, h⟩
  let r : (Fin K ↪ Fin L) → (T ↪ Fin L) := fun G => (Function.Embedding.subtype _).trans G
  have hext : ∀ G : Fin K ↪ Fin L, ∀ z, z ∉ S → ext (r G) z = G z := by
    intro G z hz
    simp only [ext, r, hz, dif_neg, not_false_eq_true, Function.Embedding.trans_apply]
    rfl
  let cond : (T ↪ Fin L) → (Fin m → Fin L) → Prop := fun H φ =>
    η * m ≤ |∑ i, b2r (sim D S (ext H) (φ i)) - avg (LGf S (ext H)) (sim D S (ext H)) * m|
  let tgt : Finset (Σ _ : (T ↪ Fin L), (Fin m → Fin L)) :=
    (Finset.univ : Finset (T ↪ Fin L)).sigma
      (fun H => (Fintype.piFinset fun _ : Fin m => LGf S (ext H)).filter (cond H))
  let Φ : (Fin K ↪ Fin L) → (Σ _ : (T ↪ Fin L), (Fin m → Fin L)) :=
    fun G => ⟨r G, fun i => G (s i)⟩
  have hcardLG : ∀ H : T ↪ Fin L, (LGf S (ext H)).card = L - K + m := by
    intro H
    rw [card_LGf, hScard]
    · omega
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      simp only [ext, ha, hb, dif_neg, not_false_eq_true] at hab
      exact congrArg Subtype.val (H.injective hab)
  have hmaps : Set.MapsTo Φ ↑(Finset.univ.filter fun G : Fin K ↪ Fin L =>
        η * m ≤ |∑ i, b2r (sim D S G (G (s i))) - avg (LGf S G) (sim D S G) * m|) ↑tgt := by
    intro G hG
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hG
    simp only [tgt, Φ, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_univ, Set.mem_univ,
      true_and, Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset]
    have hsim : sim D S (ext (r G)) = sim D S G := sim_congr D S _ _ (hext G)
    have hLG : LGf S (ext (r G)) = LGf S G := LGf_congr S _ _ (hext G)
    refine ⟨?_, ?_⟩
    · intro i
      rw [hLG]
      unfold LGf
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_filter, not_exists, not_and]
      intro x hx hxe
      apply hx
      have := G.injective hxe
      rw [this, hS]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · show cond (r G) (fun i => G (s i))
      simp only [cond, hsim, hLG]
      exact hG
  have hinj : Set.InjOn Φ ↑(Finset.univ.filter fun G : Fin K ↪ Fin L =>
        η * m ≤ |∑ i, b2r (sim D S G (G (s i))) - avg (LGf S G) (sim D S G) * m|) := by
    intro G1 _ G2 _ h
    simp only [Φ, Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    have h2' := eq_of_heq h2
    ext x
    by_cases hx : x ∈ S
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hS ▸ hx)
      exact congrArg Fin.val (congrFun h2' i)
    · have := congrArg (fun H : T ↪ Fin L => H ⟨x, hx⟩) h1
      simp only [r, Function.Embedding.trans_apply, Function.Embedding.subtype_apply] at this
      exact congrArg Fin.val this
  have hle := Finset.card_le_card_of_injOn Φ hmaps hinj
  have hT : Fintype.card T = K - m := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    simp [hScard]
  have hU : ∀ H : T ↪ Fin L, (LGf S (ext H)).Nonempty := by
    intro H
    rw [← Finset.card_pos, hcardLG]
    omega
  calc _ ≤ (tgt.card : ℝ) := by exact_mod_cast hle
    _ = ∑ H : T ↪ Fin L, (((Fintype.piFinset fun _ : Fin m => LGf S (ext H)).filter
          (cond H)).card : ℝ) := by
        simp only [tgt, Finset.card_sigma]; push_cast; rfl
    _ ≤ ∑ _H : T ↪ Fin L, 2 * Real.exp (-(m * η ^ 2 / 4)) * ((L - K + m : ℕ) : ℝ) ^ m := by
        apply Finset.sum_le_sum
        intro H _
        have := chernoff_two (LGf S (ext H)) (hU H) (sim D S (ext H)) m η hη0 hη1
        rw [hcardLG H] at this
        exact this
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq, hT, Fintype.card_fin,
          nsmul_eq_mul]
        ring

end Sim

section Main
variable {K L : ℕ}

lemma sum_diff_le {α : Type} [DecidableEq α] (A E : Finset α) (f g : α → Bool)
    (h : ∀ a ∈ A, a ∉ E → f a = g a) :
    |∑ a ∈ A, b2r (f a) - ∑ a ∈ A, b2r (g a)| ≤ E.card := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ a ∈ A, (b2r (f a) - b2r (g a))| ≤ ∑ a ∈ A, |b2r (f a) - b2r (g a)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ A, (if a ∈ E then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases hE : a ∈ E
        · simp only [hE, if_true]
          rw [abs_le]; constructor <;>
            linarith [b2r_nonneg (f a), b2r_le_one (f a), b2r_nonneg (g a), b2r_le_one (g a)]
        · simp [hE, h a ha hE]
    _ = ((A.filter (· ∈ E)).card : ℝ) := by
        rw [Finset.card_filter]; push_cast; rfl
    _ ≤ E.card := by
        exact_mod_cast Finset.card_le_card (fun a ha => (Finset.mem_filter.mp ha).2)

lemma gap_of_good (D : Fin L → QTree K L) {m : ℕ} (hm : 0 < m) (s : Fin m ↪ Fin K)
    (G : Fin K ↪ Fin L) (ε : ℝ) (hε0 : 0 < ε) (hKL : 2 * K ≤ L) (hKε : (K : ℝ) / L ≤ ε / 16)
    (hgap : ε < |prX D G - prY D G|)
    (ha : |∑ i, b2r ((D (G (s i))).run G) - prX D G * m| < ε / 8 * m)
    (hc : ((badPos D G s).card : ℝ) ≤ ε * m / 16)
    (hd : ((hitY D G s).card : ℝ) ≤ ε * L / 16) :
    ε / 2 * m ≤ |∑ i, b2r (sim D (Finset.univ.image s) G (G (s i))) -
      avg (LGf (Finset.univ.image s) G) (sim D (Finset.univ.image s) G) * m| := by
  classical
  set S : Finset (Fin K) := Finset.univ.image s with hS
  set A := LGf S G with hA
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hScard : S.card = m := by
    rw [hS, Finset.card_image_of_injective _ s.injective]; simp
  have hmK : m ≤ K := by
    have := Finset.card_le_univ S
    rw [hScard, Fintype.card_fin] at this; exact this
  have hAcard : A.card = L - (K - m) := by
    rw [hA, card_LGf, hScard]
    intro a _ b _ hab
    exact G.injective hab
  have hLr : (0 : ℝ) < L := by
    have : 0 < L := by
      rcases Nat.eq_zero_or_pos K with h | h
      · rcases Nat.eq_zero_or_pos L with h' | h'
        · subst h; omega
        · exact h'
      · omega
    exact_mod_cast this
  have hAhalf : (L : ℝ) / 2 ≤ A.card := by
    rw [hAcard]
    have : L - K ≤ L - (K - m) := by omega
    have h2 : (L : ℝ) / 2 ≤ ((L - K : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      have : (2 * K : ℝ) ≤ L := by exact_mod_cast hKL
      linarith
    exact h2.trans (by exact_mod_cast this)
  have hApos : (0 : ℝ) < A.card := lt_of_lt_of_le (by positivity) hAhalf
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hApos
  -- positions
  have h1 : |∑ i, b2r (sim D S G (G (s i))) - ∑ i, b2r ((D (G (s i))).run G)| ≤ ε * m / 16 := by
    refine le_trans ?_ hc
    apply sum_diff_le Finset.univ (badPos D G s)
    intro i _ hi
    apply sim_eq_run_at
    simpa [badPos] using hi
  -- simulator vs run on A
  have h2 : |avg A (sim D S G) - avg A (fun y => (D y).run G)| ≤ ε / 8 := by
    refine (avg_diff_le A (hitY D G s) _ _ ?_).trans ?_
    · intro y _ hy
      apply sim_eq_run_of_not_hits
      simpa [hitY] using hy
    · rw [div_le_iff₀ hApos]
      calc ((hitY D G s).card : ℝ) ≤ ε * L / 16 := hd
        _ ≤ ε / 8 * A.card := by nlinarith
  -- A vs everything
  have h3 : |avg A (fun y => (D y).run G) - prY D G| ≤ ε / 16 := by
    refine (avg_subset_le A Finset.univ _ (Finset.subset_univ _) hAne).trans ?_
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      hAcard]
    refine le_trans ?_ hKε
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (show L - (L - (K - m)) ≤ K by omega)
  set X1 := ∑ i, b2r (sim D S G (G (s i)))
  set X0 := ∑ i, b2r ((D (G (s i))).run G)
  set a := avg A (sim D S G)
  set p := avg A (fun y => (D y).run G)
  set px := prX D G
  set py := prY D G
  have e3 : |a * m - p * m| ≤ ε / 8 * m := by
    rw [← sub_mul, abs_mul, abs_of_pos hmr]; exact mul_le_mul_of_nonneg_right h2 hmr.le
  have e4 : |p * m - py * m| ≤ ε / 16 * m := by
    rw [← sub_mul, abs_mul, abs_of_pos hmr]; exact mul_le_mul_of_nonneg_right h3 hmr.le
  have e5 : ε * m < |px * m - py * m| := by
    rw [← sub_mul, abs_mul, abs_of_pos hmr]; exact mul_lt_mul_of_pos_right hgap hmr
  rw [abs_le] at e3 e4 h1
  rw [abs_lt] at ha
  rcases lt_abs.mp e5 with h | h
  · rw [le_abs]; left; linarith
  · rw [le_abs]; right; linarith

theorem bad_le (D : Fin L → QTree K L) (m q : ℕ) (ε : ℝ) (hm : 0 < m) (hmK : 4 * m ^ 2 ≤ K)
    (hq : ∀ y, (D y).depth ≤ q) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hK : 2 ≤ K) (hL : K ^ 2 ≤ L)
    (hKε : (K : ℝ) / L ≤ ε / 16)
    (hA : 2 * Real.exp (-(m * (ε / 8) ^ 2 / 4)) ≤ 1 / 12)
    (hB : 192 * (m : ℝ) * q ≤ ε * K) :
    ((Finset.univ.filter fun G : Fin K ↪ Fin L => ε < |prX D G - prY D G|).card : ℝ) ≤
      8 * Real.exp (-(m * (ε / 2) ^ 2 / 4)) * (Fintype.card (Fin K ↪ Fin L) : ℝ) := by
  classical
  have hKL2 : 2 * K ≤ L := by nlinarith
  have hKL : K < L := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  let Good : (Fin K ↪ Fin L) → (Fin m → Fin K) → Prop := fun G s =>
    |∑ i, b2r ((D (G (s i))).run G) - prX D G * m| < ε / 8 * m ∧
      ((badPos D G s).card : ℝ) ≤ ε * m / 16 ∧ ((hitY D G s).card : ℝ) ≤ ε * L / 16
  have hKm : (K : ℝ) ^ m = K * (K : ℝ) ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  -- Step 1: few bad samples (functions)
  have step1 : ∀ G : Fin K ↪ Fin L,
      ((Finset.univ.filter fun s : Fin m → Fin K => ¬ Good G s).card : ℝ) ≤ (K : ℝ) ^ m / 4 := by
    intro G
    set F1 := Finset.univ.filter fun s : Fin m → Fin K =>
      ε / 8 * m ≤ |∑ i, b2r ((D (G (s i))).run G) - prX D G * m|
    set F2 := Finset.univ.filter fun s : Fin m → Fin K => ε * m / 16 < ((badPos D G s).card : ℝ)
    set F3 := Finset.univ.filter fun s : Fin m → Fin K => ε * L / 16 < ((hitY D G s).card : ℝ)
    have hsub : (Finset.univ.filter fun s : Fin m → Fin K => ¬ Good G s) ⊆ F1 ∪ F2 ∪ F3 := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Good, not_and_or, not_lt,
        not_le] at hs
      simp only [F1, F2, F3, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have c1 : (F1.card : ℝ) ≤ (K : ℝ) ^ m / 12 := by
      have := chernoff_two (Finset.univ : Finset (Fin K)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
        (fun x => (D (G x)).run G) m (ε / 8) (by positivity) (by linarith)
      · rw [Fintype.piFinset_univ, Finset.card_univ, Fintype.card_fin] at this
        have h' : avg Finset.univ (fun x => (D (G x)).run G) = prX D G := rfl
        rw [h'] at this
        calc (F1.card : ℝ) ≤ _ := this
          _ ≤ 1 / 12 * (K : ℝ) ^ m := mul_le_mul_of_nonneg_right hA (by positivity)
          _ = _ := by ring
    have hmq : 16 * ((m : ℝ) * (q * (K : ℝ) ^ (m - 1))) / ε ≤ (K : ℝ) ^ m / 12 := by
      rw [div_le_div_iff₀ hε0 (by norm_num), hKm]
      have : (0 : ℝ) ≤ (K : ℝ) ^ (m - 1) := by positivity
      nlinarith
    have c2 : (F2.card : ℝ) ≤ (K : ℝ) ^ m / 12 := by
      refine (markov_count _ (fun s => (badPos D G s).card) _ (by positivity)).trans ?_
      have hs := sum_badPos_le D q hq G m
      have hs' : (∑ s : Fin m → Fin K, ((badPos D G s).card : ℝ)) ≤
          (m : ℝ) * (m * (q * (K : ℝ) ^ (m - 1))) := by exact_mod_cast hs
      calc _ ≤ (m : ℝ) * (m * (q * (K : ℝ) ^ (m - 1))) / (ε * m / 16) :=
            div_le_div_of_nonneg_right hs' (by positivity)
        _ = 16 * ((m : ℝ) * (q * (K : ℝ) ^ (m - 1))) / ε := by
            field_simp
        _ ≤ _ := hmq
    have c3 : (F3.card : ℝ) ≤ (K : ℝ) ^ m / 12 := by
      refine (markov_count _ (fun s => (hitY D G s).card) _ (by positivity)).trans ?_
      have hs := sum_hitY_le D q hq G m
      have hs' : (∑ s : Fin m → Fin K, ((hitY D G s).card : ℝ)) ≤
          (L : ℝ) * (m * (q * (K : ℝ) ^ (m - 1))) := by exact_mod_cast hs
      calc _ ≤ (L : ℝ) * (m * (q * (K : ℝ) ^ (m - 1))) / (ε * L / 16) :=
            div_le_div_of_nonneg_right hs' (by positivity)
        _ = 16 * ((m : ℝ) * (q * (K : ℝ) ^ (m - 1))) / ε := by
            field_simp
        _ ≤ _ := hmq
    calc _ ≤ ((F1 ∪ F2 ∪ F3).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ (F1.card : ℝ) + F2.card + F3.card := by
          have := (Finset.card_union_le (F1 ∪ F2) F3).trans
            (Nat.add_le_add_right (Finset.card_union_le F1 F2) _)
          exact_mod_cast this
      _ ≤ _ := by linarith
  -- Step 2: transfer to embeddings
  set E := (Finset.univ : Finset (Fin m ↪ Fin K))
  have hE : (E.card : ℝ) = K.descFactorial m := by
    simp [E, Fintype.card_embedding_eq]
  have hKpow : (K : ℝ) ^ m ≤ 2 * E.card := by
    rw [hE]; exact pow_le_two_descFactorial K m hmK
  have step2 : ∀ G : Fin K ↪ Fin L, (E.card : ℝ) / 2 ≤ ((E.filter fun s : Fin m ↪ Fin K => Good G ⇑s).card : ℝ) := by
    intro G
    have hinj : ((E.filter fun s : Fin m ↪ Fin K => ¬ Good G ⇑s).card : ℝ) ≤
        ((Finset.univ.filter fun s : Fin m → Fin K => ¬ Good G s).card : ℝ) := by
      apply Nat.cast_le.mpr
      apply Finset.card_le_card_of_injOn (fun s : Fin m ↪ Fin K => (⇑s : Fin m → Fin K))
      · intro s hs
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
        exact hs.2
      · intro a _ b _ h
        exact DFunLike.coe_injective (F := Fin m ↪ Fin K) h
    have hsplit := Finset.card_filter_add_card_filter_not (s := E) (fun s : Fin m ↪ Fin K => Good G ⇑s)
    have hsplit' : ((E.filter fun s : Fin m ↪ Fin K => Good G ⇑s).card : ℝ) +
        ((E.filter fun s : Fin m ↪ Fin K => ¬ Good G ⇑s).card : ℝ) = E.card := by exact_mod_cast hsplit
    have := step1 G
    linarith
  -- Step 3: per-sample count
  set Bad := Finset.univ.filter fun G : Fin K ↪ Fin L => ε < |prX D G - prY D G|
  have hN : 4 * m ^ 2 ≤ L - K + m := by
    have : K ≤ L - K := by
      have : K * 2 ≤ K ^ 2 := by nlinarith
      omega
    omega
  have hB_eq : (Fintype.card (Fin K ↪ Fin L) : ℝ) =
      ((L - K + m).descFactorial m : ℝ) * (L.descFactorial (K - m) : ℝ) := by
    have hmK' : m ≤ K := by nlinarith
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    have := Nat.descFactorial_mul_descFactorial (n := L) (k := K - m) (m := K) (Nat.sub_le K m)
    rw [show K - (K - m) = m by omega, show L - (K - m) = L - K + m by omega] at this
    rw [← this]; push_cast; ring
  have step3 : ∀ s ∈ E, ((Bad.filter fun G => Good G ⇑s).card : ℝ) ≤
      4 * Real.exp (-(m * (ε / 2) ^ 2 / 4)) * (Fintype.card (Fin K ↪ Fin L) : ℝ) := by
    intro s _
    have hsub : (Bad.filter fun G => Good G ⇑s) ⊆ Finset.univ.filter fun G : Fin K ↪ Fin L =>
        ε / 2 * m ≤ |∑ i, b2r (sim D (Finset.univ.image s) G (G (s i))) -
          avg (LGf (Finset.univ.image s) G) (sim D (Finset.univ.image s) G) * m| := by
      intro G hG
      simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, Good] at hG
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact gap_of_good D hm s G ε hε0 hKL2 hKε hG.1 hG.2.1 hG.2.2.1 hG.2.2.2
    have hc := encode_count D s (ε / 2) (by positivity) (by linarith) hKL
    have hpow := pow_le_two_descFactorial (L - K + m) m hN
    calc _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ _ := hc
      _ ≤ 2 * Real.exp (-(m * (ε / 2) ^ 2 / 4)) * (2 * ((L - K + m).descFactorial m : ℝ)) *
            (L.descFactorial (K - m) : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by rw [hB_eq]; ring
  -- double counting
  have hdc : ∑ G ∈ Bad, ((E.filter fun s : Fin m ↪ Fin K => Good G ⇑s).card : ℝ) =
      ∑ s ∈ E, ((Bad.filter fun G => Good G ⇑s).card : ℝ) := by
    simp_rw [Finset.card_filter]
    push_cast
    exact Finset.sum_comm
  have hlow : (Bad.card : ℝ) * ((E.card : ℝ) / 2) ≤ ∑ G ∈ Bad, ((E.filter fun s : Fin m ↪ Fin K => Good G ⇑s).card : ℝ) := by
    calc (Bad.card : ℝ) * ((E.card : ℝ) / 2) = ∑ _G ∈ Bad, ((E.card : ℝ) / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun G _ => step2 G)
  have hup : ∑ s ∈ E, ((Bad.filter fun G => Good G ⇑s).card : ℝ) ≤
      E.card * (4 * Real.exp (-(m * (ε / 2) ^ 2 / 4)) * (Fintype.card (Fin K ↪ Fin L) : ℝ)) := by
    calc _ ≤ ∑ _s ∈ E, (4 * Real.exp (-(m * (ε / 2) ^ 2 / 4)) *
          (Fintype.card (Fin K ↪ Fin L) : ℝ)) := Finset.sum_le_sum step3
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hEpos : (0 : ℝ) < E.card := by
    rw [hE]; exact_mod_cast Nat.descFactorial_pos.mpr (by nlinarith)
  have := hlow.trans (hdc ▸ hup)
  nlinarith

end Main

end ObfImpossibility.PseudoOracle

set_option maxHeartbeats 1000000 in
open ObfImpossibility.PseudoOracle in
theorem solution :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K₀ : ℕ, ∀ K L : ℕ, K₀ ≤ K → K ^ 2 ≤ L →
      ∀ D : Fin L → QTree K L, (∀ y, ((D y).depth : ℝ) ≤ (K : ℝ) ^ δ) →
        1 - (2 : ℝ) ^ (-(K : ℝ) ^ δ) ≤
          ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
              |prX D G - prY D G| ≤ 1 / (K : ℝ) ^ δ).card : ℝ) /
            (Fintype.card (Fin K ↪ Fin L) : ℝ) := by
  classical
  refine ⟨(1 : ℝ) / 10, by norm_num, 30 ^ 10, ?_⟩
  intro K L hK hL D hD
  set k : ℝ := (K : ℝ) ^ ((1 : ℝ) / 10) with hk
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hk10 : k ^ 10 = K := by
    rw [hk, ← Real.rpow_natCast, ← Real.rpow_mul hK0]; norm_num
  have hk30 : 30 ≤ k := by
    have h1 : ((30 : ℝ) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) = 30 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← h1, hk]
    apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast hK) (by norm_num)
  have hkpos : 0 < k := by linarith
  have hk3 : 27000 ≤ k ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hk30 3; norm_num at this; linarith
  have hk5eq : k ^ 5 = k ^ 3 * k ^ 2 := by ring
  have hk9 : k ^ 9 = k ^ 3 * k ^ 3 * k ^ 3 := by ring
  have hk10' : k ^ 10 = k ^ 5 * k ^ 5 := by ring
  have hk2pos : 0 < k ^ 2 := by positivity
  have hk9ge : 16 ≤ k ^ 9 := by
    have := pow_le_pow_left₀ (by norm_num) hk30 9; norm_num at this; linarith
  have hk10k : k ^ 10 = k * k ^ 9 := by ring
  have hk5pos : 0 < k ^ 5 := by positivity
  -- the sample size
  set n := Nat.sqrt K with hn
  set m := n / 2 with hm
  have hn1 : n ^ 2 ≤ K := Nat.sqrt_le' K
  have hn2 : K < (n + 1) ^ 2 := Nat.lt_succ_sqrt' K
  have hmn : 2 * m ≤ n ∧ n ≤ 2 * m + 1 := by omega
  have hnk : (n : ℝ) ≤ k ^ 5 := by
    have : (n : ℝ) ^ 2 ≤ (k ^ 5) ^ 2 := by
      rw [← pow_mul, show 5 * 2 = 10 by norm_num, hk10]; exact_mod_cast hn1
    exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg n) hk5pos.le (by norm_num)).mp this
  have hnk' : k ^ 5 < (n : ℝ) + 1 := by
    have : (k ^ 5) ^ 2 < ((n : ℝ) + 1) ^ 2 := by
      rw [← pow_mul, show 5 * 2 = 10 by norm_num, hk10]; exact_mod_cast hn2
    exact (pow_lt_pow_iff_left₀ hk5pos.le (by positivity) (by norm_num)).mp this
  have hmr1 : (m : ℝ) ≤ k ^ 5 / 2 := by
    have : (2 * m : ℝ) ≤ n := by exact_mod_cast hmn.1
    linarith
  have hmr2 : k ^ 5 / 4 ≤ (m : ℝ) := by
    have : (n : ℝ) ≤ 2 * m + 1 := by exact_mod_cast hmn.2
    nlinarith
  have hm0 : 0 < m := by
    have : (0 : ℝ) < m := by nlinarith
    exact_mod_cast this
  have hmK : 4 * m ^ 2 ≤ K := by
    have : (2 * m) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hmn.1 2
    nlinarith
  -- query bound
  set q := ⌊k⌋₊ with hq
  have hqD : ∀ y, (D y).depth ≤ q := fun y => Nat.le_floor (hD y)
  have hqk : (q : ℝ) ≤ k := Nat.floor_le hkpos.le
  set ε : ℝ := 1 / k with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by rw [hε, div_le_one hkpos]; linarith
  have hK2 : 2 ≤ K := le_trans (by norm_num) hK
  have hLr : (K : ℝ) * K ≤ L := by
    have : K * K ≤ L := by nlinarith
    exact_mod_cast this
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKε : (K : ℝ) / L ≤ ε / 16 := by
    have hLpos : (0 : ℝ) < L := by nlinarith
    rw [div_le_iff₀ hLpos, hε]
    have h16 : 16 * k ≤ K := by rw [← hk10, hk10k]; nlinarith
    rw [div_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hA : 2 * Real.exp (-(m * (ε / 8) ^ 2 / 4)) ≤ 1 / 12 := by
    have hx : 26 ≤ (m : ℝ) * (ε / 8) ^ 2 / 4 := by
      have : (m : ℝ) * (ε / 8) ^ 2 / 4 = m / (256 * k ^ 2) := by rw [hε]; field_simp; ring
      rw [this, le_div_iff₀ (by positivity)]
      nlinarith
    have : Real.exp (-(m * (ε / 8) ^ 2 / 4)) ≤ Real.exp (-26) := Real.exp_le_exp.mpr (by linarith)
    have h26 : 27 ≤ Real.exp 26 := by linarith [Real.add_one_le_exp (26 : ℝ)]
    have : Real.exp (-26) ≤ 1 / 27 := by
      rw [Real.exp_neg, inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h26
    linarith
  have hB : 192 * (m : ℝ) * q ≤ ε * K := by
    have : ε * K = k ^ 9 := by
      rw [hε, ← hk10, one_div, hk10k, ← mul_assoc, inv_mul_cancel₀ hkpos.ne', one_mul]
    rw [this, hk9]
    have h1 : 192 * (m : ℝ) * q ≤ 96 * k ^ 6 := by
      have : (m : ℝ) * q ≤ k ^ 5 / 2 * k := mul_le_mul hmr1 hqk (Nat.cast_nonneg _) (by positivity)
      nlinarith
    have h2 : 96 * k ^ 6 ≤ k ^ 3 * k ^ 3 * k ^ 3 := by
      have : k ^ 6 = k ^ 3 * k ^ 3 := by ring
      rw [this]
      have ha : 0 ≤ k ^ 3 := by positivity
      nlinarith [mul_nonneg (mul_nonneg ha ha) (sub_nonneg.mpr (show (96 : ℝ) ≤ k ^ 3 by linarith))]
    linarith
  have hbad := bad_le D m q ε hm0 hmK hqD hε0 hε1 hK2 hL hKε hA hB
  -- the final exponent
  have hfin : 8 * Real.exp (-(m * (ε / 2) ^ 2 / 4)) ≤ (2 : ℝ) ^ (-k) := by
    have hy : k + 7 ≤ (m : ℝ) * (ε / 2) ^ 2 / 4 := by
      have : (m : ℝ) * (ε / 2) ^ 2 / 4 = m / (16 * k ^ 2) := by rw [hε]; field_simp; ring
      rw [this, le_div_iff₀ (by positivity)]
      nlinarith
    have h1 : Real.exp (-(m * (ε / 2) ^ 2 / 4)) ≤ Real.exp (-k - 7) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : 8 * Real.exp (-k - 7) ≤ Real.exp (-k) := by
      have : Real.exp (-k - 7) = Real.exp (-k) / Real.exp 7 := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg 7]; ring
      rw [this]
      have h7 : 8 ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
      rw [mul_div_assoc', div_le_iff₀ (Real.exp_pos 7)]
      nlinarith [Real.exp_pos (-k)]
    have h3 : Real.exp (-k) ≤ (2 : ℝ) ^ (-k) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      apply Real.exp_le_exp.mpr
      have := Real.log_two_lt_d9
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
      nlinarith
    linarith
  -- assemble
  have hB0 : (0 : ℝ) < Fintype.card (Fin K ↪ Fin L) := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    exact_mod_cast Nat.descFactorial_pos.mpr (by nlinarith)
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin K ↪ Fin L)))
    (fun G => |prX D G - prY D G| ≤ 1 / k)
  have hneg : (Finset.univ.filter fun G : Fin K ↪ Fin L => ¬ |prX D G - prY D G| ≤ 1 / k) =
      Finset.univ.filter fun G : Fin K ↪ Fin L => ε < |prX D G - prY D G| := by
    apply Finset.filter_congr
    intro G _
    rw [not_le]
  rw [hneg, Finset.card_univ] at hsplit
  have hsplit' : ((Finset.univ.filter fun G : Fin K ↪ Fin L => |prX D G - prY D G| ≤ 1 / k).card : ℝ)
      = (Fintype.card (Fin K ↪ Fin L) : ℝ) -
        ((Finset.univ.filter fun G : Fin K ↪ Fin L => ε < |prX D G - prY D G|).card : ℝ) := by
    rw [eq_sub_iff_add_eq]; exact_mod_cast hsplit
  rw [hsplit', le_div_iff₀ hB0]
  have : ((Finset.univ.filter fun G : Fin K ↪ Fin L => ε < |prX D G - prY D G|).card : ℝ) ≤
      (2 : ℝ) ^ (-k) * (Fintype.card (Fin K ↪ Fin L) : ℝ) :=
    hbad.trans (mul_le_mul_of_nonneg_right hfin hB0.le)
  nlinarith

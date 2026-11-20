-- Prove2me | solution 1 for XorParallelRepetition.Exponential.tensorized_correlation_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:02:24.778175+00:00
-- url     : https://prove2.me/submissions/65d66554-9599-4a0b-a61b-ddd11b2d5f28

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_Games
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_Contradiction
import Definitions.Def_XorParallelRepetition_Exponential_Gluing
import Theorems.Thm_XorParallelRepetition_Exponential_finite_gluing_chain
universe u

section
set_option autoImplicit false

open scoped ENNReal ComplexConjugate

namespace XorParallelRepetition.Dev.Tensor

open XorParallelRepetition.Exponential
open Classical

section Sums

variable {α β γ : Type*}

theorem summable_w_mul (w : α → ℝ≥0∞) (hw : ∑' a, w a ≠ ∞) (F : α → ℂ) (C : ℝ)
    (hF : ∀ a, ‖F a‖ ≤ C) : Summable fun a => ((w a).toReal : ℂ) * F a := by
  refine Summable.of_norm_bounded ((ENNReal.summable_toReal hw).mul_left C) fun a => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg, mul_comm]
  exact mul_le_mul_of_nonneg_right (hF a) ENNReal.toReal_nonneg

theorem summable_pmf_mul (μ : PMF α) (F : α → ℂ) (C : ℝ) (hF : ∀ a, ‖F a‖ ≤ C) :
    Summable fun a => ((μ a).toReal : ℂ) * F a :=
  summable_w_mul μ μ.tsum_coe_ne_top F C hF

theorem summable_pmf_real (μ : PMF α) (h : α → ℝ) (h0 : ∀ a, 0 ≤ h a) (h1 : ∀ a, h a ≤ 1) :
    Summable fun a => (μ a).toReal * h a :=
  Summable.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (h0 a))
    (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (h1 a))
    (ENNReal.summable_toReal μ.tsum_coe_ne_top)

theorem tsum_pmf_toReal (μ : PMF α) : ∑' a, (μ a).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun a => PMF.apply_ne_top _ _), PMF.tsum_coe,
    ENNReal.toReal_one]

/-- Fubini for weighted bounded double sums. -/
theorem tsum_comm_w (w : α → β → ℝ≥0∞) (hw : ∑' a, ∑' b, w a b ≠ ∞) (H : α → β → ℂ) (C : ℝ)
    (hH : ∀ a b, ‖H a b‖ ≤ C) :
    ∑' a, ∑' b, ((w a b).toReal : ℂ) * H a b = ∑' b, ∑' a, ((w a b).toReal : ℂ) * H a b := by
  have hs : Summable (Function.uncurry fun a b => ((w a b).toReal : ℂ) * H a b) :=
    summable_w_mul (fun x : α × β => w x.1 x.2) (by rw [ENNReal.tsum_prod]; exact hw)
      (fun x => H x.1 x.2) C (fun x => hH _ _)
  exact hs.tsum_comm.symm

theorem tsum_prod_w (w : α × β → ℝ≥0∞) (hw : ∑' x, w x ≠ ∞) (H : α × β → ℂ) (C : ℝ)
    (hH : ∀ x, ‖H x‖ ≤ C) :
    ∑' x, ((w x).toReal : ℂ) * H x = ∑' a, ∑' b, ((w (a, b)).toReal : ℂ) * H (a, b) :=
  (summable_w_mul w hw H C hH).tsum_prod

theorem expect_pure (a : α) (F : α → ℂ) : expect (PMF.pure a) F = F a := by
  unfold expect
  rw [tsum_eq_single a]
  · simp
  · intro b hb
    simp [PMF.pure_apply, hb]

theorem expect_bind (μ : PMF α) (f : α → PMF β) (F : β → ℂ) (C : ℝ) (hF : ∀ b, ‖F b‖ ≤ C) :
    expect (μ.bind f) F = expect μ fun a => expect (f a) F := by
  unfold expect
  simp only [PMF.bind_apply]
  have h1 : ∀ b, (((∑' a, μ a * f a b).toReal : ℝ) : ℂ) * F b =
      ∑' a, (((μ a * f a b).toReal : ℝ) : ℂ) * F b := by
    intro b
    rw [ENNReal.tsum_toReal_eq (fun a => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _)), Complex.ofReal_tsum, tsum_mul_right]
  simp_rw [h1]
  rw [tsum_comm_w (fun b a => μ a * f a b) ?_ (fun b _ => F b) C (fun _ _ => hF _)]
  · congr 1
    funext a
    simp_rw [ENNReal.toReal_mul, Complex.ofReal_mul, mul_assoc]
    rw [tsum_mul_left]
  · rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one, PMF.tsum_coe]
    exact ENNReal.one_ne_top

theorem expect_map (μ : PMF α) (g : α → β) (F : β → ℂ) (C : ℝ) (hF : ∀ b, ‖F b‖ ≤ C) :
    expect (μ.map g) F = expect μ (fun a => F (g a)) := by
  rw [← PMF.bind_pure_comp, expect_bind μ _ F C hF]
  congr 1
  funext a
  exact expect_pure _ _

theorem expect_mul_const (μ : PMF α) (F : α → ℂ) (c : ℂ) :
    expect μ (fun a => F a * c) = expect μ F * c := by
  unfold expect
  rw [← tsum_mul_right]
  congr 1
  funext a
  ring

theorem expect_const_mul (μ : PMF α) (F : α → ℂ) (c : ℂ) :
    expect μ (fun a => c * F a) = c * expect μ F := by
  unfold expect
  rw [← tsum_mul_left]
  congr 1
  funext a
  ring

theorem norm_prod_le_one {ι : Type*} (s : Finset ι) (g : ι → ℂ) (hg : ∀ i, ‖g i‖ ≤ 1) :
    ‖∏ i ∈ s, g i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hg i)

end Sums

section Iid

variable {α β : Type*}

theorem iid_succ (μ : PMF α) (n : ℕ) :
    iidPMF μ (n + 1) = μ.bind fun a => (iidPMF μ n).map (Fin.cons a) := rfl

theorem iid_map (μ : PMF α) (g : α → β) :
    ∀ n, iidPMF (μ.map g) n = (iidPMF μ n).map fun s j => g (s j)
  | 0 => by
    simp only [iidPMF]
    rw [PMF.pure_map]
    congr 1
    funext j
    exact j.elim0
  | n + 1 => by
    rw [iid_succ, iid_succ, iid_map μ g n, PMF.bind_map, PMF.map_bind]
    congr 1
    funext a
    simp only [Function.comp_apply, PMF.map_comp]
    congr 1
    funext t j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp

theorem map_cons_apply {n : ℕ} (ν : PMF (Fin n → α)) (a : α) (s : Fin (n + 1) → α) :
    (ν.map (Fin.cons a)) s = if s 0 = a then ν (Fin.tail s) else 0 := by
  rw [PMF.map_apply]
  split_ifs with h
  · rw [tsum_eq_single (Fin.tail s)]
    · rw [if_pos]
      rw [← h, Fin.cons_self_tail]
    · intro t ht
      rw [if_neg]
      rintro rfl
      exact ht (by simp)
  · refine ENNReal.tsum_eq_zero.2 fun t => if_neg ?_
    rintro rfl
    exact h (Fin.cons_zero _ _)

theorem iid_apply (μ : PMF α) : ∀ (n : ℕ) (s : Fin n → α), iidPMF μ n s = ∏ j, μ (s j)
  | 0, s => by
    simp only [iidPMF, PMF.pure_apply, Finset.univ_eq_empty, Finset.prod_empty]
    rw [if_pos]
    funext j
    exact j.elim0
  | n + 1, s => by
    rw [iid_succ, PMF.bind_apply, Fin.prod_univ_succ]
    simp_rw [map_cons_apply]
    rw [tsum_eq_single (s 0)]
    · rw [if_pos rfl, iid_apply μ n]
      rfl
    · intro b hb
      rw [if_neg (Ne.symm hb), mul_zero]

theorem expect_iid_prod (μ : PMF α) :
    ∀ (n : ℕ) (g : Fin n → α → ℂ), (∀ j a, ‖g j a‖ ≤ 1) →
      expect (iidPMF μ n) (fun s => ∏ j, g j (s j)) = ∏ j, expect μ (g j)
  | 0, g, _ => by
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact expect_pure _ _
  | n + 1, g, hg => by
    have hb : ∀ s : Fin (n + 1) → α, ‖∏ j, g j (s j)‖ ≤ 1 :=
      fun s => norm_prod_le_one _ _ fun j => hg _ _
    rw [iid_succ, expect_bind _ _ _ 1 hb]
    have h2 : ∀ a, expect ((iidPMF μ n).map (Fin.cons a)) (fun s => ∏ j, g j (s j)) =
        g 0 a * ∏ j : Fin n, expect μ (g j.succ) := by
      intro a
      rw [expect_map _ _ _ 1 hb]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [expect_const_mul, expect_iid_prod μ n (fun j => g j.succ) (fun j a => hg _ _)]
    simp_rw [h2]
    rw [expect_mul_const, Fin.prod_univ_succ]

end Iid

section Pair

variable {α β γ K : Type*}

/-- The law of a pair `(x, y)` with `x ∼ ν` and `y ∼ ν` conditioned on `κ y = κ x`. -/
noncomputable def pairLaw (ν : PMF α) (κ : α → K) : PMF (α × α) :=
  ν.bindOnSupport fun x hx => (ν.filter {y | κ y = κ x} ⟨x, rfl, hx⟩).map (Prod.mk x)

theorem map_prodMk_apply (q : PMF β) (x x' : α) (y : β) :
    (q.map (Prod.mk x)) (x', y) = if x' = x then q y else 0 := by
  rw [PMF.map_apply]
  split_ifs with h
  · subst h
    rw [tsum_eq_single y]
    · simp
    · intro b hb
      simp [Ne.symm hb]
  · refine ENNReal.tsum_eq_zero.2 fun b => if_neg ?_
    intro e
    exact h (Prod.mk.inj e).1

theorem map_key_apply (ν : PMF α) (κ : α → K) (c : K) :
    (ν.map κ) c = ∑' z, if κ z = c then ν z else 0 := by
  rw [PMF.map_apply]
  simp_rw [eq_comm (a := c)]

theorem pairLaw_apply (ν : PMF α) (κ : α → K) (x y : α) :
    pairLaw ν κ (x, y) = if κ y = κ x then ν x * ν y * ((ν.map κ) (κ x))⁻¹ else 0 := by
  rw [pairLaw, PMF.bindOnSupport_apply, tsum_eq_single x]
  · by_cases hx : ν x = 0
    · simp [hx]
    · rw [dif_neg hx, map_prodMk_apply, if_pos rfl, PMF.filter_apply, map_key_apply]
      have hs : ∀ z, ({y | κ y = κ x} : Set α).indicator ν z = if κ z = κ x then ν z else 0 :=
        fun z => by simp [Set.indicator_apply]
      simp_rw [hs]
      split_ifs <;> ring
  · intro x' hx'
    split_ifs with h
    · simp
    · rw [map_prodMk_apply, if_neg (Ne.symm hx'), mul_zero]

theorem map_bindOnSupport (p : PMF α) (f : ∀ a ∈ p.support, PMF β) (g : β → γ) :
    (p.bindOnSupport f).map g = p.bindOnSupport fun a h => (f a h).map g := by
  ext c
  simp only [PMF.map_apply, PMF.bindOnSupport_apply]
  have e : ∀ b, (if c = g b then ∑' a, p a * (if h : p a = 0 then 0 else f a h b) else 0) =
      ∑' a, p a * (if h : p a = 0 then 0 else if c = g b then f a h b else 0) := by
    intro b
    split_ifs with hc
    · rfl
    · symm
      refine ENNReal.tsum_eq_zero.2 fun a => ?_
      split_ifs <;> simp
  simp_rw [e]
  rw [ENNReal.tsum_comm]
  congr 1
  funext a
  split_ifs with h0
  · simp
  · rw [ENNReal.tsum_mul_left]

theorem filter_congr (q : PMF α) {s t : Set α} (hst : s = t) (hs : ∃ a ∈ s, a ∈ q.support)
    (ht : ∃ a ∈ t, a ∈ q.support) : q.filter s hs = q.filter t ht := by
  subst hst
  rfl

theorem pairLaw_iid (μ : PMF α) (k : α → K) (n : ℕ) :
    pairLaw (iidPMF μ n) (fun s j => k (s j)) =
      (iidPMF (pairLaw μ k) n).map fun x => (fun j => (x j).1, fun j => (x j).2) := by
  ext ⟨s, s'⟩
  rw [PMF.map_apply, tsum_eq_single (fun j => (s j, s' j))]
  · rw [if_pos rfl, iid_apply, pairLaw_apply, ← iid_map, iid_apply, iid_apply, iid_apply]
    simp_rw [pairLaw_apply]
    split_ifs with h
    · have h' : ∀ j, k (s' j) = k (s j) := fun j => congrFun h j
      simp_rw [if_pos (h' _)]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ENNReal.prod_inv_distrib]
      intro i _ j _ _
      exact Or.inr (PMF.apply_ne_top _ _)
    · have : ∃ j, k (s' j) ≠ k (s j) := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      obtain ⟨j, hj⟩ := this
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)).symm
  · intro x hx
    rw [if_neg]
    intro e
    apply hx
    funext j
    simp only [Prod.mk.injEq] at e
    rw [e.1, e.2]

end Pair

section Glue


variable {p : ℕ} {κ : Type}

/-- The key of a challenge over the players of `I`. -/
def keyI {Φ : GeneralizedXorGame.{u} p κ} (I : Finset κ) (ω : (∀ i, Φ.Q i) × ZMod p) :
    ∀ i : {i // i ∈ I}, Φ.Q i.1 :=
  fun i => ω.1 i.1

theorem glue_eq (Φ : GeneralizedXorGame.{u} p κ) (I : Finset κ) :
    (Φ.glue I).μ = (pairLaw Φ.μ (keyI (Φ := Φ) I)).map
      (fun x => Φ.glueChallenge I x.1 x.2) := by
  rw [pairLaw, map_bindOnSupport]
  show Φ.μ.bindOnSupport _ = _
  congr 1
  funext x hx
  rw [PMF.map_comp]
  congr 1
  apply filter_congr
  ext y
  simp only [GeneralizedXorGame.fiber, Set.mem_ofPred_eq, keyI, funext_iff, Subtype.forall]

end Glue


section CS

variable {α K : Type*}

theorem norm_tsum_w_le (w : α → ℝ≥0∞) (hw : ∑' a, w a ≠ ∞) (F : α → ℂ)
    (hF : ∀ a, ‖F a‖ ≤ 1) : ‖∑' a, ((w a).toReal : ℂ) * F a‖ ≤ (∑' a, w a).toReal := by
  have hs : Summable fun a => (w a).toReal := ENNReal.summable_toReal hw
  have hb : ∀ a, ‖((w a).toReal : ℂ) * F a‖ ≤ (w a).toReal := by
    intro a
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (hF a)
  have hs' : Summable fun a => ‖((w a).toReal : ℂ) * F a‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs
  calc ‖∑' a, ((w a).toReal : ℂ) * F a‖ ≤ ∑' a, ‖((w a).toReal : ℂ) * F a‖ :=
        norm_tsum_le_tsum_norm hs'
    _ ≤ ∑' a, (w a).toReal := Summable.tsum_le_tsum hb hs' hs
    _ = (∑' a, w a).toReal := (ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hw)).symm

theorem norm_expect_le_one (μ : PMF α) (F : α → ℂ) (hF : ∀ a, ‖F a‖ ≤ 1) :
    ‖expect μ F‖ ≤ 1 := by
  have := norm_tsum_w_le μ μ.tsum_coe_ne_top F hF
  rwa [PMF.tsum_coe, ENNReal.toReal_one] at this

theorem jensen (μ : PMF α) (h : α → ℝ) (h0 : ∀ a, 0 ≤ h a) (h1 : ∀ a, h a ≤ 1) :
    (∑' a, (μ a).toReal * h a) ^ 2 ≤ ∑' a, (μ a).toReal * h a ^ 2 := by
  set m := ∑' a, (μ a).toReal * h a
  have s1 := summable_pmf_real μ h h0 h1
  have s2 := summable_pmf_real μ (fun a => h a ^ 2) (fun a => sq_nonneg _)
    (fun a => by nlinarith [h0 a, h1 a])
  have s0 : Summable fun a => (μ a).toReal := ENNReal.summable_toReal μ.tsum_coe_ne_top
  have key : ∑' a, (μ a).toReal * (h a - m) ^ 2 =
      ∑' a, (μ a).toReal * h a ^ 2 - 2 * m * m + m ^ 2 * ∑' a, (μ a).toReal := by
    rw [tsum_congr (fun a => show (μ a).toReal * (h a - m) ^ 2 =
        ((μ a).toReal * h a ^ 2 - 2 * m * ((μ a).toReal * h a)) + m ^ 2 * (μ a).toReal by ring),
      Summable.tsum_add (s2.sub (s1.mul_left _)) (s0.mul_left _),
      Summable.tsum_sub s2 (s1.mul_left _), tsum_mul_left, tsum_mul_left]
  have hnn : 0 ≤ ∑' a, (μ a).toReal * (h a - m) ^ 2 :=
    tsum_nonneg fun a => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  rw [key, tsum_pmf_toReal] at hnn
  nlinarith

theorem pairLaw_symm (ν : PMF α) (κ : α → K) (x y : α) :
    pairLaw ν κ (x, y) = pairLaw ν κ (y, x) := by
  rw [pairLaw_apply, pairLaw_apply]
  by_cases h : κ y = κ x
  · rw [if_pos h, if_pos h.symm, h, mul_comm (ν x)]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem pairLaw_eq_zero (ν : PMF α) (κ : α → K) (x y : α) (h : κ x ≠ κ y) :
    pairLaw ν κ (x, y) = 0 := by
  rw [pairLaw_apply, if_neg (Ne.symm h)]

/-- The conditional weight of `y` given `x`. -/
noncomputable def condW (ν : PMF α) (κ : α → K) (x y : α) : ℝ≥0∞ :=
  if κ y = κ x then ν y * ((ν.map κ) (κ x))⁻¹ else 0

theorem pairLaw_eq_mul (ν : PMF α) (κ : α → K) (x y : α) :
    pairLaw ν κ (x, y) = ν x * condW ν κ x y := by
  rw [pairLaw_apply, condW]
  split_ifs <;> simp [mul_assoc]

theorem tsum_condW (ν : PMF α) (κ : α → K) (x : α) :
    ∑' y, condW ν κ x y = (ν.map κ) (κ x) * ((ν.map κ) (κ x))⁻¹ := by
  have e : ∀ y, condW ν κ x y = (if κ y = κ x then ν y else 0) * ((ν.map κ) (κ x))⁻¹ :=
    fun y => by unfold condW; split_ifs <;> simp
  simp_rw [e]
  rw [ENNReal.tsum_mul_right, map_key_apply ν κ (κ x)]

theorem tsum_condW_le (ν : PMF α) (κ : α → K) (x : α) : ∑' y, condW ν κ x y ≤ 1 := by
  rw [tsum_condW]
  exact ENNReal.mul_inv_le_one _

theorem tsum_pairLaw_right (ν : PMF α) (κ : α → K) (x : α) :
    ∑' y, pairLaw ν κ (x, y) = ν x := by
  simp_rw [pairLaw_eq_mul]
  rw [ENNReal.tsum_mul_left, tsum_condW]
  by_cases hx : ν x = 0
  · rw [hx, zero_mul]
  · have h1 : ν x ≤ (ν.map κ) (κ x) := by
      rw [map_key_apply]
      have := ENNReal.le_tsum (f := fun z => if κ z = κ x then ν z else 0) x
      simpa using this
    have h0 : (ν.map κ) (κ x) ≠ 0 := fun h => hx (by rw [h] at h1; exact le_antisymm h1 bot_le)
    rw [ENNReal.mul_inv_cancel h0 (PMF.apply_ne_top _ _), mul_one]

theorem condW_congr (ν : PMF α) (κ : α → K) (x x' : α) (h : κ x = κ x') :
    condW ν κ x = condW ν κ x' := by
  funext y
  unfold condW
  rw [h]

/-- The conditional expectation of `B` given the key of `x`. -/
noncomputable def condE (ν : PMF α) (κ : α → K) (B : α → ℂ) (x : α) : ℂ :=
  ∑' y, ((condW ν κ x y).toReal : ℂ) * B y

theorem norm_condE_le (ν : PMF α) (κ : α → K) (B : α → ℂ) (hB : ∀ x, ‖B x‖ ≤ 1) (x : α) :
    ‖condE ν κ B x‖ ≤ 1 := by
  have hne : ∑' y, condW ν κ x y ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (tsum_condW_le _ _ _)
  refine (norm_tsum_w_le _ hne B hB).trans ?_
  have := tsum_condW_le ν κ x
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)

theorem tower (ν : PMF α) (κ : α → K) (B : α → ℂ) (hB : ∀ x, ‖B x‖ ≤ 1) (G : α → ℂ)
    (hG : ∀ x, ‖G x‖ ≤ 1) (hGk : ∀ x y, κ x = κ y → G x = G y) :
    ∑' x, ((ν x).toReal : ℂ) * (G x * B x) =
      ∑' x, ((ν x).toReal : ℂ) * (G x * condE ν κ B x) := by
  have e1 : ∀ x, ((ν x).toReal : ℂ) * (G x * condE ν κ B x) =
      ∑' y, ((pairLaw ν κ (x, y)).toReal : ℂ) * (G x * B y) := by
    intro x
    unfold condE
    rw [← tsum_mul_left, ← tsum_mul_left]
    congr 1
    funext y
    rw [pairLaw_eq_mul, ENNReal.toReal_mul, Complex.ofReal_mul]
    ring
  have hw : ∑' x, ∑' y, pairLaw ν κ (x, y) ≠ ∞ := by
    simp_rw [tsum_pairLaw_right]
    exact ν.tsum_coe_ne_top
  have hb : ∀ x y, ‖G x * B y‖ ≤ 1 := fun x y => by
    rw [norm_mul]
    exact mul_le_one₀ (hG x) (norm_nonneg _) (hB y)
  rw [tsum_congr e1, tsum_comm_w (fun x y => pairLaw ν κ (x, y)) hw (fun x y => G x * B y) 1 hb]
  refine tsum_congr fun y => ?_
  have e2 : ∀ x, ((pairLaw ν κ (x, y)).toReal : ℂ) * (G x * B y) =
      ((pairLaw ν κ (y, x)).toReal : ℂ) * (G y * B y) := by
    intro x
    rw [pairLaw_symm ν κ x y]
    by_cases h : κ y = κ x
    · rw [hGk x y h.symm]
    · rw [pairLaw_eq_zero ν κ y x h]
      simp
  rw [tsum_congr e2, tsum_mul_right, ← Complex.ofReal_tsum,
    ← ENNReal.tsum_toReal_eq (fun _ => PMF.apply_ne_top _ _), tsum_pairLaw_right]

/-- Cauchy–Schwarz after conditioning on a key. -/
theorem cs_pair (ν : PMF α) (κ : α → K) (A B : α → ℂ) (hA : ∀ x, ‖A x‖ ≤ 1)
    (hB : ∀ x, ‖B x‖ ≤ 1) (hAk : ∀ x y, κ x = κ y → A x = A y) :
    ‖expect ν (fun x => A x * B x)‖ ^ 2 ≤
      ‖expect (pairLaw ν κ) (fun z => B z.1 * conj (B z.2))‖ := by
  set β := condE ν κ B with hβdef
  have hβ : ∀ x, ‖β x‖ ≤ 1 := norm_condE_le ν κ B hB
  have hβk : ∀ x y, κ x = κ y → β x = β y := by
    intro x y h
    simp only [hβdef, condE, condW_congr ν κ x y h]
  have step1 : expect ν (fun x => A x * B x) = ∑' x, ((ν x).toReal : ℂ) * (A x * β x) :=
    tower ν κ B hB A hA hAk
  have step2 : expect (pairLaw ν κ) (fun z => B z.1 * conj (B z.2)) =
      ∑' x, ((ν x).toReal : ℂ) * (conj (β x) * B x) := by
    unfold expect
    rw [tsum_prod_w (pairLaw ν κ) (PMF.tsum_coe_ne_top _) _ 1 (fun z => by
      rw [norm_mul, Complex.norm_conj]; exact mul_le_one₀ (hB _) (norm_nonneg _) (hB _))]
    refine tsum_congr fun x => ?_
    simp only [hβdef, condE]
    rw [Complex.conj_tsum, ← tsum_mul_right, ← tsum_mul_left]
    refine tsum_congr fun y => ?_
    rw [pairLaw_eq_mul, map_mul, Complex.conj_ofReal, ENNReal.toReal_mul, Complex.ofReal_mul]
    ring
  have step3 : ∑' x, ((ν x).toReal : ℂ) * (conj (β x) * B x) =
      ∑' x, ((ν x).toReal : ℂ) * (conj (β x) * β x) :=
    tower ν κ B hB (fun x => conj (β x)) (fun x => by rw [Complex.norm_conj]; exact hβ x)
      (fun x y h => by rw [hβk x y h])
  have step4 : ∑' x, ((ν x).toReal : ℂ) * (conj (β x) * β x) =
      ((∑' x, (ν x).toReal * ‖β x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun x => ?_
    rw [Complex.conj_mul', Complex.ofReal_mul, Complex.ofReal_pow]
  rw [step2, step3, step4, Complex.norm_real,
    Real.norm_of_nonneg (tsum_nonneg fun x => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)),
    step1]
  have hn : ‖∑' x, ((ν x).toReal : ℂ) * (A x * β x)‖ ≤ ∑' x, (ν x).toReal * ‖β x‖ := by
    have hb : ∀ x, ‖((ν x).toReal : ℂ) * (A x * β x)‖ ≤ (ν x).toReal * ‖β x‖ := by
      intro x
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) (hA x))
        ENNReal.toReal_nonneg
    have s2 := summable_pmf_real ν (fun x => ‖β x‖) (fun _ => norm_nonneg _) hβ
    have s1 : Summable fun x => ‖((ν x).toReal : ℂ) * (A x * β x)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb s2
    exact (norm_tsum_le_tsum_norm s1).trans (Summable.tsum_le_tsum hb s1 s2)
  calc ‖∑' x, ((ν x).toReal : ℂ) * (A x * β x)‖ ^ 2 ≤ (∑' x, (ν x).toReal * ‖β x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ ∑' x, (ν x).toReal * ‖β x‖ ^ 2 :=
        jensen ν (fun x => ‖β x‖) (fun _ => norm_nonneg _) hβ

end CS

section Phase

variable {p : ℕ} [hp : Fact p.Prime]

theorem omega_prim : IsPrimitiveRoot (omega p) p :=
  Complex.isPrimitiveRoot_exp p hp.out.ne_zero

theorem norm_phase (x : ZMod p) : ‖phase p x‖ = 1 := by
  unfold phase
  rw [norm_pow, omega_prim.norm'_eq_one hp.out.ne_zero, one_pow]

theorem phase_add (x y : ZMod p) : phase p (x + y) = phase p x * phase p y := by
  unfold phase
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) p, pow_add, pow_mul,
    omega_prim.pow_eq_one, one_pow, mul_one]

theorem phase_zero : phase p 0 = 1 := by
  unfold phase
  rw [ZMod.val_zero, pow_zero]

theorem phase_neg (x : ZMod p) : phase p (-x) = conj (phase p x) := by
  have h1 : phase p x * phase p (-x) = 1 := by rw [← phase_add, add_neg_cancel, phase_zero]
  have h2 : phase p x * conj (phase p x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]
    simp
  have hne : phase p x ≠ 0 := by
    intro h
    have := norm_phase x
    rw [h, norm_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem phase_sub (x y : ZMod p) : phase p (x - y) = phase p x * conj (phase p y) := by
  rw [sub_eq_add_neg, phase_add, phase_neg]

theorem phase_inj {x y : ZMod p} (h : phase p x = phase p y) : x = y :=
  ZMod.val_injective p (omega_prim.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h)

end Phase

section Step


variable {p : ℕ}

/-- The correlation of the theorem for a packed game. -/
noncomputable def corr (G : PackedGame.{u} p) (n : ℕ) (a : Fin n → ZMod p)
    (f : ∀ i, (Fin n → G.game.Q i) → ℂ) : ℂ :=
  expect (iidPMF G.game.μ n) fun s =>
    (∏ i, f i fun j => (s j).1 i) * ∏ j, phase p (a j * (s j).2)

/-- `H` is reached from `G` in `k` squarings. -/
def Reach (n : ℕ) (a : Fin n → ZMod p) (G H : PackedGame.{u} p) (k : ℕ) : Prop :=
  ∀ f : ∀ i, (Fin n → G.game.Q i) → ℂ, (∀ i x, ‖f i x‖ ≤ 1) →
    ∃ g : ∀ i, (Fin n → H.game.Q i) → ℂ, (∀ i x, ‖g i x‖ ≤ 1) ∧
      ‖corr G n a f‖ ^ (2 ^ k) ≤ ‖corr H n a g‖

theorem reach_zero (n : ℕ) (a : Fin n → ZMod p) (G : PackedGame.{u} p) : Reach n a G G 0 :=
  fun f hf => ⟨f, hf, by simp⟩

theorem reach_trans {n : ℕ} {a : Fin n → ZMod p} {G H L : PackedGame.{u} p} {k : ℕ}
    (hGH : Reach n a G H k) (hHL : Reach n a H L 1) : Reach n a G L (k + 1) := by
  intro f hf
  obtain ⟨g, hg, h1⟩ := hGH f hf
  obtain ⟨g', hg', h2⟩ := hHL g hg
  refine ⟨g', hg', ?_⟩
  rw [pow_succ, pow_mul]
  calc (‖corr G n a f‖ ^ 2 ^ k) ^ 2 ≤ ‖corr H n a g‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
    _ ≤ _ := by simpa using h2

variable [Fact p.Prime]

theorem norm_phase_prod {n : ℕ} (c : Fin n → ZMod p) : ‖∏ j, phase p (c j)‖ = 1 := by
  rw [norm_prod]
  simp [norm_phase]

theorem reach_glue (G : PackedGame.{u} p) (I : Finset G.Player) (n : ℕ) (a : Fin n → ZMod p) :
    Reach n a G (G.glue I) 1 := by
  intro f hf
  let g : ∀ i : (G.glue I).Player, (Fin n → (G.glue I).game.Q i) → ℂ :=
    fun s v => if s.2 then conj (f s.1.1 v) else f s.1.1 v
  have hg : ∀ s v, ‖g s v‖ ≤ 1 := by
    intro s v
    simp only [g]
    split_ifs
    · rw [Complex.norm_conj]; exact hf _ _
    · exact hf _ _
  refine ⟨g, hg, ?_⟩
  rw [pow_one]
  let k := keyI (Φ := G.game) I
  let A : (Fin n → (∀ i, G.game.Q i) × ZMod p) → ℂ := fun s =>
    ∏ i : {i // i ∈ I}, f i.1 (fun j => (s j).1 i.1)
  let B : (Fin n → (∀ i, G.game.Q i) × ZMod p) → ℂ := fun s =>
    (∏ i : {i // i ∉ I}, f i.1 (fun j => (s j).1 i.1)) * ∏ j, phase p (a j * (s j).2)
  have hA : ∀ s, ‖A s‖ ≤ 1 := fun s => norm_prod_le_one _ _ fun i => hf _ _
  have hB : ∀ s, ‖B s‖ ≤ 1 := fun s => by
    simp only [B]
    rw [norm_mul, norm_phase_prod, mul_one]
    exact norm_prod_le_one _ _ fun i => hf _ _
  have hAk : ∀ s s', (fun j => k (s j)) = (fun j => k (s' j)) → A s = A s' := by
    intro s s' h
    simp only [A]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    funext j
    exact congrFun (congrFun h j) i
  have hcorr : corr G n a f = expect (iidPMF G.game.μ n) fun s => A s * B s := by
    unfold corr
    congr 1
    funext s
    simp only [A, B]
    rw [← mul_assoc]
    congr 1
    convert (Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ I)
      (fun i => f i (fun j => (s j).1 i))).symm using 3
    exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)
  have hpair : expect (pairLaw (iidPMF G.game.μ n) (fun s j => k (s j)))
      (fun z => B z.1 * conj (B z.2)) =
      expect (iidPMF (pairLaw G.game.μ k) n)
        (fun x => B (fun j => (x j).1) * conj (B (fun j => (x j).2))) := by
    rw [pairLaw_iid, expect_map _ _ _ 1 (fun z => by
      rw [norm_mul, Complex.norm_conj]; exact mul_le_one₀ (hB _) (norm_nonneg _) (hB _))]
  rw [hcorr]
  refine (cs_pair _ (fun s j => k (s j)) A B hA hB hAk).trans (le_of_eq ?_)
  rw [hpair]
  congr 1
  unfold corr
  show _ = expect (iidPMF (G.game.glue I).μ n) _
  rw [glue_eq]
  erw [iid_map]
  erw [expect_map _ _ _ 1 (fun s => by
    rw [norm_mul, norm_phase_prod, mul_one]
    exact norm_prod_le_one _ _ fun i => hg _ _)]
  congr 1
  funext x
  simp only [B, GeneralizedXorGame.glueChallenge]
  erw [Fintype.prod_prod_type]
  simp only [g, Fintype.prod_bool, if_true, Bool.false_eq_true, if_false, map_mul, map_prod,
    mul_sub, phase_sub, Finset.prod_mul_distrib]
  ring

end Step

section Base


variable {p : ℕ} [Fact p.Prime]

theorem char_lt_one {Ω : Type*} (μ : PMF Ω) (t : Ω → ZMod p) (b : ZMod p) (hb : b ≠ 0)
    (h2 : ∃ ω₁ ∈ μ.support, ∃ ω₂ ∈ μ.support, t ω₁ ≠ t ω₂) :
    ‖expect μ fun ω => phase p (b * t ω)‖ < 1 := by
  set E := expect μ fun ω => phase p (b * t ω) with hEdef
  by_cases hE : E = 0
  · rw [hE, norm_zero]; exact zero_lt_one
  have hEpos : 0 < ‖E‖ := norm_pos_iff.2 hE
  set φ : Ω → ℂ := fun ω => phase p (b * t ω)
  have hφ : ∀ ω, ‖starRingEnd ℂ E * φ ω‖ = ‖E‖ := fun ω => by
    rw [norm_mul, Complex.norm_conj, norm_phase, mul_one]
  have hsum : Summable fun ω => ((μ ω).toReal : ℂ) * (starRingEnd ℂ E * φ ω) :=
    summable_pmf_mul μ _ ‖E‖ (fun ω => (hφ ω).le)
  have key : ‖E‖ ^ 2 = ∑' ω, (μ ω).toReal * (starRingEnd ℂ E * φ ω).re := by
    have e1 : ((‖E‖ ^ 2 : ℝ) : ℂ) = ∑' ω, ((μ ω).toReal : ℂ) * (starRingEnd ℂ E * φ ω) := by
      rw [Complex.ofReal_pow, ← Complex.conj_mul', hEdef]
      unfold expect
      rw [← tsum_mul_left]
      refine tsum_congr fun ω => ?_
      ring
    have := congrArg Complex.re e1
    rw [Complex.ofReal_re, Complex.re_tsum hsum] at this
    rw [this]
    refine tsum_congr fun ω => ?_
    rw [Complex.re_ofReal_mul]
  -- some supported point has a strictly smaller real part
  obtain ⟨ω₁, h1, ω₂, h2', ht⟩ := h2
  have hstrict : ∃ ω ∈ μ.support, (starRingEnd ℂ E * φ ω).re < ‖E‖ := by
    by_contra hc
    push Not at hc
    have heq : ∀ ω ∈ μ.support, starRingEnd ℂ E * φ ω = (‖E‖ : ℂ) := by
      intro ω hω
      have hre : (starRingEnd ℂ E * φ ω).re = ‖starRingEnd ℂ E * φ ω‖ := by
        rw [hφ]; exact le_antisymm (by rw [← hφ ω]; exact Complex.re_le_norm _) (hc ω hω)
      have h0 := Complex.re_eq_norm.1 hre
      rw [← hφ ω]
      apply Complex.ext
      · simpa using hre
      · simp only [Complex.ofReal_im]
        exact ((Complex.nonneg_iff.1 h0).2).symm
    have hφeq : φ ω₁ = φ ω₂ := by
      have := (heq ω₁ h1).trans (heq ω₂ h2').symm
      exact mul_left_cancel₀ (by simpa using hE) this
    apply ht
    have := phase_inj hφeq
    exact mul_left_cancel₀ hb this
  obtain ⟨ω₀, hω₀, hlt⟩ := hstrict
  have hpos : 0 < (μ ω₀).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).1 hω₀) (PMF.apply_ne_top _ _)
  have hs1 : Summable fun ω => (μ ω).toReal * (starRingEnd ℂ E * φ ω).re := by
    have := (Complex.reCLM.summable hsum)
    refine this.congr fun ω => ?_
    simp
  have hs2 : Summable fun ω => (μ ω).toReal * ‖E‖ :=
    (ENNReal.summable_toReal μ.tsum_coe_ne_top).mul_right _
  have hlt' : ∑' ω, (μ ω).toReal * (starRingEnd ℂ E * φ ω).re < ∑' ω, (μ ω).toReal * ‖E‖ := by
    refine Summable.tsum_lt_tsum (i := ω₀) (fun ω => ?_) ?_ hs1 hs2
    · exact mul_le_mul_of_nonneg_left
        ((Complex.re_le_norm _).trans (hφ ω).le) ENNReal.toReal_nonneg
    · exact mul_lt_mul_of_pos_left hlt hpos
  rw [tsum_mul_right, tsum_pmf_toReal, one_mul, ← key] at hlt'
  nlinarith

theorem base_bound (H : PackedGame.{u} p) (he : IsEmpty H.Player) (h2 : H.game.HasTwoTargets) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (n : ℕ) (a : Fin n → ZMod p) g,
      ‖corr H n a g‖ ≤ ρ ^ (Finset.univ.filter fun j => a j ≠ 0).card := by
  let c : ZMod p → ℝ := fun b => ‖expect H.game.μ fun ω => phase p (b * ω.2)‖
  have hc1 : ∀ b, c b ≤ 1 := fun b =>
    norm_expect_le_one _ _ fun ω => (norm_phase _).le
  have hlt : ∀ b, b ≠ 0 → c b < 1 := by
    intro b hb
    obtain ⟨ω₁, h1, ω₂, h2', ht⟩ := h2
    exact char_lt_one H.game.μ (fun ω => ω.2) b hb ⟨ω₁, h1, ω₂, h2', ht⟩
  have : Nonempty {b : ZMod p // b ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  obtain ⟨b₀, hb₀⟩ := Finite.exists_max fun b : {b : ZMod p // b ≠ 0} => c b.1
  refine ⟨c b₀.1, norm_nonneg _, hlt _ b₀.2, ?_⟩
  intro n a g
  have e : corr H n a g = ∏ j, expect H.game.μ fun ω => phase p (a j * ω.2) := by
    unfold corr
    simp only [Fintype.prod_empty, one_mul]
    exact expect_iid_prod H.game.μ n (fun j ω => phase p (a j * ω.2))
      (fun j ω => (norm_phase _).le)
  rw [e, norm_prod]
  calc ∏ j, c (a j) ≤ ∏ j, (if a j ≠ 0 then c b₀.1 else 1) := by
        refine Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_
        split_ifs with hj
        · exact hb₀ ⟨a j, hj⟩
        · exact hc1 _
    _ = c b₀.1 ^ (Finset.univ.filter fun j => a j ≠ 0).card := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

end Base

section Chain


variable {p : ℕ} [Fact p.Prime]

theorem reach_chain (T : ℕ) (chain : Fin (T + 1) → PackedGame.{u} p)
    (hstep : ∀ i : Fin T, ∃ I : Finset (chain i.castSucc).Player,
      I.Nonempty ∧ chain i.succ = (chain i.castSucc).glue I)
    (n : ℕ) (a : Fin n → ZMod p) :
    ∀ (i : ℕ) (hi : i ≤ T), Reach n a (chain 0) (chain ⟨i, by omega⟩) i
  | 0, _ => by
    have : (⟨0, by omega⟩ : Fin (T + 1)) = 0 := rfl
    rw [this]
    exact reach_zero n a _
  | i + 1, hi => by
    obtain ⟨I, -, hI⟩ := hstep ⟨i, by omega⟩
    have e : chain ⟨i + 1, by omega⟩ = (chain ⟨i, by omega⟩).glue I := hI
    rw [e]
    exact reach_trans (reach_chain T chain hstep n a i (by omega)) (reach_glue _ I n a)

end Chain

end XorParallelRepetition.Dev.Tensor

namespace XorParallelRepetition.Exponential


theorem chk_tensorized_correlation_decay {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
    (Ψ : GeneralizedXorGame.{u} p ι) (N : ℕ) (h : HasOrderedContradiction Ψ N)
    (hnd : Nonempty ι ∨ Ψ.HasTwoTargets) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (n d : ℕ) (a : Fin n → ZMod p),
      d ≤ (Finset.univ.filter fun j => a j ≠ 0).card →
      ∀ f : ∀ i, (Fin n → Ψ.Q i) → ℂ, (∀ i x, ‖f i x‖ ≤ 1) →
        ‖expect (iidPMF Ψ.μ n) fun s =>
          (∏ i, f i fun j => (s j).1 i) * ∏ j, phase p (a j * (s j).2)‖ ≤ (1 - ε) ^ d := by
  classical
  obtain ⟨B, hB⟩ := finite_gluing_chain.{u}
  obtain ⟨T, chain, -, h0, hstep, hempty, htwo⟩ := hB Ψ N h hnd
  obtain ⟨ρ, hρ0, hρ1, hbase⟩ :=
    XorParallelRepetition.Dev.Tensor.base_bound (chain (Fin.last T)) hempty htwo
  set σ : ℝ := ρ ^ ((1 : ℝ) / 2 ^ T) with hσdef
  have hσ0 : 0 ≤ σ := Real.rpow_nonneg hρ0 _
  have hσ1 : σ < 1 := Real.rpow_lt_one hρ0 hρ1 (by positivity)
  have hσT : σ ^ (2 ^ T) = ρ := by
    rw [hσdef, ← Real.rpow_natCast, ← Real.rpow_mul hρ0]
    norm_num
  refine ⟨1 - σ, by linarith, ?_⟩
  intro n d a hd f hf
  have hr := XorParallelRepetition.Dev.Tensor.reach_chain T chain hstep n a T le_rfl
  have hlast : (⟨T, by omega⟩ : Fin (T + 1)) = Fin.last T := rfl
  rw [h0, hlast] at hr
  obtain ⟨g, -, hle⟩ := hr f hf
  rw [sub_sub_cancel]
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (pow_nonneg hσ0 _) (pow_ne_zero T two_ne_zero)]
  calc _ ≤ _ := hle
    _ ≤ ρ ^ (Finset.univ.filter fun j => a j ≠ 0).card := hbase n a g
    _ ≤ ρ ^ d := pow_le_pow_of_le_one hρ0 hρ1.le hd
    _ = (σ ^ d) ^ (2 ^ T) := by rw [← pow_mul, mul_comm, pow_mul, hσT]


end XorParallelRepetition.Exponential
end

theorem solution : type_of% @XorParallelRepetition.Exponential.chk_tensorized_correlation_decay := @XorParallelRepetition.Exponential.chk_tensorized_correlation_decay

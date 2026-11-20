-- Prove2me | solution 1 for XorParallelRepetition.Exponential.gluing_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:28:44.745338+00:00
-- url     : https://prove2.me/submissions/c2bd7e03-5b00-469c-93d9-62e9318eb0ce

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_Gluing
universe u

section
set_option autoImplicit false

open scoped ENNReal ComplexConjugate

namespace XorParallelRepetition.Dev.GlueCS

open XorParallelRepetition.Exponential
open Classical

section Sums

variable {α β γ : Type*}

theorem summable_w_mul (w : α → ℝ≥0∞) (hw : ∑' a, w a ≠ ∞) (F : α → ℂ) (C : ℝ)
    (hF : ∀ a, ‖F a‖ ≤ C) : Summable fun a => ((w a).toReal : ℂ) * F a := by
  refine Summable.of_norm_bounded ((ENNReal.summable_toReal hw).mul_left C) fun a => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg, mul_comm]
  exact mul_le_mul_of_nonneg_right (hF a) ENNReal.toReal_nonneg

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

theorem norm_prod_le_one {ι : Type*} (s : Finset ι) (g : ι → ℂ) (hg : ∀ i, ‖g i‖ ≤ 1) :
    ‖∏ i ∈ s, g i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hg i)

end Sums



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

end Phase

section Main


variable {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem main (Ψ : GeneralizedXorGame.{u} p ι) (I : Finset ι) (a : ZMod p)
    (f : ∀ i, Ψ.Q i → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) :
    ‖expect Ψ.μ fun ω => (∏ i, f i (ω.1 i)) * phase p (-(a * ω.2))‖ ^ 2 ≤
      ‖expect (Ψ.glue I).μ fun ω =>
        (∏ i : {i // i ∉ I}, f i.1 (ω.1 (i, false)) * conj (f i.1 (ω.1 (i, true)))) *
          phase p (-(a * ω.2))‖ := by
  set A : (∀ i, Ψ.Q i) × ZMod p → ℂ := fun ω => ∏ i : {i // i ∈ I}, f i.1 (ω.1 i.1) with hAdef
  set B : (∀ i, Ψ.Q i) × ZMod p → ℂ :=
    fun ω => (∏ i : {i // i ∉ I}, f i.1 (ω.1 i.1)) * phase p (-(a * ω.2)) with hBdef
  have hA : ∀ x, ‖A x‖ ≤ 1 := fun x => by
    simp only [hAdef]
    exact norm_prod_le_one _ _ fun i => hf _ _
  have hB : ∀ x, ‖B x‖ ≤ 1 := fun x => by
    simp only [hBdef]
    rw [norm_mul, norm_phase, mul_one]
    exact norm_prod_le_one _ _ fun i => hf _ _
  have hAk : ∀ x y, keyI (Φ := Ψ) I x = keyI (Φ := Ψ) I y → A x = A y := by
    intro x y h
    simp only [hAdef]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := congrFun h i
    simp only [keyI] at this
    rw [this]
  have hL : (fun ω : (∀ i, Ψ.Q i) × ZMod p => (∏ i, f i (ω.1 i)) * phase p (-(a * ω.2))) =
      fun ω => A ω * B ω := by
    funext ω
    simp only [hAdef, hBdef]
    rw [← mul_assoc]
    congr 1
    convert (Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ I) (fun i => f i (ω.1 i))).symm
      using 3
    exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)
  have hFb : ∀ ω : (∀ s : {i // i ∉ I} × Bool, Ψ.Q s.1.1) × ZMod p,
      ‖(∏ i : {i // i ∉ I}, f i.1 (ω.1 (i, false)) * conj (f i.1 (ω.1 (i, true)))) *
          phase p (-(a * ω.2))‖ ≤ 1 := by
    intro ω
    rw [norm_mul, norm_phase, mul_one]
    refine norm_prod_le_one _ _ fun i => ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (hf _ _) (norm_nonneg _) (hf _ _)
  have hR : expect (Ψ.glue I).μ (fun ω =>
        (∏ i : {i // i ∉ I}, f i.1 (ω.1 (i, false)) * conj (f i.1 (ω.1 (i, true)))) *
          phase p (-(a * ω.2))) =
      expect (pairLaw Ψ.μ (keyI (Φ := Ψ) I)) (fun z => B z.1 * conj (B z.2)) := by
    rw [glue_eq]
    refine (expect_map _ _ _ 1 hFb).trans ?_
    congr 1
    funext z
    simp only [hBdef, GeneralizedXorGame.glueChallenge, Bool.false_eq_true, if_false, if_true,
      map_mul, map_prod]
    have hph : phase p (-(a * (z.1.2 - z.2.2))) =
        phase p (-(a * z.1.2)) * conj (phase p (-(a * z.2.2))) := by
      rw [← phase_sub]
      congr 1
      ring
    rw [hph, Finset.prod_mul_distrib]
    ring
  rw [hL, hR]
  exact cs_pair Ψ.μ (keyI (Φ := Ψ) I) A B hA hB hAk

end Main

end XorParallelRepetition.Dev.GlueCS

namespace XorParallelRepetition.Exponential


theorem chk_gluing_cauchy_schwarz {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : GeneralizedXorGame.{u} p ι) (I : Finset ι) (hI : I.Nonempty) (a : ZMod p)
    (f : ∀ i, Ψ.Q i → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) :
    ‖expect Ψ.μ fun ω => (∏ i, f i (ω.1 i)) * phase p (-(a * ω.2))‖ ^ 2 ≤
      ‖expect (Ψ.glue I).μ fun ω =>
        (∏ i : {i // i ∉ I}, f i.1 (ω.1 (i, false)) * conj (f i.1 (ω.1 (i, true)))) *
          phase p (-(a * ω.2))‖ :=
  XorParallelRepetition.Dev.GlueCS.main Ψ I a f hf

end XorParallelRepetition.Exponential
end

theorem solution : type_of% @XorParallelRepetition.Exponential.chk_gluing_cauchy_schwarz := @XorParallelRepetition.Exponential.chk_gluing_cauchy_schwarz

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_agree_of_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:33.946956+00:00
-- url     : https://prove2.me/submissions/6e772cf8-7149-438b-a024-41d20a76f6bb

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
private theorem hs_lemma {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero ha
private theorem pc_lemma_9 {σ τ : Type*} {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {m : σ →₀ ℕ} (hm : m ≠ 0) :
    constantCoeff (m.prod fun s n => a s ^ n) = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, m s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hm (Finsupp.ext hc)
  unfold Finsupp.prod
  rw [map_prod]
  exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [ha s, hs])
private theorem sp_lemma_13 {σ τ : Type*} {a : σ → MvPowerSeries τ C} {m : σ →₀ ℕ} {s : σ}
    (hle : Finsupp.single s 1 ≤ m) :
    (m.prod fun s n => a s ^ n) = a s * ((m - Finsupp.single s 1).prod fun s n => a s ^ n) := by
  conv_lhs => rw [← add_tsub_cancel_of_le hle]
  rw [Finsupp.prod_add_index' (h := fun s n => a s ^ n) (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _), Finsupp.prod_single_index (h := fun s n => a s ^ n) (pow_zero _),
    pow_one]
private theorem mu_lemma_16 {τ : Type*} {f f' g g' : MvPowerSeries τ C} (n : ℕ)
    (hf : ∀ e : τ →₀ ℕ, e.degree < n → coeff e f = coeff e f')
    (hg : ∀ e : τ →₀ ℕ, e.degree < n → coeff e g = coeff e g') :
    ∀ e : τ →₀ ℕ, e.degree < n → coeff e (f * g) = coeff e (f' * g') := by
  intro e he
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hd : p.1.degree + p.2.degree = e.degree := by rw [← hp, map_add]
  rw [hf p.1 (by omega), hg p.2 (by omega)]
private theorem m1_lemma_17 {τ : Type*} {f f' g g' : MvPowerSeries τ C} (n : ℕ)
    (hf0 : constantCoeff f = 0) (hf0' : constantCoeff f' = 0)
    (hg0 : constantCoeff g = 0) (hg0' : constantCoeff g' = 0)
    (hf : ∀ e : τ →₀ ℕ, e.degree < n → coeff e f = coeff e f')
    (hg : ∀ e : τ →₀ ℕ, e.degree < n → coeff e g = coeff e g') :
    ∀ e : τ →₀ ℕ, e.degree ≤ n → coeff e (f * g) = coeff e (f' * g') := by
  intro e he
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hd : p.1.degree + p.2.degree = e.degree := by rw [← hp, map_add]
  by_cases h1 : p.1 = 0
  · rw [h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, hf0', zero_mul, zero_mul]
  · by_cases h2 : p.2 = 0
    · rw [h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg0, hg0', mul_zero, mul_zero]
    · have d1 : p.1.degree ≠ 0 := fun h => h1 ((Finsupp.degree_eq_zero_iff _).mp h)
      have d2 : p.2.degree ≠ 0 := fun h => h2 ((Finsupp.degree_eq_zero_iff _).mp h)
      rw [hf p.1 (by omega), hg p.2 (by omega)]
private theorem tp_lemma_14 {σ τ : Type*} {x y : σ → MvPowerSeries τ C} (n : ℕ)
    (hxy : ∀ s (e : τ →₀ ℕ), e.degree < n → coeff e (x s) = coeff e (y s)) (m : σ →₀ ℕ) :
    ∀ e : τ →₀ ℕ, e.degree < n →
      coeff e (m.prod fun s k => x s ^ k) = coeff e (m.prod fun s k => y s ^ k) := by
  have hpow : ∀ s (k : ℕ), ∀ e : τ →₀ ℕ, e.degree < n → coeff e (x s ^ k) = coeff e (y s ^ k) := by
    intro s k
    induction k with
    | zero =>
      intro e _
      simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mu_lemma_16 n ih (hxy s)
  unfold Finsupp.prod
  induction m.support using Finset.induction_on with
  | empty =>
    intro e _
    simp
  | @insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact mu_lemma_16 n (hpow j (m j)) ih
private theorem ag_lemma_15 {σ τ : Type*} [Finite σ] {x y : σ → MvPowerSeries τ C}
    (hx : ∀ s, constantCoeff (x s) = 0) (hy : ∀ s, constantCoeff (y s) = 0) (n : ℕ)
    (hxy : ∀ s (e : τ →₀ ℕ), e.degree < n → coeff e (x s) = coeff e (y s))
    (r : MvPowerSeries σ C) (hr0 : constantCoeff r = 0)
    (hr1 : ∀ s, coeff (Finsupp.single s 1) r = 0) (e : τ →₀ ℕ) (he : e.degree ≤ n) :
    coeff e (subst x r) = coeff e (subst y r) := by
  rw [coeff_subst (hs_lemma hx), coeff_subst (hs_lemma hy)]
  apply finsum_congr
  intro m
  by_cases h0 : m = 0
  · rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hr0, zero_smul, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, m s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h0 (Finsupp.ext hc)
    have hle : Finsupp.single s 1 ≤ m :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hs)
    by_cases hm' : m - Finsupp.single s 1 = 0
    · have hms : m = Finsupp.single s 1 := by
        rw [← add_tsub_cancel_of_le hle, hm', add_zero]
      rw [hms, hr1 s, zero_smul, zero_smul]
    · rw [sp_lemma_13 hle, sp_lemma_13 hle]
      congr 1
      exact m1_lemma_17 n (hx s) (hy s) (pc_lemma_9 hx hm') (pc_lemma_9 hy hm') (hxy s)
        (tp_lemma_14 n hxy _) e he
end
end ReciprocityTheory.ChartRestriction.G.Sh
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (k : ℕ)
    (h : ∀ a (e : τ →₀ ℕ), e.degree < k →
      coeff e (subst x (G.lg a)) = coeff e (subst y (G.lg a))) : PTAgree k x y := by
  have hsx := hs_lemma hx
  have hsy := hs_lemma hy
  have hr0 : ∀ i, constantCoeff (G.lg i - X i) = 0 := fun i => by simp [G.lg_const i]
  have hr1 : ∀ i s, coeff (Finsupp.single s 1) (G.lg i - X i) = 0 := fun i s => by
    rw [map_sub, G.lg_lin]
    by_cases his : i = s
    · subst his
      simp [coeff_X]
    · have hne : ¬ Finsupp.single s 1 = Finsupp.single i 1 := fun h' =>
        his (Finsupp.single_left_injective one_ne_zero h').symm
      simp [his, coeff_X, hne]
  have key : ∀ n, ∀ i (e : τ →₀ ℕ), e.degree = n → n < k → coeff e (x i) = coeff e (y i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i e hen hnk
      have hlow : ∀ s (e' : τ →₀ ℕ), e'.degree < n → coeff e' (x s) = coeff e' (y s) :=
        fun s e' he' => ih _ he' s e' rfl (by omega)
      have h1 := h i e (by omega)
      have hlg : G.lg i = X i + (G.lg i - X i) := by ring
      rw [hlg, subst_add hsx, subst_add hsy, subst_X hsx, subst_X hsy, map_add, map_add,
        ag_lemma_15 hx hy n hlow _ (hr0 i) (hr1 i) e (le_of_eq hen)] at h1
      exact add_right_cancel h1
  intro i e he
  exact key _ i e rfl he
end ReciprocityTheory.ChartRestriction.G.Sh

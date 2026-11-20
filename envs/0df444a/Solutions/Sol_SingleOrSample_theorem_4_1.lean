-- Prove2me | solution 1 for SingleOrSample.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T03:45:04.117655+00:00
-- url     : https://prove2.me/submissions/b41eb7da-a56f-47b2-abbc-4243f290fc98

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SingleOrSample_IsValuation
import Definitions.Def_SingleOrSample_runLaw
import Definitions.Def_SingleOrSample_IsSafe

namespace SingleOrSample_Proof

open SingleOrSample
open scoped Classical ENNReal

/-! ### Section 1: `ENNReal` Expectations on `PMF` and `toOuterMeasure` Combinators -/

section PMFHelpers

noncomputable def pmfExp {α : Type*} (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, p a * f a

private lemma pmfExp_pure {α : Type*} (x : α) (f : α → ℝ≥0∞) :
    pmfExp (PMF.pure x) f = f x := by
  simp [pmfExp, PMF.pure_apply]

private lemma pmfExp_const {α : Type*} (p : PMF α) (c : ℝ≥0∞) :
    pmfExp p (fun _ => c) = c := by
  simp [pmfExp, ENNReal.tsum_mul_right, p.tsum_coe]

private lemma pmfExp_bind {α β : Type*} (p : PMF α) (q : α → PMF β) (f : β → ℝ≥0∞) :
    pmfExp (p.bind q) f = pmfExp p (fun a => pmfExp (q a) f) := by
  simp only [pmfExp, PMF.bind_apply]
  calc
    ∑' b, (∑' a, p a * q a b) * f b
      = ∑' b, ∑' a, (p a * q a b) * f b := by
          refine tsum_congr fun b => ?_
          rw [ENNReal.tsum_mul_right]
    _ = ∑' a, ∑' b, p a * (q a b * f b) := by
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun a => tsum_congr fun b => mul_assoc _ _ _
    _ = ∑' a, p a * ∑' b, q a b * f b := by
          refine tsum_congr fun a => ?_
          rw [ENNReal.tsum_mul_left]

private lemma pmfExp_map {α β : Type*} (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    pmfExp (p.map g) f = pmfExp p (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, pmfExp_bind]
  refine tsum_congr fun a => ?_
  simp [pmfExp_pure]

private lemma pmfExp_uniformOfFinset {α : Type*} (B : Finset α) (hB : B.Nonempty) (f : α → ℝ≥0∞) :
    pmfExp (PMF.uniformOfFinset B hB) f = (B.card : ℝ≥0∞)⁻¹ * ∑ e ∈ B, f e := by
  unfold pmfExp
  rw [tsum_eq_sum (s := B)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    simp [PMF.uniformOfFinset_apply, he]
  · intro a ha
    simp [PMF.uniformOfFinset_apply, ha]

private lemma pmfExp_mono_support {α : Type*} (p : PMF α) {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ p.support, f a ≤ g a) :
    pmfExp p f ≤ pmfExp p g := by
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : p a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonneg_left (h a ((PMF.mem_support_iff p a).mpr ha)) zero_le'

private lemma pmfExp_congr_support {α : Type*} (p : PMF α) {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ p.support, f a = g a) :
    pmfExp p f = pmfExp p g :=
  le_antisymm
    (pmfExp_mono_support p fun a ha => (h a ha).le)
    (pmfExp_mono_support p fun a ha => (h a ha).ge)

private lemma toOuterMeasure_eq_pmfExp {α : Type*} (p : PMF α) (S : Set α) :
    p.toOuterMeasure S = pmfExp p (fun a => if a ∈ S then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply]
  unfold pmfExp
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ S <;> simp [ha]

private lemma toOuterMeasure_univ {α : Type*} (p : PMF α) :
    p.toOuterMeasure Set.univ = 1 := by
  rw [toOuterMeasure_eq_pmfExp]
  simpa using pmfExp_const p 1

private lemma toOuterMeasure_add_compl {α : Type*} (p : PMF α) (S : Set α) :
    p.toOuterMeasure S + p.toOuterMeasure Sᶜ = 1 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  have hpt : ∀ a : α, S.indicator p a + Sᶜ.indicator p a = p a := fun a => by
    by_cases ha : a ∈ S <;> simp [ha]
  simp_rw [hpt]
  exact p.tsum_coe

private lemma pmf_markov {α : Type*} (p : PMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) (S : Set α)
    (h : ∀ a ∈ p.support, a ∈ S → c ≤ f a) :
    c * p.toOuterMeasure S ≤ pmfExp p f := by
  rw [toOuterMeasure_eq_pmfExp, pmfExp, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha0 : p a = 0
  · simp [ha0]
  · by_cases haS : a ∈ S
    · simp only [haS, ↓reduceIte, mul_one, mul_comm c (p a)]
      exact mul_le_mul_of_nonneg_left (h a ((PMF.mem_support_iff p a).mpr ha0) haS) zero_le'
    · simp [haS]

private lemma toOuterMeasure_bind_iff {α β : Type*} (p : PMF α) (q : α → PMF β)
    (S : Set β) (T : Set α)
    (h : ∀ a ∈ p.support, ∀ b ∈ (q a).support, (b ∈ S ↔ a ∈ T)) :
    (p.bind q).toOuterMeasure S = p.toOuterMeasure T := by
  rw [toOuterMeasure_eq_pmfExp, pmfExp_bind, toOuterMeasure_eq_pmfExp]
  refine pmfExp_congr_support p fun a ha => ?_
  have hcongr : pmfExp (q a) (fun b => if b ∈ S then (1 : ℝ≥0∞) else 0) =
      pmfExp (q a) (fun _ => if a ∈ T then (1 : ℝ≥0∞) else 0) := by
    refine pmfExp_congr_support (q a) fun b hb => ?_
    simp [h a ha b hb]
  rw [hcongr, pmfExp_const]

private lemma toOuterMeasure_bind_ge {α β : Type*} (p : PMF α) (q : α → PMF β)
    (S : Set β) (T : Set α)
    (h : ∀ a ∈ p.support, a ∈ T → ∀ b ∈ (q a).support, b ∈ S) :
    p.toOuterMeasure T ≤ (p.bind q).toOuterMeasure S := by
  rw [toOuterMeasure_eq_pmfExp, toOuterMeasure_eq_pmfExp, pmfExp_bind]
  refine pmfExp_mono_support p fun a ha => ?_
  by_cases haT : a ∈ T
  · simp only [haT, ↓reduceIte]
    have h1 : pmfExp (q a) (fun _ => (1 : ℝ≥0∞)) ≤
        pmfExp (q a) (fun b => if b ∈ S then 1 else 0) := by
      refine pmfExp_mono_support (q a) fun b hb => ?_
      simp [h a ha haT b hb]
    simpa [pmfExp_const] using h1
  · simp [haT]

private lemma ennreal_tsum_finsetSum {α ι : Type*} (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    (∑ i ∈ s, ∑' a, f i a) = ∑' a, ∑ i ∈ s, f i a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s' hx ih =>
    rw [Finset.sum_insert hx, ih, ← ENNReal.tsum_add]
    refine tsum_congr fun a => (Finset.sum_insert (f := fun i => f i a) hx).symm

private lemma toOuterMeasure_union_bound {α : Type*} {n : ℕ} (p : PMF α)
    (Inv : Set α) (Good : Fin n → Set α)
    (hInv : ∀ a ∈ p.support, a ∈ Inv) :
    1 ≤ p.toOuterMeasure {a | a ∈ Inv ∧ ∀ i, a ∈ Good i} +
      ∑ i : Fin n, p.toOuterMeasure (Good i)ᶜ := by
  let GAll : Set α := {a | a ∈ Inv ∧ ∀ i, a ∈ Good i}
  simp only [PMF.toOuterMeasure_apply]
  rw [ennreal_tsum_finsetSum, ← ENNReal.tsum_add, ← p.tsum_coe]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha0 : p a = 0
  · simp [ha0]
  · have haInv : a ∈ Inv := hInv a ((PMF.mem_support_iff p a).mpr ha0)
    by_cases hall : ∀ i : Fin n, a ∈ Good i
    · have haG : a ∈ GAll := ⟨haInv, hall⟩
      calc
        p a = GAll.indicator p a := by simp [haG]
        _ ≤ GAll.indicator p a + ∑ i : Fin n, (Good i)ᶜ.indicator p a := self_le_add_right _ _
    · push_neg at hall
      rcases hall with ⟨i₀, hi₀⟩
      have hi₀c : a ∈ (Good i₀)ᶜ := hi₀
      have hle_sum : p a ≤ ∑ i : Fin n, (Good i)ᶜ.indicator p a := by
        calc
          p a = (Good i₀)ᶜ.indicator p a := by simp [hi₀c]
          _ ≤ ∑ i : Fin n, (Good i)ᶜ.indicator p a :=
            Finset.single_le_sum (f := fun i => (Good i)ᶜ.indicator p a)
              (fun _ _ => zero_le') (Finset.mem_univ i₀)
      exact le_add_of_le_right hle_sum

end PMFHelpers

/-! ### Section 2: Numerical Inequalities and Failure Probabilities `qParam` -/

section Numerics

noncomputable def alphaBase : ℝ :=
  Real.exp (-((5 : ℝ) / 8) * Real.log 5)

noncomputable def qParam (n : ℕ) (i : Fin n) : ℝ :=
  alphaBase ^ (n - i.val)

private lemma alphaBase_pos : 0 < alphaBase :=
  Real.exp_pos _

private lemma qParam_nonneg (n : ℕ) (i : Fin n) : 0 ≤ qParam n i :=
  pow_nonneg alphaBase_pos.le _

private lemma alphaBase_pow_eight : alphaBase ^ 8 = (1 : ℝ) / 3125 := by
  unfold alphaBase
  rw [← Real.exp_nat_mul]
  have hexp : (8 : ℕ) * (-((5 : ℝ) / 8) * Real.log 5) = -((5 : ℕ) * Real.log 5) := by
    push_cast; ring
  rw [hexp, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  norm_num

private lemma alphaBase_le : alphaBase ≤ 577 / 1577 := by
  have hp : alphaBase ^ 8 ≤ (577 / 1577 : ℝ) ^ 8 := by
    rw [alphaBase_pow_eight]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : 8 ≠ 0) (by norm_num : (0 : ℝ) ≤ 577 / 1577) hp

private lemma alphaBase_lt_one : alphaBase < 1 :=
  lt_of_le_of_lt alphaBase_le (by norm_num)

private lemma geom_sum_telescoping (x : ℝ) (n : ℕ) :
    (1 - x) * ∑ j ∈ Finset.range n, x ^ j = 1 - x ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

private lemma qParam_sum_le (n : ℕ) : ∑ i : Fin n, qParam n i ≤ 0.577 := by
  have hrev : ∑ i : Fin n, qParam n i = ∑ j : Fin n, alphaBase ^ (j.val + 1) := by
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold qParam
    congr 1
    simp [Fin.revPerm_apply, Fin.val_rev]
    omega
  rw [hrev, Fin.sum_univ_eq_sum_range (fun k => alphaBase ^ (k + 1)) n]
  have hfac : ∑ k ∈ Finset.range n, alphaBase ^ (k + 1) =
      alphaBase * ∑ k ∈ Finset.range n, alphaBase ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hfac]
  have h1pos : 0 < 1 - alphaBase := sub_pos.mpr alphaBase_lt_one
  have htel : (1 - alphaBase) * ∑ k ∈ Finset.range n, alphaBase ^ k ≤ 1 := by
    rw [geom_sum_telescoping]
    have hpow : 0 ≤ alphaBase ^ n := pow_nonneg alphaBase_pos.le n
    linarith
  have hsum_le : ∑ k ∈ Finset.range n, alphaBase ^ k ≤ 1 / (1 - alphaBase) := by
    rw [le_div_iff₀ h1pos, mul_comm]
    exact htel
  have hprod_le : alphaBase * ∑ k ∈ Finset.range n, alphaBase ^ k ≤
      alphaBase / (1 - alphaBase) := by
    calc
      alphaBase * ∑ k ∈ Finset.range n, alphaBase ^ k
        ≤ alphaBase * (1 / (1 - alphaBase)) :=
          mul_le_mul_of_nonneg_left hsum_le alphaBase_pos.le
      _ = alphaBase / (1 - alphaBase) := by ring
  have hnum : alphaBase / (1 - alphaBase) ≤ 0.577 := by
    rw [div_le_iff₀ h1pos]
    have ha := alphaBase_le
    linarith
  exact hprod_le.trans hnum

private lemma one_le_five_eighths_log5 : (1 : ℝ) ≤ (5 / 8) * Real.log 5 := by
  have hexp8 : Real.exp 8 < (5 : ℝ) ^ 5 := by
    have h1 : Real.exp 8 = (Real.exp 1) ^ 8 := by
      have : (8 : ℝ) = (8 : ℕ) * (1 : ℝ) := by norm_num
      rw [this, Real.exp_nat_mul]
    rw [h1]
    have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hp : (Real.exp 1) ^ 8 < (2.7182818286 : ℝ) ^ 8 :=
      pow_lt_pow_left₀ he1 (Real.exp_pos 1).le (by norm_num)
    exact hp.trans (by norm_num)
  have hexp85 : Real.exp (8 / 5) ≤ 5 := by
    have hp : (Real.exp (8 / 5)) ^ 5 ≤ (5 : ℝ) ^ 5 := by
      rw [← Real.exp_nat_mul]
      have : (5 : ℕ) * ((8 : ℝ) / 5) = 8 := by norm_num
      rw [this]
      exact hexp8.le
    exact le_of_pow_le_pow_left₀ (by norm_num : 5 ≠ 0) (by norm_num : (0 : ℝ) ≤ 5) hp
  have hlog : (8 : ℝ) / 5 ≤ Real.log 5 := by
    rw [← Real.log_exp (8 / 5)]
    exact Real.log_le_log (Real.exp_pos _) hexp85
  linarith

private lemma exp_mul_le_linear {lam t : ℝ} (_hlam : 0 ≤ lam) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (lam * t) ≤ 1 + (Real.exp lam - 1) * t := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ lam)
    (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  calc
    Real.exp (lam * t) = Real.exp (t * lam) := by rw [mul_comm]
    _ ≤ 1 - t + t * Real.exp lam := hconv
    _ = 1 + (Real.exp lam - 1) * t := by ring

private lemma qParam_mul_exp_eq_one (n : ℕ) (i : Fin n) :
    qParam n i * Real.exp (((5 : ℝ) / 8) * Real.log 5 * ((n - i.val : ℕ) : ℝ)) = 1 := by
  unfold qParam alphaBase
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  have : ((n - i.val : ℕ) : ℝ) * (-((5 : ℝ) / 8) * Real.log 5) +
      ((5 : ℝ) / 8) * Real.log 5 * ((n - i.val : ℕ) : ℝ) = 0 := by ring
  rw [this, Real.exp_zero]

end Numerics

/-! ### Section 3: Submodularity, MMS Partition, and Supporting Prices -/

section SubmodularAndMMS

private lemma val_nonneg {m : ℕ} {v : Finset (Fin m) → ℝ} (hv : IsValuation v)
    (S : Finset (Fin m)) : 0 ≤ v S := by
  rw [← hv.2]
  exact hv.1 ∅ S (Finset.empty_subset S)

private lemma marginal_eq_insert {m : ℕ} (v : Finset (Fin m) → ℝ)
    (A : Finset (Fin m)) (e : Fin m) :
    marginal v A e = v (insert e A) - v A := by
  unfold marginal
  rw [Finset.union_comm, Finset.singleton_union]

private lemma marginal_nonneg {m : ℕ} {v : Finset (Fin m) → ℝ} (hv : IsValuation v)
    (A : Finset (Fin m)) (e : Fin m) :
    0 ≤ marginal v A e := by
  rw [marginal_eq_insert]
  exact sub_nonneg.mpr (hv.1 A (insert e A) (Finset.subset_insert e A))

private lemma marginal_empty {m : ℕ} {v : Finset (Fin m) → ℝ} (hv : IsValuation v) (e : Fin m) :
    marginal v ∅ e = v {e} := by
  simp [marginal, hv.2]

private lemma marginal_antitone {m : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) (hsub : SubsamplingSM.Offline.IsSubmodular v)
    {A B : Finset (Fin m)} (hAB : A ⊆ B) (e : Fin m) :
    marginal v B e ≤ marginal v A e := by
  by_cases heB : e ∈ B
  · rw [marginal_eq_insert, Finset.insert_eq_of_mem heB, sub_self]
    exact marginal_nonneg hv A e
  · rw [marginal_eq_insert, marginal_eq_insert]
    exact hsub A B e hAB heB

private lemma submodular_union_le_sum_marginal {m : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) (hsub : SubsamplingSM.Offline.IsSubmodular v)
    (A D : Finset (Fin m)) :
    v (A ∪ D) - v A ≤ ∑ g ∈ D, marginal v A g := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert x D' hx ih =>
    rw [Finset.union_insert, Finset.sum_insert hx]
    have hstep : v (insert x (A ∪ D')) - v A =
        marginal v (A ∪ D') x + (v (A ∪ D') - v A) := by
      rw [marginal_eq_insert]
      ring
    rw [hstep]
    exact add_le_add (marginal_antitone hv hsub Finset.subset_union_left x) ih

private lemma submodular_diff_le_sum_marginal {m : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) (hsub : SubsamplingSM.Offline.IsSubmodular v)
    (A S : Finset (Fin m)) :
    v S - v A ≤ ∑ g ∈ S \ A, marginal v A g := by
  have hmono : v S ≤ v (A ∪ (S \ A)) := by
    rw [Finset.union_sdiff_self_eq_union]
    exact hv.1 S (A ∪ S) Finset.subset_union_right
  linarith [submodular_union_le_sum_marginal hv hsub A (S \ A)]

private lemma sum_chain_marginal_eq {m : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) (S : Finset (Fin m)) :
    ∑ e ∈ S, marginal v (S.filter (· < e)) e = v S := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ k ih =>
    by_cases hS : S.Nonempty
    · let x := S.max' hS
      have hxS : x ∈ S := Finset.max'_mem S hS
      let S' := S.erase x
      have hcard : S'.card < k := by
        rw [← hn]
        exact Finset.card_erase_lt_of_mem hxS
      have hsplit : ∑ e ∈ S, marginal v (S.filter (· < e)) e =
          marginal v (S.filter (· < x)) x +
          ∑ e ∈ S', marginal v (S.filter (· < e)) e := by
        rw [← Finset.add_sum_erase S _ hxS]
      rw [hsplit]
      have hfx : S.filter (· < x) = S' := by
        ext y
        simp only [Finset.mem_filter, S', Finset.mem_erase, ne_eq]
        constructor
        · rintro ⟨hyS, hylt⟩
          exact ⟨ne_of_lt hylt, hyS⟩
        · rintro ⟨hyne, hyS⟩
          exact ⟨hyS, lt_of_le_of_ne (Finset.le_max' S y hyS) hyne⟩
      have hfS' : ∀ e ∈ S', S.filter (· < e) = S'.filter (· < e) := by
        intro e heS'
        have hex : e < x := by
          have heS : e ∈ S := Finset.mem_of_mem_erase heS'
          have hene : e ≠ x := (Finset.mem_erase.mp heS').1
          exact lt_of_le_of_ne (Finset.le_max' S e heS) hene
        ext y
        simp only [Finset.mem_filter, S', Finset.mem_erase, ne_eq]
        constructor
        · rintro ⟨hyS, hye⟩
          exact ⟨⟨ne_of_lt (hye.trans hex), hyS⟩, hye⟩
        · rintro ⟨⟨_, hyS⟩, hye⟩
          exact ⟨hyS, hye⟩
      have hsumS' : ∑ e ∈ S', marginal v (S.filter (· < e)) e = v S' := by
        calc
          ∑ e ∈ S', marginal v (S.filter (· < e)) e
            = ∑ e ∈ S', marginal v (S'.filter (· < e)) e :=
              Finset.sum_congr rfl fun e he => by rw [hfS' e he]
          _ = v S' := ih S'.card hcard S' rfl
      rw [hfx, hsumS', marginal_eq_insert, Finset.insert_erase hxS]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty, hv.2]

private lemma sum_chain_marginal_subset_le {m : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) (hsub : SubsamplingSM.Offline.IsSubmodular v)
    {Q P : Finset (Fin m)} (hQP : Q ⊆ P) :
    ∑ e ∈ Q, marginal v (P.filter (· < e)) e ≤ v Q := by
  calc
    ∑ e ∈ Q, marginal v (P.filter (· < e)) e
      ≤ ∑ e ∈ Q, marginal v (Q.filter (· < e)) e := by
        refine Finset.sum_le_sum fun e _ => ?_
        refine marginal_antitone hv hsub ?_ e
        intro y hy
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨hQP hy.1, hy.2⟩
    _ = v Q := sum_chain_marginal_eq hv Q

private lemma mms_exists_partition {n m : ℕ} (hn : 0 < n) (v : Finset (Fin m) → ℝ) :
    ∃ fstar : Fin m → Fin n, ∀ b : Fin n,
      LittleCharity.MMS.mms v n Finset.univ ≤ v (Finset.univ.filter (fun g => fstar g = b)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : Nonempty (Fin m → Fin n) := ⟨fun _ => ⟨0, hn⟩⟩
  obtain ⟨fstar, hfstar⟩ := exists_eq_ciSup_of_finite
    (f := fun f : Fin m → Fin n => ⨅ j : Fin n, v (Finset.univ.filter (fun g => f g = j)))
  refine ⟨fstar, fun b => ?_⟩
  have hmms_eq : LittleCharity.MMS.mms v n Finset.univ =
      ⨅ j : Fin n, v (Finset.univ.filter (fun g => fstar g = j)) := hfstar.symm
  rw [hmms_eq]
  exact ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) b

def bundleOf {m n : ℕ} (fstar : Fin m → Fin n) (b : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun g => fstar g = b)

@[simp]
private lemma mem_bundleOf {m n : ℕ} (fstar : Fin m → Fin n) (b : Fin n) (e : Fin m) :
    e ∈ bundleOf fstar b ↔ fstar e = b := by
  simp [bundleOf]

private lemma bundleOf_pairwise_disjoint {m n : ℕ} (fstar : Fin m → Fin n) :
    Pairwise (fun b₁ b₂ => Disjoint (bundleOf fstar b₁) (bundleOf fstar b₂)) := by
  intro b₁ b₂ hne
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rw [mem_bundleOf] at he₁ he₂
  exact hne (he₁.symm.trans he₂)

noncomputable def suppPrice {m n : ℕ} (v : Finset (Fin m) → ℝ)
    (fstar : Fin m → Fin n) (e : Fin m) : ℝ :=
  marginal v ((bundleOf fstar (fstar e)).filter (· < e)) e / v (bundleOf fstar (fstar e))

private lemma suppPrice_bounds {m n : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) {fstar : Fin m → Fin n} {M : ℝ} (hMpos : 0 < M)
    (hpart : ∀ b : Fin n, M ≤ v (bundleOf fstar b)) (e : Fin m) :
    0 ≤ suppPrice v fstar e ∧ suppPrice v fstar e ≤ 1 := by
  have hvpos : 0 < v (bundleOf fstar (fstar e)) := lt_of_lt_of_le hMpos (hpart (fstar e))
  have hnum_nonneg : 0 ≤ marginal v ((bundleOf fstar (fstar e)).filter (· < e)) e :=
    marginal_nonneg hv _ e
  constructor
  · exact div_nonneg hnum_nonneg hvpos.le
  · rw [ suppPrice, div_le_one hvpos]
    have he_mem : e ∈ bundleOf fstar (fstar e) := (mem_bundleOf fstar _ e).mpr rfl
    calc
      marginal v ((bundleOf fstar (fstar e)).filter (· < e)) e
        ≤ ∑ g ∈ bundleOf fstar (fstar e),
            marginal v ((bundleOf fstar (fstar e)).filter (· < g)) g :=
          Finset.single_le_sum
            (f := fun g => marginal v ((bundleOf fstar (fstar e)).filter (· < g)) g)
            (fun g _ => marginal_nonneg hv _ g) he_mem
      _ = v (bundleOf fstar (fstar e)) := sum_chain_marginal_eq hv _

private lemma sum_suppPrice_bundle {m n : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) {fstar : Fin m → Fin n} {M : ℝ} (hMpos : 0 < M)
    (hpart : ∀ b : Fin n, M ≤ v (bundleOf fstar b)) (b : Fin n) :
    ∑ e ∈ bundleOf fstar b, suppPrice v fstar e = 1 := by
  have hvpos : 0 < v (bundleOf fstar b) := lt_of_lt_of_le hMpos (hpart b)
  calc
    ∑ e ∈ bundleOf fstar b, suppPrice v fstar e
      = ∑ e ∈ bundleOf fstar b,
          marginal v ((bundleOf fstar b).filter (· < e)) e / v (bundleOf fstar b) := by
          refine Finset.sum_congr rfl fun e he => ?_
          have hfe : fstar e = b := (mem_bundleOf fstar b e).mp he
          simp [suppPrice, hfe]
    _ = (∑ e ∈ bundleOf fstar b, marginal v ((bundleOf fstar b).filter (· < e)) e) /
          v (bundleOf fstar b) := by rw [← Finset.sum_div]
    _ = v (bundleOf fstar b) / v (bundleOf fstar b) := by rw [sum_chain_marginal_eq hv]
    _ = 1 := div_self hvpos.ne'

private lemma sum_suppPrice_inter_le {m n : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) (hsub : SubsamplingSM.Offline.IsSubmodular v)
    {fstar : Fin m → Fin n} {M : ℝ} (hMpos : 0 < M)
    (hpart : ∀ b : Fin n, M ≤ v (bundleOf fstar b))
    (b : Fin n) (R : Finset (Fin m)) :
    M * ∑ e ∈ bundleOf fstar b ∩ R, suppPrice v fstar e ≤ v (bundleOf fstar b ∩ R) := by
  have hvpos : 0 < v (bundleOf fstar b) := lt_of_lt_of_le hMpos (hpart b)
  have hsum_eq : ∑ e ∈ bundleOf fstar b ∩ R, suppPrice v fstar e =
      (∑ e ∈ bundleOf fstar b ∩ R, marginal v ((bundleOf fstar b).filter (· < e)) e) /
        v (bundleOf fstar b) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun e he => ?_
    have hfe : fstar e = b := (mem_bundleOf fstar b e).mp (Finset.mem_inter.mp he).1
    simp [suppPrice, hfe]
  rw [hsum_eq]
  have hchain : ∑ e ∈ bundleOf fstar b ∩ R, marginal v ((bundleOf fstar b).filter (· < e)) e ≤
      v (bundleOf fstar b ∩ R) :=
    sum_chain_marginal_subset_le hv hsub Finset.inter_subset_left
  have hdiv : (∑ e ∈ bundleOf fstar b ∩ R, marginal v ((bundleOf fstar b).filter (· < e)) e) /
      v (bundleOf fstar b) ≤ v (bundleOf fstar b ∩ R) / M := by
    calc
      (∑ e ∈ bundleOf fstar b ∩ R, marginal v ((bundleOf fstar b).filter (· < e)) e) /
          v (bundleOf fstar b)
        ≤ v (bundleOf fstar b ∩ R) / v (bundleOf fstar b) :=
          div_le_div_of_nonneg_right hchain hvpos.le
      _ ≤ v (bundleOf fstar b ∩ R) / M :=
          div_le_div_of_nonneg_left (val_nonneg hv _) hMpos (hpart b)
  calc
    M * ((∑ e ∈ bundleOf fstar b ∩ R, marginal v ((bundleOf fstar b).filter (· < e)) e) /
        v (bundleOf fstar b))
      ≤ M * (v (bundleOf fstar b ∩ R) / M) :=
        mul_le_mul_of_nonneg_left hdiv hMpos.le
    _ = v (bundleOf fstar b ∩ R) := mul_div_cancel₀ _ hMpos.ne'

end SubmodularAndMMS

/-! ### Section 4: History, `loopLaw`, `roundLaw`, `runLaw` Invariants & Disjointness -/

section HistAndRunInvariants

def nonSpecialCount {m : ℕ} (h : Hist m) : ℕ :=
  h.countP (fun r => match r with | .special _ => false | .sampled _ => true)

@[simp]
private lemma remaining_nil {m : ℕ} : remaining ([] : Hist m) = Finset.univ := rfl

@[simp]
private lemma remaining_append_singleton {m : ℕ} (h : Hist m) (r : Round m) :
    remaining (h ++ [r]) = remaining h \ r.goods := by
  simp [remaining]

@[simp]
private lemma specialCount_nil {m : ℕ} : specialCount ([] : Hist m) = 0 := rfl

@[simp]
private lemma specialCount_append_special {m : ℕ} (h : Hist m) (e : Fin m) :
    specialCount (h ++ [.special e]) = specialCount h + 1 := by
  simp [specialCount]

@[simp]
private lemma specialCount_append_sampled {m : ℕ} (h : Hist m)
    (picks : List (Finset (Fin m) × Fin m)) :
    specialCount (h ++ [.sampled picks]) = specialCount h := by
  simp [specialCount]

@[simp]
private lemma nonSpecialCount_nil {m : ℕ} : nonSpecialCount ([] : Hist m) = 0 := rfl

@[simp]
private lemma nonSpecialCount_append_special {m : ℕ} (h : Hist m) (e : Fin m) :
    nonSpecialCount (h ++ [.special e]) = nonSpecialCount h := by
  simp [nonSpecialCount]

@[simp]
private lemma nonSpecialCount_append_sampled {m : ℕ} (h : Hist m)
    (picks : List (Finset (Fin m) × Fin m)) :
    nonSpecialCount (h ++ [.sampled picks]) = nonSpecialCount h + 1 := by
  simp [nonSpecialCount]

private lemma specialCount_add_nonSpecialCount {m : ℕ} (h : Hist m) :
    specialCount h + nonSpecialCount h = h.length := by
  induction h with
  | nil => simp [specialCount, nonSpecialCount]
  | cons r tl ih =>
    cases r <;> simp [specialCount, nonSpecialCount] at ih ⊢ <;> omega

private lemma specialCount_le_length {m : ℕ} (h : Hist m) :
    specialCount h ≤ h.length := by
  have := specialCount_add_nonSpecialCount h
  omega

@[simp]
private lemma pending_nil {m : ℕ} (h : Hist m) : pending h [] = remaining h := rfl

@[simp]
private lemma pending_append_singleton {m : ℕ} (h : Hist m)
    (picks : List (Finset (Fin m) × Fin m)) (B : Finset (Fin m)) (e : Fin m) :
    pending h (picks ++ [(B, e)]) = pending h picks \ B := by
  simp [pending]

private lemma pending_subset_remaining {m : ℕ} (h : Hist m)
    (picks : List (Finset (Fin m) × Fin m)) :
    pending h picks ⊆ remaining h := by
  unfold pending
  suffices ∀ init : Finset (Fin m), init ⊆ remaining h →
      picks.foldl (fun G p => G \ p.1) init ⊆ remaining h from
    this (remaining h) Finset.Subset.rfl
  induction picks with
  | nil => intro init hinit; exact hinit
  | cons p tl ih =>
    intro init hinit
    exact ih (init \ p.1) (Finset.sdiff_subset.trans hinit)

@[simp]
private lemma items_nil {m : ℕ} : items ([] : List (Finset (Fin m) × Fin m)) = ∅ := by
  simp [items]

@[simp]
private lemma items_append_singleton {m : ℕ}
    (picks : List (Finset (Fin m) × Fin m)) (B : Finset (Fin m)) (e : Fin m) :
    items (picks ++ [(B, e)]) = insert e (items picks) := by
  ext x
  simp [items, or_comm]

private lemma loopLaw_support_items_subset {m n k : ℕ} {σ : Strategy m} {h : Hist m}
    (hLegal : Legal n k σ) (ht : specialCount h < n) :
    ∀ (fuel : ℕ) (picks picks' : List (Finset (Fin m) × Fin m)),
      items picks ⊆ remaining h →
      picks' ∈ (loopLaw n k σ h fuel picks).support →
      items picks' ⊆ remaining h
  | 0, picks, picks', hsub, hmem => by
    simp [loopLaw] at hmem
    subst hmem
    exact hsub
  | fuel + 1, picks, picks', hsub, hmem => by
    unfold loopLaw at hmem
    split_ifs at hmem with hcond hB
    · simp at hmem; subst hmem; exact hsub
    · rw [PMF.mem_support_bind_iff] at hmem
      rcases hmem with ⟨e, heB, hmem'⟩
      rw [PMF.mem_support_uniformOfFinset_iff] at heB
      have hcard_ge : k * (n - specialCount h) ≤ (pending h picks).card := by
        push_neg at hcond
        exact hcond.2
      have hBsub : σ.bucket h picks ⊆ pending h picks :=
        ((hLegal h ht).2 picks hcard_ge).1
      have he_rem : e ∈ remaining h :=
        pending_subset_remaining h picks (hBsub heB)
      refine loopLaw_support_items_subset hLegal ht fuel _ picks' ?_ hmem'
      rw [items_append_singleton]
      exact Finset.insert_subset he_rem hsub
    · simp at hmem; subst hmem; exact hsub

private lemma roundLaw_support_goods_subset {m n k : ℕ} {σ : Strategy m} {h : Hist m}
    (hLegal : Legal n k σ) (ht : specialCount h < n)
    {r : Round m} (hr : r ∈ (roundLaw n k σ h).support) :
    r.goods ⊆ remaining h := by
  unfold roundLaw at hr
  cases hch : σ.choose h with
  | some e =>
    rw [hch] at hr
    simp at hr
    subst hr
    have he : e ∈ remaining h := (hLegal h ht).1 e hch
    simpa [Round.goods] using he
  | none =>
    rw [hch, PMF.mem_support_map_iff] at hr
    rcases hr with ⟨picks, hpicks, rfl⟩
    simpa [Round.goods] using
      loopLaw_support_items_subset hLegal ht (m + 1) [] picks (by simp) hpicks

private lemma runLaw_support_valid {m n k : ℕ} {σ : Fin n → Strategy m}
    (hLegal : ∀ j : Fin n, Legal n k (σ j)) :
    ∀ (j : ℕ), j ≤ n → ∀ h ∈ (runLaw k σ j).support,
      h.length = j ∧
      (∀ (a : ℕ) (ha : a < h.length), Disjoint h[a].goods (remaining h)) ∧
      (∀ (a b : ℕ) (ha : a < h.length) (hb : b < h.length), a < b →
        Disjoint h[a].goods h[b].goods)
  | 0, _, h, hh => by
    simp [runLaw] at hh
    subst hh
    simp
  | j + 1, hjle, h', hh' => by
    have hj : j < n := Nat.lt_of_succ_le hjle
    simp only [runLaw, hj, ↓reduceDIte, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hh'
    rcases hh' with ⟨h, hh, r, hr, rfl⟩
    obtain ⟨hlen, hdisj_rem, hdisj_pair⟩ := runLaw_support_valid hLegal j hj.le h hh
    have ht : specialCount h < n := lt_of_le_of_lt (specialCount_le_length h) (hlen ▸ hj)
    have hr_sub : r.goods ⊆ remaining h :=
      roundLaw_support_goods_subset (hLegal ⟨j, hj⟩) ht hr
    have hlen' : (h ++ [r]).length = j + 1 := by simp [hlen]
    refine ⟨hlen', ?_, ?_⟩
    · intro a ha
      rw [remaining_append_singleton]
      by_cases haj : a < h.length
      · rw [List.getElem_append_left haj]
        exact (hdisj_rem a haj).mono_right Finset.sdiff_subset
      · have haeq : a = h.length := by simp [hlen] at ha haj ⊢; omega
        subst haeq
        simp [Finset.disjoint_sdiff]
    · intro a b ha hb hab
      by_cases hbj : b < h.length
      · have haj : a < h.length := hab.trans hbj
        rw [List.getElem_append_left haj, List.getElem_append_left hbj]
        exact hdisj_pair a b haj hbj hab
      · have hbeq : b = h.length := by simp [hlen] at hb hbj ⊢; omega
        subst hbeq
        rw [List.getElem_append_left hab]
        simp only [List.getElem_append_right (le_refl h.length), Nat.sub_self,
          List.getElem_singleton]
        exact (hdisj_rem a hab).mono_right hr_sub

private lemma runLaw_support_length {m n k : ℕ} {σ : Fin n → Strategy m}
    (hLegal : ∀ j : Fin n, Legal n k (σ j)) {j : ℕ} (hj : j ≤ n)
    {h : Hist m} (hh : h ∈ (runLaw k σ j).support) :
    h.length = j :=
  (runLaw_support_valid hLegal j hj h hh).1

private lemma runLaw_support_isPartialAllocation {m n k : ℕ} {σ : Fin n → Strategy m}
    (hLegal : ∀ j : Fin n, Legal n k (σ j))
    {h : Hist m} (hh : h ∈ (runLaw k σ n).support) :
    LittleCharity.EFX.IsPartialAllocation (fun i : Fin n => (allocOf h i : Finset (Fin m))) := by
  obtain ⟨hlen, _, hpair⟩ := runLaw_support_valid hLegal n le_rfl h hh
  intro i₁ i₂ hne
  have hi₁ : i₁.val < h.length := hlen ▸ i₁.isLt
  have hi₂ : i₂.val < h.length := hlen ▸ i₂.isLt
  have ha₁ : allocOf h i₁ = h[i₁.val].goods := by
    simp [allocOf, List.getElem?_eq_getElem hi₁]
  have ha₂ : allocOf h i₂ = h[i₂.val].goods := by
    simp [allocOf, List.getElem?_eq_getElem hi₂]
  dsimp only
  rw [ha₁, ha₂]
  rcases lt_trichotomy i₁.val i₂.val with hlt | heq | hgt
  · exact hpair i₁.val i₂.val hi₁ hi₂ hlt
  · exact absurd (Fin.ext heq) hne
  · exact (hpair i₂.val i₁.val hi₂ hi₁ hgt).symm

private lemma runLaw_toOuterMeasure_allocOf_after {m n k : ℕ} {σ : Fin n → Strategy m}
    (hLegal : ∀ j : Fin n, Legal n k (σ j))
    (i : Fin n) (P : Finset (Fin m) → Prop) :
    ∀ j : ℕ, i.val + 1 ≤ j → j ≤ n →
      (runLaw k σ j).toOuterMeasure {h | P (allocOf h i)} =
      (runLaw k σ (i.val + 1)).toOuterMeasure {h | P (allocOf h i)} := by
  intro j hij hjn
  induction j with
  | zero => omega
  | succ j' ih =>
    by_cases heq : j' = i.val
    · subst heq; rfl
    · have hij' : i.val + 1 ≤ j' := by omega
      have hjn' : j' < n := Nat.lt_of_succ_le hjn
      rw [← ih hij' hjn'.le]
      simp only [runLaw, hjn', ↓reduceDIte]
      refine toOuterMeasure_bind_iff (runLaw k σ j') _ _ _ ?_
      intro h hh h' hh'
      rw [PMF.mem_support_map_iff] at hh'
      rcases hh' with ⟨r, _, rfl⟩
      have hlen : h.length = j' := runLaw_support_length hLegal hjn'.le hh
      have hilt : i.val < h.length := by omega
      have halloc : allocOf (h ++ [r]) i = allocOf h i := by
        simp [allocOf, List.getElem?_append_left hilt]
      simp [halloc]

end HistAndRunInvariants

/-! ### Section 5: Lemma 4.3 — Deterministic Safe-Strategy Greedy Bucketing Guarantee -/

section SafeGreedyGuarantee

private lemma loopLaw_greedy_charge_step {m n : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) (hsub : SubsamplingSM.Offline.IsSubmodular v)
    {τ : ℝ} {σ : Strategy m} {h : Hist m}
    (ht : specialCount h < n)
    (hbucket : ∀ picks : List (Finset (Fin m) × Fin m),
      4 * (n - specialCount h) ≤ (pending h picks).card →
        σ.bucket h picks ⊆ pending h picks ∧
        (σ.bucket h picks).card = 4 * (n - specialCount h) ∧
        ∀ x ∈ σ.bucket h picks, ∀ y ∈ pending h picks \ σ.bucket h picks,
          marginal v (items picks) y ≤ marginal v (items picks) x) :
    ∀ (fuel : ℕ) (picks picks' : List (Finset (Fin m) × Fin m)) (Δ : ℝ),
      (pending h picks).card < fuel →
      0 ≤ Δ →
      items picks ⊆ remaining h →
      Disjoint (items picks) (pending h picks) →
      (∀ y ∈ pending h picks, marginal v (items picks) y ≤ Δ) →
      ∑ g ∈ (remaining h \ pending h picks) \ items picks, marginal v (items picks) g ≤
        4 * ((n - specialCount h : ℕ) : ℝ) * τ +
          4 * ((n - specialCount h : ℕ) : ℝ) * (v (items picks) - Δ) →
      picks' ∈ (loopLaw n 4 σ h fuel picks).support →
      ∑ g ∈ remaining h \ items picks', marginal v (items picks') g ≤
        4 * ((n - specialCount h : ℕ) : ℝ) * (τ + v (items picks'))
  | 0, picks, _, _, hfuel, _, _, _, _, _, _ => by omega
  | fuel + 1, picks, picks', Δ, hfuel, hΔ0, hAsub, hdisj, hG, hU, hmem => by
    let s : ℕ := 4 * (n - specialCount h)
    have hs_pos : 0 < s := by dsimp [s]; omega
    unfold loopLaw at hmem
    by_cases hlt : (pending h picks).card < s
    · have hcond : 4 * (n - specialCount h) = 0 ∨
          (pending h picks).card < 4 * (n - specialCount h) := Or.inr hlt
      simp only [hcond, ↓reduceIte, PMF.mem_support_pure_iff] at hmem
      rw [hmem]
      have hGsub : pending h picks ⊆ remaining h := pending_subset_remaining h picks
      have hpart : remaining h \ items picks =
          ((remaining h \ pending h picks) \ items picks) ∪ pending h picks := by
        ext g
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hgR, hgA⟩
          by_cases hgG : g ∈ pending h picks
          · exact Or.inr hgG
          · exact Or.inl ⟨⟨hgR, hgG⟩, hgA⟩
        · rintro (⟨⟨hgR, _⟩, hgA⟩ | hgG)
          · exact ⟨hgR, hgA⟩
          · exact ⟨hGsub hgG, Finset.disjoint_right.mp hdisj hgG⟩
      have hdisj_part : Disjoint ((remaining h \ pending h picks) \ items picks)
          (pending h picks) := by
        rw [Finset.disjoint_left]
        intro g hg hgG
        simp only [Finset.mem_sdiff] at hg
        exact hg.1.2 hgG
      rw [hpart, Finset.sum_union hdisj_part]
      have hsumG : ∑ y ∈ pending h picks, marginal v (items picks) y ≤
          4 * ((n - specialCount h : ℕ) : ℝ) * Δ := by
        calc
          ∑ y ∈ pending h picks, marginal v (items picks) y
            ≤ ∑ _y ∈ pending h picks, Δ := Finset.sum_le_sum fun y hy => hG y hy
          _ = ((pending h picks).card : ℝ) * Δ := by simp
          _ ≤ (s : ℝ) * Δ := by
              refine mul_le_mul_of_nonneg_right ?_ hΔ0
              exact_mod_cast hlt.le
          _ = 4 * ((n - specialCount h : ℕ) : ℝ) * Δ := by dsimp [s]; push_cast; ring
      linarith
    · have hs_le : 4 * (n - specialCount h) ≤ (pending h picks).card := le_of_not_gt hlt
      have hcond : ¬ (4 * (n - specialCount h) = 0 ∨
          (pending h picks).card < 4 * (n - specialCount h)) := by
        push_neg
        exact ⟨hs_pos.ne', hs_le⟩
      obtain ⟨hBsub, hBcard, hgreedy⟩ := hbucket picks hs_le
      have hBne : (σ.bucket h picks).Nonempty :=
        Finset.card_pos.mp (by omega)
      simp only [hcond, ↓reduceIte, ↓reduceDIte, hBne, PMF.mem_support_bind_iff,
        PMF.mem_support_uniformOfFinset_iff] at hmem
      rcases hmem with ⟨e, heB, hmem'⟩
      let B := σ.bucket h picks
      let picks1 := picks ++ [(B, e)]
      let Δ' := marginal v (items picks) e
      have heG : e ∈ pending h picks := hBsub heB
      have heR : e ∈ remaining h := pending_subset_remaining h picks heG
      have he_not_A : e ∉ items picks := Finset.disjoint_right.mp hdisj heG
      have hfuel1 : (pending h picks1).card < fuel := by
        simp only [picks1, pending_append_singleton]
        have hBsub' : B ⊆ pending h picks := hBsub
        have hBcard' : B.card = 4 * (n - specialCount h) := hBcard
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBsub']
        omega
      have hΔ'0 : 0 ≤ Δ' := marginal_nonneg hv _ e
      have hA1sub : items picks1 ⊆ remaining h := by
        simp only [picks1, items_append_singleton]
        exact Finset.insert_subset heR hAsub
      have hdisj1 : Disjoint (items picks1) (pending h picks1) := by
        simp only [picks1, items_append_singleton, pending_append_singleton]
        rw [Finset.disjoint_insert_left]
        refine ⟨?_, hdisj.mono_right Finset.sdiff_subset⟩
        intro hmem_sdiff
        exact (Finset.mem_sdiff.mp hmem_sdiff).2 heB
      have hA_sub_A1 : items picks ⊆ items picks1 := by
        simp [picks1, items_append_singleton]
      have hG1 : ∀ y ∈ pending h picks1, marginal v (items picks1) y ≤ Δ' := by
        intro y hy
        simp only [picks1, pending_append_singleton] at hy
        calc
          marginal v (items picks1) y
            ≤ marginal v (items picks) y := marginal_antitone hv hsub hA_sub_A1 y
          _ ≤ marginal v (items picks) e := hgreedy e heB y hy
          _ = Δ' := rfl
      have hU1_eq : (remaining h \ pending h picks1) \ items picks1 =
          ((remaining h \ pending h picks) \ items picks) ∪ (B \ {e}) := by
        have hB_R : B ⊆ remaining h := hBsub.trans (pending_subset_remaining h picks)
        ext g
        simp only [picks1, pending_append_singleton, items_append_singleton,
          Finset.mem_sdiff, Finset.mem_insert, not_or, Finset.mem_union, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hgR, hgGB⟩, hge, hgA⟩
          by_cases hgB : g ∈ B
          · exact Or.inr ⟨hgB, hge⟩
          · have hgG : g ∉ pending h picks := fun hgG => hgGB ⟨hgG, hgB⟩
            exact Or.inl ⟨⟨hgR, hgG⟩, hgA⟩
        · rintro (⟨⟨hgR, hgG⟩, hgA⟩ | ⟨hgB, hge⟩)
          · refine ⟨⟨hgR, fun h => hgG h.1⟩, ?_, hgA⟩
            rintro rfl
            exact hgG heG
          · refine ⟨⟨hB_R hgB, fun h => h.2 hgB⟩, hge, ?_⟩
            exact Finset.disjoint_right.mp hdisj (hBsub hgB)
      have hU1_disj : Disjoint ((remaining h \ pending h picks) \ items picks) (B \ {e}) := by
        rw [Finset.disjoint_left]
        intro g hg1 hg2
        simp only [Finset.mem_sdiff] at hg1 hg2
        exact hg1.1.2 (hBsub hg2.1)
      have hU1 : ∑ g ∈ (remaining h \ pending h picks1) \ items picks1,
          marginal v (items picks1) g ≤
            4 * ((n - specialCount h : ℕ) : ℝ) * τ +
              4 * ((n - specialCount h : ℕ) : ℝ) * (v (items picks1) - Δ') := by
        rw [hU1_eq, Finset.sum_union hU1_disj]
        have hp1 : ∑ g ∈ (remaining h \ pending h picks) \ items picks,
            marginal v (items picks1) g ≤
              4 * ((n - specialCount h : ℕ) : ℝ) * τ +
                4 * ((n - specialCount h : ℕ) : ℝ) * (v (items picks) - Δ) := by
          calc
            ∑ g ∈ (remaining h \ pending h picks) \ items picks, marginal v (items picks1) g
              ≤ ∑ g ∈ (remaining h \ pending h picks) \ items picks, marginal v (items picks) g :=
                Finset.sum_le_sum fun g _ => marginal_antitone hv hsub hA_sub_A1 g
            _ ≤ _ := hU
        have hp2 : ∑ g ∈ B \ {e}, marginal v (items picks1) g ≤
            4 * ((n - specialCount h : ℕ) : ℝ) * Δ := by
          calc
            ∑ g ∈ B \ {e}, marginal v (items picks1) g
              ≤ ∑ g ∈ B \ {e}, marginal v (items picks) g :=
                Finset.sum_le_sum fun g _ => marginal_antitone hv hsub hA_sub_A1 g
            _ ≤ ∑ _g ∈ B \ {e}, Δ :=
                Finset.sum_le_sum fun g hg => hG g (hBsub (Finset.sdiff_subset hg))
            _ = ((B \ {e}).card : ℝ) * Δ := by simp
            _ ≤ (B.card : ℝ) * Δ := by
                refine mul_le_mul_of_nonneg_right ?_ hΔ0
                exact_mod_cast Finset.card_le_card Finset.sdiff_subset
            _ = 4 * ((n - specialCount h : ℕ) : ℝ) * Δ := by
                rw [hBcard]; push_cast; ring
        have hvA1 : v (items picks1) - Δ' = v (items picks) := by
          simp only [picks1, items_append_singleton, Δ', marginal_eq_insert]
          ring
        rw [hvA1]
        linarith
      exact loopLaw_greedy_charge_step hv hsub ht hbucket fuel picks1 picks' Δ'
        hfuel1 hΔ'0 hA1sub hdisj1 hG1 hU1 hmem'

private lemma loopLaw_greedy_charge_top {m n : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) (hsub : SubsamplingSM.Offline.IsSubmodular v)
    {τ : ℝ} (hτ0 : 0 ≤ τ) {σ : Strategy m} {h : Hist m}
    (ht : specialCount h < n)
    (hall : ∀ e ∈ remaining h, v {e} < τ)
    (hbucket : ∀ picks : List (Finset (Fin m) × Fin m),
      4 * (n - specialCount h) ≤ (pending h picks).card →
        σ.bucket h picks ⊆ pending h picks ∧
        (σ.bucket h picks).card = 4 * (n - specialCount h) ∧
        ∀ x ∈ σ.bucket h picks, ∀ y ∈ pending h picks \ σ.bucket h picks,
          marginal v (items picks) y ≤ marginal v (items picks) x)
    {picks' : List (Finset (Fin m) × Fin m)}
    (hmem : picks' ∈ (loopLaw n 4 σ h (m + 1) []).support) :
    ∑ g ∈ remaining h \ items picks', marginal v (items picks') g ≤
      4 * ((n - specialCount h : ℕ) : ℝ) * (τ + v (items picks')) := by
  let s : ℕ := 4 * (n - specialCount h)
  have hs_pos : 0 < s := by dsimp [s]; omega
  unfold loopLaw at hmem
  by_cases hlt : (pending h []).card < s
  · have hcond : 4 * (n - specialCount h) = 0 ∨
        (pending h []).card < 4 * (n - specialCount h) := Or.inr hlt
    simp only [hcond, ↓reduceIte, PMF.mem_support_pure_iff] at hmem
    subst hmem
    simp only [items_nil, Finset.sdiff_empty, hv.2, add_zero, marginal_empty hv]
    calc
      ∑ g ∈ remaining h, v {g}
        ≤ ∑ _g ∈ remaining h, τ := Finset.sum_le_sum fun g hg => (hall g hg).le
      _ = ((remaining h).card : ℝ) * τ := by simp
      _ ≤ (s : ℝ) * τ := by
          refine mul_le_mul_of_nonneg_right ?_ hτ0
          exact_mod_cast hlt.le
      _ = 4 * ((n - specialCount h : ℕ) : ℝ) * τ := by dsimp [s]; push_cast; ring
  · have hs_le : 4 * (n - specialCount h) ≤ (pending h []).card := le_of_not_gt hlt
    have hcond : ¬ (4 * (n - specialCount h) = 0 ∨
        (pending h []).card < 4 * (n - specialCount h)) := by
      push_neg; exact ⟨hs_pos.ne', hs_le⟩
    obtain ⟨hBsub, hBcard, hgreedy⟩ := hbucket [] hs_le
    have hBne : (σ.bucket h []).Nonempty := Finset.card_pos.mp (by omega)
    simp only [hcond, ↓reduceIte, ↓reduceDIte, hBne, PMF.mem_support_bind_iff,
      PMF.mem_support_uniformOfFinset_iff] at hmem
    rcases hmem with ⟨e, heB, hmem'⟩
    let B := σ.bucket h []
    let picks1 : List (Finset (Fin m) × Fin m) := [(B, e)]
    let Δ1 := v {e}
    have heR : e ∈ remaining h := hBsub heB
    have hcardR : (remaining h).card ≤ m := by
      simpa using Finset.card_le_univ (remaining h)
    have hfuel1 : (pending h picks1).card < m := by
      have hp1 : pending h picks1 = remaining h \ B := rfl
      have hBsub' : B ⊆ remaining h := hBsub
      have hBcard' : B.card = 4 * (n - specialCount h) := hBcard
      have hs_le' : 4 * (n - specialCount h) ≤ (remaining h).card := hs_le
      rw [hp1, Finset.card_sdiff, Finset.inter_eq_left.mpr hBsub']
      omega
    have hΔ1_0 : 0 ≤ Δ1 := val_nonneg hv {e}
    have hA1sub : items picks1 ⊆ remaining h := by
      simpa [picks1, items] using heR
    have hdisj1 : Disjoint (items picks1) (pending h picks1) := by
      have hA1 : items picks1 = {e} := by simp [picks1, items]
      have hG1 : pending h picks1 = remaining h \ B := rfl
      rw [hA1, hG1, Finset.disjoint_singleton_left]
      intro hmem_sdiff
      exact (Finset.mem_sdiff.mp hmem_sdiff).2 heB
    have hG1 : ∀ y ∈ pending h picks1, marginal v (items picks1) y ≤ Δ1 := by
      intro y hy
      have hA1 : items picks1 = {e} := by simp [picks1, items]
      rw [hA1]
      calc
        marginal v {e} y ≤ marginal v ∅ y :=
          marginal_antitone hv hsub (Finset.empty_subset {e}) y
        _ ≤ marginal v ∅ e := by
            have hy' : y ∈ pending h [] \ B := hy
            simpa [items_nil] using hgreedy e heB y hy'
        _ = Δ1 := marginal_empty hv e
    have hU1_eq : (remaining h \ pending h picks1) \ items picks1 = B \ {e} := by
      have hA1 : items picks1 = {e} := by simp [picks1, items]
      have hG1' : pending h picks1 = remaining h \ B := rfl
      rw [hA1, hG1']
      ext g
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hgR, hgRB⟩, hge⟩
        refine ⟨?_, hge⟩
        by_contra hgB
        exact hgRB ⟨hgR, hgB⟩
      · rintro ⟨hgB, hge⟩
        exact ⟨⟨hBsub hgB, fun h => h.2 hgB⟩, hge⟩
    have hU1 : ∑ g ∈ (remaining h \ pending h picks1) \ items picks1,
        marginal v (items picks1) g ≤
          4 * ((n - specialCount h : ℕ) : ℝ) * τ +
            4 * ((n - specialCount h : ℕ) : ℝ) * (v (items picks1) - Δ1) := by
      have hA1 : items picks1 = {e} := by simp [picks1, items]
      rw [hU1_eq, hA1]
      have hsub0 : v ({e} : Finset (Fin m)) - Δ1 = 0 := sub_self _
      rw [hsub0, mul_zero, add_zero]
      calc
        ∑ g ∈ B \ {e}, marginal v {e} g
          ≤ ∑ g ∈ B \ {e}, marginal v ∅ g :=
            Finset.sum_le_sum fun g _ => marginal_antitone hv hsub (Finset.empty_subset _) g
        _ = ∑ g ∈ B \ {e}, v {g} :=
            Finset.sum_congr rfl fun g _ => marginal_empty hv g
        _ ≤ ∑ _g ∈ B \ {e}, τ :=
            Finset.sum_le_sum fun g hg => (hall g (hBsub (Finset.sdiff_subset hg))).le
        _ = ((B \ {e}).card : ℝ) * τ := by simp
        _ ≤ (B.card : ℝ) * τ := by
            refine mul_le_mul_of_nonneg_right ?_ hτ0
            exact_mod_cast Finset.card_le_card Finset.sdiff_subset
        _ = 4 * ((n - specialCount h : ℕ) : ℝ) * τ := by
            rw [hBcard]; push_cast; ring
    exact loopLaw_greedy_charge_step hv hsub ht hbucket m picks1 picks' Δ1
      hfuel1 hΔ1_0 hA1sub hdisj1 hG1 hU1 hmem'

private lemma safe_round_guarantee {m n : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) (hsub : SubsamplingSM.Offline.IsSubmodular v)
    {fstar : Fin m → Fin n} {τ : ℝ} (hτ : 0 < τ)
    {σ : Strategy m} (hSafe : IsSafe n 4 τ v σ)
    {h : Hist m} (ht : specialCount h < n)
    {B_act : Finset (Fin n)} (hBcard : B_act.card = n - specialCount h)
    (hPi : 9 * τ * ((n - specialCount h : ℕ) : ℝ) ≤
      ∑ b ∈ B_act, v (bundleOf fstar b ∩ remaining h))
    {r : Round m} (hr : r ∈ (roundLaw n 4 σ h).support) :
    τ ≤ v r.goods := by
  obtain ⟨hspec, hsamp⟩ := hSafe hτ h ht
  by_cases hex : ∃ e ∈ remaining h, τ ≤ v {e}
  · rcases hex with ⟨e₀, he₀R, he₀τ⟩
    obtain ⟨e_star, _, hchoose, hmax⟩ := hspec ⟨e₀, he₀R, he₀τ⟩
    unfold roundLaw at hr
    rw [hchoose, PMF.mem_support_pure_iff] at hr
    subst hr
    exact he₀τ.trans (hmax e₀ he₀R)
  · push_neg at hex
    obtain ⟨hchoose, hbucket⟩ := hsamp hex
    unfold roundLaw at hr
    rw [hchoose, PMF.mem_support_map_iff] at hr
    rcases hr with ⟨picks, hpicks, rfl⟩
    let A := items picks
    have hcharge : ∑ g ∈ remaining h \ A, marginal v A g ≤
        4 * ((n - specialCount h : ℕ) : ℝ) * (τ + v A) :=
      loopLaw_greedy_charge_top hv hsub hτ.le ht hex hbucket hpicks
    have hsum_diff : ∑ b ∈ B_act, (v (bundleOf fstar b ∩ remaining h) - v A) ≤
        ∑ g ∈ remaining h \ A, marginal v A g := by
      calc
        ∑ b ∈ B_act, (v (bundleOf fstar b ∩ remaining h) - v A)
          ≤ ∑ b ∈ B_act, ∑ g ∈ (bundleOf fstar b ∩ remaining h) \ A, marginal v A g :=
            Finset.sum_le_sum fun b _ => submodular_diff_le_sum_marginal hv hsub A _
        _ = ∑ g ∈ B_act.biUnion (fun b => (bundleOf fstar b ∩ remaining h) \ A),
              marginal v A g := by
            rw [Finset.sum_biUnion]
            intro b₁ _ b₂ _ hne
            exact ((bundleOf_pairwise_disjoint fstar hne).mono
              Finset.inter_subset_left Finset.inter_subset_left).mono
              Finset.sdiff_subset Finset.sdiff_subset
        _ ≤ ∑ g ∈ remaining h \ A, marginal v A g := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun g _ _ => marginal_nonneg hv A g
            intro g hg
            rw [Finset.mem_biUnion] at hg
            rcases hg with ⟨b, _, hgb⟩
            simp only [Finset.mem_sdiff, Finset.mem_inter] at hgb ⊢
            exact ⟨hgb.1.2, hgb.2⟩
    have hsum_expand : ∑ b ∈ B_act, (v (bundleOf fstar b ∩ remaining h) - v A) =
        (∑ b ∈ B_act, v (bundleOf fstar b ∩ remaining h)) -
          ((n - specialCount h : ℕ) : ℝ) * v A := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, hBcard, nsmul_eq_mul]
    have hNcast : ((n - specialCount h : ℕ) : ℝ) = (n : ℝ) - (specialCount h : ℝ) :=
      Nat.cast_sub ht.le
    have hNpos : (0 : ℝ) < ((n - specialCount h : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt ht
    have hineq : 9 * τ * ((n - specialCount h : ℕ) : ℝ) -
        ((n - specialCount h : ℕ) : ℝ) * v A ≤
          4 * ((n - specialCount h : ℕ) : ℝ) * (τ + v A) := by
      linarith
    have h5 : 5 * ((n - specialCount h : ℕ) : ℝ) * τ ≤
        5 * ((n - specialCount h : ℕ) : ℝ) * v A := by
      linarith
    have h5pos : 0 < 5 * ((n - specialCount h : ℕ) : ℝ) := by positivity
    exact le_of_mul_le_mul_left h5 h5pos

end SafeGreedyGuarantee

/-! ### Section 6: `loopLaw` MGF Bound, Active Bundles, Deficit Supermartingale & Single-Agent Tail -/

section DeficitMGF

private lemma loopLaw_mgf {m n k : ℕ} (hk : 0 < k) {σ : Strategy m} {h : Hist m}
    (hLegal : Legal n k σ) (ht : specialCount h < n)
    {lam : ℝ} (hlam : 0 ≤ lam) {x : Fin m → ℝ}
    (hx : ∀ e : Fin m, 0 ≤ x e ∧ x e ≤ 1) :
    ∀ (fuel : ℕ) (picks : List (Finset (Fin m) × Fin m)),
      (pending h picks).card ≤ fuel →
      Disjoint (items picks) (pending h picks) →
      pmfExp (loopLaw n k σ h fuel picks)
        (fun picks' => ENNReal.ofReal (Real.exp (lam * ∑ g ∈ items picks', x g))) ≤
      ENNReal.ofReal (Real.exp
        (lam * ∑ g ∈ items picks, x g +
          ((Real.exp lam - 1) / ((k * (n - specialCount h) : ℕ) : ℝ)) *
            ∑ g ∈ pending h picks, x g))
  | 0, picks, hfuel, _ => by
    have hempty : pending h picks = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hfuel)
    simp [loopLaw, pmfExp_pure, hempty]
  | fuel + 1, picks, hfuel, hdisj => by
    let s : ℕ := k * (n - specialCount h)
    have hs_pos : 0 < s := Nat.mul_pos hk (Nat.sub_pos_of_lt ht)
    have hs_real_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos
    unfold loopLaw
    by_cases hlt : (pending h picks).card < s
    · have hcond : k * (n - specialCount h) = 0 ∨
          (pending h picks).card < k * (n - specialCount h) := Or.inr hlt
      simp only [hcond, ↓reduceIte, pmfExp_pure]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have hexp_ge : 0 ≤ Real.exp lam - 1 := sub_nonneg.mpr (Real.one_le_exp hlam)
      have hsum_ge : 0 ≤ ∑ g ∈ pending h picks, x g :=
        Finset.sum_nonneg fun g _ => (hx g).1
      have hextra : 0 ≤ ((Real.exp lam - 1) / (s : ℝ)) * ∑ g ∈ pending h picks, x g :=
        mul_nonneg (div_nonneg hexp_ge hs_real_pos.le) hsum_ge
      dsimp [s] at hextra
      linarith
    · have hs_le : k * (n - specialCount h) ≤ (pending h picks).card := le_of_not_gt hlt
      have hcond : ¬ (k * (n - specialCount h) = 0 ∨
          (pending h picks).card < k * (n - specialCount h)) := by
        push_neg; exact ⟨hs_pos.ne', hs_le⟩
      obtain ⟨hBsub, hBcard⟩ := (hLegal h ht).2 picks hs_le
      have hBne : (σ.bucket h picks).Nonempty := Finset.card_pos.mp (by omega)
      simp only [hcond, ↓reduceIte, ↓reduceDIte, hBne, pmfExp_bind, pmfExp_uniformOfFinset]
      let B := σ.bucket h picks
      have hstep_each : ∀ e ∈ B,
          pmfExp (loopLaw n k σ h fuel (picks ++ [(B, e)]))
            (fun picks' => ENNReal.ofReal (Real.exp (lam * ∑ g ∈ items picks', x g))) ≤
          ENNReal.ofReal (Real.exp (lam * x e)) *
            ENNReal.ofReal (Real.exp
              (lam * ∑ g ∈ items picks, x g +
                ((Real.exp lam - 1) / (s : ℝ)) * ∑ g ∈ pending h picks \ B, x g)) := by
        intro e heB
        have hfuel1 : (pending h (picks ++ [(B, e)])).card ≤ fuel := by
          rw [pending_append_singleton, Finset.card_sdiff, Finset.inter_eq_left.mpr hBsub]
          dsimp [B] at *
          omega
        have hdisj1 : Disjoint (items (picks ++ [(B, e)])) (pending h (picks ++ [(B, e)])) := by
          rw [items_append_singleton, pending_append_singleton, Finset.disjoint_insert_left]
          refine ⟨?_, hdisj.mono_right Finset.sdiff_subset⟩
          intro hmem_sdiff
          exact (Finset.mem_sdiff.mp hmem_sdiff).2 heB
        have he_not_A : e ∉ items picks := Finset.disjoint_right.mp hdisj (hBsub heB)
        have hih := loopLaw_mgf hk hLegal ht hlam hx fuel (picks ++ [(B, e)]) hfuel1 hdisj1
        refine hih.trans ?_
        rw [items_append_singleton, Finset.sum_insert he_not_A, pending_append_singleton,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        dsimp [s]
        refine le_of_eq (congrArg (fun z => ENNReal.ofReal (Real.exp z)) ?_)
        ring
      have hsum_le : (B.card : ℝ≥0∞)⁻¹ * ∑ e ∈ B,
          pmfExp (loopLaw n k σ h fuel (picks ++ [(B, e)]))
            (fun picks' => ENNReal.ofReal (Real.exp (lam * ∑ g ∈ items picks', x g))) ≤
          (B.card : ℝ≥0∞)⁻¹ *
            ((∑ e ∈ B, ENNReal.ofReal (Real.exp (lam * x e))) *
              ENNReal.ofReal (Real.exp
                (lam * ∑ g ∈ items picks, x g +
                  ((Real.exp lam - 1) / (s : ℝ)) * ∑ g ∈ pending h picks \ B, x g))) := by
        rw [Finset.sum_mul]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e he => hstep_each e he) zero_le'
      refine hsum_le.trans ?_
      have hcard_inv : (B.card : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / (s : ℝ)) := by
        have hscard : B.card = s := hBcard
        rw [hscard, one_div, ENNReal.ofReal_inv_of_pos hs_real_pos, ENNReal.ofReal_natCast]
      have hsum_ofReal : ∑ e ∈ B, ENNReal.ofReal (Real.exp (lam * x e)) =
          ENNReal.ofReal (∑ e ∈ B, Real.exp (lam * x e)) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun e _ => (Real.exp_pos _).le]
      rw [hcard_inv, hsum_ofReal, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (s : ℝ)),
        ← ENNReal.ofReal_mul (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun e _ => (Real.exp_pos _).le))]
      refine ENNReal.ofReal_le_ofReal ?_
      have havg : (1 / (s : ℝ)) * ∑ e ∈ B, Real.exp (lam * x e) ≤
          Real.exp (((Real.exp lam - 1) / (s : ℝ)) * ∑ e ∈ B, x e) := by
        have hlin : ∑ e ∈ B, Real.exp (lam * x e) ≤
            (s : ℝ) + (Real.exp lam - 1) * ∑ e ∈ B, x e := by
          calc
            ∑ e ∈ B, Real.exp (lam * x e)
              ≤ ∑ e ∈ B, (1 + (Real.exp lam - 1) * x e) :=
                Finset.sum_le_sum fun e _ => exp_mul_le_linear hlam (hx e).1 (hx e).2
            _ = (B.card : ℝ) + (Real.exp lam - 1) * ∑ e ∈ B, x e := by
                rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
                  ← Finset.mul_sum]
            _ = (s : ℝ) + (Real.exp lam - 1) * ∑ e ∈ B, x e := by rw [hBcard]
        calc
          (1 / (s : ℝ)) * ∑ e ∈ B, Real.exp (lam * x e)
            ≤ (1 / (s : ℝ)) * ((s : ℝ) + (Real.exp lam - 1) * ∑ e ∈ B, x e) :=
              mul_le_mul_of_nonneg_left hlin (by positivity)
          _ = (((Real.exp lam - 1) / (s : ℝ)) * ∑ e ∈ B, x e) + 1 := by
              field_simp [hs_real_pos.ne']
              ring
          _ ≤ Real.exp (((Real.exp lam - 1) / (s : ℝ)) * ∑ e ∈ B, x e) :=
              Real.add_one_le_exp _
      calc
        ((1 / (s : ℝ)) * ∑ e ∈ B, Real.exp (lam * x e)) *
            Real.exp (lam * ∑ g ∈ items picks, x g +
              ((Real.exp lam - 1) / (s : ℝ)) * ∑ g ∈ pending h picks \ B, x g)
          ≤ Real.exp (((Real.exp lam - 1) / (s : ℝ)) * ∑ e ∈ B, x e) *
              Real.exp (lam * ∑ g ∈ items picks, x g +
                ((Real.exp lam - 1) / (s : ℝ)) * ∑ g ∈ pending h picks \ B, x g) :=
            mul_le_mul_of_nonneg_right havg (Real.exp_pos _).le
        _ = Real.exp
              (lam * ∑ g ∈ items picks, x g +
                ((Real.exp lam - 1) / ((k * (n - specialCount h) : ℕ) : ℝ)) *
                  ∑ g ∈ pending h picks, x g) := by
            rw [← Real.exp_add]
            congr 1
            have hsdiff : ∑ g ∈ pending h picks \ B, x g + ∑ e ∈ B, x e =
                ∑ g ∈ pending h picks, x g := Finset.sum_sdiff hBsub
            rw [← hsdiff]
            dsimp [s]
            ring

def stepActive {m n : ℕ} (fstar : Fin m → Fin n) (B : Finset (Fin n)) (r : Round m) :
    Finset (Fin n) :=
  match r with
  | .sampled _ => B
  | .special e =>
    if fstar e ∈ B then B.erase (fstar e)
    else if hB : B.Nonempty then B.erase (B.min' hB)
    else B

def activeBundles {m n : ℕ} (fstar : Fin m → Fin n) (h : Hist m) : Finset (Fin n) :=
  h.foldl (stepActive fstar) Finset.univ

@[simp]
private lemma activeBundles_nil {m n : ℕ} (fstar : Fin m → Fin n) :
    activeBundles fstar [] = Finset.univ := rfl

@[simp]
private lemma activeBundles_append_singleton {m n : ℕ} (fstar : Fin m → Fin n)
    (h : Hist m) (r : Round m) :
    activeBundles fstar (h ++ [r]) = stepActive fstar (activeBundles fstar h) r := by
  simp [activeBundles]

private lemma card_activeBundles {m n : ℕ} (fstar : Fin m → Fin n) (h : Hist m) :
    (activeBundles fstar h).card = n - specialCount h := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h r ih =>
    cases r with
    | sampled picks =>
      simp [stepActive, ih]
    | special e =>
      simp only [activeBundles_append_singleton, specialCount_append_special, stepActive]
      by_cases hfe : fstar e ∈ activeBundles fstar h
      · simp only [hfe, ↓reduceIte, Finset.card_erase_of_mem hfe, ih]
        omega
      · simp only [hfe, ↓reduceIte]
        by_cases hB : (activeBundles fstar h).Nonempty
        · simp only [hB, ↓reduceDIte, Finset.card_erase_of_mem (Finset.min'_mem _ hB), ih]
          omega
        · simp only [hB, ↓reduceDIte]
          have hempty : activeBundles fstar h = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
          have h0 : n - specialCount h = 0 := by rw [← ih, hempty]; simp
          rw [hempty]
          simp
          omega

noncomputable def survWeight {m n : ℕ} (v : Finset (Fin m) → ℝ)
    (fstar : Fin m → Fin n) (h : Hist m) : ℝ :=
  ∑ b ∈ activeBundles fstar h, ∑ e ∈ bundleOf fstar b ∩ remaining h, suppPrice v fstar e

noncomputable def deficit {m n : ℕ} (v : Finset (Fin m) → ℝ)
    (fstar : Fin m → Fin n) (h : Hist m) : ℝ :=
  ((n - specialCount h : ℕ) : ℝ) - survWeight v fstar h

private lemma survWeight_eq_sum_remaining {m n : ℕ} (v : Finset (Fin m) → ℝ)
    (fstar : Fin m → Fin n) (h : Hist m) :
    survWeight v fstar h =
      ∑ e ∈ remaining h, (if fstar e ∈ activeBundles fstar h then suppPrice v fstar e else 0) := by
  unfold survWeight
  have hbi : ∑ b ∈ activeBundles fstar h,
      ∑ e ∈ bundleOf fstar b ∩ remaining h, suppPrice v fstar e =
      ∑ e ∈ (activeBundles fstar h).biUnion (fun b => bundleOf fstar b ∩ remaining h),
        suppPrice v fstar e := by
    rw [Finset.sum_biUnion]
    intro b₁ _ b₂ _ hne
    exact (bundleOf_pairwise_disjoint fstar hne).mono
      Finset.inter_subset_left Finset.inter_subset_left
  rw [hbi, ← Finset.sum_filter]
  congr 1
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_inter, mem_bundleOf, Finset.mem_filter]
  constructor
  · rintro ⟨b, hb, rfl, heR⟩
    exact ⟨heR, hb⟩
  · rintro ⟨heR, hfe⟩
    exact ⟨fstar e, hfe, rfl, heR⟩

private lemma survWeight_le_active {m n : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) {fstar : Fin m → Fin n} {M : ℝ} (hMpos : 0 < M)
    (hpart : ∀ b : Fin n, M ≤ v (bundleOf fstar b)) (h : Hist m) :
    survWeight v fstar h ≤ ((n - specialCount h : ℕ) : ℝ) := by
  unfold survWeight
  calc
    ∑ b ∈ activeBundles fstar h, ∑ e ∈ bundleOf fstar b ∩ remaining h, suppPrice v fstar e
      ≤ ∑ b ∈ activeBundles fstar h, ∑ e ∈ bundleOf fstar b, suppPrice v fstar e := by
        refine Finset.sum_le_sum fun b _ => ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
          fun e _ _ => (suppPrice_bounds hv hMpos hpart e).1
    _ = ∑ _b ∈ activeBundles fstar h, (1 : ℝ) :=
        Finset.sum_congr rfl fun b _ => sum_suppPrice_bundle hv hMpos hpart b
    _ = ((activeBundles fstar h).card : ℝ) := by simp
    _ = ((n - specialCount h : ℕ) : ℝ) := by rw [card_activeBundles]

private lemma deficit_nil {m n : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) {fstar : Fin m → Fin n} {M : ℝ} (hMpos : 0 < M)
    (hpart : ∀ b : Fin n, M ≤ v (bundleOf fstar b)) :
    deficit v fstar [] = 0 := by
  unfold deficit survWeight
  simp only [specialCount_nil, Nat.sub_zero, activeBundles_nil, remaining_nil,
    Finset.inter_univ, sum_suppPrice_bundle hv hMpos hpart, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sub_self]

private lemma deficit_special_le {m n : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) {fstar : Fin m → Fin n} {M : ℝ} (hMpos : 0 < M)
    (hpart : ∀ b : Fin n, M ≤ v (bundleOf fstar b))
    {h : Hist m} (ht : specialCount h < n) (e₀ : Fin m) :
    deficit v fstar (h ++ [.special e₀]) ≤ deficit v fstar h := by
  let B := activeBundles fstar h
  have hBcard : B.card = n - specialCount h := card_activeBundles fstar h
  have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
  let b_drop : Fin n := if fstar e₀ ∈ B then fstar e₀ else B.min' hBne
  have hb_mem : b_drop ∈ B := by
    dsimp [b_drop]
    split_ifs with hfe
    · exact hfe
    · exact Finset.min'_mem B hBne
  have hB' : activeBundles fstar (h ++ [.special e₀]) = B.erase b_drop := by
    simp only [activeBundles_append_singleton, stepActive, B, b_drop]
    split_ifs with hfe <;> simp [hfe, hBne]
  have hno_touch : ∀ b ∈ B.erase b_drop,
      bundleOf fstar b ∩ (remaining h \ {e₀}) = bundleOf fstar b ∩ remaining h := by
    intro b hb
    obtain ⟨hbne, hbB⟩ := Finset.mem_erase.mp hb
    have hbf : fstar e₀ ≠ b := by
      intro heq
      apply hbne
      dsimp [b_drop]
      have hfeB : fstar e₀ ∈ B := heq ▸ hbB
      rw [if_pos hfeB]
      exact heq.symm
    ext g
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton, mem_bundleOf]
    constructor
    · rintro ⟨hg1, hg2, _⟩; exact ⟨hg1, hg2⟩
    · rintro ⟨hg1, hg2⟩
      refine ⟨hg1, hg2, ?_⟩
      rintro rfl
      exact hbf hg1
  have hW' : survWeight v fstar (h ++ [.special e₀]) =
      survWeight v fstar h -
        ∑ e ∈ bundleOf fstar b_drop ∩ remaining h, suppPrice v fstar e := by
    unfold survWeight
    rw [hB', remaining_append_singleton]
    simp only [Round.goods]
    have hcongr : ∑ b ∈ B.erase b_drop,
        ∑ e ∈ bundleOf fstar b ∩ (remaining h \ {e₀}), suppPrice v fstar e =
        ∑ b ∈ B.erase b_drop,
          ∑ e ∈ bundleOf fstar b ∩ remaining h, suppPrice v fstar e :=
      Finset.sum_congr rfl fun b hb => by rw [hno_touch b hb]
    rw [hcongr]
    have hadd := Finset.add_sum_erase B
      (fun b => ∑ e ∈ bundleOf fstar b ∩ remaining h, suppPrice v fstar e) hb_mem
    dsimp [B] at hadd
    linarith
  have hdrop_le : ∑ e ∈ bundleOf fstar b_drop ∩ remaining h, suppPrice v fstar e ≤ 1 := by
    calc
      ∑ e ∈ bundleOf fstar b_drop ∩ remaining h, suppPrice v fstar e
        ≤ ∑ e ∈ bundleOf fstar b_drop, suppPrice v fstar e :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
            fun e _ _ => (suppPrice_bounds hv hMpos hpart e).1
      _ = 1 := sum_suppPrice_bundle hv hMpos hpart b_drop
  unfold deficit
  rw [specialCount_append_special, hW']
  have hcast : ((n - (specialCount h + 1) : ℕ) : ℝ) = ((n - specialCount h : ℕ) : ℝ) - 1 := by
    have h1 : n - (specialCount h + 1) + 1 = n - specialCount h := by omega
    have h2 : (((n - (specialCount h + 1)) + 1 : ℕ) : ℝ) = ((n - specialCount h : ℕ) : ℝ) :=
      by exact_mod_cast h1
    push_cast at h2
    linarith
  rw [hcast]
  linarith

private lemma deficit_sampled_eq {m n : ℕ} (v : Finset (Fin m) → ℝ)
    (fstar : Fin m → Fin n) (h : Hist m) (picks : List (Finset (Fin m) × Fin m))
    (hsub : items picks ⊆ remaining h) :
    deficit v fstar (h ++ [.sampled picks]) =
      deficit v fstar h +
        ∑ e ∈ items picks,
          (if fstar e ∈ activeBundles fstar h then suppPrice v fstar e else 0) := by
  unfold deficit
  rw [specialCount_append_sampled, survWeight_eq_sum_remaining, survWeight_eq_sum_remaining]
  simp only [activeBundles_append_singleton, stepActive, remaining_append_singleton, Round.goods]
  have hsdiff := Finset.sum_sdiff (f := fun e =>
    if fstar e ∈ activeBundles fstar h then suppPrice v fstar e else 0) hsub
  linarith

private lemma roundLaw_mgf_step {m n : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) {fstar : Fin m → Fin n} {M : ℝ} (hMpos : 0 < M)
    (hpart : ∀ b : Fin n, M ≤ v (bundleOf fstar b))
    {σ : Strategy m} (hLegal : Legal n 4 σ)
    {h : Hist m} (ht : specialCount h < n) :
    pmfExp ((roundLaw n 4 σ h).map (fun r => h ++ [r]))
      (fun h' => ENNReal.ofReal
        (Real.exp (Real.log 5 * deficit v fstar h' - (nonSpecialCount h' : ℝ)))) ≤
    ENNReal.ofReal
      (Real.exp (Real.log 5 * deficit v fstar h - (nonSpecialCount h : ℝ))) := by
  rw [pmfExp_map]
  unfold roundLaw
  cases hch : σ.choose h with
  | some e₀ =>
    rw [pmfExp_pure]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    rw [nonSpecialCount_append_special]
    have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    have hdef := deficit_special_le hv hMpos hpart ht e₀
    nlinarith
  | none =>
    rw [pmfExp_map]
    let x : Fin m → ℝ := fun e =>
      if fstar e ∈ activeBundles fstar h then suppPrice v fstar e else 0
    have hx : ∀ e : Fin m, 0 ≤ x e ∧ x e ≤ 1 := by
      intro e
      dsimp [x]
      split_ifs
      · exact suppPrice_bounds hv hMpos hpart e
      · exact ⟨le_rfl, zero_le_one⟩
    have hrew : pmfExp (loopLaw n 4 σ h (m + 1) [])
        (fun picks => ENNReal.ofReal
          (Real.exp (Real.log 5 * deficit v fstar (h ++ [.sampled picks]) -
            (nonSpecialCount (h ++ [.sampled picks]) : ℝ)))) =
        pmfExp (loopLaw n 4 σ h (m + 1) [])
          (fun picks =>
            ENNReal.ofReal (Real.exp (Real.log 5 * deficit v fstar h -
              (nonSpecialCount h : ℝ) - 1)) *
            ENNReal.ofReal (Real.exp (Real.log 5 * ∑ e ∈ items picks, x e))) := by
      refine pmfExp_congr_support _ fun picks hpicks => ?_
      have hsub : items picks ⊆ remaining h :=
        loopLaw_support_items_subset hLegal ht (m + 1) [] picks (by simp) hpicks
      rw [deficit_sampled_eq v fstar h picks hsub, nonSpecialCount_append_sampled,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      push_cast
      congr 1
      congr 1
      dsimp [x]
      ring
    rw [hrew]
    have hpull : pmfExp (loopLaw n 4 σ h (m + 1) [])
        (fun picks =>
          ENNReal.ofReal (Real.exp (Real.log 5 * deficit v fstar h -
            (nonSpecialCount h : ℝ) - 1)) *
          ENNReal.ofReal (Real.exp (Real.log 5 * ∑ e ∈ items picks, x e))) =
        ENNReal.ofReal (Real.exp (Real.log 5 * deficit v fstar h -
          (nonSpecialCount h : ℝ) - 1)) *
        pmfExp (loopLaw n 4 σ h (m + 1) [])
          (fun picks => ENNReal.ofReal (Real.exp (Real.log 5 * ∑ e ∈ items picks, x e))) := by
      unfold pmfExp
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun picks => by dsimp only; ring
    rw [hpull]
    have hfuel0 : (pending h []).card ≤ m + 1 := by
      have : (remaining h).card ≤ m := by simpa using Finset.card_le_univ (remaining h)
      simp only [pending_nil]
      omega
    have hlog5 : 0 ≤ Real.log 5 := (Real.log_pos (by norm_num)).le
    have hmgf := loopLaw_mgf (by norm_num : 0 < 4) hLegal ht hlog5 hx (m + 1) [] hfuel0 (by simp)
    simp only [items_nil, Finset.sum_empty, mul_zero, zero_add, pending_nil] at hmgf
    have hmgf_le_exp1 : ENNReal.ofReal (Real.exp
        (((Real.exp (Real.log 5) - 1) / ((4 * (n - specialCount h) : ℕ) : ℝ)) *
          ∑ g ∈ remaining h, x g)) ≤ ENNReal.ofReal (Real.exp 1) := by
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 5)]
      have hsum_eq : ∑ g ∈ remaining h, x g = survWeight v fstar h :=
        (survWeight_eq_sum_remaining v fstar h).symm
      rw [hsum_eq]
      have hW := survWeight_le_active hv hMpos hpart h
      have hNpos : (0 : ℝ) < ((n - specialCount h : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt ht
      have hcast : ((4 * (n - specialCount h) : ℕ) : ℝ) = 4 * ((n - specialCount h : ℕ) : ℝ) := by
        push_cast; ring
      rw [hcast]
      rw [show ((5 : ℝ) - 1) / (4 * ((n - specialCount h : ℕ) : ℝ)) * survWeight v fstar h =
        survWeight v fstar h / ((n - specialCount h : ℕ) : ℝ) by field_simp [hNpos.ne']; ring]
      exact (div_le_one hNpos).mpr hW
    calc
      ENNReal.ofReal (Real.exp (Real.log 5 * deficit v fstar h - (nonSpecialCount h : ℝ) - 1)) *
          pmfExp (loopLaw n 4 σ h (m + 1) [])
            (fun picks => ENNReal.ofReal (Real.exp (Real.log 5 * ∑ e ∈ items picks, x e)))
        ≤ ENNReal.ofReal (Real.exp (Real.log 5 * deficit v fstar h -
            (nonSpecialCount h : ℝ) - 1)) * ENNReal.ofReal (Real.exp 1) :=
          mul_le_mul_of_nonneg_left (hmgf.trans hmgf_le_exp1) zero_le'
      _ = ENNReal.ofReal
            (Real.exp (Real.log 5 * deficit v fstar h - (nonSpecialCount h : ℝ))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 1; congr 1; ring

private lemma runLaw_mgf_le_one {m n : ℕ} {v : Finset (Fin m) → ℝ}
    (hv : IsValuation v) {fstar : Fin m → Fin n} {M : ℝ} (hMpos : 0 < M)
    (hpart : ∀ b : Fin n, M ≤ v (bundleOf fstar b))
    {σ : Fin n → Strategy m} (hLegal : ∀ j : Fin n, Legal n 4 (σ j)) :
    ∀ j : ℕ, j ≤ n →
      pmfExp (runLaw 4 σ j)
        (fun h => ENNReal.ofReal
          (Real.exp (Real.log 5 * deficit v fstar h - (nonSpecialCount h : ℝ)))) ≤ 1
  | 0, _ => by
    simp [runLaw, pmfExp_pure, deficit_nil hv hMpos hpart]
  | j + 1, hjle => by
    have hj : j < n := Nat.lt_of_succ_le hjle
    simp only [runLaw, hj, ↓reduceDIte, pmfExp_bind]
    have hmono : pmfExp (runLaw 4 σ j)
        (fun h => pmfExp ((roundLaw n 4 (σ ⟨j, hj⟩) h).map (fun r => h ++ [r]))
          (fun h' => ENNReal.ofReal
            (Real.exp (Real.log 5 * deficit v fstar h' - (nonSpecialCount h' : ℝ))))) ≤
        pmfExp (runLaw 4 σ j)
          (fun h => ENNReal.ofReal
            (Real.exp (Real.log 5 * deficit v fstar h - (nonSpecialCount h : ℝ)))) := by
      refine pmfExp_mono_support (runLaw 4 σ j) fun h hh => ?_
      have hlen : h.length = j := runLaw_support_length hLegal hj.le hh
      have ht : specialCount h < n := lt_of_le_of_lt (specialCount_le_length h) (hlen ▸ hj)
      exact roundLaw_mgf_step hv hMpos hpart (hLegal ⟨j, hj⟩) ht
    exact hmono.trans (runLaw_mgf_le_one hv hMpos hpart hLegal j hj.le)

private lemma single_agent_bad_bound {m n : ℕ} (i : Fin n)
    {v : Finset (Fin m) → ℝ} (hv : IsValuation v)
    (hsub : SubsamplingSM.Offline.IsSubmodular v)
    {σ : Fin n → Strategy m} (hLegal : ∀ j : Fin n, Legal n 4 (σ j))
    (hSafe : IsSafe n 4 ((1 / 24) * LittleCharity.MMS.mms v n Finset.univ) v (σ i)) :
    (runLaw 4 σ n).toOuterMeasure
      {h | ¬ ((1 / 24) * LittleCharity.MMS.mms v n Finset.univ ≤ v (allocOf h i))} ≤
      ENNReal.ofReal (qParam n i) := by
  let M := LittleCharity.MMS.mms v n Finset.univ
  let τ := (1 / 24 : ℝ) * M
  by_cases hM : M ≤ 0
  · have hempty : {h : Hist m | ¬ (τ ≤ v (allocOf h i))} = ∅ := by
      ext h
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      have hτ0 : τ ≤ 0 := by dsimp [τ]; linarith
      exact hτ0.trans (val_nonneg hv _)
    rw [hempty]
    simp
  · have hMpos : 0 < M := lt_of_not_ge hM
    have hτpos : 0 < τ := by dsimp [τ]; positivity
    have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    obtain ⟨fstar, hpart⟩ := mms_exists_partition hn v
    have hafter : (runLaw 4 σ n).toOuterMeasure {h | τ ≤ v (allocOf h i)} =
        (runLaw 4 σ (i.val + 1)).toOuterMeasure {h | τ ≤ v (allocOf h i)} :=
      runLaw_toOuterMeasure_allocOf_after hLegal i (fun A => τ ≤ v A) n
        (Nat.succ_le_of_lt i.isLt) le_rfl
    let GoodPre : Set (Hist m) :=
      {h | deficit v fstar h ≤ (5 / 8) * ((n - specialCount h : ℕ) : ℝ)}
    have hstep_good : (runLaw 4 σ i.val).toOuterMeasure GoodPre ≤
        (runLaw 4 σ (i.val + 1)).toOuterMeasure {h | τ ≤ v (allocOf h i)} := by
      simp only [runLaw, i.isLt, ↓reduceDIte]
      have hi_eq : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.eta i i.isLt
      rw [hi_eq]
      refine toOuterMeasure_bind_ge (runLaw 4 σ i.val) _ _ GoodPre ?_
      intro h hh hgood h' hh'
      rw [PMF.mem_support_map_iff] at hh'
      rcases hh' with ⟨r, hr, rfl⟩
      have hlen : h.length = i.val := runLaw_support_length hLegal i.isLt.le hh
      have ht : specialCount h < n := lt_of_le_of_lt (specialCount_le_length h) (hlen ▸ i.isLt)
      have halloc : allocOf (h ++ [r]) i = r.goods := by
        simp [allocOf, hlen]
      rw [Set.mem_setOf_eq, halloc]
      have hW_ge : (3 / 8) * ((n - specialCount h : ℕ) : ℝ) ≤ survWeight v fstar h := by
        simp only [GoodPre, Set.mem_setOf_eq, deficit] at hgood
        linarith
      have hPi : 9 * τ * ((n - specialCount h : ℕ) : ℝ) ≤
          ∑ b ∈ activeBundles fstar h, v (bundleOf fstar b ∩ remaining h) := by
        have hMW : M * survWeight v fstar h ≤
            ∑ b ∈ activeBundles fstar h, v (bundleOf fstar b ∩ remaining h) := by
          unfold survWeight
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun b _ => sum_suppPrice_inter_le hv hsub hMpos hpart b _
        have hM38 : 9 * τ * ((n - specialCount h : ℕ) : ℝ) ≤ M * survWeight v fstar h := by
          have : M * ((3 / 8) * ((n - specialCount h : ℕ) : ℝ)) ≤ M * survWeight v fstar h :=
            mul_le_mul_of_nonneg_left hW_ge hMpos.le
          dsimp [τ]
          linarith
        exact hM38.trans hMW
      exact safe_round_guarantee hv hsub hτpos hSafe ht (card_activeBundles fstar h) hPi hr
    have hbad_pre : (runLaw 4 σ i.val).toOuterMeasure GoodPreᶜ ≤ ENNReal.ofReal (qParam n i) := by
      let c : ℝ := Real.exp (((5 : ℝ) / 8) * Real.log 5 * ((n - i.val : ℕ) : ℝ))
      have hc_pos : 0 ≤ c := (Real.exp_pos _).le
      have hmarkov : ENNReal.ofReal c * (runLaw 4 σ i.val).toOuterMeasure GoodPreᶜ ≤ 1 := by
        refine (pmf_markov (runLaw 4 σ i.val)
          (fun h => ENNReal.ofReal
            (Real.exp (Real.log 5 * deficit v fstar h - (nonSpecialCount h : ℝ))))
          (ENNReal.ofReal c) GoodPreᶜ ?_).trans
          (runLaw_mgf_le_one hv hMpos hpart hLegal i.val i.isLt.le)
        intro h hh hbad
        simp only [GoodPre, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hbad
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        have hlen : h.length = i.val := runLaw_support_length hLegal i.isLt.le hh
        have ht_add : specialCount h + nonSpecialCount h = i.val := by
          rw [specialCount_add_nonSpecialCount, hlen]
        have hN_eq : n - specialCount h = (n - i.val) + nonSpecialCount h := by
          have := i.isLt
          omega
        have hN_real : ((n - specialCount h : ℕ) : ℝ) =
            ((n - i.val : ℕ) : ℝ) + (nonSpecialCount h : ℝ) := by
          exact_mod_cast hN_eq
        have hlog5_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
        have hlog_ge : (1 : ℝ) ≤ (5 / 8) * Real.log 5 := one_le_five_eighths_log5
        have hr_nonneg : (0 : ℝ) ≤ (nonSpecialCount h : ℝ) := Nat.cast_nonneg _
        have hprod1 : Real.log 5 * ((5 / 8) * ((n - specialCount h : ℕ) : ℝ)) ≤
            Real.log 5 * deficit v fstar h :=
          mul_le_mul_of_nonneg_left hbad.le hlog5_pos.le
        have hprod2 : (0 : ℝ) ≤ ((5 / 8) * Real.log 5 - 1) * (nonSpecialCount h : ℝ) :=
          mul_nonneg (by linarith) hr_nonneg
        rw [hN_real] at hprod1
        linarith
      calc
        (runLaw 4 σ i.val).toOuterMeasure GoodPreᶜ
          = 1 * (runLaw 4 σ i.val).toOuterMeasure GoodPreᶜ := (one_mul _).symm
        _ = (ENNReal.ofReal (qParam n i) * ENNReal.ofReal c) *
              (runLaw 4 σ i.val).toOuterMeasure GoodPreᶜ := by
            rw [← ENNReal.ofReal_mul (qParam_nonneg n i), qParam_mul_exp_eq_one,
              ENNReal.ofReal_one]
        _ = ENNReal.ofReal (qParam n i) *
              (ENNReal.ofReal c * (runLaw 4 σ i.val).toOuterMeasure GoodPreᶜ) :=
            mul_assoc _ _ _
        _ ≤ ENNReal.ofReal (qParam n i) * 1 :=
            mul_le_mul_of_nonneg_left hmarkov zero_le'
        _ = ENNReal.ofReal (qParam n i) := mul_one _
    have hsum_n := toOuterMeasure_add_compl (runLaw 4 σ n) {h | τ ≤ v (allocOf h i)}
    have hsum_pre := toOuterMeasure_add_compl (runLaw 4 σ i.val) GoodPre
    have hgood_ge : (runLaw 4 σ i.val).toOuterMeasure GoodPre ≤
        (runLaw 4 σ n).toOuterMeasure {h | τ ≤ v (allocOf h i)} := by
      rw [hafter]
      exact hstep_good
    have hfin : (runLaw 4 σ i.val).toOuterMeasure GoodPre ≠ ⊤ := by
      intro htop
      rw [htop, top_add] at hsum_pre
      exact ENNReal.top_ne_one hsum_pre
    have hbad_le_pre : (runLaw 4 σ n).toOuterMeasure {h | ¬ (τ ≤ v (allocOf h i))} ≤
        (runLaw 4 σ i.val).toOuterMeasure GoodPreᶜ := by
      have hc_eq : ({h : Hist m | τ ≤ v (allocOf h i)}ᶜ : Set (Hist m)) =
          {h | ¬ (τ ≤ v (allocOf h i))} := rfl
      rw [← hc_eq]
      have hineq : (runLaw 4 σ i.val).toOuterMeasure GoodPre +
          (runLaw 4 σ n).toOuterMeasure {h | τ ≤ v (allocOf h i)}ᶜ ≤
          (runLaw 4 σ i.val).toOuterMeasure GoodPre +
          (runLaw 4 σ i.val).toOuterMeasure GoodPreᶜ := by
        calc
          (runLaw 4 σ i.val).toOuterMeasure GoodPre +
              (runLaw 4 σ n).toOuterMeasure {h | τ ≤ v (allocOf h i)}ᶜ
            ≤ (runLaw 4 σ n).toOuterMeasure {h | τ ≤ v (allocOf h i)} +
                (runLaw 4 σ n).toOuterMeasure {h | τ ≤ v (allocOf h i)}ᶜ :=
              add_le_add hgood_ge le_rfl
          _ = 1 := hsum_n
          _ = (runLaw 4 σ i.val).toOuterMeasure GoodPre +
                (runLaw 4 σ i.val).toOuterMeasure GoodPreᶜ := hsum_pre.symm
      exact (ENNReal.add_le_add_iff_left hfin).mp hineq
    exact hbad_le_pre.trans hbad_pre

end DeficitMGF

/-! ### Section 7: Assembly of Theorem 4.1 and Corollary 4.2 -/

theorem theorem_4_1_proof (n m : ℕ) :
    (∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i ≤ 0.577 ∧
      ∀ (i : Fin n) (v : Finset (Fin m) → ℝ), IsValuation v →
        SubsamplingSM.Offline.IsSubmodular v →
        ∀ σ : Fin n → Strategy m, (∀ j, Legal n 4 (σ j)) →
          IsSafe n 4 ((1 / 24) * LittleCharity.MMS.mms v n Finset.univ) v (σ i) →
          ENNReal.ofReal (1 - q i) ≤ (runLaw 4 σ n).toOuterMeasure
            {h | (1 / 24) * LittleCharity.MMS.mms v n Finset.univ ≤ v (allocOf h i)}) ∧
    (∀ vs : Fin n → Finset (Fin m) → ℝ,
      (∀ i, IsValuation (vs i) ∧ SubsamplingSM.Offline.IsSubmodular (vs i)) →
      ∀ σ : Fin n → Strategy m, (∀ j, Legal n 4 (σ j)) →
        (∀ i, IsSafe n 4 ((1 / 24) * LittleCharity.MMS.mms (vs i) n Finset.univ) (vs i) (σ i)) →
        ENNReal.ofReal 0.423 ≤ (runLaw 4 σ n).toOuterMeasure
          {h | LittleCharity.EFX.IsPartialAllocation (fun i : Fin n => (allocOf h i : Finset (Fin m))) ∧
            ∀ i, (1 / 24) * LittleCharity.MMS.mms (vs i) n Finset.univ ≤ vs i (allocOf h i)}) := by
  constructor
  · refine ⟨qParam n, qParam_nonneg n, qParam_sum_le n, ?_⟩
    intro i v hv hsub σ hLegal hSafe
    let Good : Set (Hist m) :=
      {h | (1 / 24) * LittleCharity.MMS.mms v n Finset.univ ≤ v (allocOf h i)}
    have hbad : (runLaw 4 σ n).toOuterMeasure Goodᶜ ≤ ENNReal.ofReal (qParam n i) :=
      single_agent_bad_bound i hv hsub hLegal hSafe
    have hsum := toOuterMeasure_add_compl (runLaw 4 σ n) Good
    have h1 : 1 ≤ (runLaw 4 σ n).toOuterMeasure Good + ENNReal.ofReal (qParam n i) := by
      rw [← hsum]
      exact add_le_add le_rfl hbad
    rw [ENNReal.ofReal_sub 1 (qParam_nonneg n i), ENNReal.ofReal_one]
    exact tsub_le_iff_right.mpr h1
  · intro vs hvs σ hLegal hSafe
    let Inv : Set (Hist m) :=
      {h | LittleCharity.EFX.IsPartialAllocation (fun i : Fin n => (allocOf h i : Finset (Fin m)))}
    let Good : Fin n → Set (Hist m) := fun i =>
      {h | (1 / 24) * LittleCharity.MMS.mms (vs i) n Finset.univ ≤ vs i (allocOf h i)}
    have hInv : ∀ h ∈ (runLaw 4 σ n).support, h ∈ Inv :=
      fun _ hh => runLaw_support_isPartialAllocation hLegal hh
    have hunion := toOuterMeasure_union_bound (runLaw 4 σ n) Inv Good hInv
    have hsum_bad : ∑ i : Fin n, (runLaw 4 σ n).toOuterMeasure (Good i)ᶜ ≤
        ENNReal.ofReal 0.577 := by
      calc
        ∑ i : Fin n, (runLaw 4 σ n).toOuterMeasure (Good i)ᶜ
          ≤ ∑ i : Fin n, ENNReal.ofReal (qParam n i) :=
            Finset.sum_le_sum fun i _ =>
              single_agent_bad_bound i (hvs i).1 (hvs i).2 hLegal (hSafe i)
        _ = ENNReal.ofReal (∑ i : Fin n, qParam n i) :=
            (ENNReal.ofReal_sum_of_nonneg fun i _ => qParam_nonneg n i).symm
        _ ≤ ENNReal.ofReal 0.577 :=
            ENNReal.ofReal_le_ofReal (qParam_sum_le n)
    have h1 : 1 ≤ (runLaw 4 σ n).toOuterMeasure {h | h ∈ Inv ∧ ∀ i, h ∈ Good i} +
        ENNReal.ofReal 0.577 :=
      hunion.trans (add_le_add le_rfl hsum_bad)
    have h423 : ENNReal.ofReal 0.423 = 1 - ENNReal.ofReal 0.577 := by
      have : (0.423 : ℝ) = 1 - 0.577 := by norm_num
      rw [this, ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 0.577), ENNReal.ofReal_one]
    rw [h423]
    exact tsub_le_iff_right.mpr h1

end SingleOrSample_Proof

open SingleOrSample

theorem solution (n m : ℕ) :
    (∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i ≤ 0.577 ∧
      ∀ (i : Fin n) (v : Finset (Fin m) → ℝ), IsValuation v →
        SubsamplingSM.Offline.IsSubmodular v →
        ∀ σ : Fin n → Strategy m, (∀ j, Legal n 4 (σ j)) →
          IsSafe n 4 ((1 / 24) * LittleCharity.MMS.mms v n Finset.univ) v (σ i) →
          ENNReal.ofReal (1 - q i) ≤ (runLaw 4 σ n).toOuterMeasure
            {h | (1 / 24) * LittleCharity.MMS.mms v n Finset.univ ≤ v (allocOf h i)}) ∧
    (∀ vs : Fin n → Finset (Fin m) → ℝ,
      (∀ i, IsValuation (vs i) ∧ SubsamplingSM.Offline.IsSubmodular (vs i)) →
      ∀ σ : Fin n → Strategy m, (∀ j, Legal n 4 (σ j)) →
        (∀ i, IsSafe n 4 ((1 / 24) * LittleCharity.MMS.mms (vs i) n Finset.univ) (vs i) (σ i)) →
        ENNReal.ofReal 0.423 ≤ (runLaw 4 σ n).toOuterMeasure
          {h | LittleCharity.EFX.IsPartialAllocation (fun i : Fin n => (allocOf h i : Finset (Fin m))) ∧
            ∀ i, (1 / 24) * LittleCharity.MMS.mms (vs i) n Finset.univ ≤ vs i (allocOf h i)}) :=
  SingleOrSample_Proof.theorem_4_1_proof n m

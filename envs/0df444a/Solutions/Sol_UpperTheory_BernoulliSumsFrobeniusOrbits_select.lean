-- Prove2me | solution 1 for UpperTheory.BernoulliSumsFrobeniusOrbits.select
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:17.35533+00:00
-- url     : https://prove2.me/submissions/d8cb64fa-98c6-4ddd-9ae3-c4b0076e48e4

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_select
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
private theorem sel_moment {α : Type} [DecidableEq α] (p g : α → ℝ) (S : Finset α) (c : ℝ) :
    ∑ T ∈ S.powerset, ((∏ a ∈ T, p a) * ∏ a ∈ S \ T, (1 - p a)) * (c + ∑ a ∈ T, g a) ^ 2 =
      (c + ∑ a ∈ S, g a * p a) ^ 2 + ∑ a ∈ S, g a ^ 2 * (p a * (1 - p a)) := by
  induction S using Finset.induction_on generalizing c with
  | empty => simp
  | insert x S hx ih =>
    rw [Finset.sum_powerset_insert hx, Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 : ∑ T ∈ S.powerset, ((∏ a ∈ T, p a) * ∏ a ∈ insert x S \ T, (1 - p a)) *
          (c + ∑ a ∈ T, g a) ^ 2 =
        (1 - p x) * ∑ T ∈ S.powerset, ((∏ a ∈ T, p a) * ∏ a ∈ S \ T, (1 - p a)) *
          (c + ∑ a ∈ T, g a) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hxT : x ∉ T := fun h => hx (Finset.mem_powerset.1 hT h)
      rw [Finset.insert_sdiff_of_notMem _ hxT,
        Finset.prod_insert (fun h => hx (Finset.mem_sdiff.1 h).1)]
      ring
    have h2 : ∑ T ∈ S.powerset, ((∏ a ∈ insert x T, p a) *
          ∏ a ∈ insert x S \ insert x T, (1 - p a)) * (c + ∑ a ∈ insert x T, g a) ^ 2 =
        p x * ∑ T ∈ S.powerset, ((∏ a ∈ T, p a) * ∏ a ∈ S \ T, (1 - p a)) *
          ((c + g x) + ∑ a ∈ T, g a) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hxT : x ∉ T := fun h => hx (Finset.mem_powerset.1 hT h)
      rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hx,
        Finset.prod_insert hxT, Finset.sum_insert hxT]
      ring
    rw [h1, h2, ih, ih]
    ring
private theorem sel_moment' {α : Type} [Fintype α] [DecidableEq α] (p g : α → ℝ) (c : ℝ) :
    ∑ T : Finset α, pw p T * (c + ∑ a ∈ T, g a) ^ 2 =
      (c + ∑ a, g a * p a) ^ 2 + ∑ a, g a ^ 2 * (p a * (1 - p a)) := by
  have := sel_moment p g univ c
  rw [Finset.powerset_univ] at this
  exact this
private theorem sel_exists {γ : Type} [Fintype γ] (w F : γ → ℝ) (hw : ∀ T, 0 ≤ w T)
    (h1 : ∑ T, w T = 1) : ∃ T, 0 < w T ∧ F T ≤ ∑ U, w U * F U := by
  by_contra hc
  push Not at hc
  obtain ⟨T₀, hT₀⟩ : ∃ T, 0 < w T := by
    by_contra h
    push Not at h
    have : ∑ T, w T ≤ 0 := Finset.sum_nonpos fun T _ => h T
    linarith
  have : ∑ T, w T * (∑ U, w U * F U) < ∑ T, w T * F T := by
    refine Finset.sum_lt_sum (fun T _ => ?_) ⟨T₀, Finset.mem_univ _, ?_⟩
    · rcases (hw T).eq_or_lt with h | h
      · rw [← h]; simp
      · exact mul_le_mul_of_nonneg_left (hc T h).le h.le
    · exact mul_lt_mul_of_pos_left (hc T₀ hT₀) hT₀
  rw [← Finset.sum_mul, h1, one_mul] at this
  exact lt_irrefl _ this
private theorem sel_ncard {α : Type} [Fintype α] (P : α → Prop) :
    (({t | P t}.ncard : ℕ) : ℝ) = ∑ t, ind (P t) := by
  classical
  have : {t | P t} = ((univ.filter P : Finset α) : Set α) := by ext; simp
  rw [this, Set.ncard_coe_finset, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold ind
  by_cases h : P t <;> simp [h]
end

set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
namespace UpperTheory.BernoulliSumsFrobeniusOrbits
theorem _root_.solution :
    ∀ (α κ ι : Type) [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] (cl : α → κ) (p : α → ℝ) (δ β D : ℝ)
        (I : Finset ι) (ω : ι → ℝ) (BAD : ι → α → Finset α → Prop),
      (∀ a, 0 ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 → 0 ≤ β → (∀ i, 0 ≤ ω i) → 0 < D → 2 * δ * Fintype.card α ≤ D ^ 2 →
      (∀ i ∈ I, ∀ t, ∑ T : Finset α, pw p T * ind (t ∈ T ∧ BAD i t T) ≤ β * δ) →
      ∃ T : Finset α, (∀ c : κ, |((T.filter fun a => cl a = c).card : ℝ) - ∑ a ∈ univ.filter (fun a => cl a = c), p a| ≤ D) ∧
        ∑ i ∈ I, ω i * (({t | t ∈ T ∧ BAD i t T}.ncard : ℕ) : ℝ) ≤ 4 * β * δ * Fintype.card α * ∑ i ∈ I, ω i := by
  intro α κ ι _ _ _ _ cl p δ β D I ω BAD hp hδ hδ1 hβ hω hD hD2 hbad
  have hw : ∀ T : Finset α, 0 ≤ pw p T := fun T =>
    mul_nonneg (Finset.prod_nonneg fun a _ => (hp a).1)
      (Finset.prod_nonneg fun a _ => by linarith [(hp a).2])
  have h1 : ∑ T : Finset α, pw p T = 1 := by
    simpa using sel_moment' p (fun _ => 0) 1
  set Y : κ → Finset α → ℝ := fun c T =>
    ((T.filter fun a => cl a = c).card : ℝ) - ∑ a ∈ univ.filter (fun a => cl a = c), p a with hY
  set B : Finset α → ℝ := fun T =>
    ∑ i ∈ I, ω i * (({t | t ∈ T ∧ BAD i t T}.ncard : ℕ) : ℝ) with hB
  set m : ℝ := β * δ * Fintype.card α * ∑ i ∈ I, ω i with hm
  have hm0 : 0 ≤ m := by
    have : 0 ≤ ∑ i ∈ I, ω i := Finset.sum_nonneg fun i _ => hω i
    positivity
  have hB0 : ∀ T, 0 ≤ B T := fun T =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hω i) (Nat.cast_nonneg _)
  have hEY : ∀ c, ∑ T, pw p T * Y c T ^ 2 ≤ ∑ a, if cl a = c then δ else 0 := by
    intro c
    have h := sel_moment' p (fun a => if cl a = c then 1 else 0)
      (-∑ a ∈ univ.filter (fun a => cl a = c), p a)
    have e1 : ∀ T : Finset α, Y c T = -∑ a ∈ univ.filter (fun a => cl a = c), p a +
        ∑ a ∈ T, (if cl a = c then (1 : ℝ) else 0) := by
      intro T
      simp only [hY]
      rw [Finset.card_filter]
      push_cast
      ring
    have e2 : ∑ a, (if cl a = c then (1 : ℝ) else 0) * p a =
        ∑ a ∈ univ.filter (fun a => cl a = c), p a := by
      rw [Finset.sum_filter]
      simp
    simp only [e1]
    rw [h, e2, neg_add_cancel, zero_pow two_ne_zero, zero_add]
    refine Finset.sum_le_sum fun a _ => ?_
    split_ifs
    · nlinarith [(hp a).1, (hp a).2, sq_nonneg (p a)]
    · simp
  have hEX : ∑ T, pw p T * ∑ c, Y c T ^ 2 ≤ D ^ 2 / 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine (Finset.sum_le_sum fun c _ => hEY c).trans ?_
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    linarith
  have hEB : ∑ T, pw p T * B T ≤ m := by
    simp only [hB, sel_ncard, Finset.mul_sum, hm]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.sum_comm]
    calc ∑ t, ∑ T, pw p T * (ω i * ind (t ∈ T ∧ BAD i t T))
        ≤ ∑ _t : α, ω i * (β * δ) := by
          refine Finset.sum_le_sum fun t _ => ?_
          refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (hbad i hi t) (hω i))
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun T _ => by ring
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  obtain ⟨T, hT0, hT⟩ := sel_exists (pw p)
    (fun T => (∑ c, Y c T ^ 2) / D ^ 2 + B T / (4 * m)) hw h1
  have hD0 : 0 < D ^ 2 := by positivity
  have hE : ∑ U, pw p U * ((∑ c, Y c U ^ 2) / D ^ 2 + B U / (4 * m)) ≤ 1 := by
    have e : ∑ U, pw p U * ((∑ c, Y c U ^ 2) / D ^ 2 + B U / (4 * m)) =
        (∑ U, pw p U * ∑ c, Y c U ^ 2) / D ^ 2 + (∑ U, pw p U * B U) / (4 * m) := by
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun U _ => by ring
    have a1 : (∑ U, pw p U * ∑ c, Y c U ^ 2) / D ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ hD0]; linarith
    have a2 : (∑ U, pw p U * B U) / (4 * m) ≤ 1 / 2 :=
      div_le_of_le_mul₀ (by positivity) (by norm_num) (by linarith)
    rw [e]; linarith
  have hT1 := hT.trans hE
  have n1 : 0 ≤ (∑ c, Y c T ^ 2) / D ^ 2 :=
    div_nonneg (Finset.sum_nonneg fun c _ => sq_nonneg _) hD0.le
  have n2 : 0 ≤ B T / (4 * m) := div_nonneg (hB0 T) (by positivity)
  refine ⟨T, fun c => ?_, ?_⟩
  · have a1 : (∑ c, Y c T ^ 2) / D ^ 2 ≤ 1 := by linarith
    rw [div_le_one hD0] at a1
    have a2 : Y c T ^ 2 ≤ ∑ c, Y c T ^ 2 :=
      Finset.single_le_sum (f := fun c => Y c T ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ c)
    exact abs_le_of_sq_le_sq (a2.trans a1) hD.le
  · have key : B T ≤ 4 * m := by
      rcases hm0.eq_or_lt with h | h
      · have a1 : pw p T * B T ≤ ∑ U, pw p U * B U :=
          Finset.single_le_sum (f := fun U => pw p U * B U)
            (fun U _ => mul_nonneg (hw U) (hB0 U)) (Finset.mem_univ T)
        have a2 : pw p T * B T ≤ 0 := by linarith
        have a3 : B T ≤ 0 := by
          by_contra hc
          push Not at hc
          linarith [mul_pos hT0 hc]
        linarith
      · have a1 : B T / (4 * m) ≤ 1 := by linarith
        rwa [div_le_one (by positivity)] at a1
    calc _ = B T := rfl
      _ ≤ 4 * m := key
      _ = _ := by rw [hm]; ring
end UpperTheory.BernoulliSumsFrobeniusOrbits

-- Prove2me | solution 1 for ReusablePricing.DPCB.batch_error_sq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T03:24:49.741539+00:00
-- url     : https://prove2.me/submissions/bcfaca96-e48d-4673-b389-c6a64f55ef80

import Mathlib
import Definitions.Def_ReusablePricing_DPCB_Events

open Finset

set_option linter.unusedSectionVars false



namespace DPCBTower

variable {α : Type} [Fintype α] [DecidableEq α] [Inhabited α]

/-- `f` depends on a tuple only through its coordinates `< j`. -/
def Causal {n : ℕ} (j : ℕ) {γ : Type} (f : (Fin n → α) → γ) : Prop :=
  ∀ ω ω' : Fin n → α, (∀ i : Fin n, i.val < j → ω i = ω' i) → f ω = f ω'

lemma snoc_agree {n : ℕ} (ω ω' : Fin n → α) (a b : α) (j : ℕ) (hj : j ≤ n)
    (h : ∀ i : Fin n, i.val < j → ω i = ω' i) :
    ∀ i : Fin (n + 1), i.val < j → Fin.snoc (α := fun _ => α) ω a i = Fin.snoc (α := fun _ => α) ω' b i := by
  intro i hi
  have hin : i.val < n := lt_of_lt_of_le hi hj
  have : i = Fin.castSucc ⟨i.val, hin⟩ := Fin.ext rfl
  rw [this, Fin.snoc_castSucc, Fin.snoc_castSucc]
  exact h _ hi

lemma sum_snoc {n : ℕ} (H : (Fin (n + 1) → α) → ℝ) :
    ∑ ω, H ω = ∑ ω' : Fin n → α, ∑ a : α, H (Fin.snoc ω' a) := by
  rw [← (Fin.snocEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type_right]
  rfl

theorem mass : ∀ (n : ℕ) (q : Fin n → (Fin n → α) → α → ℝ),
    (∀ j : Fin n, Causal j.val (q j)) → (∀ j ω, ∑ a, q j ω a = 1) →
    ∑ ω, ∏ j, q j ω (ω j) = 1 := by
  intro n
  induction n with
  | zero => intro q _ _; simp
  | succ n ih =>
    intro q hc h1
    set q' : Fin n → (Fin n → α) → α → ℝ := fun j ω' => q (Fin.castSucc j) (Fin.snoc ω' default)
    have hq'c : ∀ j : Fin n, Causal j.val (q' j) := by
      intro j ω ω' h
      exact hc _ _ _ (snoc_agree ω ω' default default j.val (le_of_lt j.isLt) h)
    have hq'1 : ∀ j ω, ∑ a, q' j ω a = 1 := fun j ω => h1 _ _
    rw [sum_snoc]
    have : ∀ ω' : Fin n → α, ∑ a : α, ∏ j, q j (Fin.snoc ω' a) ((Fin.snoc ω' a : Fin (n+1) → α) j)
        = ∏ j, q' j ω' (ω' j) := by
      intro ω'
      have hr : ∀ a, q (Fin.last n) (Fin.snoc ω' a) = q (Fin.last n) (Fin.snoc ω' default) :=
        fun a => hc _ _ _ (snoc_agree ω' ω' a default n le_rfl (fun _ _ => rfl))
      have hs : ∀ a (j : Fin n), q (Fin.castSucc j) (Fin.snoc ω' a) = q' j ω' :=
        fun a j => hc _ _ _ (snoc_agree ω' ω' a default j.val (le_of_lt j.isLt) (fun _ _ => rfl))
      simp_rw [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hs, hr, ← Finset.mul_sum,
        h1, mul_one]
    simp_rw [this]
    exact ih q' hq'c hq'1

theorem tower : ∀ (n : ℕ) (q : Fin n → (Fin n → α) → α → ℝ),
    (∀ j : Fin n, Causal j.val (q j)) → (∀ j ω, ∑ a, q j ω a = 1) →
    ∀ (s : Fin n) (G : (Fin n → α) → α → ℝ), Causal s.val G →
    ∑ ω, (∏ j, q j ω (ω j)) * G ω (ω s) = ∑ ω, (∏ j, q j ω (ω j)) * ∑ a, q s ω a * G ω a := by
  intro n
  induction n with
  | zero => intro q _ _ s; exact s.elim0
  | succ n ih =>
    intro q hc h1 s G hG
    set q' : Fin n → (Fin n → α) → α → ℝ := fun j ω' => q (Fin.castSucc j) (Fin.snoc ω' default)
    have hq'c : ∀ j : Fin n, Causal j.val (q' j) := by
      intro j ω ω' h
      exact hc _ _ _ (snoc_agree ω ω' default default j.val (le_of_lt j.isLt) h)
    have hq'1 : ∀ j ω, ∑ a, q' j ω a = 1 := fun j ω => h1 _ _
    set r : (Fin n → α) → α → ℝ := fun ω' => q (Fin.last n) (Fin.snoc ω' default)
    have hr : ∀ ω' a, q (Fin.last n) (Fin.snoc ω' a) = r ω' :=
      fun ω' a => hc _ _ _ (snoc_agree ω' ω' a default n le_rfl (fun _ _ => rfl))
    have hs : ∀ ω' a (j : Fin n), q (Fin.castSucc j) (Fin.snoc ω' a) = q' j ω' :=
      fun ω' a j => hc _ _ _ (snoc_agree ω' ω' a default j.val (le_of_lt j.isLt) (fun _ _ => rfl))
    have hprod : ∀ ω' a, ∏ j, q j (Fin.snoc ω' a) ((Fin.snoc ω' a : Fin (n+1) → α) j)
        = (∏ j, q' j ω' (ω' j)) * r ω' a := by
      intro ω' a
      simp_rw [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hs, hr]
    have hr1 : ∀ ω', ∑ a, r ω' a = 1 := fun ω' => h1 _ _
    rw [sum_snoc, sum_snoc]
    simp_rw [hprod]
    revert hG
    refine Fin.lastCases ?_ (fun s' => ?_) s
    · -- s = last
      intro hG
      have hG' : ∀ ω' a, G (Fin.snoc ω' a) = G (Fin.snoc ω' default) :=
        fun ω' a => hG _ _ (snoc_agree ω' ω' a default n le_rfl (fun _ _ => rfl))
      simp_rw [Fin.snoc_last, hr, hG', mul_assoc, ← Finset.mul_sum]
      congr 1; funext ω'; congr 1
      rw [← Finset.sum_mul, hr1, one_mul]
    · -- s = castSucc s'
      intro hG
      have hs'lt : (Fin.castSucc s').val = s'.val := rfl
      set G' : (Fin n → α) → α → ℝ := fun ω' => G (Fin.snoc ω' default)
      have hG' : ∀ ω' a, G (Fin.snoc ω' a) = G' ω' :=
        fun ω' a => hG _ _ (snoc_agree ω' ω' a default s'.val (le_of_lt s'.isLt) (fun _ _ => rfl))
      have hG'c : Causal s'.val G' := by
        intro ω ω' h
        exact hG _ _ (snoc_agree ω ω' default default s'.val (le_of_lt s'.isLt) h)
      simp_rw [Fin.snoc_castSucc, hs, hG', mul_assoc, ← Finset.mul_sum]
      have e1 : ∀ ω', ∑ a, r ω' a * G' ω' (ω' s') = G' ω' (ω' s') := by
        intro ω'; rw [← Finset.sum_mul, hr1, one_mul]
      have e2 : ∀ ω', ∑ a, r ω' a * ∑ b, q' s' ω' b * G' ω' b = ∑ b, q' s' ω' b * G' ω' b := by
        intro ω'; rw [← Finset.sum_mul, hr1, one_mul]
      simp_rw [e1, e2]
      exact ih q' hq'c hq'1 s' G' hG'c

end DPCBTower

namespace DPCBTower

open ReusablePricing.DPCB General

variable (P : General) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)

/-- the kernel of period `j+1` -/
noncomputable def qk (j : Fin P.T) (ω : P.Path) (a : Option (Fin P.K)) : ℝ :=
  P.outcomeProb (P.rate nl m ε β (j.val + 1) ω) a

lemma outcome_fin (j : Fin P.T) (ω : P.Path) : P.outcome (j.val + 1) ω = ω j := by
  unfold General.outcome
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1

lemma pathProb_eq (ω : P.Path) :
    P.pathProb nl m ε β ω = ∏ j : Fin P.T, qk P nl m ε β j ω (ω j) := by
  unfold General.pathProb qk
  set F : ℕ → ℝ := fun t => P.outcomeProb (P.rate nl m ε β t ω) (P.outcome t ω)
  have hj : ∀ j : Fin P.T, P.outcomeProb (P.rate nl m ε β (j.val + 1) ω) (ω j) = F (j.val + 1) := by
    intro j; simp only [F]; rw [outcome_fin]
  rw [Finset.prod_congr rfl (fun j _ => hj j), Fin.prod_univ_eq_prod_range (fun j => F (j + 1)),
    Finset.range_eq_Ico, Finset.prod_Ico_add' F 0 P.T 1]
  congr 1

lemma sum_outcomeProb (x : Fin P.K → ℝ) : ∑ a, P.outcomeProb x a = 1 := by
  rw [Fintype.sum_option]; simp [General.outcomeProb]

lemma D_congr (t : ℕ) (ω ω' : P.Path) (h : ∀ i : Fin P.T, i.val + 1 < t → ω i = ω' i)
    (v : ℕ) (hv : v < t) : P.D v ω = P.D v ω' := by
  unfold General.D General.outcome
  by_cases hb : 1 ≤ v ∧ v ≤ P.T
  · rw [dif_pos hb, dif_pos hb, h ⟨v - 1, by omega⟩ (by simp; omega)]
  · rw [dif_neg hb, dif_neg hb]

lemma stepRate_congr (prev : ℕ → Fin P.K → ℝ) (t : ℕ) (ω ω' : P.Path)
    (h : ∀ v, v < t → P.D v ω = P.D v ω') :
    P.stepRate nl m ε β prev t ω = P.stepRate nl m ε β prev t ω' := by
  have hC : ∀ s i, P.Ctil t s ω i = P.Ctil t s ω' i := by
    intro s i
    unfold General.Ctil
    congr 1
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun v hv => ?_))
    simp only [Finset.mem_filter, Finset.mem_Icc] at hv
    rw [h v (by omega)]
  have hE : ∀ k, P.prevErrWith β prev t ω k = P.prevErrWith β prev t ω' k := by
    intro k
    unfold General.prevErrWith
    refine Finset.sum_congr rfl (fun v hv => ?_)
    simp only [Finset.mem_filter, Finset.mem_Icc] at hv
    rw [h v (by omega)]
  funext k
  unfold General.stepRate
  simp only [hC, hE]

lemma ratesUpTo_congr : ∀ (t : ℕ) (ω ω' : P.Path),
    (∀ i : Fin P.T, i.val + 1 < t → ω i = ω' i) →
    P.ratesUpTo nl m ε β ω t = P.ratesUpTo nl m ε β ω' t := by
  intro t
  induction t with
  | zero => intro ω ω' _; rfl
  | succ t ih =>
    intro ω ω' h
    have h' : ∀ i : Fin P.T, i.val + 1 < t → ω i = ω' i := fun i hi => h i (by omega)
    funext s
    simp only [General.ratesUpTo]
    rw [ih ω ω' h']
    split_ifs
    · exact stepRate_congr P nl m ε β _ (t + 1) ω ω'
        (fun v hv => D_congr P (t + 1) ω ω' h v hv)
    · rfl

lemma rate_congr (t : ℕ) (ω ω' : P.Path) (h : ∀ i : Fin P.T, i.val + 1 < t → ω i = ω' i) :
    P.rate nl m ε β t ω = P.rate nl m ε β t ω' := by
  unfold General.rate
  rw [ratesUpTo_congr P nl m ε β t ω ω' h]

lemma qk_causal (j : Fin P.T) : Causal j.val (qk P nl m ε β j) := by
  intro ω ω' h
  funext a
  unfold qk
  rw [rate_congr P nl m ε β (j.val + 1) ω ω' (fun i hi => h i (by omega))]

lemma tower_P (j : Fin P.T) (G : P.Path → Option (Fin P.K) → ℝ) (hG : Causal j.val G) :
    ∑ ω, P.pathProb nl m ε β ω * G ω (ω j) =
      ∑ ω, P.pathProb nl m ε β ω *
        ∑ a, P.outcomeProb (P.rate nl m ε β (j.val + 1) ω) a * G ω a := by
  simp_rw [pathProb_eq]
  exact tower P.T (qk P nl m ε β) (qk_causal P nl m ε β)
    (fun j ω => sum_outcomeProb P _) j G hG

lemma mass_P : ∑ ω, P.pathProb nl m ε β ω = 1 := by
  simp_rw [pathProb_eq]
  exact mass P.T (qk P nl m ε β) (qk_causal P nl m ε β) (fun j ω => sum_outcomeProb P _)

/-- `err s` reads the path only through periods `≤ s`. -/
lemma err_causal (s j : ℕ) (hs : s ≤ j) (k : Fin P.K) :
    Causal j (fun ω => P.err nl m ε β s ω k) := by
  intro ω ω' h
  show P.D s ω k - P.rate nl m ε β s ω k = P.D s ω' k - P.rate nl m ε β s ω' k
  rw [D_congr P (s + 1) ω ω' (fun i hi => h i (by omega)) s (by omega),
    rate_congr P nl m ε β s ω ω' (fun i hi => h i (by omega))]

lemma sum_ind_mul (x : Fin P.K → ℝ) (k : Fin P.K) (c : ℝ) :
    ∑ a, P.outcomeProb x a * ((if a = some k then (1:ℝ) else 0) - c) = x k - c := by
  have h1 := sum_outcomeProb P x
  have : ∑ a, P.outcomeProb x a * ((if a = some k then (1:ℝ) else 0) - c)
      = ∑ a, (if a = some k then P.outcomeProb x a else 0) - c * ∑ a, P.outcomeProb x a := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    split_ifs <;> ring
  rw [this, h1, Finset.sum_ite_eq']
  simp [General.outcomeProb]

lemma sum_ind_sq (x : Fin P.K → ℝ) (k : Fin P.K) (c : ℝ) (hc : c = x k) :
    ∑ a, P.outcomeProb x a * ((if a = some k then (1:ℝ) else 0) - c) ^ 2 = x k - x k ^ 2 := by
  have h1 := sum_outcomeProb P x
  have : ∑ a, P.outcomeProb x a * ((if a = some k then (1:ℝ) else 0) - c) ^ 2
      = (1 - 2 * c) * ∑ a, (if a = some k then P.outcomeProb x a else 0)
        + c ^ 2 * ∑ a, P.outcomeProb x a := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    split_ifs <;> ring
  rw [this, h1, Finset.sum_ite_eq']
  simp [General.outcomeProb, hc]
  ring

lemma D_eq (j : Fin P.T) (ω : P.Path) (k : Fin P.K) :
    P.D (j.val + 1) ω k = if ω j = some k then 1 else 0 := by
  unfold General.D; rw [outcome_fin]

/-- Martingale-difference property: `E[F · Δ^s_k] = 0` when `F` reads only periods `< s`. -/
lemma err_mean (s : ℕ) (hs : s ∈ Icc 1 P.T) (k : Fin P.K) (F : P.Path → ℝ)
    (hF : Causal (s - 1) F) :
    ∑ ω, P.pathProb nl m ε β ω * (F ω * P.err nl m ε β s ω k) = 0 := by
  rw [Finset.mem_Icc] at hs
  set j : Fin P.T := ⟨s - 1, by omega⟩
  have hsj : s = j.val + 1 := by simp [j]; omega
  set G : P.Path → Option (Fin P.K) → ℝ := fun ω a =>
    F ω * ((if a = some k then (1:ℝ) else 0) - P.rate nl m ε β s ω k)
  have hG : Causal j.val G := by
    intro ω ω' h
    funext a
    simp only [G]
    rw [hF ω ω' h, rate_congr P nl m ε β s ω ω' (fun i hi => h i (by simp [j]; omega))]
  have key := tower_P P nl m ε β j G hG
  have lhs : ∀ ω, F ω * P.err nl m ε β s ω k = G ω (ω j) := by
    intro ω; simp only [G, General.err]; rw [hsj, D_eq]
  simp_rw [lhs, key]
  refine Finset.sum_eq_zero (fun ω _ => ?_)
  simp only [G]
  rw [← hsj]
  simp_rw [mul_left_comm _ (F ω), ← Finset.mul_sum, sum_ind_mul, sub_self, mul_zero]

end DPCBTower

namespace DPCBTower

open ReusablePricing.DPCB General

variable (P : General) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)

lemma rate_succ (t : ℕ) (ω : P.Path) :
    P.rate nl m ε β (t + 1) ω = P.stepRate nl m ε β (P.ratesUpTo nl m ε β ω t) (t + 1) ω := by
  simp [General.rate, General.ratesUpTo]

lemma rate_bounds (hP : P.ModelFacts) (t : ℕ) (ω : P.Path) (k : Fin P.K) :
    0 ≤ P.rate nl m ε β t ω k ∧ P.rate nl m ε β t ω k ≤ P.lamU := by
  have hU := hP.lamU_pos
  cases t with
  | zero => simp [General.rate, General.ratesUpTo]; exact le_of_lt hU
  | succ t =>
    rw [rate_succ]
    unfold General.stepRate
    split_ifs <;> first
      | exact ⟨le_max_left _ _, max_le (le_of_lt hU) (min_le_left _ _)⟩
      | exact ⟨le_rfl, le_of_lt hU⟩

lemma rate_zero_of_nonpos (t : ℕ) (ω : P.Path) (k : Fin P.K) (ht : 1 ≤ t)
    (hk : ¬ 0 < P.lamD t k) : P.rate nl m ε β t ω k = 0 := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [rate_succ]
  unfold General.stepRate
  have hk' : P.lamD (t' + 1) k ≤ 0 := not_lt.mp hk
  split_ifs with h1
  · rw [mul_zero, sub_zero]
    exact le_antisymm (max_le le_rfl (le_trans (min_le_right _ _) hk')) (le_max_left _ _)
  · rfl

lemma pathProb_nonneg (hP : P.ModelFacts) (ω : P.Path) : 0 ≤ P.pathProb nl m ε β ω := by
  unfold General.pathProb
  refine Finset.prod_nonneg (fun t _ => ?_)
  cases h : P.outcome t ω with
  | some k => exact (rate_bounds P nl m ε β hP t ω k).1
  | none =>
    simp only [General.outcomeProb]
    have : ∑ k, P.rate nl m ε β t ω k ≤ ∑ _k : Fin P.K, P.lamU :=
      Finset.sum_le_sum (fun k _ => (rate_bounds P nl m ε β hP t ω k).2)
    simp at this
    have h2 := hP.K_mul_lamU_le_one
    linarith

end DPCBTower

open ReusablePricing.DPCB General DPCBTower in
theorem solution (P : General) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ)
    (β : Fin P.K → ℕ → ℕ) (B : Fin P.K → ℕ)
    (hP : P.ModelFacts) (hbat : P.BatchesValid m β B) :
    ∀ k, ∀ b ∈ Icc 1 (B k),
      P.expect nl m ε β (fun ω => (∑ s ∈ P.batch β k b, P.err nl m ε β s ω k) ^ 2) ≤ (m k : ℝ) := by
  intro k b hb
  set S := P.batch β k b
  set μ := P.pathProb nl m ε β
  set X : ℕ → P.Path → ℝ := fun s ω => P.err nl m ε β s ω k
  have hS : ∀ s ∈ S, 1 ≤ s ∧ s ≤ P.T := by
    intro s hs
    simp only [S, General.batch, Finset.mem_filter, Finset.mem_Icc] at hs
    exact hs.1
  -- cross terms vanish
  have hcross : ∀ s s', s ∈ S → s' ∈ S → s < s' → ∑ ω, μ ω * (X s ω * X s' ω) = 0 := by
    intro s s' hs hs' hlt
    have h1 := hS s' hs'
    exact err_mean P nl m ε β s' (by rw [Finset.mem_Icc]; exact h1) k (X s)
      (err_causal P nl m ε β s (s' - 1) (by omega) k)
  -- diagonal terms
  have hdiag : ∀ s ∈ S, ∑ ω, μ ω * (X s ω * X s ω) ≤ if 0 < P.lamD s k then 1 else 0 := by
    intro s hs
    have h1 := hS s hs
    set j : Fin P.T := ⟨s - 1, by omega⟩
    have hsj : s = j.val + 1 := by simp [j]; omega
    set G : P.Path → Option (Fin P.K) → ℝ := fun ω a =>
      ((if a = some k then (1:ℝ) else 0) - P.rate nl m ε β s ω k) ^ 2
    have hG : Causal j.val G := by
      intro ω ω' h
      funext a
      simp only [G]
      rw [rate_congr P nl m ε β s ω ω' (fun i hi => h i (by simp [j]; omega))]
    have key := tower_P P nl m ε β j G hG
    have lhs : ∀ ω, X s ω * X s ω = G ω (ω j) := by
      intro ω; simp only [G, X, General.err]; rw [hsj, D_eq]; ring
    simp_rw [lhs]
    rw [key, ← hsj]
    simp only [G]
    simp_rw [sum_ind_sq P _ k _ rfl]
    have hb' : ∀ ω, P.rate nl m ε β s ω k - P.rate nl m ε β s ω k ^ 2 ≤
        (if 0 < P.lamD s k then 1 else 0) := by
      intro ω
      have hr := rate_bounds P nl m ε β hP s ω k
      have hU := hP.lamU_le_one
      split_ifs with hpos
      · nlinarith
      · rw [rate_zero_of_nonpos P nl m ε β s ω k h1.1 hpos]; norm_num
    calc ∑ ω, μ ω * (P.rate nl m ε β s ω k - P.rate nl m ε β s ω k ^ 2)
        ≤ ∑ ω, μ ω * (if 0 < P.lamD s k then (1:ℝ) else 0) :=
          Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hb' ω)
            (pathProb_nonneg P nl m ε β hP ω))
      _ = (if 0 < P.lamD s k then 1 else 0) := by
          rw [← Finset.sum_mul, mass_P, one_mul]
  -- expand
  have hexp : P.expect nl m ε β (fun ω => (∑ s ∈ S, X s ω) ^ 2)
      = ∑ s ∈ S, ∑ s' ∈ S, ∑ ω, μ ω * (X s ω * X s' ω) := by
    unfold General.expect
    simp_rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.sum_comm]
  have hrow : ∀ s ∈ S, ∑ s' ∈ S, ∑ ω, μ ω * (X s ω * X s' ω) = ∑ ω, μ ω * (X s ω * X s ω) := by
    intro s hs
    refine Finset.sum_eq_single_of_mem s hs (fun s' hs' hne => ?_)
    rcases lt_or_gt_of_ne hne with h | h
    · simp_rw [mul_comm (X s _) (X s' _)]
      exact hcross s' s hs' hs h
    · exact hcross s s' hs hs' h
  show P.expect nl m ε β (fun ω => (∑ s ∈ S, X s ω) ^ 2) ≤ (m k : ℝ)
  rw [hexp, Finset.sum_congr rfl hrow]
  calc ∑ s ∈ S, ∑ ω, μ ω * (X s ω * X s ω) ≤ ∑ s ∈ S, (if 0 < P.lamD s k then (1:ℝ) else 0) :=
        Finset.sum_le_sum hdiag
    _ = (m k : ℝ) := by
        rw [Finset.sum_boole]
        congr 1
        rw [← (hbat k).2.2.2 b hb]
        simp only [S, General.batch, Finset.filter_filter]

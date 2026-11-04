-- Prove2me | solution 1 for ReusablePricing.DPCB.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T03:37:40.309568+00:00
-- url     : https://prove2.me/submissions/0e36488b-083c-48e3-8c3a-cd71399607bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ReusablePricing_DPCB_Events
import Theorems.Thm_ReusablePricing_DPCB_eq_EC22
import Theorems.Thm_ReusablePricing_DPCB_lemma_EC4
import Theorems.Thm_ReusablePricing_DPCB_batch_error_sq
import Theorems.Thm_ReusablePricing_DPCB_grad_correction_mean_zero

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false



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


namespace DPCB3

/-- Second-order lower Taylor bound on a box. -/
theorem taylor_lower {K : ℕ} (f : (Fin K → ℝ) → ℝ) (lo hi : Fin K → ℝ) (Ψ : ℝ)
    (hf : ∀ x : Fin K → ℝ, (∀ k, lo k ≤ x k ∧ x k ≤ hi k) →
      DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ (fderiv ℝ f) x ∧
      ∀ v : Fin K → ℝ, |fderiv ℝ (fderiv ℝ f) x v v| ≤ Ψ * ∑ k, v k ^ 2)
    (x0 x1 : Fin K → ℝ) (h0 : ∀ k, lo k ≤ x0 k ∧ x0 k ≤ hi k)
    (h1 : ∀ k, lo k ≤ x1 k ∧ x1 k ≤ hi k) :
    f x0 - f x1 ≤ fderiv ℝ f x0 (x0 - x1) + Ψ * ∑ k, (x1 k - x0 k) ^ 2 := by
  set v : Fin K → ℝ := x1 - x0
  set p : ℝ → Fin K → ℝ := fun s => x0 + s • v
  have hp : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ k, lo k ≤ p s k ∧ p s k ≤ hi k := by
    intro s hs k
    obtain ⟨hs0, hs1⟩ := hs
    simp only [p, v, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have e : x0 k + s * (x1 k - x0 k) = (1 - s) * x0 k + s * x1 k := by ring
    rw [e]
    constructor
    · nlinarith [(h0 k).1, (h1 k).1]
    · nlinarith [(h0 k).2, (h1 k).2]
  have hpd : ∀ s, HasDerivAt p v s := by
    intro s
    have := ((hasDerivAt_id s).smul_const v).const_add x0
    simpa [p] using this
  set S : ℝ := ∑ k, v k ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  -- h(s) = Df(p s) v
  set h : ℝ → ℝ := fun s => fderiv ℝ f (p s) v
  have hh : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivAt h (fderiv ℝ (fderiv ℝ f) (p s) v v) s := by
    intro s hs
    have hd := (hf (p s) (hp s hs)).2.1
    have h2 : HasDerivAt (fun s => fderiv ℝ f (p s)) (fderiv ℝ (fderiv ℝ f) (p s) v) s :=
      hd.hasFDerivAt.comp_hasDerivAt s (hpd s)
    have h3 := h2.clm_apply (hasDerivAt_const s v)
    simpa [h] using h3
  have hbound1 : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖h s - h 0‖ ≤ (Ψ * S) * (s - 0) := by
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := h)
      (f' := fun s => fderiv ℝ (fderiv ℝ f) (p s) v v) (a := 0) (b := 1) (C := Ψ * S)
      (fun s hs => (hh s hs).hasDerivWithinAt)
      (fun s hs => by
        rw [Real.norm_eq_abs]
        exact (hf (p s) (hp s (Set.Ico_subset_Icc_self hs))).2.2 v)
    exact this
  -- g(s) = f(p s) - s * h 0
  set g : ℝ → ℝ := fun s => f (p s) - s * h 0
  have hg : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivAt g (h s - h 0) s := by
    intro s hs
    have hd := (hf (p s) (hp s hs)).1
    have h2 : HasDerivAt (fun s => f (p s)) (fderiv ℝ f (p s) v) s :=
      hd.hasFDerivAt.comp_hasDerivAt s (hpd s)
    have h3 : HasDerivAt (fun s => f (p s) - s * h 0) (fderiv ℝ f (p s) v - 1 * h 0) s :=
      h2.sub ((hasDerivAt_id' s).mul_const (h 0))
    convert h3 using 1
    simp [h]
  have hbound2 := norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
      (f' := fun s => h s - h 0) (a := 0) (b := 1) (C := Ψ * S)
      (fun s hs => (hg s hs).hasDerivWithinAt)
      (fun s hs => by
        have := hbound1 s (Set.Ico_subset_Icc_self hs)
        have hs1 : s - 0 ≤ 1 := by linarith [hs.2]
        have hΨS : 0 ≤ Ψ * S := le_trans (abs_nonneg _) ((hf x0 h0).2.2 v)
        calc ‖h s - h 0‖ ≤ Ψ * S * (s - 0) := this
          _ ≤ Ψ * S * 1 := mul_le_mul_of_nonneg_left hs1 hΨS
          _ = Ψ * S := mul_one _)
      1 (by simp)
  have hp0 : p 0 = x0 := by simp [p]
  have hp1 : p 1 = x1 := by simp [p, v]
  have hgv : g 1 - g 0 = f x1 - f x0 - fderiv ℝ f x0 v := by
    simp only [g, h, hp0, hp1]; ring
  rw [hgv, Real.norm_eq_abs] at hbound2
  have hlin : fderiv ℝ f x0 (x0 - x1) = - fderiv ℝ f x0 v := by
    rw [← map_neg]; congr 1; simp [v]
  have hSv : S = ∑ k, (x1 k - x0 k) ^ 2 := by simp [S, v]
  rw [hlin, ← hSv]
  have := neg_abs_le (f x1 - f x0 - fderiv ℝ f x0 v)
  nlinarith [abs_le.mp (le_trans (le_refl _) hbound2)]

end DPCB3

namespace DPCB3

open ReusablePricing.DPCB General DPCBTower

variable (P : General) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
  (B : Fin P.K → ℕ)

lemma beta_ge_one (hbat : P.BatchesValid m β B) (k : Fin P.K) :
    ∀ s, 1 ≤ s → s ≤ P.T → 1 ≤ β k s := by
  intro s
  induction s with
  | zero => intro h; omega
  | succ s ih =>
    intro _ hT
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0; rw [(hbat k).1]
    · rcases (hbat k).2.1 s hpos (by omega) with h | h
      · rw [h]; exact ih hpos (by omega)
      · rw [h]; omega

lemma beta_mono (hbat : P.BatchesValid m β B) (k : Fin P.K) :
    ∀ d s, 1 ≤ s → s + d ≤ P.T → β k s ≤ β k (s + d) := by
  intro d
  induction d with
  | zero => intro s _ _; exact le_rfl
  | succ d ih =>
    intro s hs hT
    have h1 := ih s hs (by omega)
    rcases (hbat k).2.1 (s + d) (by omega) (by omega) with h | h
    · rw [← add_assoc, h]; exact h1
    · rw [← add_assoc, h]; omega

lemma beta_le_B (hbat : P.BatchesValid m β B) (k : Fin P.K) (s : ℕ) (hs : 1 ≤ s) (hT : s ≤ P.T) :
    β k s ≤ B k := by
  have := beta_mono P m β B hbat k (P.T - s) s hs (by omega)
  rw [show s + (P.T - s) = P.T by omega, (hbat k).2.2.1] at this
  exact this

lemma lt_of_beta_lt (hbat : P.BatchesValid m β B) (k : Fin P.K) (s t : ℕ) (hs : 1 ≤ s)
    (ht : 1 ≤ t) (hsT : s ≤ P.T) (htT : t ≤ P.T) (h : β k s < β k t) : s < t := by
  by_contra hc
  push_neg at hc
  have := beta_mono P m β B hbat k (s - t) t ht (by omega)
  rw [show t + (s - t) = s by omega] at this
  omega

lemma batch_zero_empty (hbat : P.BatchesValid m β B) (k : Fin P.K) : P.batch β k 0 = ∅ := by
  ext s
  simp only [General.batch, Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]
  intro ⟨⟨h1, h2⟩, h3⟩
  have := beta_ge_one P m β B hbat k s h1 h2
  omega

/-- The previous-batch error sum is the full error sum over batch `β_k(t) - 1`. -/
lemma prevErr_eq (hbat : P.BatchesValid m β B) (t : ℕ) (ht : t ∈ Icc 1 P.T) (ω : P.Path)
    (k : Fin P.K) :
    P.prevErr nl m ε β t ω k = ∑ s ∈ P.batch β k (β k t - 1), P.err nl m ε β s ω k := by
  rw [Finset.mem_Icc] at ht
  have hbt := beta_ge_one P m β B hbat k t ht.1 ht.2
  unfold General.prevErr General.prevErrWith
  refine Finset.sum_congr ?_ (fun s _ => rfl)
  ext s
  simp only [General.batch, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, by omega⟩, by omega⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hbs := beta_ge_one P m β B hbat k s h1 h2
    have := lt_of_beta_lt P m β B hbat k s t h1 ht.1 h2 ht.2 (by omega)
    exact ⟨⟨h1, by omega⟩, by omega⟩

lemma epsMin_le (hK : 1 ≤ P.K) (k : Fin P.K) : P.epsMin ε ≤ ε k :=
  ciInf_le (Set.finite_range ε).bddBelow k

lemma one_lt_epsMin (hK : 1 ≤ P.K) (hε : ∀ k, 1 < ε k) : 1 < P.epsMin ε := by
  haveI : Nonempty (Fin P.K) := ⟨⟨0, by omega⟩⟩
  obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := ε)
  unfold General.epsMin; rw [← hk]; exact hε k

lemma one_le_nlMin (hK : 1 ≤ P.K) (hnl : ∀ k, 1 ≤ nl k) : 1 ≤ P.nlMin nl := by
  haveI : Nonempty (Fin P.K) := ⟨⟨0, by omega⟩⟩
  unfold General.nlMin
  have : 1 ≤ ⨅ k, nl k := le_ciInf hnl
  exact_mod_cast this

lemma delta_le (hK : 1 ≤ P.K) (hnl : ∀ k, 1 ≤ nl k) (hε : ∀ k, 1 < ε k) (k : Fin P.K) (b : ℕ) :
    P.delta nl ε β k b ≤ (ε k - 1) / 4 := by
  have h1 := one_le_nlMin P nl hK hnl
  have hc0 : 0 ≤ (P.nlMin nl - 1) / P.nlMin nl := div_nonneg (by linarith) (by linarith)
  have hc1 : (P.nlMin nl - 1) / P.nlMin nl ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have he := epsMin_le P ε hK k
  have he1 := one_lt_epsMin P ε hK hε
  have hKr : (1:ℝ) ≤ P.K := by exact_mod_cast hK
  have hk1 := hε k
  unfold General.delta
  split_ifs
  · have : (P.epsMin ε - 1) / (4 * (P.K : ℝ)) ≤ (ε k - 1) / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h0 : 0 ≤ (P.epsMin ε - 1) / (4 * (P.K : ℝ)) := div_nonneg (by linarith) (by positivity)
    nlinarith
  · have h0 : 0 ≤ (ε k - 1) / 4 := div_nonneg (by linarith) (by norm_num)
    nlinarith

/-- On `𝒢`, the previous-batch error sum is at most `(ϵ_k - 1)/4` in absolute value. -/
lemma prevErr_abs_le_G (hbat : P.BatchesValid m β B) (hK : 1 ≤ P.K) (hnl : ∀ k, 1 ≤ nl k)
    (hε : ∀ k, 1 < ε k) (t : ℕ) (ht : t ∈ Icc 1 P.T) (ω : P.Path) (k : Fin P.K)
    (hG : P.inG nl m ε β B (P.delta nl ε β) ω) :
    |P.prevErr nl m ε β t ω k| ≤ (ε k - 1) / 4 := by
  rw [prevErr_eq P nl m ε β B hbat t ht ω k]
  have hk1 := hε k
  have hpos : 0 ≤ (ε k - 1) / 4 := div_nonneg (by linarith) (by norm_num)
  set b' := β k t - 1
  rcases (P.batch β k b').eq_empty_or_nonempty with he | hne
  · rw [he]; simpa using hpos
  · have hb' : b' ∈ Icc 1 (B k) := by
      obtain ⟨s, hs⟩ := hne
      simp only [General.batch, Finset.mem_filter, Finset.mem_Icc] at hs
      have h1 := beta_ge_one P m β B hbat k s hs.1.1 hs.1.2
      rw [Finset.mem_Icc] at ht ⊢
      have h2 := beta_le_B P m β B hbat k t ht.1 ht.2
      omega
    set t' := (P.batch β k b').max' hne
    have hA := hG k b' hb' t' (Finset.max'_mem _ hne)
    have hfil : (P.batch β k b').filter (fun s => s ≤ t') = P.batch β k b' :=
      Finset.filter_true_of_mem (fun s hs => Finset.le_max' _ s hs)
    rw [hfil] at hA
    exact le_trans (le_of_lt hA) (delta_le P nl ε β hK hnl hε k b')

end DPCB3

namespace DPCB3

open ReusablePricing.DPCB General DPCBTower

variable (P : General) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
  (B : Fin P.K → ℕ)

lemma err_zero_pos (s : ℕ) (hs : s ∈ Icc 1 P.T) (ω : P.Path)
    (hω : 0 < P.pathProb nl m ε β ω) (k : Fin P.K) (hk : ¬ 0 < P.lamD s k) :
    P.err nl m ε β s ω k = 0 := by
  have hr := rate_zero_of_nonpos P nl m ε β s ω k (Finset.mem_Icc.mp hs).1 hk
  unfold General.err General.D
  rw [hr]
  split_ifs with h
  · exfalso
    have : P.pathProb nl m ε β ω = 0 := by
      unfold General.pathProb
      exact Finset.prod_eq_zero hs (by rw [h]; simp [General.outcomeProb, hr])
    linarith
  · simp

lemma err_abs_le_one (hP : P.ModelFacts) (s : ℕ) (ω : P.Path) (k : Fin P.K) :
    |P.err nl m ε β s ω k| ≤ 1 := by
  have hr := rate_bounds P nl m ε β hP s ω k
  have hU := hP.lamU_le_one
  unfold General.err General.D
  rw [abs_le]
  split_ifs <;> constructor <;> linarith [hr.1, hr.2]

lemma prevErr_abs_le_m (hP : P.ModelFacts) (hbat : P.BatchesValid m β B) (t : ℕ)
    (ht : t ∈ Icc 1 P.T) (ω : P.Path) (hω : 0 < P.pathProb nl m ε β ω) (k : Fin P.K) :
    |P.prevErr nl m ε β t ω k| ≤ (m k : ℝ) := by
  rw [prevErr_eq P nl m ε β B hbat t ht ω k]
  set b' := β k t - 1
  have hle : ∀ s ∈ P.batch β k b', |P.err nl m ε β s ω k| ≤ if 0 < P.lamD s k then 1 else 0 := by
    intro s hs
    have hs' : s ∈ Icc 1 P.T := (Finset.mem_filter.mp hs).1
    split_ifs with hpos
    · exact err_abs_le_one P nl m ε β hP s ω k
    · rw [err_zero_pos P nl m ε β s hs' ω hω k hpos]; simp
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum hle) ?_)
  rw [Finset.sum_boole]
  rcases Nat.eq_zero_or_pos b' with h0 | hpos
  · rw [h0, batch_zero_empty P m β B hbat k]; simp
  · have hb' : b' ∈ Icc 1 (B k) := by
      rw [Finset.mem_Icc] at ht ⊢
      have h2 := beta_le_B P m β B hbat k t ht.1 ht.2
      omega
    rw [← (hbat k).2.2.2 b' hb']
    simp only [General.batch, Finset.filter_filter]
    exact le_rfl

end DPCB3

namespace DPCB3

open ReusablePricing.DPCB General DPCBTower

variable (P : General) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
  (B : Fin P.K → ℕ)

lemma clm_apply_eq_sum (L : (Fin P.K → ℝ) →L[ℝ] ℝ) (d : Fin P.K → ℝ) :
    L d = ∑ k, d k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single d]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : (Pi.single k (d k) : Fin P.K → ℝ) = d k • (Pi.single k (1:ℝ) : Fin P.K → ℝ) := by
    ext j; simp [Pi.single_apply]
  rw [this, map_smul, smul_eq_mul]

open Classical in
/-- Pathwise bound of EC.4 Step 2, on every path of positive probability. -/
lemma path_bound (R Ψ φL φU : ℝ) (hst : P.Standing R Ψ φL φU nl)
    (hbat : P.BatchesValid m β B) (hm : ∀ k, 1 ≤ m k ∧ m k ≤ nl k)
    (hε : ∀ k, 1 < ε k ∧
      ε k ≤ min ((nl k : ℝ) * min 1 ((1 + 4 * (m k : ℝ) * min φL φU) / (4 * (m k : ℝ) + (nl k : ℝ))))
                (1 + 16 * min P.maxC (m k : ℝ)))
    (t : ℕ) (ht : t ∈ Icc 1 P.T) (ω : P.Path) (hω : 0 < P.pathProb nl m ε β ω) :
    P.r t (P.lamD t) - P.r t (P.rate nl m ε β t ω) ≤
      ∑ k, Ψ * (ε k / (nl k : ℝ)) + 2 * Ψ * ∑ k, (ε k / (nl k : ℝ)) ^ 2
      + ∑ k, fderiv ℝ (P.r t) (P.lamD t) (Pi.single k 1) *
          (P.etaDelta nl m ε β t ω k * P.etaE t k)
      + 2 * Ψ * ∑ k, (P.etaDelta nl m ε β t ω k) ^ 2
      + (if P.inG nl m ε β B (P.delta nl ε β) ω then 0 else 1) * (2 * R + Ψ * (P.K : ℝ)) := by
  have hP := hst.facts
  obtain ⟨hφL, hφU, hΨ, hbox, hA5⟩ := hst.a5
  set c : Fin P.K → ℝ := fun k => fderiv ℝ (P.r t) (P.lamD t) (Pi.single k 1)
  set a : Fin P.K → ℝ := fun k => ε k / (nl k : ℝ)
  set η : Fin P.K → ℝ := fun k => P.etaDelta nl m ε β t ω k
  set e : Fin P.K → ℝ := fun k => P.etaE t k
  have hnl : ∀ k, (1:ℝ) ≤ nl k := fun k => by exact_mod_cast le_trans (hm k).1 (hm k).2
  have hmr : ∀ k, (1:ℝ) ≤ m k := fun k => by exact_mod_cast (hm k).1
  have ha0 : ∀ k, 0 ≤ a k := fun k => div_nonneg (by linarith [(hε k).1]) (by linarith [hnl k])
  have he01 : ∀ k, e k = 0 ∨ e k = 1 := by
    intro k; simp only [e, General.etaE]; split_ifs <;> simp
  have hlamD_box : ∀ k, P.lamD t k - φL ≤ P.lamD t k ∧ P.lamD t k ≤ P.lamD t k + φU :=
    fun k => ⟨by linarith, by linarith⟩
  have hc : ∀ k, |c k| ≤ Ψ := fun k => ((hA5 t ht (P.lamD t) hlamD_box).2.2.1 k)
  -- `|η_k| e_k ≤ 1` on paths of positive probability
  have hηe : ∀ k, |η k * e k| ≤ 1 := by
    intro k
    have h1 := prevErr_abs_le_m P nl m ε β B hP hbat t ht ω hω k
    have : |η k| ≤ 1 := by
      simp only [η, General.etaDelta]
      rw [abs_div, abs_of_pos (by linarith [hmr k] : (0:ℝ) < m k), div_le_one (by linarith [hmr k])]
      exact h1
    rcases he01 k with h | h <;> rw [h] <;> simp [this]
  have hAlow : -(Ψ * (P.K : ℝ)) ≤ ∑ k, c k * (η k * e k) := by
    have : ∀ k ∈ (Finset.univ : Finset (Fin P.K)), -Ψ ≤ c k * (η k * e k) := by
      intro k _
      have h1 := abs_mul (c k) (η k * e k)
      have h2 : |c k * (η k * e k)| ≤ Ψ := by
        rw [h1]; nlinarith [hc k, hηe k, abs_nonneg (c k), abs_nonneg (η k * e k)]
      linarith [neg_abs_le (c k * (η k * e k))]
    have := Finset.sum_le_sum this
    simp at this
    linarith
  have hsa : 0 ≤ ∑ k, Ψ * a k := Finset.sum_nonneg (fun k _ => mul_nonneg hΨ.le (ha0 k))
  have hsa2 : 0 ≤ 2 * Ψ * ∑ k, a k ^ 2 :=
    mul_nonneg (by linarith) (Finset.sum_nonneg (fun k _ => sq_nonneg _))
  have hsη : 0 ≤ 2 * Ψ * ∑ k, η k ^ 2 :=
    mul_nonneg (by linarith) (Finset.sum_nonneg (fun k _ => sq_nonneg _))
  have hT1 := (Finset.mem_Icc.mp ht)
  have hlamΩ : P.lamD t ∈ P.Omega := hst.opt.1.1 t ht
  have hrateΩ : P.rate nl m ε β t ω ∈ P.Omega := fun k => rate_bounds P nl m ε β hP t ω k
  have hR1 := ((hst.a4 t ht).2.1 _ hlamΩ)
  have hR2 := ((hst.a4 t ht).2.1 _ hrateΩ)
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) hR1
  have hKr : (0:ℝ) ≤ P.K := by positivity
  change P.r t (P.lamD t) - P.r t (P.rate nl m ε β t ω) ≤
      ∑ k, Ψ * a k + 2 * Ψ * ∑ k, a k ^ 2 + ∑ k, c k * (η k * e k) + 2 * Ψ * ∑ k, η k ^ 2
      + (if P.inG nl m ε β B (P.delta nl ε β) ω then 0 else 1) * (2 * R + Ψ * (P.K : ℝ))
  by_cases hG : P.inG nl m ε β B (P.delta nl ε β) ω
  · rw [if_pos hG, zero_mul, add_zero]
    have hε' : ∀ k, ε k ≤ (nl k : ℝ) *
        min 1 ((1 + 4 * (m k : ℝ) * min φL φU) / ((nl k : ℝ) + 4 * (m k : ℝ))) := by
      intro k; rw [add_comm (nl k : ℝ)]; exact le_trans (hε k).2 (min_le_left _ _)
    have h22 := eq_EC22 P R Ψ φL φU nl m ε β B hst hbat hm hε' ω hω hG t ht
    set d : Fin P.K → ℝ := fun k => (a k + η k) * e k
    have hx1 : ∀ k, P.rate nl m ε β t ω k = P.lamD t k - d k := by
      intro k; rw [h22 k]; simp only [d, a, η, e, General.etaDelta, General.etaE]; ring
    -- box bound on `d`
    have hd : ∀ k, -φU ≤ d k ∧ d k ≤ φL := by
      intro k
      rcases he01 k with h0 | h1
      · simp only [d, h0, mul_zero]; exact ⟨by linarith, by linarith⟩
      · have hpos : 0 < P.lamD t k := by
          by_contra hc; simp only [e, General.etaE, if_neg hc] at h1; norm_num at h1
        have hεk := hε k
        have hmk := hmr k
        have hnk := hnl k
        have hφ : min φL φU > 0 := lt_min hφL hφU
        have hprev := prevErr_abs_le_G P nl m ε β B hbat hP.one_le_K
          (fun k => le_trans (hm k).1 (hm k).2) (fun k => (hε k).1) t ht ω k hG
        have hηb : |η k| ≤ (ε k - 1) / (4 * m k) := by
          simp only [η, General.etaDelta]
          rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < m k), div_le_iff₀ (by linarith)]
          calc |P.prevErr nl m ε β t ω k| ≤ (ε k - 1) / 4 := hprev
            _ = (ε k - 1) / (4 * m k) * m k := by field_simp
        have hcond : ε k ≤ (nl k : ℝ) * ((1 + 4 * (m k : ℝ) * min φL φU) / (4 * (m k : ℝ) + (nl k : ℝ))) :=
          le_trans (le_trans hεk.2 (min_le_left _ _))
            (mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith))
        rw [mul_div_assoc', le_div_iff₀ (by linarith)] at hcond
        have hkey : a k + (ε k - 1) / (4 * m k) ≤ min φL φU := by
          simp only [a]
          rw [div_add_div _ _ (by linarith) (by linarith), div_le_iff₀ (by positivity)]
          nlinarith
        have hφ1 := min_le_left φL φU
        have hφ2 := min_le_right φL φU
        have hab := abs_le.mp hηb
        simp only [d, h1, mul_one]
        constructor <;> nlinarith [ha0 k]
    have hbox1 : ∀ k, P.lamD t k - φL ≤ P.rate nl m ε β t ω k ∧
        P.rate nl m ε β t ω k ≤ P.lamD t k + φU := by
      intro k; rw [hx1 k]; constructor <;> linarith [hd k]
    have htay := taylor_lower (P.r t) (fun k => P.lamD t k - φL) (fun k => P.lamD t k + φU) Ψ
      (fun x hx => ⟨(hA5 t ht x hx).1, (hA5 t ht x hx).2.1, (hA5 t ht x hx).2.2.2⟩) (P.lamD t) (P.rate nl m ε β t ω) hlamD_box hbox1
    have hdiff : P.lamD t - P.rate nl m ε β t ω = d := by
      funext k; simp only [Pi.sub_apply]; rw [hx1 k]; ring
    rw [hdiff, clm_apply_eq_sum] at htay
    have hsq : ∀ k, (P.rate nl m ε β t ω k - P.lamD t k) ^ 2 = d k ^ 2 := by
      intro k; rw [hx1 k]; ring
    simp_rw [hsq] at htay
    have hlin : ∑ k, d k * fderiv ℝ (P.r t) (P.lamD t) (Pi.single k 1)
        ≤ ∑ k, Ψ * a k + ∑ k, c k * (η k * e k) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun k _ => ?_)
      change d k * c k ≤ Ψ * a k + c k * (η k * e k)
      simp only [d]
      have hck := abs_le.mp (hc k)
      rcases he01 k with h | h <;> rw [h]
      · simp; nlinarith [ha0 k]
      · nlinarith [ha0 k]
    have hquad : Ψ * ∑ k, d k ^ 2 ≤ 2 * Ψ * ∑ k, a k ^ 2 + 2 * Ψ * ∑ k, η k ^ 2 := by
      have hpt : ∀ k ∈ (Finset.univ : Finset (Fin P.K)), d k ^ 2 ≤ 2 * a k ^ 2 + 2 * η k ^ 2 := by
        intro k _
        simp only [d]
        rcases he01 k with h | h <;> rw [h]
        · simp; positivity
        · nlinarith [sq_nonneg (a k - η k)]
      have hs := Finset.sum_le_sum hpt
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
      nlinarith
    linarith
  · rw [if_neg hG, one_mul]
    have : P.r t (P.lamD t) - P.r t (P.rate nl m ε β t ω) ≤ 2 * R := by
      have := abs_le.mp hR1; have := abs_le.mp hR2; linarith
    linarith

end DPCB3

namespace DPCB3

open ReusablePricing.DPCB General DPCBTower

variable (P : General) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ) (β : Fin P.K → ℕ → ℕ)
  (B : Fin P.K → ℕ)

lemma E_const (c : ℝ) : ∑ ω, P.pathProb nl m ε β ω * c = c := by
  rw [← Finset.sum_mul, mass_P, one_mul]

lemma E_cmul (c : ℝ) (X : P.Path → ℝ) :
    ∑ ω, P.pathProb nl m ε β ω * (c * X ω) = c * ∑ ω, P.pathProb nl m ε β ω * X ω := by
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun ω _ => by ring)

/-- `E[(η^t_δ)_k^2] ≤ 1/m_k`, from the batch second-moment bound. -/
lemma E_eta_sq (hP : P.ModelFacts) (hbat : P.BatchesValid m β B) (hm : ∀ k, 1 ≤ m k)
    (t : ℕ) (ht : t ∈ Icc 1 P.T) (k : Fin P.K) :
    ∑ ω, P.pathProb nl m ε β ω * (P.etaDelta nl m ε β t ω k) ^ 2 ≤ 1 / (m k : ℝ) := by
  have hmr : (1:ℝ) ≤ m k := by exact_mod_cast hm k
  set b' := β k t - 1
  have hS : ∑ ω, P.pathProb nl m ε β ω * (∑ s ∈ P.batch β k b', P.err nl m ε β s ω k) ^ 2
      ≤ (m k : ℝ) := by
    rcases Nat.eq_zero_or_pos b' with h0 | hpos
    · rw [h0, batch_zero_empty P m β B hbat k]; simp
    · have hb' : b' ∈ Icc 1 (B k) := by
        rw [Finset.mem_Icc] at ht ⊢
        have h2 := beta_le_B P m β B hbat k t ht.1 ht.2
        omega
      exact batch_error_sq P nl m ε β B hP hbat k b' hb'
  have heq : ∀ ω, (P.etaDelta nl m ε β t ω k) ^ 2 =
      (1 / (m k : ℝ) ^ 2) * (∑ s ∈ P.batch β k b', P.err nl m ε β s ω k) ^ 2 := by
    intro ω
    simp only [General.etaDelta]
    rw [prevErr_eq P nl m ε β B hbat t ht ω k]
    field_simp
    rfl
  simp_rw [heq, E_cmul]
  calc 1 / (m k : ℝ) ^ 2 * ∑ ω, P.pathProb nl m ε β ω *
        (∑ s ∈ P.batch β k b', P.err nl m ε β s ω k) ^ 2 ≤ 1 / (m k : ℝ) ^ 2 * (m k : ℝ) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 1 / (m k : ℝ) := by field_simp

end DPCB3

open ReusablePricing.DPCB General DPCBTower DPCB3 in
open Classical in
theorem solution :
    ∀ (K : ℕ) (Ψ R : ℝ), ∃ M₃ : ℝ, 0 < M₃ ∧
      ∀ (P : General) (φL φU : ℝ) (nl m : Fin P.K → ℕ) (ε : Fin P.K → ℝ)
        (β : Fin P.K → ℕ → ℕ) (B : Fin P.K → ℕ),
        P.K = K →
        P.Standing R Ψ φL φU nl →
        P.BatchesValid m β B →
        (∀ k, 1 ≤ m k ∧ m k ≤ nl k) →
        (∀ k, 1 < ε k ∧
          ε k ≤ min ((nl k : ℝ) * min 1 ((1 + 4 * (m k : ℝ) * min φL φU) / (4 * (m k : ℝ) + (nl k : ℝ))))
                    (1 + 16 * min P.maxC (m k : ℝ))) →
        P.lossB nl m ε β ≤
          M₃ * ∑ k, (ε k / (nl k : ℝ) + 1 / (m k : ℝ) +
            (P.T : ℝ) / (m k : ℝ) *
              Real.exp (-(P.epsMin ε - 1) ^ 2 / (256 * (K : ℝ) ^ 2 * min P.maxC (m k : ℝ)))) := by
  intro K Ψ R
  refine ⟨1 + 3 * |Ψ| + 4 * (2 * |R| + |Ψ| * K), by positivity, ?_⟩
  intro P φL φU nl m ε β B hK hst hbat hm hε
  subst hK
  have hP := hst.facts
  obtain ⟨hφL, hφU, hΨ, -, hA5⟩ := hst.a5
  set μ := P.pathProb nl m ε β
  set D0 : ℝ := 2 * R + Ψ * (P.K : ℝ)
  set pG : ℝ := P.prob nl m ε β (fun ω => ¬ P.inG nl m ε β B (P.delta nl ε β) ω)
  set a : Fin P.K → ℝ := fun k => ε k / (nl k : ℝ)
  set C1 : ℝ := ∑ k, (Ψ * a k + 2 * Ψ * a k ^ 2 + 2 * Ψ * (1 / (m k : ℝ)))
  have hT : 1 ≤ P.T := hP.one_le_T
  have hTr : (0:ℝ) < P.T := by exact_mod_cast hT
  have hKr : (1:ℝ) ≤ P.K := by exact_mod_cast hP.one_le_K
  have hμ0 : ∀ ω, 0 ≤ μ ω := pathProb_nonneg P nl m ε β hP
  -- R ≥ 0
  have hR0 : 0 ≤ R := by
    have h0 : (fun _ => (0:ℝ)) ∈ P.Omega := fun k => ⟨le_rfl, le_of_lt hP.lamU_pos⟩
    exact le_trans (abs_nonneg _) ((hst.a4 1 (Finset.mem_Icc.mpr ⟨le_rfl, hT⟩)).2.1 _ h0)
  have hD0 : 0 ≤ D0 := by positivity
  -- per-period bound
  have hper : ∀ t ∈ Icc 1 P.T,
      ∑ ω, μ ω * (P.r t (P.lamD t) - P.r t (P.rate nl m ε β t ω)) ≤ C1 + D0 * pG := by
    intro t ht
    have hpt := fun ω (hω : 0 < μ ω) => path_bound P nl m ε β B R Ψ φL φU hst hbat hm hε t ht ω hω
    have hle : ∑ ω, μ ω * (P.r t (P.lamD t) - P.r t (P.rate nl m ε β t ω)) ≤
        ∑ ω, μ ω * ((∑ k, Ψ * (ε k / (nl k : ℝ)) + 2 * Ψ * ∑ k, (ε k / (nl k : ℝ)) ^ 2)
          + ∑ k, fderiv ℝ (P.r t) (P.lamD t) (Pi.single k 1) *
              (P.etaDelta nl m ε β t ω k * P.etaE t k)
          + 2 * Ψ * ∑ k, (P.etaDelta nl m ε β t ω k) ^ 2
          + (if P.inG nl m ε β B (P.delta nl ε β) ω then 0 else 1) * D0) := by
      refine Finset.sum_le_sum (fun ω _ => ?_)
      rcases (hμ0 ω).lt_or_eq with hpos | hz
      · exact mul_le_mul_of_nonneg_left (by have := hpt ω hpos; linarith) (hμ0 ω)
      · rw [← hz]; simp
    have heqE : ∑ ω, μ ω * ((∑ k, Ψ * (ε k / (nl k : ℝ)) + 2 * Ψ * ∑ k, (ε k / (nl k : ℝ)) ^ 2)
          + ∑ k, fderiv ℝ (P.r t) (P.lamD t) (Pi.single k 1) *
              (P.etaDelta nl m ε β t ω k * P.etaE t k)
          + 2 * Ψ * ∑ k, (P.etaDelta nl m ε β t ω k) ^ 2
          + (if P.inG nl m ε β B (P.delta nl ε β) ω then 0 else 1) * D0)
        = (∑ k, Ψ * (ε k / (nl k : ℝ)) + 2 * Ψ * ∑ k, (ε k / (nl k : ℝ)) ^ 2) + 0
          + 2 * Ψ * ∑ k, ∑ ω, μ ω * (P.etaDelta nl m ε β t ω k) ^ 2 + D0 * pG := by
      have hc1 : ∑ ω, μ ω * ∑ k, Ψ * (ε k / (nl k : ℝ)) = ∑ k, Ψ * (ε k / (nl k : ℝ)) :=
        E_const P nl m ε β _
      have hc1' : ∑ ω, μ ω * (2 * Ψ * ∑ k, (ε k / (nl k : ℝ)) ^ 2)
          = 2 * Ψ * ∑ k, (ε k / (nl k : ℝ)) ^ 2 := E_const P nl m ε β _
      have hA := grad_correction_mean_zero P nl m ε β hP t ht
      unfold General.expect at hA
      have hc3 : ∑ ω, μ ω * (2 * Ψ * ∑ k, (P.etaDelta nl m ε β t ω k) ^ 2)
          = 2 * Ψ * ∑ k, ∑ ω, μ ω * (P.etaDelta nl m ε β t ω k) ^ 2 := by
        rw [E_cmul P nl m ε β (2 * Ψ) (fun ω => ∑ k, (P.etaDelta nl m ε β t ω k) ^ 2)]
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
      have hc4 : ∑ ω, μ ω * ((if P.inG nl m ε β B (P.delta nl ε β) ω then 0 else 1) * D0)
          = D0 * pG := by
        simp only [pG]
        unfold General.prob General.expect
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ω _ => ?_)
        by_cases hG : P.inG nl m ε β B (P.delta nl ε β) ω <;> simp [hG] <;> ring
      simp only [mul_add, Finset.sum_add_distrib]
      rw [hc1, hc1', hA, hc3, hc4]
    rw [heqE] at hle
    have hη : ∑ k, ∑ ω, μ ω * (P.etaDelta nl m ε β t ω k) ^ 2 ≤ ∑ k, 1 / (m k : ℝ) :=
      Finset.sum_le_sum (fun k _ => E_eta_sq P nl m ε β B hP hbat (fun k => (hm k).1) t ht k)
    have hC1 : C1 = ∑ k, Ψ * a k + 2 * Ψ * ∑ k, a k ^ 2 + 2 * Ψ * ∑ k, 1 / (m k : ℝ) := by
      simp only [C1, Finset.sum_add_distrib, Finset.mul_sum]
    rw [hC1]
    have := mul_le_mul_of_nonneg_left hη (by linarith : (0:ℝ) ≤ 2 * Ψ)
    simp only [a] at *
    linarith
  -- the loss
  have hloss : P.lossB nl m ε β ≤ C1 + D0 * pG := by
    have hdiff : P.JD - P.expect nl m ε β (fun ω => ∑ t ∈ Icc 1 P.T, P.r t (P.rate nl m ε β t ω))
        = ∑ t ∈ Icc 1 P.T, ∑ ω, μ ω * (P.r t (P.lamD t) - P.r t (P.rate nl m ε β t ω)) := by
      unfold General.JD General.detValue General.expect
      have e1 : ∀ t ∈ Icc 1 P.T, ∑ ω, μ ω * (P.r t (P.lamD t) - P.r t (P.rate nl m ε β t ω))
          = P.r t (P.lamD t) - ∑ ω, μ ω * P.r t (P.rate nl m ε β t ω) := by
        intro t _
        simp only [mul_sub, Finset.sum_sub_distrib]
        rw [E_const]
      rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl (fun ω _ => ?_)
      rw [Finset.mul_sum]
    unfold General.lossB
    rw [hdiff, div_le_iff₀ hTr]
    calc ∑ t ∈ Icc 1 P.T, ∑ ω, μ ω * (P.r t (P.lamD t) - P.r t (P.rate nl m ε β t ω))
        ≤ ∑ t ∈ Icc 1 P.T, (C1 + D0 * pG) := Finset.sum_le_sum hper
      _ = (C1 + D0 * pG) * P.T := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring_nf
  -- the bad-event probability
  have hmaxC : (1:ℝ) ≤ P.maxC := by
    unfold General.maxC
    have h1 : P.C ⟨0, by have := hP.one_le_I; omega⟩ ≤ Finset.univ.sup P.C :=
      Finset.le_sup (Finset.mem_univ _)
    have h2 := hP.one_le_C ⟨0, by have := hP.one_le_I; omega⟩
    exact_mod_cast le_trans h2 h1
  have he1 := one_lt_epsMin P ε hP.one_le_K (fun k => (hε k).1)
  have hmn : ∀ k, (1:ℝ) ≤ min P.maxC (m k : ℝ) := fun k =>
    le_min hmaxC (by exact_mod_cast (hm k).1)
  set γ : Fin P.K → ℝ := fun k => (P.epsMin ε - 1) / (16 * (P.K : ℝ) * min P.maxC (m k : ℝ))
  have hγ : ∀ k, 0 < γ k ∧ γ k ≤ 1 := by
    intro k
    have h1 := hmn k
    refine ⟨div_pos (by linarith) (by positivity), ?_⟩
    rw [div_le_one (by positivity)]
    have h2 := epsMin_le P ε hP.one_le_K k
    have h3 := le_trans (hε k).2 (min_le_right _ _)
    nlinarith
  have hEC4 := lemma_EC4 P R Ψ φL φU nl m ε β B hst hbat hm hε γ hγ
  set X : Fin P.K → ℝ := fun k =>
    Real.exp (-(P.epsMin ε - 1) ^ 2 / (256 * (P.K : ℝ) ^ 2 * min P.maxC (m k : ℝ)))
  have hexp : ∀ k, min P.maxC (m k : ℝ) * γ k ^ 2 - (P.epsMin ε - 1) / (8 * (P.K : ℝ)) * γ k
      = -(P.epsMin ε - 1) ^ 2 / (256 * (P.K : ℝ) ^ 2 * min P.maxC (m k : ℝ)) := by
    intro k
    have h1 := hmn k
    simp only [γ]
    field_simp
    ring
  simp_rw [hexp] at hEC4
  -- final assembly
  have hmr : ∀ k, (1:ℝ) ≤ m k := fun k => by exact_mod_cast (hm k).1
  have hnl : ∀ k, (1:ℝ) ≤ nl k := fun k => by exact_mod_cast le_trans (hm k).1 (hm k).2
  have ha : ∀ k, 0 ≤ a k ∧ a k ≤ 1 := by
    intro k
    have h1 := hε k
    have h2 : ε k ≤ nl k := le_trans (le_trans h1.2 (min_le_left _ _))
      (by have := min_le_left (1:ℝ) ((1 + 4 * (m k : ℝ) * min φL φU) / (4 * (m k : ℝ) + (nl k : ℝ)))
          nlinarith [hnl k])
    refine ⟨div_nonneg (by linarith) (by linarith [hnl k]), ?_⟩
    rw [div_le_one (by linarith [hnl k])]; exact h2
  set M₃ := 1 + 3 * |Ψ| + 4 * (2 * |R| + |Ψ| * (P.K : ℝ))
  have hM1 : 3 * Ψ ≤ M₃ := by
    have := le_abs_self Ψ; have := abs_nonneg R; have : 0 ≤ |Ψ| * (P.K : ℝ) := by positivity
    simp only [M₃]; linarith
  have hM3 : 4 * D0 ≤ M₃ := by
    have := le_abs_self Ψ; have := le_abs_self R
    have : Ψ * (P.K : ℝ) ≤ |Ψ| * P.K := mul_le_mul_of_nonneg_right (le_abs_self Ψ) (by linarith)
    simp only [M₃, D0]; linarith [abs_nonneg Ψ]
  calc P.lossB nl m ε β ≤ C1 + D0 * pG := hloss
    _ ≤ C1 + D0 * ∑ k, 4 * (P.T : ℝ) / (m k : ℝ) * X k :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hEC4 hD0)
    _ = ∑ k, (Ψ * a k + 2 * Ψ * a k ^ 2 + 2 * Ψ * (1 / (m k : ℝ))
          + 4 * D0 * ((P.T : ℝ) / (m k : ℝ) * X k)) := by
        simp only [C1, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => by ring)
    _ ≤ ∑ k, M₃ * (a k + 1 / (m k : ℝ) + (P.T : ℝ) / (m k : ℝ) * X k) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have hu : 0 ≤ 1 / (m k : ℝ) := by have := hmr k; positivity
        have hY : 0 ≤ (P.T : ℝ) / (m k : ℝ) * X k := by
          have := hmr k; have := Real.exp_pos (-(P.epsMin ε - 1) ^ 2 /
            (256 * (P.K : ℝ) ^ 2 * min P.maxC (m k : ℝ))); positivity
        obtain ⟨ha0, ha1⟩ := ha k
        have hsq : a k ^ 2 ≤ a k := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.2 hM1) ha0, mul_nonneg (sub_nonneg.2 hM3) hY,
          mul_le_mul_of_nonneg_left hsq hΨ.le, mul_nonneg (by linarith : (0:ℝ) ≤ M₃ - 2 * Ψ) hu]
    _ = M₃ * ∑ k, (ε k / (nl k : ℝ) + 1 / (m k : ℝ) + (P.T : ℝ) / (m k : ℝ) *
          Real.exp (-(P.epsMin ε - 1) ^ 2 / (256 * (P.K : ℝ) ^ 2 * min P.maxC (m k : ℝ)))) := by
        rw [Finset.mul_sum]

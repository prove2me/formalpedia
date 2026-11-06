-- Prove2me | solution 1 for StochasticRewardMatching.Decomposable.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T08:28:21.145847+00:00
-- url     : https://prove2.me/submissions/1d1bb944-07e9-478e-a4d2-de9f9bf134ca

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Algorithm
import Definitions.Def_StochasticRewardMatching_Decomposable_Benchmarks
import Definitions.Def_StochasticRewardMatching_Decomposable_OnlinePolicies

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory
noncomputable section

namespace StochasticRewardMatching.Decomposable
namespace WD

variable {n m : ℕ} (D : Instance n m)

/-! ### Expectation over outcomes -/

lemma E_def (f : Outcome D → ℝ) :
    edgeAverage D f = ∑ ω : Outcome D, pathWeight D ω * f ω := rfl

lemma pathWeight_nonneg (ω : Outcome D) : 0 ≤ pathWeight D ω := by
  unfold pathWeight
  apply Finset.prod_nonneg
  intro e _
  have h := D.probability_mem e.val e.2
  split_ifs <;> linarith [h.1, h.2]

lemma E_add (f g : Outcome D → ℝ) :
    edgeAverage D (fun ω => f ω + g ω) = edgeAverage D f + edgeAverage D g := by
  simp only [E_def, mul_add, Finset.sum_add_distrib]

lemma E_const_mul (c : ℝ) (f : Outcome D → ℝ) :
    edgeAverage D (fun ω => c * f ω) = c * edgeAverage D f := by
  simp only [E_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma E_mono (f g : Outcome D → ℝ) (hfg : ∀ ω, f ω ≤ g ω) :
    edgeAverage D f ≤ edgeAverage D g := by
  simp only [E_def]
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (pathWeight_nonneg D ω)

lemma E_mono_pos (f g : Outcome D → ℝ) (hfg : ∀ ω, pathWeight D ω ≠ 0 → f ω ≤ g ω) :
    edgeAverage D f ≤ edgeAverage D g := by
  simp only [E_def]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hw : pathWeight D ω = 0
  · simp [hw]
  · exact mul_le_mul_of_nonneg_left (hfg ω hw) (pathWeight_nonneg D ω)

/-- An outcome of positive weight never succeeds on a probability-zero edge. -/
lemma possible_of_weight (ω : Outcome D) (hw : pathWeight D ω ≠ 0) :
    ∀ f : Edge D, D.probability f.val = 0 → ω f = false := by
  intro f hf
  by_contra hc
  apply hw
  unfold pathWeight
  apply Finset.prod_eq_zero (Finset.mem_univ f)
  simp [Bool.not_eq_false] at hc
  simp [hc, hf]

lemma E_zero : edgeAverage D (fun _ => (0:ℝ)) = 0 := by simp [E_def]

lemma E_one : edgeAverage D (fun _ => (1:ℝ)) = 1 := by
  simp only [E_def, mul_one, pathWeight]
  rw [← Fintype.prod_sum (fun (e : Edge D) (b : Bool) =>
    if b then D.probability e.val else 1 - D.probability e.val)]
  apply Finset.prod_eq_one
  intro e _
  simp

lemma E_sum_mul {ι : Type*} [Fintype ι] (φ : Outcome D → ℝ) (c : ι → ℝ)
    (F : ι → Outcome D → ℝ) :
    edgeAverage D (fun ω => φ ω * ∑ a, c a * F a ω) =
      ∑ a, c a * edgeAverage D (fun ω => φ ω * F a ω) := by
  simp only [E_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-! ### Resampling one edge preserves the expectation -/

def wE (e : Edge D) (b : Bool) : ℝ := if b then D.probability e.val else 1 - D.probability e.val

def Rest (e : Edge D) (ω : Outcome D) : ℝ := ∏ e' ∈ Finset.univ.erase e, wE D e' (ω e')

lemma pathWeight_split (e : Edge D) (ω : Outcome D) :
    pathWeight D ω = wE D e (ω e) * Rest D e ω := by
  unfold pathWeight Rest
  rw [Finset.mul_prod_erase Finset.univ (fun e' => wE D e' (ω e')) (Finset.mem_univ e)]
  rfl

lemma Rest_update (e : Edge D) (ω : Outcome D) (b : Bool) :
    Rest D e (Function.update ω e b) = Rest D e ω := by
  unfold Rest
  apply Finset.prod_congr rfl
  intro e' he'
  rw [Function.update_of_ne (Finset.ne_of_mem_erase he')]

lemma sum_pair (e : Edge D) (H : Outcome D → ℝ) :
    2 * ∑ ω, H ω = ∑ ω, (H (Function.update ω e true) + H (Function.update ω e false)) := by
  let σ : Outcome D → Outcome D := fun ω => Function.update ω e (!ω e)
  have hσ : Function.Involutive σ := by
    intro ω
    simp [σ]
  have h1 : ∑ ω, H (σ ω) = ∑ ω, H ω := Equiv.sum_comp hσ.toPerm H
  have h2 : ∀ ω, H ω + H (σ ω) =
      H (Function.update ω e true) + H (Function.update ω e false) := by
    intro ω
    cases hb : ω e
    · have : Function.update ω e false = ω := by
        rw [← hb]; exact Function.update_eq_self e ω
      simp [σ, hb, this, add_comm]
    · have : Function.update ω e true = ω := by
        rw [← hb]; exact Function.update_eq_self e ω
      simp [σ, hb, this]
  rw [two_mul]
  nth_rewrite 2 [← h1]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun ω _ => h2 ω)

lemma two_E (e : Edge D) (g : Outcome D → ℝ) :
    2 * edgeAverage D g = ∑ ω, Rest D e ω *
      ((1 - D.probability e.val) * g (Function.update ω e false) +
        D.probability e.val * g (Function.update ω e true)) := by
  rw [E_def, sum_pair D e]
  apply Finset.sum_congr rfl
  intro ω _
  rw [pathWeight_split D e, pathWeight_split D e, Rest_update, Rest_update]
  simp [wE]
  ring

lemma E_resample (e : Edge D) (f : Outcome D → ℝ) :
    edgeAverage D (fun ω => resample D e ω f) = edgeAverage D f := by
  have : (2:ℝ) * edgeAverage D (fun ω => resample D e ω f) = 2 * edgeAverage D f := by
    rw [two_E D e, two_E D e]
    apply Finset.sum_congr rfl
    intro ω _
    simp only [resample, Function.update_idem]
    ring
  linarith

lemma E_indicator (e : Edge D) (φ : Outcome D → ℝ)
    (hφ : ∀ ω b, φ (Function.update ω e b) = φ ω) :
    edgeAverage D (fun ω => φ ω * indicator ω e) =
      D.probability e.val * edgeAverage D φ := by
  rw [← E_resample D e, ← E_const_mul]
  congr 1
  funext ω
  simp [resample, indicator, hφ]

lemma resample_mul_inv (e : Edge D) (φ g : Outcome D → ℝ)
    (hφ : ∀ ω b, φ (Function.update ω e b) = φ ω) (ω : Outcome D) :
    resample D e ω (fun ω' => φ ω' * g ω') = φ ω * resample D e ω g := by
  simp only [resample, hφ]
  ring


/-! ### Histories -/

lemma RA_append (h : History n m) (z : Action n m × Bool) :
    remainingArrivals (h ++ [z]) = (remainingArrivals h).erase z.1.1 := by
  ext t
  simp only [remainingArrivals, List.map_append, List.toFinset_append, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_erase, List.map_cons, List.map_nil,
    List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false]
  tauto

lemma RS_append_false (h : History n m) (a : Action n m) :
    remainingResources (h ++ [(a, false)]) = remainingResources h := by
  simp [remainingResources]

lemma RS_append_true_some (h : History n m) (t : Fin m) (i : Fin n) :
    remainingResources (h ++ [((t, some i), true)]) = (remainingResources h).erase i := by
  ext x
  simp [remainingResources]

lemma RS_append_sub (h : History n m) (z : Action n m × Bool) :
    remainingResources (h ++ [z]) ⊆ remainingResources h := by
  intro x
  simp [remainingResources]
  tauto

variable (ordered : Bool) (π : RandPolicy n m)

def cstep (c : History n m → ℝ) (h : History n m) (a : Option (Action n m)) : ℝ := by
  classical
  exact match a with
  | none => 0
  | some a => if a ∈ legalActions D ordered (remainingResources h) (remainingArrivals h) then
      actionProbability D a * (actionReward D a + c (h ++ [(a, true)])) +
      (1 - actionProbability D a) * c (h ++ [(a, false)])
    else 0

lemma cont_succ (k : ℕ) (h : History n m) :
    randomizedContinuation D ordered π (k+1) h =
      ∑ a, (π h a).toReal * cstep D ordered (randomizedContinuation D ordered π k) h a := rfl

variable (lam : Outcome D → Fin m → ℝ) (θ : Outcome D → Fin n → ℝ)

def bitR (ω : Outcome D) (a : Action n m) : ℝ := if actionBit D ω a then 1 else 0

def gain (ω : Outcome D) (a : Action n m) : ℝ :=
  match a.2 with
  | none => 0
  | some i => lam ω a.1 + θ ω i * bitR D ω a

def gstep (F : History n m → Outcome D → ℝ) (h : History n m) (ω : Outcome D)
    (a : Option (Action n m)) : ℝ := by
  classical
  exact match a with
  | none => 0
  | some a => if a ∈ legalActions D ordered (remainingResources h) (remainingArrivals h) then
      gain D lam θ ω a + bitR D ω a * F (h ++ [(a, true)]) ω +
        (1 - bitR D ω a) * F (h ++ [(a, false)]) ω
    else 0

def G : ℕ → History n m → Outcome D → ℝ
  | 0, _, _ => 0
  | k + 1, h, ω => ∑ a, (π h a).toReal * gstep D ordered lam θ (G k) h ω a

def Inv (h : History n m) (φ : Outcome D → ℝ) : Prop :=
  ∀ e : Edge D, e.val.2 ∈ remainingArrivals h → ∀ (ω : Outcome D) (b : Bool),
    φ (Function.update ω e b) = φ ω

lemma Inv_append {h : History n m} {φ : Outcome D → ℝ} (hφ : Inv D h φ) (z : Action n m × Bool) :
    Inv D (h ++ [z]) φ := by
  intro e he
  rw [RA_append] at he
  exact hφ e (Finset.mem_of_mem_erase he)

lemma actionBit_update (a : Action n m) (e : Edge D) (he : e.val.2 ≠ a.1) (ω : Outcome D)
    (b : Bool) : actionBit D (Function.update ω e b) a = actionBit D ω a := by
  rcases a with ⟨t, _ | i⟩
  · rfl
  · simp only [actionBit, bit]
    split_ifs with hm
    · rw [Function.update_of_ne]
      rintro rfl
      exact he rfl
    · rfl

lemma bitR_update (a : Action n m) (e : Edge D) (he : e.val.2 ≠ a.1) (ω : Outcome D)
    (b : Bool) : bitR D (Function.update ω e b) a = bitR D ω a := by
  unfold bitR
  rw [actionBit_update D a e he]

lemma Inv_mul_bitR {h : History n m} {φ : Outcome D → ℝ} (hφ : Inv D h φ) (a : Action n m)
    (b : Bool) : Inv D (h ++ [(a, b)]) (fun ω => φ ω * bitR D ω a) := by
  intro e he ω b'
  rw [RA_append] at he
  simp only [bitR_update D a e (Finset.ne_of_mem_erase he), hφ e (Finset.mem_of_mem_erase he)]

lemma Inv_mul_one_sub_bitR {h : History n m} {φ : Outcome D → ℝ} (hφ : Inv D h φ)
    (a : Action n m) (b : Bool) :
    Inv D (h ++ [(a, b)]) (fun ω => φ ω * (1 - bitR D ω a)) := by
  intro e he ω b'
  rw [RA_append] at he
  simp only [bitR_update D a e (Finset.ne_of_mem_erase he), hφ e (Finset.mem_of_mem_erase he)]

lemma bitR_nonneg (ω : Outcome D) (a : Action n m) : 0 ≤ bitR D ω a := by
  unfold bitR; split_ifs <;> norm_num

lemma bitR_le_one (ω : Outcome D) (a : Action n m) : bitR D ω a ≤ 1 := by
  unfold bitR; split_ifs <;> norm_num

set_option maxHeartbeats 1000000 in
theorem key (α : ℝ)
    (hyp : ∀ (e : Edge D) (ω : Outcome D),
        (∀ f : Edge D, D.probability f.val = 0 → ω f = false) →
        α * D.probability e.val * D.reward e.val.1 ≤
          resample D e ω (fun ω' => lam ω' e.val.2 + θ ω' e.val.1 * indicator ω' e)) :
    ∀ (k : ℕ) (h : History n m) (φ : Outcome D → ℝ), (∀ ω, 0 ≤ φ ω) → Inv D h φ →
      α * randomizedContinuation D ordered π k h * edgeAverage D φ ≤
        edgeAverage D (fun ω => φ ω * G D ordered π lam θ k h ω) := by
  intro k
  induction k with
  | zero =>
    intro h φ _ _
    simp [randomizedContinuation, G, E_zero]
  | succ k ih =>
    intro h φ hφ0 hφ
    have hsplit : edgeAverage D (fun ω => φ ω * G D ordered π lam θ (k+1) h ω) =
        ∑ a, (π h a).toReal * edgeAverage D
          (fun ω => φ ω * gstep D ordered lam θ (G D ordered π lam θ k) h ω a) :=
      E_sum_mul D φ (fun a => (π h a).toReal)
        (fun a ω => gstep D ordered lam θ (G D ordered π lam θ k) h ω a)
    rw [hsplit, cont_succ, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    rw [show α * ((π h a).toReal * cstep D ordered (randomizedContinuation D ordered π k) h a) *
        edgeAverage D φ = (π h a).toReal *
          (α * cstep D ordered (randomizedContinuation D ordered π k) h a * edgeAverage D φ) by ring]
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    rcases a with _ | a
    · simp [cstep, gstep, E_zero]
    by_cases hl : a ∈ legalActions D ordered (remainingResources h) (remainingArrivals h)
    swap
    · simp [cstep, gstep, hl, E_zero]
    have hc : cstep D ordered (randomizedContinuation D ordered π k) h (some a) =
        actionProbability D a * (actionReward D a +
          randomizedContinuation D ordered π k (h ++ [(a, true)])) +
        (1 - actionProbability D a) * randomizedContinuation D ordered π k (h ++ [(a, false)]) := by
      simp [cstep, hl]
    have hg : ∀ ω, gstep D ordered lam θ (G D ordered π lam θ k) h ω (some a) =
        gain D lam θ ω a + bitR D ω a * G D ordered π lam θ k (h ++ [(a, true)]) ω +
        (1 - bitR D ω a) * G D ordered π lam θ k (h ++ [(a, false)]) ω := by
      intro ω; simp [gstep, hl]
    simp only [hc, hg]
    have hl' := hl
    simp only [legalActions, Finset.mem_filter, Finset.mem_univ, true_and] at hl'
    rcases a with ⟨t, _ | i⟩
    · -- a skip action
      have hb : ∀ ω, bitR D ω (t, none) = 0 := fun ω => by simp [bitR, actionBit]
      have h0 : ∀ ω, gain D lam θ ω (t, none) = 0 := fun ω => rfl
      simp only [hb, h0, actionProbability, actionReward, zero_mul, zero_add, sub_zero, one_mul]
      exact ih _ φ hφ0 (Inv_append D hφ _)
    · obtain ⟨ht, -, -, he⟩ := hl'
      set e : Edge D := ⟨(i, t), he⟩ with he_def
      have hφe : ∀ ω b, φ (Function.update ω e b) = φ ω := hφ e ht
      have hbit : ∀ ω, bitR D ω (t, some i) = indicator ω e := by
        intro ω; simp [bitR, actionBit, bit, he, indicator, e]
      have hgain : ∀ ω, gain D lam θ ω (t, some i) =
          lam ω e.val.2 + θ ω e.val.1 * indicator ω e := by
        intro ω; rw [← hbit]; rfl
      have hp : actionProbability D (t, some i) = D.probability e.val := rfl
      have hr : actionReward D (t, some i) = D.reward e.val.1 := rfl
      rw [hp, hr]
      set p := D.probability e.val
      set r := D.reward e.val.1
      set c1 := randomizedContinuation D ordered π k (h ++ [((t, some i), true)])
      set c0 := randomizedContinuation D ordered π k (h ++ [((t, some i), false)])
      have hsum : edgeAverage D (fun ω => φ ω * (gain D lam θ ω (t, some i) +
            bitR D ω (t, some i) * G D ordered π lam θ k (h ++ [((t, some i), true)]) ω +
            (1 - bitR D ω (t, some i)) * G D ordered π lam θ k (h ++ [((t, some i), false)]) ω)) =
          edgeAverage D (fun ω => φ ω * gain D lam θ ω (t, some i)) +
          edgeAverage D (fun ω => (φ ω * bitR D ω (t, some i)) *
            G D ordered π lam θ k (h ++ [((t, some i), true)]) ω) +
          edgeAverage D (fun ω => (φ ω * (1 - bitR D ω (t, some i))) *
            G D ordered π lam θ k (h ++ [((t, some i), false)]) ω) := by
        rw [← E_add, ← E_add]
        congr 1
        funext ω
        ring
      rw [hsum]
      -- F1 : the reward term
      have F1 : α * p * r * edgeAverage D φ ≤
          edgeAverage D (fun ω => φ ω * gain D lam θ ω (t, some i)) := by
        simp only [hgain]
        rw [← E_resample D e (fun ω => φ ω * _)]
        simp only [resample_mul_inv D e φ _ hφe]
        rw [← E_const_mul]
        apply E_mono_pos
        intro ω hw
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (hyp e ω (possible_of_weight D ω hw)) (hφ0 ω)
      have Eb : edgeAverage D (fun ω => φ ω * bitR D ω (t, some i)) = p * edgeAverage D φ := by
        simp only [hbit]
        exact E_indicator D e φ hφe
      have Enb : edgeAverage D (fun ω => φ ω * (1 - bitR D ω (t, some i))) =
          edgeAverage D φ - p * edgeAverage D φ := by
        rw [← Eb, show (fun ω => φ ω * (1 - bitR D ω (t, some i))) =
          fun ω => φ ω + (-1) * (φ ω * bitR D ω (t, some i)) by funext ω; ring, E_add, E_const_mul]
        ring
      have F2 := ih (h ++ [((t, some i), true)]) (fun ω => φ ω * bitR D ω (t, some i))
        (fun ω => mul_nonneg (hφ0 ω) (bitR_nonneg D ω _)) (Inv_mul_bitR D hφ _ _)
      have F3 := ih (h ++ [((t, some i), false)]) (fun ω => φ ω * (1 - bitR D ω (t, some i)))
        (fun ω => mul_nonneg (hφ0 ω) (by linarith [bitR_le_one D ω (t, some i)]))
        (Inv_mul_one_sub_bitR D hφ _ _)
      rw [Eb] at F2
      rw [Enb] at F3
      nlinarith [F1, F2, F3]

def Phi (h : History n m) (ω : Outcome D) : ℝ :=
  ∑ t ∈ remainingArrivals h, lam ω t + ∑ i ∈ remainingResources h, θ ω i

lemma Phi_nonneg (hlam : ∀ ω t, 0 ≤ lam ω t) (hθ : ∀ ω i, 0 ≤ θ ω i)
    (h : History n m) (ω : Outcome D) : 0 ≤ Phi D lam θ h ω :=
  add_nonneg (Finset.sum_nonneg fun t _ => hlam ω t) (Finset.sum_nonneg fun i _ => hθ ω i)

lemma Phi_append_le (hlam : ∀ ω t, 0 ≤ lam ω t) (hθ : ∀ ω i, 0 ≤ θ ω i)
    (h : History n m) (z : Action n m × Bool) (ω : Outcome D) :
    Phi D lam θ (h ++ [z]) ω ≤ Phi D lam θ h ω := by
  unfold Phi
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · rw [RA_append]; exact Finset.erase_subset _ _
    · intro t _ _; exact hlam ω t
  · apply Finset.sum_le_sum_of_subset_of_nonneg (RS_append_sub h z)
    intro i _ _; exact hθ ω i

lemma pmf_sum {α : Type*} [Fintype α] (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  have h1 := PMF.tsum_coe p
  rw [tsum_fintype] at h1
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a), h1]
  simp

theorem bound (hlam : ∀ ω t, 0 ≤ lam ω t) (hθ : ∀ ω i, 0 ≤ θ ω i) :
    ∀ (k : ℕ) (h : History n m) (ω : Outcome D), G D ordered π lam θ k h ω ≤ Phi D lam θ h ω := by
  intro k
  induction k with
  | zero => intro h ω; exact Phi_nonneg D lam θ hlam hθ h ω
  | succ k ih =>
    intro h ω
    show ∑ a, (π h a).toReal * gstep D ordered lam θ (G D ordered π lam θ k) h ω a ≤ _
    calc ∑ a, (π h a).toReal * gstep D ordered lam θ (G D ordered π lam θ k) h ω a
        ≤ ∑ a, (π h a).toReal * Phi D lam θ h ω := by
          apply Finset.sum_le_sum
          intro a _
          apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          rcases a with _ | a
          · simp only [gstep]; exact Phi_nonneg D lam θ hlam hθ h ω
          by_cases hl : a ∈ legalActions D ordered (remainingResources h) (remainingArrivals h)
          swap
          · simp only [gstep, hl, if_false]; exact Phi_nonneg D lam θ hlam hθ h ω
          have hg : gstep D ordered lam θ (G D ordered π lam θ k) h ω (some a) =
              gain D lam θ ω a + bitR D ω a * G D ordered π lam θ k (h ++ [(a, true)]) ω +
              (1 - bitR D ω a) * G D ordered π lam θ k (h ++ [(a, false)]) ω := by
            simp [gstep, hl]
          rw [hg]
          have hl' := hl
          simp only [legalActions, Finset.mem_filter, Finset.mem_univ, true_and] at hl'
          rcases a with ⟨t, _ | i⟩
          · have hb : bitR D ω (t, none) = 0 := by simp [bitR, actionBit]
            have h0 : gain D lam θ ω (t, none) = 0 := rfl
            rw [hb, h0]
            have := ih (h ++ [((t, none), false)]) ω
            have := Phi_append_le D lam θ hlam hθ h ((t, none), false) ω
            linarith
          · obtain ⟨ht, -, hi, he⟩ := hl'
            have e1 : Phi D lam θ (h ++ [((t, some i), true)]) ω + lam ω t + θ ω i =
                Phi D lam θ h ω := by
              simp only [Phi, RA_append, RS_append_true_some]
              rw [← Finset.add_sum_erase (remainingArrivals h) (lam ω) ht,
                ← Finset.add_sum_erase (remainingResources h) (θ ω) hi]
              ring
            have e0 : Phi D lam θ (h ++ [((t, some i), false)]) ω + lam ω t = Phi D lam θ h ω := by
              simp only [Phi, RA_append, RS_append_false]
              rw [← Finset.add_sum_erase (remainingArrivals h) (lam ω) ht]
              ring
            have g1 := ih (h ++ [((t, some i), true)]) ω
            have g0 := ih (h ++ [((t, some i), false)]) ω
            have hgain : gain D lam θ ω (t, some i) = lam ω t + θ ω i * bitR D ω (t, some i) := rfl
            rw [hgain]
            by_cases hb : actionBit D ω (t, some i) = true
            · have : bitR D ω (t, some i) = 1 := by simp [bitR, hb]
              rw [this]; linarith
            · have : bitR D ω (t, some i) = 0 := by simp [bitR, hb]
              rw [this]; linarith
      _ = Phi D lam θ h ω := by rw [← Finset.sum_mul, pmf_sum, one_mul]

end WD

theorem WD.weak_duality :
    ∀ (n m : ℕ) (D : Instance n m) (ordered : Bool) (α : ℝ),
    ∀ (lam : Outcome D → Fin m → ℝ) (θ : Outcome D → Fin n → ℝ),
      (∀ ω t, 0 ≤ lam ω t) → (∀ ω i, 0 ≤ θ ω i) →
      (∀ (e : Edge D) (ω : Outcome D),
          (∀ f : Edge D, D.probability f.val = 0 → ω f = false) →
          α * D.probability e.val * D.reward e.val.1 ≤
            resample D e ω (fun ω' => lam ω' e.val.2 + θ ω' e.val.1 * indicator ω' e)) →
      ∀ π : RandPolicy n m,
        α * randomizedValue D ordered π ≤ edgeAverage D (fun ω => ∑ t, lam ω t + ∑ i, θ ω i) := by
  intro n m D ordered α lam θ hlam hθ hyp π
  have hk := WD.key D ordered π lam θ α hyp m [] (fun _ => 1) (fun _ => zero_le_one)
    (by intro e _ ω b; rfl)
  rw [WD.E_one, mul_one] at hk
  unfold randomizedValue
  refine hk.trans (WD.E_mono D _ _ fun ω => ?_)
  rw [one_mul]
  have := WD.bound D ordered π lam θ hlam hθ m [] ω
  simpa [WD.Phi, remainingArrivals, remainingResources] using this


namespace Fit

/-! ### The preference order used by `bestOf` (max score, least index on ties) -/

def Pref {n : ℕ} (s : Fin n → ℝ) (x y : Fin n) : Prop := s y < s x ∨ (s y = s x ∧ x ≤ y)

lemma Pref_refl {n : ℕ} (s : Fin n → ℝ) (x : Fin n) : Pref s x x := Or.inr ⟨rfl, le_rfl⟩

lemma Pref_trans {n : ℕ} (s : Fin n → ℝ) {x y z : Fin n} (h1 : Pref s x y) (h2 : Pref s y z) :
    Pref s x z := by
  unfold Pref at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨by linarith, le_trans h1' h2'⟩

lemma Pref_antisymm {n : ℕ} (s : Fin n → ℝ) {x y : Fin n} (h1 : Pref s x y) (h2 : Pref s y x) :
    x = y := by
  unfold Pref at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · linarith
  · linarith
  · linarith
  · exact le_antisymm h1' h2'

lemma Pref_score_le {n : ℕ} (s : Fin n → ℝ) {x y : Fin n} (h : Pref s x y) : s y ≤ s x := by
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

lemma Pref_of_lt {n : ℕ} (s : Fin n → ℝ) {x y : Fin n} (h : s y < s x) : Pref s x y := Or.inl h

lemma Pref_mul {n : ℕ} (w : Fin n → ℝ) (c : ℝ) (hc : 0 < c) {x y : Fin n} :
    Pref (fun j => c * w j) x y ↔ Pref w x y := by
  unfold Pref
  constructor
  · rintro (h | ⟨h, h'⟩)
    · left; exact lt_of_mul_lt_mul_left h hc.le
    · right; exact ⟨mul_left_cancel₀ hc.ne' h, h'⟩
  · rintro (h | ⟨h, h'⟩)
    · left; exact mul_lt_mul_of_pos_left h hc
    · right; exact ⟨by simp only [h], h'⟩

lemma bestOf_eq_none {α : Type} (s : α → ℝ) : ∀ L : List α, bestOf s L = none ↔ L = []
  | [] => by simp [bestOf]
  | a :: rest => by
    simp only [bestOf, reduceCtorEq, iff_false]
    cases bestOf s rest with
    | none => simp
    | some b => simp only; split_ifs <;> simp

lemma bestOf_spec {n : ℕ} (s : Fin n → ℝ) : ∀ L : List (Fin n), L.Pairwise (· ≤ ·) →
    ∀ x, bestOf s L = some x → x ∈ L ∧ ∀ y ∈ L, Pref s x y
  | [] => by intro _ x hx; simp [bestOf] at hx
  | a :: rest => by
    intro hL x hx
    rw [List.pairwise_cons] at hL
    have ih := bestOf_spec s rest hL.2
    simp only [bestOf] at hx
    rcases hbr : bestOf s rest with _ | b
    · rw [hbr] at hx
      simp only [Option.some.injEq] at hx
      subst hx
      have : rest = [] := (bestOf_eq_none s rest).mp hbr
      subst this
      refine ⟨by simp, ?_⟩
      intro y hy
      simp at hy
      subst hy
      exact Pref_refl s _
    · rw [hbr] at hx
      obtain ⟨hb, hbp⟩ := ih b hbr
      simp only at hx
      split_ifs at hx with hle
      · simp only [Option.some.injEq] at hx
        subst hx
        refine ⟨by simp, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Pref_refl s _
        · have hay := hL.1 y hy
          rcases hbp y hy with h | ⟨h, _⟩
          · left; linarith
          · rcases lt_or_eq_of_le hle with h' | h'
            · left; linarith
            · right; exact ⟨by linarith, hay⟩
      · simp only [Option.some.injEq] at hx
        subst hx
        refine ⟨List.mem_cons_of_mem _ hb, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · left; exact not_le.mp hle
        · exact hbp y hy

/-! ### The algorithm's choice -/

variable {n m : ℕ} (D : Instance n m)

lemma choice_spec (Y : Seeds n) (S : Finset (Fin n)) (t : Fin m) (x : Fin n)
    (hx : algorithmChoice D Y S t = some x) :
    x ∈ S ∧ (x, t) ∈ D.edges ∧ ∀ y ∈ S, (y, t) ∈ D.edges → Pref (score D Y t) x y := by
  unfold algorithmChoice at hx
  obtain ⟨hmem, hp⟩ := bestOf_spec (score D Y t) _ (Finset.pairwise_sort _ _) x hx
  rw [Finset.mem_sort] at hmem
  simp only [neighbors, Finset.mem_filter] at hmem
  refine ⟨hmem.1, hmem.2, fun y hy hyt => hp y ?_⟩
  rw [Finset.mem_sort]
  simp only [neighbors, Finset.mem_filter]
  exact ⟨hy, hyt⟩

lemma choice_none (Y : Seeds n) (S : Finset (Fin n)) (t : Fin m)
    (h : algorithmChoice D Y S t = none) : ∀ y ∈ S, (y, t) ∉ D.edges := by
  unfold algorithmChoice at h
  rw [bestOf_eq_none] at h
  intro y hy hyt
  have : y ∈ (neighbors D S t).sort (· ≤ ·) := by
    rw [Finset.mem_sort]; simp only [neighbors, Finset.mem_filter]; exact ⟨hy, hyt⟩
  rw [h] at this
  simp at this

lemma choice_unique (Y : Seeds n) (S : Finset (Fin n)) (t : Fin m) (x : Fin n)
    (hxS : x ∈ S) (hxt : (x, t) ∈ D.edges)
    (hbest : ∀ y ∈ S, (y, t) ∈ D.edges → Pref (score D Y t) x y) :
    algorithmChoice D Y S t = some x := by
  rcases hc : algorithmChoice D Y S t with _ | z
  · exact absurd hxt (choice_none D Y S t hc x hxS)
  · obtain ⟨hzS, hzt, hz⟩ := choice_spec D Y S t z hc
    rw [Pref_antisymm _ (hz x hxS hxt) (hbest z hzS hzt)]

lemma choice_subset (Y : Seeds n) (S S' : Finset (Fin n)) (hS : S' ⊆ S) (t : Fin m) (x : Fin n)
    (hx : algorithmChoice D Y S t = some x) (hx' : x ∈ S') :
    algorithmChoice D Y S' t = some x := by
  obtain ⟨_, hxt, hb⟩ := choice_spec D Y S t x hx
  exact choice_unique D Y S' t x hx' hxt fun y hy hyt => hb y (hS hy) hyt

/-! ### One step of the run -/

def stepSet (ω : Outcome D) (S : Finset (Fin n)) (a : Action n m) : Finset (Fin n) :=
  if actionBit D ω a then afterSuccess S a else S

lemma run_succ (Y : Seeds n) (ω : Outcome D) (S : Finset (Fin n)) (k : ℕ) (hk : k < m) :
    algorithmRun D Y ω S (k + 1) =
      (stepSet D ω (algorithmRun D Y ω S k).1
          (⟨k, hk⟩, algorithmChoice D Y (algorithmRun D Y ω S k).1 ⟨k, hk⟩),
        (algorithmRun D Y ω S k).2 ++
          [((⟨k, hk⟩, algorithmChoice D Y (algorithmRun D Y ω S k).1 ⟨k, hk⟩),
            actionBit D ω (⟨k, hk⟩, algorithmChoice D Y (algorithmRun D Y ω S k).1 ⟨k, hk⟩))]) := by
  rw [algorithmRun]
  simp only [dif_pos hk, stepSet]

lemma run_stop (Y : Seeds n) (ω : Outcome D) (S : Finset (Fin n)) (k : ℕ) (hk : ¬ k < m) :
    algorithmRun D Y ω S (k + 1) = algorithmRun D Y ω S k := by
  rw [algorithmRun]
  simp only [dif_neg hk]

lemma stepSet_none (ω : Outcome D) (S : Finset (Fin n)) (t : Fin m) :
    stepSet D ω S (t, none) = S := by
  simp [stepSet, actionBit]

lemma stepSet_some (ω : Outcome D) (S : Finset (Fin n)) (t : Fin m) (x : Fin n) :
    stepSet D ω S (t, some x) = if bit D ω (x, t) then S.erase x else S := by
  unfold stepSet
  by_cases h : bit D ω (x, t) = true <;> simp [actionBit, afterSuccess, h]

lemma stepSet_sub (ω : Outcome D) (S : Finset (Fin n)) (a : Action n m) :
    stepSet D ω S a ⊆ S := by
  unfold stepSet afterSuccess
  split_ifs
  · rcases a with ⟨t, _ | x⟩
    · exact le_rfl
    · exact Finset.erase_subset _ _
  · exact le_rfl

lemma prob_ne_zero_of_bit (ω : Outcome D)
    (hZ : ∀ f : Edge D, D.probability f.val = 0 → ω f = false) (x : Fin n) (t : Fin m)
    (h : bit D ω (x, t) = true) : D.probability (x, t) ≠ 0 := by
  unfold bit at h
  split_ifs at h with hm
  · intro h0
    have := hZ ⟨(x, t), hm⟩ h0
    rw [this] at h
    exact Bool.false_ne_true h

/-! ### Lemma 5 / Lemma 6 core: the run with `i` against the run without `i` -/

/-- Decomposable weight: `score D Y t j = b t * w j` on edges. -/
def wt (a : Fin n → ℝ) (Y : Seeds n) (j : Fin n) : ℝ := a j * D.reward j * (1 - g (Y j))

lemma Pref_score_iff (a : Fin n → ℝ) (b : Fin m → ℝ)
    (hab : ∀ e ∈ D.edges, D.probability e = a e.1 * b e.2) (Y : Seeds n) (t : Fin m)
    (hbt : 0 < b t) (x y : Fin n) (hx : (x, t) ∈ D.edges) (hy : (y, t) ∈ D.edges) :
    Pref (score D Y t) x y ↔ Pref (wt D a Y) x y := by
  have key : ∀ j, (j, t) ∈ D.edges → score D Y t j = b t * wt D a Y j := by
    intro j hj
    simp only [score, wt, hab _ hj]
    ring
  rw [← Pref_mul (wt D a Y) (b t) hbt]
  unfold Pref
  rw [key x hx, key y hy]

set_option maxHeartbeats 1000000 in
theorem compare_runs (a : Fin n → ℝ) (b : Fin m → ℝ) (hb0 : ∀ t, 0 ≤ b t)
    (hab : ∀ e ∈ D.edges, D.probability e = a e.1 * b e.2)
    (Y : Seeds n) (ω : Outcome D) (hZ : ∀ f : Edge D, D.probability f.val = 0 → ω f = false)
    (i : Fin n) : ∀ k : ℕ,
      (algorithmRun D Y ω (Finset.univ.erase i) k).1 ⊆ (algorithmRun D Y ω Finset.univ k).1 ∧
      (i ∈ (algorithmRun D Y ω Finset.univ k).1 →
        ∀ x ∈ (algorithmRun D Y ω Finset.univ k).1,
          x ∉ (algorithmRun D Y ω (Finset.univ.erase i) k).1 → x ≠ i → Pref (wt D a Y) i x) := by
  intro k
  induction k with
  | zero =>
    refine ⟨Finset.subset_univ _, ?_⟩
    intro _ x _ hx hxi
    exact absurd (Finset.mem_erase.mpr ⟨hxi, Finset.mem_univ x⟩) hx
  | succ k ih =>
    by_cases hk : k < m
    swap
    · rw [run_stop D Y ω _ k hk, run_stop D Y ω _ k hk]; exact ih
    rw [run_succ D Y ω _ k hk, run_succ D Y ω _ k hk]
    simp only
    obtain ⟨hsub, hext⟩ := ih
    set A := (algorithmRun D Y ω Finset.univ k).1 with hA
    set A' := (algorithmRun D Y ω (Finset.univ.erase i) k).1 with hA'
    set s : Fin m := ⟨k, hk⟩
    rcases hc : algorithmChoice D Y A s with _ | x
    · -- no available neighbour in the run with i, hence none without i
      have hc' : algorithmChoice D Y A' s = none := by
        rcases hc' : algorithmChoice D Y A' s with _ | y
        · rfl
        · obtain ⟨hyA', hys, _⟩ := choice_spec D Y A' s y hc'
          exact absurd hys (choice_none D Y A s hc y (hsub hyA'))
      rw [hc', stepSet_none, stepSet_none]
      exact ⟨hsub, hext⟩
    by_cases hxA' : x ∈ A'
    · have hc' : algorithmChoice D Y A' s = some x := choice_subset D Y A A' hsub s x hc hxA'
      rw [hc', stepSet_some, stepSet_some]
      split_ifs with hbit
      · refine ⟨Finset.erase_subset_erase x hsub, ?_⟩
        intro hi z hz hz' hzi
        have hzx : z ≠ x := Finset.ne_of_mem_erase hz
        exact hext (Finset.mem_of_mem_erase hi) z (Finset.mem_of_mem_erase hz)
          (fun h => hz' (Finset.mem_erase.mpr ⟨hzx, h⟩)) hzi
      · exact ⟨hsub, hext⟩
    · -- the run with i picks an extra resource x
      obtain ⟨hxA, hxs, hxbest⟩ := choice_spec D Y A s x hc
      rw [stepSet_some]
      refine ⟨?_, ?_⟩
      · intro z hz
        have hzA' : z ∈ A' := stepSet_sub D ω A' _ hz
        have hzA : z ∈ A := hsub hzA'
        have hzx : z ≠ x := fun h => hxA' (h ▸ hzA')
        split_ifs
        · exact Finset.mem_erase.mpr ⟨hzx, hzA⟩
        · exact hzA
      · intro hi z hz hz' hzi
        have hiA : i ∈ A := by
          split_ifs at hi
          · exact Finset.mem_of_mem_erase hi
          · exact hi
        have hzA : z ∈ A := by
          split_ifs at hz
          · exact Finset.mem_of_mem_erase hz
          · exact hz
        have hix : Pref (wt D a Y) i x := by
          by_cases h : x = i
          · rw [h]; exact Pref_refl _ _
          · exact hext hiA x hxA hxA' h
        by_cases hzA' : z ∈ A'
        · rcases hc' : algorithmChoice D Y A' s with _ | y
          · rw [hc', stepSet_none] at hz'; exact absurd hzA' hz'
          · rw [hc', stepSet_some] at hz'
            split_ifs at hz' with hby
            · have hzy : z = y := by
                by_contra hne; exact hz' (Finset.mem_erase.mpr ⟨hne, hzA'⟩)
              subst hzy
              obtain ⟨_, hzs, _⟩ := choice_spec D Y A' s z hc'
              have hp := prob_ne_zero_of_bit D ω hZ z s hby
              have hbs : 0 < b s := by
                by_contra hle
                have h0 : b s = 0 := le_antisymm (not_lt.mp hle) (hb0 s)
                apply hp
                rw [hab _ hzs]
                simp [h0]
              have hxz : Pref (score D Y s) x z := hxbest z hzA hzs
              rw [Pref_score_iff D a b hab Y s hbs x z hxs hzs] at hxz
              exact Pref_trans _ hix hxz
            · exact absurd hzA' hz'
        · exact hext hiA z hzA hzA' hzi


/-! ### Consequences at the arrival `t` (Lemma 5 and Lemma 6 cores) -/

lemma choice_ge (Y : Seeds n) (A A' : Finset (Fin n)) (hsub : A' ⊆ A) (t : Fin m) (z : Fin n)
    (hz : z ∈ A') (hzt : (z, t) ∈ D.edges) :
    ∃ x, algorithmChoice D Y A t = some x ∧ score D Y t z ≤ score D Y t x := by
  rcases hc : algorithmChoice D Y A t with _ | x
  · exact absurd hzt (choice_none D Y A t hc z (hsub hz))
  · obtain ⟨_, _, hb⟩ := choice_spec D Y A t x hc
    exact ⟨x, rfl, Pref_score_le _ (hb z (hsub hz) hzt)⟩

lemma choice_eq_i (a : Fin n → ℝ) (b : Fin m → ℝ)
    (hab : ∀ e ∈ D.edges, D.probability e = a e.1 * b e.2) (Y : Seeds n)
    (A A' : Finset (Fin n)) (i : Fin n) (t : Fin m)
    (hext : ∀ x ∈ A, x ∉ A' → x ≠ i → Pref (wt D a Y) i x)
    (hiA : i ∈ A) (hit : (i, t) ∈ D.edges) (hbt : 0 < b t)
    (hlt : ∀ z ∈ A', (z, t) ∈ D.edges → score D Y t z < score D Y t i) :
    algorithmChoice D Y A t = some i := by
  apply choice_unique D Y A t i hiA hit
  intro y hy hyt
  by_cases hyi : y = i
  · rw [hyi]; exact Pref_refl _ _
  by_cases hyA' : y ∈ A'
  · exact Pref_of_lt _ (hlt y hyA' hyt)
  · rw [Pref_score_iff D a b hab Y t hbt i y hit hyt]
    exact hext y hy hyA' hyi

/-! ### Invariances of the run -/

lemma bestOf_mem {α : Type} (s : α → ℝ) : ∀ (L : List α) (x : α), bestOf s L = some x → x ∈ L
  | [] => by intro x hx; simp [bestOf] at hx
  | a :: rest => by
    intro x hx
    simp only [bestOf] at hx
    rcases hb : bestOf s rest with _ | b
    · rw [hb] at hx; simp only [Option.some.injEq] at hx; subst hx; simp
    · rw [hb] at hx
      simp only at hx
      split_ifs at hx
      · simp only [Option.some.injEq] at hx; subst hx; simp
      · simp only [Option.some.injEq] at hx; subst hx
        exact List.mem_cons_of_mem _ (bestOf_mem s rest _ hb)

lemma bestOf_congr {α : Type} (s s' : α → ℝ) :
    ∀ L : List α, (∀ x ∈ L, s x = s' x) → bestOf s L = bestOf s' L
  | [] => fun _ => rfl
  | a :: rest => by
    intro h
    simp only [bestOf]
    rw [bestOf_congr s s' rest (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rcases hb : bestOf s' rest with _ | b
    · rfl
    · simp only
      rw [h a (List.mem_cons_self), h b (List.mem_cons_of_mem _ (bestOf_mem s' rest b hb))]

lemma choice_congr_seed (Y Y' : Seeds n) (S : Finset (Fin n)) (t : Fin m)
    (h : ∀ j ∈ S, Y j = Y' j) : algorithmChoice D Y S t = algorithmChoice D Y' S t := by
  unfold algorithmChoice
  apply bestOf_congr
  intro x hx
  rw [Finset.mem_sort] at hx
  simp only [neighbors, Finset.mem_filter] at hx
  simp only [score, h x hx.1]

lemma run_sub (Y : Seeds n) (ω : Outcome D) (S : Finset (Fin n)) :
    ∀ k, (algorithmRun D Y ω S k).1 ⊆ S := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    by_cases hk : k < m
    · rw [run_succ D Y ω S k hk]; exact (stepSet_sub D ω _ _).trans ih
    · rw [run_stop D Y ω S k hk]; exact ih

lemma run_congr_seed (Y Y' : Seeds n) (ω : Outcome D) (S : Finset (Fin n))
    (h : ∀ j ∈ S, Y j = Y' j) : ∀ k, algorithmRun D Y ω S k = algorithmRun D Y' ω S k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < m
    · rw [run_succ D Y ω S k hk, run_succ D Y' ω S k hk, ih,
        choice_congr_seed D Y Y' _ _ (fun j hj => h j (run_sub D Y' ω S k hj))]
    · rw [run_stop D Y ω S k hk, run_stop D Y' ω S k hk, ih]

lemma run_congr_omega (Y : Seeds n) (S : Finset (Fin n)) :
    ∀ (k : ℕ) (ω ω' : Outcome D), (∀ f : Edge D, f.val.2.val < k → ω f = ω' f) →
      algorithmRun D Y ω S k = algorithmRun D Y ω' S k := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro ω ω' h
    have h' : ∀ f : Edge D, f.val.2.val < k → ω f = ω' f := fun f hf => h f (by omega)
    by_cases hk : k < m
    · rw [run_succ D Y ω S k hk, run_succ D Y ω' S k hk, ih ω ω' h']
      have hb : ∀ c : Option (Fin n), actionBit D ω (⟨k, hk⟩, c) = actionBit D ω' (⟨k, hk⟩, c) := by
        intro c
        rcases c with _ | x
        · rfl
        · simp only [actionBit, bit]
          split_ifs with hm
          · exact h ⟨(x, ⟨k, hk⟩), hm⟩ (by simp)
          · rfl
      simp only [stepSet, hb]
    · rw [run_stop D Y ω S k hk, run_stop D Y ω' S k hk, ih ω ω' h']

lemma run_hist_prefix (Y : Seeds n) (ω : Outcome D) (S : Finset (Fin n)) (k : ℕ) :
    ∀ k', k ≤ k' → (algorithmRun D Y ω S k).2 <+: (algorithmRun D Y ω S k').2 := by
  intro k' hkk'
  induction k', hkk' using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih =>
    by_cases hk : k' < m
    · rw [run_succ D Y ω S k' hk]; exact ih.trans (List.prefix_append _ _)
    · rw [run_stop D Y ω S k' hk]; exact ih

lemma removed_success (Y : Seeds n) (ω : Outcome D) (S : Finset (Fin n)) (i : Fin n)
    (hiS : i ∈ S) : ∀ k, i ∉ (algorithmRun D Y ω S k).1 →
      ∃ z ∈ (algorithmRun D Y ω S k).2, z.2 = true ∧ z.1.2 = some i := by
  intro k
  induction k with
  | zero => intro h; exact absurd hiS h
  | succ k ih =>
    intro hi
    by_cases hk : k < m
    swap
    · rw [run_stop D Y ω S k hk] at hi ⊢; exact ih hi
    rw [run_succ D Y ω S k hk] at hi ⊢
    simp only at hi ⊢
    by_cases hold : i ∈ (algorithmRun D Y ω S k).1
    · rcases hc : algorithmChoice D Y (algorithmRun D Y ω S k).1 ⟨k, hk⟩ with _ | x
      · rw [hc, stepSet_none] at hi; exact absurd hold hi
      · rw [hc, stepSet_some] at hi
        split_ifs at hi with hbit
        · have hix : i = x := by
            by_contra hne; exact hi (Finset.mem_erase.mpr ⟨hne, hold⟩)
          subst hix
          refine ⟨((⟨k, hk⟩, some i), actionBit D ω (⟨k, hk⟩, some i)), by simp, ?_, rfl⟩
          simpa [actionBit] using hbit
        · exact absurd hold hi
    · obtain ⟨z, hz, hz2⟩ := ih hold
      exact ⟨z, List.mem_append_left _ hz, hz2⟩

/-! ### The history entry of arrival `t` -/

def entry (Y : Seeds n) (ω : Outcome D) (S : Finset (Fin n)) (t : Fin m) : Action n m × Bool :=
  ((t, algorithmChoice D Y (algorithmRun D Y ω S t.val).1 t),
    actionBit D ω (t, algorithmChoice D Y (algorithmRun D Y ω S t.val).1 t))

lemma hist_arrival (Y : Seeds n) (ω : Outcome D) (S : Finset (Fin n)) (t : Fin m)
    (F : Action n m × Bool → ℝ) : ∀ k,
    ((algorithmRun D Y ω S k).2.map (fun z => if z.1.1 = t then F z else 0)).sum =
      if t.val < k then F (entry D Y ω S t) else 0 := by
  intro k
  induction k with
  | zero => simp [algorithmRun]
  | succ k ih =>
    by_cases hk : k < m
    · rw [run_succ D Y ω S k hk]
      simp only [List.map_append, List.sum_append, ih, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      by_cases htk : t.val = k
      · have ht : (⟨k, hk⟩ : Fin m) = t := Fin.ext htk.symm
        subst ht
        simp [entry]
      · have hne : (⟨k, hk⟩ : Fin m) ≠ t := fun h => htk (by rw [← h])
        simp only [hne, if_false, add_zero]
        by_cases hlt : t.val < k
        · rw [if_pos hlt, if_pos (by omega)]
        · rw [if_neg hlt, if_neg (by omega)]
    · rw [run_stop D Y ω S k hk, ih]
      have : t.val < k := by omega
      rw [if_pos this, if_pos (by omega)]

/-! ### Dual pieces: Lemma 3 (pathwise) and the averaging at arrival `t` -/

def lamPart (Y : Seeds n) (a : Action n m) : ℝ :=
  match a.2 with
  | none => 0
  | some j => D.reward j * (1 - g (Y j))

def lamP (Y : Seeds n) (ω : Outcome D) (t : Fin m) : ℝ :=
  ((algorithmHistory D Y ω).map
    (fun z => if z.1.1 = t then (if z.2 then lamPart D Y z.1 else 0) else 0)).sum

def thP (Y : Seeds n) (ω : Outcome D) (i : Fin n) : ℝ :=
  ((algorithmHistory D Y ω).map
    (fun z => if z.2 = true ∧ z.1.2 = some i then D.reward i * g (Y i) else 0)).sum

def choiceAt (Y : Seeds n) (ω : Outcome D) (t : Fin m) : Option (Fin n) :=
  algorithmChoice D Y (algorithmRun D Y ω Finset.univ t.val).1 t

def lamE (Y : Seeds n) (ω : Outcome D) (t : Fin m) : ℝ :=
  match choiceAt D Y ω t with
  | none => 0
  | some j => score D Y t j

lemma reward_split_one (Y : Seeds n) (z : Action n m × Bool) :
    (if z.2 then actionReward D z.1 else 0) =
      ∑ t : Fin m, (if z.1.1 = t then (if z.2 then lamPart D Y z.1 else 0) else 0) +
      ∑ i : Fin n, (if z.2 = true ∧ z.1.2 = some i then D.reward i * g (Y i) else 0) := by
  obtain ⟨⟨t0, _ | j⟩, bz⟩ := z
  · cases bz <;> simp [actionReward, lamPart]
  · cases bz
    · simp
    · simp [actionReward, lamPart]
      ring

lemma reward_split (Y : Seeds n) (ω : Outcome D) :
    algorithmReward D Y ω = ∑ t, lamP D Y ω t + ∑ i, thP D Y ω i := by
  unfold algorithmReward lamP thP
  generalize algorithmHistory D Y ω = H
  induction H with
  | nil => simp
  | cons z rest ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih, reward_split_one D Y z]
    ring

lemma lamP_eq (Y : Seeds n) (ω : Outcome D) (t : Fin m) :
    lamP D Y ω t = if actionBit D ω (t, choiceAt D Y ω t) then lamPart D Y (t, choiceAt D Y ω t)
      else 0 := by
  unfold lamP algorithmHistory
  have h := hist_arrival D Y ω Finset.univ t (fun z => if z.2 then lamPart D Y z.1 else 0) m
  rw [h, if_pos t.isLt]
  rfl

lemma choiceAt_update (Y : Seeds n) (ω : Outcome D) (t : Fin m) (e : Edge D)
    (he : e.val.2 = t) (b : Bool) :
    choiceAt D Y (Function.update ω e b) t = choiceAt D Y ω t := by
  unfold choiceAt
  rw [run_congr_omega D Y Finset.univ t.val (Function.update ω e b) ω]
  intro f hf
  have hfe : f ≠ e := by
    rintro rfl
    rw [he] at hf
    exact lt_irrefl _ hf
  rw [Function.update_of_ne hfe]

lemma lamE_update (Y : Seeds n) (ω : Outcome D) (t : Fin m) (e : Edge D)
    (he : e.val.2 = t) (b : Bool) :
    lamE D Y (Function.update ω e b) t = lamE D Y ω t := by
  unfold lamE
  rw [choiceAt_update D Y ω t e he b]

lemma E_fsum {ι : Type*} (s : Finset ι) (F : ι → Outcome D → ℝ) :
    edgeAverage D (fun ω => ∑ j ∈ s, F j ω) = ∑ j ∈ s, edgeAverage D (F j) := by
  simp only [WD.E_def, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma E_lam (Y : Seeds n) (t : Fin m) :
    edgeAverage D (fun ω => lamP D Y ω t) = edgeAverage D (fun ω => lamE D Y ω t) := by
  have h1 : (fun ω => lamP D Y ω t) = fun ω => ∑ j : Fin n,
      (if choiceAt D Y ω t = some j then
        (if bit D ω (j, t) then D.reward j * (1 - g (Y j)) else 0) else 0) := by
    funext ω
    rw [lamP_eq]
    rcases choiceAt D Y ω t with _ | j0
    · simp [actionBit]
    · simp [actionBit, lamPart]
      try congr
  have h2 : (fun ω => lamE D Y ω t) = fun ω => ∑ j : Fin n,
      (if choiceAt D Y ω t = some j then
        D.probability (j, t) * (D.reward j * (1 - g (Y j))) else 0) := by
    funext ω
    unfold lamE
    rcases choiceAt D Y ω t with _ | j0
    · simp
    · simp [score]
      ring
  rw [h1, h2, E_fsum, E_fsum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (j, t) ∈ D.edges
  · set e : Edge D := ⟨(j, t), hj⟩
    set φ : Outcome D → ℝ := fun ω =>
      if choiceAt D Y ω t = some j then D.reward j * (1 - g (Y j)) else 0
    have hφ : ∀ ω b, φ (Function.update ω e b) = φ ω := by
      intro ω b
      simp only [φ, choiceAt_update D Y ω t e rfl b]
    have hL : (fun ω => if choiceAt D Y ω t = some j then
        (if bit D ω (j, t) then D.reward j * (1 - g (Y j)) else 0) else 0) =
        fun ω => φ ω * indicator ω e := by
      funext ω
      simp only [φ, indicator, bit, dif_pos hj]
      split_ifs <;> simp
    have hR : (fun ω => if choiceAt D Y ω t = some j then
        D.probability (j, t) * (D.reward j * (1 - g (Y j))) else 0) =
        fun ω => D.probability e.val * φ ω := by
      funext ω
      simp only [φ]
      split_ifs
      · rfl
      · simp
    rw [hL, hR, WD.E_indicator D e φ hφ, WD.E_const_mul]
  · have h0 : ∀ ω, choiceAt D Y ω t ≠ some j := by
      intro ω hc
      exact hj (choice_spec D Y _ t j hc).2.1
    simp only [h0, if_false]

/-! ### Pathwise bounds for the dual at an edge `(i, t)` (Lemmas 5 and 6) -/

lemma g_le_one {y : ℝ} (hy : y ≤ 1) : g y ≤ 1 := by
  unfold g
  exact Real.exp_le_one_iff.mpr (by linarith)

lemma score_nonneg (Y : Seeds n) (hY : ∀ j, Y j ≤ 1) (t : Fin m) (j : Fin n)
    (hj : (j, t) ∈ D.edges) : 0 ≤ score D Y t j :=
  mul_nonneg (mul_nonneg (D.probability_mem _ hj).1 (D.reward_nonneg j))
    (by linarith [g_le_one (hY j)])

lemma lamE_nonneg (Y : Seeds n) (hY : ∀ j, Y j ≤ 1) (ω : Outcome D) (t : Fin m) :
    0 ≤ lamE D Y ω t := by
  unfold lamE
  split
  · exact le_refl 0
  · rename_i j hc
    exact score_nonneg D Y hY t j (choice_spec D Y _ t j hc).2.1

lemma thP_ge_of_mem (Y : Seeds n) (ω : Outcome D) (i : Fin n) (z : Action n m × Bool)
    (hz : z ∈ algorithmHistory D Y ω) (h2 : z.2 = true) (h1 : z.1.2 = some i) :
    D.reward i * g (Y i) ≤ thP D Y ω i := by
  unfold thP
  apply List.single_le_sum
  · intro x hx
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
    split_ifs
    · exact mul_nonneg (D.reward_nonneg i) (Real.exp_pos _).le
    · exact le_refl 0
  · exact List.mem_map.mpr ⟨z, hz, by simp [h2, h1]⟩

lemma entry_mem_hist (Y : Seeds n) (ω : Outcome D) (t : Fin m) :
    entry D Y ω Finset.univ t ∈ algorithmHistory D Y ω := by
  have h := run_hist_prefix D Y ω Finset.univ (t.val + 1) m t.isLt
  rw [run_succ D Y ω Finset.univ t.val t.isLt] at h
  exact h.subset (List.mem_append_right _ (List.mem_singleton_self _))

theorem thP_ge (a : Fin n → ℝ) (b : Fin m → ℝ) (hb0 : ∀ t, 0 ≤ b t)
    (hab : ∀ e ∈ D.edges, D.probability e = a e.1 * b e.2)
    (Y : Seeds n) (ω : Outcome D) (hZ : ∀ f : Edge D, D.probability f.val = 0 → ω f = false)
    (i : Fin n) (t : Fin m) (hit : (i, t) ∈ D.edges) (hp : 0 < D.probability (i, t))
    (hbit : bit D ω (i, t) = true)
    (hlt : ∀ z ∈ (algorithmRun D Y ω (Finset.univ.erase i) t.val).1, (z, t) ∈ D.edges →
        score D Y t z < score D Y t i) :
    D.reward i * g (Y i) ≤ thP D Y ω i := by
  obtain ⟨hsub, hext⟩ := compare_runs D a b hb0 hab Y ω hZ i t.val
  by_cases hiA : i ∈ (algorithmRun D Y ω Finset.univ t.val).1
  · have hbt : 0 < b t := by
      rcases lt_or_eq_of_le (hb0 t) with h | h
      · exact h
      · exfalso
        rw [hab _ hit] at hp
        simp [← h] at hp
    have hc : choiceAt D Y ω t = some i :=
      choice_eq_i D a b hab Y _ _ i t (hext hiA) hiA hit hbt hlt
    apply thP_ge_of_mem D Y ω i (entry D Y ω Finset.univ t) (entry_mem_hist D Y ω t)
    · show actionBit D ω (t, choiceAt D Y ω t) = true
      rw [hc]
      simpa [actionBit] using hbit
    · show choiceAt D Y ω t = some i
      exact hc
  · obtain ⟨z, hz, hz2, hz1⟩ :=
      removed_success D Y ω Finset.univ i (Finset.mem_univ i) t.val hiA
    exact thP_ge_of_mem D Y ω i z ((run_hist_prefix D Y ω _ t.val m t.isLt.le).subset hz) hz2 hz1

theorem lamE_ge (a : Fin n → ℝ) (b : Fin m → ℝ) (hb0 : ∀ t, 0 ≤ b t)
    (hab : ∀ e ∈ D.edges, D.probability e = a e.1 * b e.2)
    (Y : Seeds n) (ω : Outcome D) (hZ : ∀ f : Edge D, D.probability f.val = 0 → ω f = false)
    (i : Fin n) (t : Fin m) (z : Fin n)
    (hz : z ∈ (algorithmRun D Y ω (Finset.univ.erase i) t.val).1) (hzt : (z, t) ∈ D.edges) :
    score D Y t z ≤ lamE D Y ω t := by
  obtain ⟨hsub, -⟩ := compare_runs D a b hb0 hab Y ω hZ i t.val
  obtain ⟨x, hx, hle⟩ := choice_ge D Y _ _ hsub t z hz hzt
  unfold lamE choiceAt
  rw [hx]
  exact hle

end Fit

namespace Meas

variable {n : ℕ}

/-! ### Discrete measurability (measurable fibres) -/

def DM {α : Type*} (R : Seeds n → α) : Prop := ∀ a, MeasurableSet (R ⁻¹' {a})

lemma DM_const {α : Type*} (a : α) : DM (fun _ : Seeds n => a) := by
  intro b
  exact MeasurableSet.const _

lemma DM_bind {α β : Type*} [Countable α] (R : Seeds n → α) (hR : DM R)
    (Φ : α → Seeds n → β) (hΦ : ∀ a, DM (Φ a)) : DM (fun Y => Φ (R Y) Y) := by
  intro b
  have : (fun Y => Φ (R Y) Y) ⁻¹' {b} = ⋃ a, (R ⁻¹' {a} ∩ (Φ a) ⁻¹' {b}) := by
    ext Y; simp
  rw [this]
  exact MeasurableSet.iUnion fun a => (hR a).inter (hΦ a b)

lemma meas_bind {α β : Type*} [Countable α] [MeasurableSpace β] (R : Seeds n → α) (hR : DM R)
    (Φ : α → Seeds n → β) (hΦ : ∀ a, Measurable (Φ a)) : Measurable (fun Y => Φ (R Y) Y) := by
  intro s hs
  have : (fun Y => Φ (R Y) Y) ⁻¹' s = ⋃ a, (R ⁻¹' {a} ∩ (Φ a) ⁻¹' s) := by
    ext Y; simp
  rw [this]
  exact MeasurableSet.iUnion fun a => (hR a).inter (hΦ a hs)

lemma DM_map {α β : Type*} [Countable α] (R : Seeds n → α) (hR : DM R) (F : α → β) :
    DM (fun Y => F (R Y)) := DM_bind R hR (fun a _ => F a) (fun _ => DM_const _)

lemma DM_ite {β : Type*} (P : Seeds n → Prop) [DecidablePred P] (hP : MeasurableSet {Y | P Y})
    (x y : β) : DM (fun Y => if P Y then x else y) := by
  intro b
  have : (fun Y => if P Y then x else y) ⁻¹' {b} =
      ({Y | P Y} ∩ {_Y | x = b}) ∪ ({Y | P Y}ᶜ ∩ {_Y | y = b}) := by
    ext Y; by_cases h : P Y <;> simp [h]
  rw [this]
  exact (hP.inter (MeasurableSet.const _)).union (hP.compl.inter (MeasurableSet.const _))

lemma DM_comp {α : Type*} (R : Seeds n → α) (hR : DM R) (c : Seeds n → Seeds n)
    (hc : Measurable c) : DM (fun Y => R (c Y)) := fun a => hc (hR a)

variable {m : ℕ} (D : Instance n m)

lemma score_meas (t : Fin m) (j : Fin n) : Measurable (fun Y : Seeds n => score D Y t j) := by
  unfold score g
  exact Continuous.measurable (by fun_prop)

lemma bestOf_DM (t : Fin m) : ∀ L : List (Fin n), DM (fun Y => bestOf (score D Y t) L)
  | [] => DM_const _
  | a :: rest => by
    have h := bestOf_DM t rest
    have key : (fun Y => bestOf (score D Y t) (a :: rest)) = fun Y =>
        (fun (o : Option (Fin n)) (Y : Seeds n) => o.elim (some a)
          (fun b => if score D Y t b ≤ score D Y t a then some a else some b))
        (bestOf (score D Y t) rest) Y := by
      funext Y
      simp only [bestOf]
      rcases bestOf (score D Y t) rest with _ | b <;> rfl
    rw [key]
    refine DM_bind (Φ := fun (o : Option (Fin n)) (Y : Seeds n) => o.elim (some a)
          (fun b => if score D Y t b ≤ score D Y t a then some a else some b)) _ h ?_
    intro o
    rcases o with _ | b
    · exact DM_const _
    · exact DM_ite _ (measurableSet_le (score_meas D t b) (score_meas D t a)) _ _

lemma choice_DM (S : Finset (Fin n)) (t : Fin m) : DM (fun Y => algorithmChoice D Y S t) :=
  bestOf_DM D t _

lemma run_DM (ω : Outcome D) (S : Finset (Fin n)) : ∀ k, DM (fun Y => algorithmRun D Y ω S k)
  | 0 => DM_const _
  | k + 1 => by
    by_cases hk : k < m
    · have key : (fun Y => algorithmRun D Y ω S (k+1)) = fun Y =>
          (fun (u : Finset (Fin n) × History n m) (Y : Seeds n) =>
            (fun c : Option (Fin n) =>
              ((if actionBit D ω (⟨k, hk⟩, c) then afterSuccess u.1 (⟨k, hk⟩, c) else u.1),
                u.2 ++ [((⟨k, hk⟩, c), actionBit D ω (⟨k, hk⟩, c))]))
            (algorithmChoice D Y u.1 ⟨k, hk⟩))
          (algorithmRun D Y ω S k) Y := by
        funext Y; rw [algorithmRun]; simp only [dif_pos hk]
      rw [key]
      refine DM_bind (Φ := fun (u : Finset (Fin n) × History n m) (Y : Seeds n) =>
            (fun c : Option (Fin n) =>
              ((if actionBit D ω (⟨k, hk⟩, c) then afterSuccess u.1 (⟨k, hk⟩, c) else u.1),
                u.2 ++ [((⟨k, hk⟩, c), actionBit D ω (⟨k, hk⟩, c))]))
            (algorithmChoice D Y u.1 ⟨k, hk⟩)) _ (run_DM ω S k) ?_
      intro u
      exact DM_map _ (choice_DM D u.1 ⟨k, hk⟩) (fun c : Option (Fin n) =>
              ((if actionBit D ω (⟨k, hk⟩, c) then afterSuccess u.1 (⟨k, hk⟩, c) else u.1),
                u.2 ++ [((⟨k, hk⟩, c), actionBit D ω (⟨k, hk⟩, c))]))
    · have key : (fun Y => algorithmRun D Y ω S (k+1)) = fun Y => algorithmRun D Y ω S k := by
        funext Y; rw [algorithmRun]; simp only [dif_neg hk]
      rw [key]; exact run_DM ω S k

lemma list_sum_meas {β : Type*} (h : List β) (F : β → Seeds n → ℝ)
    (hF : ∀ z, Measurable (F z)) : Measurable (fun Y => (h.map (fun z => F z Y)).sum) := by
  induction h with
  | nil => simp only [List.map_nil, List.sum_nil]; exact measurable_const
  | cons z rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF z).add ih

lemma list_sum_le {β : Type*} (h : List β) (F : β → ℝ) (C : ℝ)
    (hF : ∀ z, F z ≤ C) : (h.map F).sum ≤ h.length * C := by
  induction h with
  | nil => simp
  | cons z rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith [hF z]

lemma list_sum_nonneg {β : Type*} (h : List β) (F : β → ℝ)
    (hF : ∀ z, 0 ≤ F z) : 0 ≤ (h.map F).sum := by
  induction h with
  | nil => simp
  | cons z rest ih =>
    simp only [List.map_cons, List.sum_cons]
    linarith [hF z]

/-! ### The seed law -/

lemma unit_prob : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
  ⟨by simp [Measure.restrict_apply_univ, Real.volume_Icc]⟩

attribute [local instance] unit_prob

lemma seedLaw_prob : IsProbabilityMeasure (seedLaw n) := by
  unfold seedLaw; infer_instance

attribute [local instance] seedLaw_prob

lemma integrable_of_bdd (f : Seeds n → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ Y, |f Y| ≤ C) : Integrable f (seedLaw n) :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (ae_of_all _ fun Y => by simpa [Real.norm_eq_abs] using hC Y)

def clamp (Y : Seeds n) : Seeds n := fun j => max 0 (min 1 (Y j))

lemma clamp_meas : Measurable (clamp : Seeds n → Seeds n) := by
  unfold clamp
  exact Continuous.measurable (by fun_prop)

lemma clamp_unit (Y : Seeds n) (j : Fin n) : clamp Y j ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma clamp_of_unit (Y : Seeds n) (hY : ∀ j, Y j ∈ Set.Icc (0:ℝ) 1) : clamp Y = Y := by
  funext j
  simp [clamp, (hY j).1, (hY j).2]

lemma clamp_update (Y : Seeds n) (i : Fin n) (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    clamp (Function.update Y i y) = Function.update (clamp Y) i y := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [clamp, hy.1, hy.2]
  · simp [clamp, Function.update_of_ne hj]

lemma ae_unit : ∀ᵐ Y ∂(seedLaw n), ∀ j, Y j ∈ Set.Icc (0:ℝ) 1 := by
  rw [ae_all_iff]
  intro j
  exact Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem measurableSet_Icc)

lemma seedAverage_clamp (f : Seeds n → ℝ) :
    seedAverage (fun Y => f (clamp Y)) = seedAverage f := by
  unfold seedAverage
  apply integral_congr_ae
  filter_upwards [ae_unit] with Y hY
  rw [clamp_of_unit Y hY]

/-! ### Tower over one coordinate (paper Lemma 4) -/

lemma lmarg_const (s : Finset (Fin n)) (c : ENNReal) (x : Seeds n) :
    (∫⋯∫⁻_s, (fun _ => c) ∂(fun _ : Fin n => volume.restrict (Set.Icc (0:ℝ) 1))) x = c := by
  unfold lmarginal
  simp [lintegral_const, Measure.pi_univ]

theorem tower (f : Seeds n → ℝ) (hf : Measurable f) (hf0 : ∀ Y, 0 ≤ f Y) (C : ℝ)
    (hC : ∀ Y, f Y ≤ C) (i : Fin n) (c : ℝ)
    (h : ∀ Y, ENNReal.ofReal c ≤
      ∫⁻ y, ENNReal.ofReal (f (Function.update Y i y)) ∂(volume.restrict (Set.Icc (0:ℝ) 1))) :
    c ≤ seedAverage f := by
  have hint : Integrable f (seedLaw n) :=
    integrable_of_bdd f hf C fun Y => by rw [abs_of_nonneg (hf0 Y)]; exact hC Y
  unfold seedAverage
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable]
  apply (ENNReal.ofReal_le_iff_le_toReal hint.lintegral_lt_top.ne).mp
  have hF : Measurable (fun Y => ENNReal.ofReal (f Y)) := ENNReal.measurable_ofReal.comp hf
  unfold seedLaw
  rw [lintegral_eq_lmarginal_univ (0 : Seeds n),
    lmarginal_erase' _ hF (Finset.mem_univ i)]
  calc ENNReal.ofReal c
      = (∫⋯∫⁻_(Finset.univ.erase i), (fun _ => ENNReal.ofReal c)
          ∂(fun _ : Fin n => volume.restrict (Set.Icc (0:ℝ) 1))) 0 := (lmarg_const _ _ _).symm
    _ ≤ _ := lmarginal_mono (fun Y => h Y) 0

/-! ### The calculus step (paper: 1 - g(y) + ∫ g = 1 - 1/e) -/

theorem calc5 (M c : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c) (F : ℝ → ℝ)
    (hF : ∀ y ∈ Set.Icc (0:ℝ) 1, M ≤ F y)
    (hF2 : ∀ y ∈ Set.Icc (0:ℝ) 1, M < c * (1 - g y) → M + c * g y ≤ F y) :
    ENNReal.ofReal (c * (1 - Real.exp (-1))) ≤
      ∫⁻ y, ENNReal.ofReal (F y) ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
  have hconst : ∫⁻ _y, ENNReal.ofReal M ∂(volume.restrict (Set.Icc (0:ℝ) 1)) =
      ENNReal.ofReal M := by
    simp [lintegral_const]
  by_cases hcase : c * (1 - Real.exp (-1)) ≤ M
  · calc ENNReal.ofReal (c * (1 - Real.exp (-1))) ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal hcase
      _ = ∫⁻ _y, ENNReal.ofReal M ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := hconst.symm
      _ ≤ _ := by
        apply lintegral_mono_ae
        rw [ae_restrict_iff' measurableSet_Icc]
        exact ae_of_all _ fun y hy => ENNReal.ofReal_le_ofReal (hF y hy)
  push Not at hcase
  have he1 : Real.exp (-1) < 1 := by
    have := Real.exp_lt_exp.mpr (show (-1:ℝ) < 0 by norm_num)
    simpa using this
  have he0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hcpos : 0 < c := by
    by_contra hc'
    have : c = 0 := le_antisymm (not_lt.mp hc') hc
    rw [this] at hcase; linarith
  set q := 1 - M / c with hq
  have hq1 : Real.exp (-1) < q := by
    rw [hq]
    have : M / c < 1 - Real.exp (-1) := by
      rw [div_lt_iff₀ hcpos]; linarith
    linarith
  have hqle : q ≤ 1 := by
    rw [hq]; have : 0 ≤ M / c := div_nonneg hM hc; linarith
  have hqpos : 0 < q := lt_trans he0 hq1
  set yc := 1 + Real.log q with hyc
  have hyc0 : 0 < yc := by
    have : -1 < Real.log q := by
      rw [← Real.log_exp (-1)]
      exact Real.log_lt_log he0 hq1
    rw [hyc]; linarith
  have hyc1 : yc ≤ 1 := by
    have : Real.log q ≤ 0 := Real.log_nonpos hqpos.le hqle
    rw [hyc]; linarith
  have hgyc : g yc = q := by
    unfold g; rw [hyc]; simp [Real.exp_log hqpos]
  -- pointwise lower bound
  have hlow : ∀ y ∈ Set.Icc (0:ℝ) 1, ENNReal.ofReal M +
      (Set.Ico 0 yc).indicator (fun y => ENNReal.ofReal (c * g y)) y ≤ ENNReal.ofReal (F y) := by
    intro y hy
    by_cases hyy : y ∈ Set.Ico 0 yc
    · rw [Set.indicator_of_mem hyy, ← ENNReal.ofReal_add hM
        (show 0 ≤ c * g y from mul_nonneg hc (Real.exp_pos _).le)]
      apply ENNReal.ofReal_le_ofReal
      apply hF2 y hy
      have hgy : g y < q := by
        rw [← hgyc]; unfold g
        exact Real.exp_lt_exp.mpr (by linarith [hyy.2])
      have : c * q = c - M := by rw [hq]; field_simp
      nlinarith
    · rw [Set.indicator_of_notMem hyy, add_zero]
      exact ENNReal.ofReal_le_ofReal (hF y hy)
  have hint : IntegrableOn (fun y => c * g y) (Set.Ico 0 yc) volume := by
    have hcont : Continuous (fun y => c * g y) := by unfold g; fun_prop
    exact (hcont.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
  have hI : ∫ y in Set.Ico 0 yc, c * g y = c * (q - Real.exp (-1)) := by
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hyc0.le,
      intervalIntegral.integral_const_mul]
    unfold g
    rw [intervalIntegral.integral_comp_sub_right (fun x => Real.exp x) 1, integral_exp]
    rw [show yc - 1 = Real.log q by rw [hyc]; ring, Real.exp_log hqpos]
    norm_num
  have hsub : Set.Ico 0 yc ∩ Set.Icc (0:ℝ) 1 = Set.Ico 0 yc :=
    Set.inter_eq_left.mpr (Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hyc1))
  have hlin : ∫⁻ y, (Set.Ico 0 yc).indicator (fun y => ENNReal.ofReal (c * g y)) y
      ∂(volume.restrict (Set.Icc (0:ℝ) 1)) = ENNReal.ofReal (c * (q - Real.exp (-1))) := by
    rw [lintegral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico, hsub,
      ← hI, ofReal_integral_eq_lintegral_ofReal hint]
    exact (ae_restrict_iff' measurableSet_Ico).mpr
      (ae_of_all _ fun y _ => mul_nonneg hc (Real.exp_pos _).le)
  calc ENNReal.ofReal (c * (1 - Real.exp (-1)))
      = ENNReal.ofReal M + ENNReal.ofReal (c * (q - Real.exp (-1))) := by
        rw [← ENNReal.ofReal_add hM (mul_nonneg hc (by linarith))]
        congr 1
        rw [hq]; field_simp; ring
    _ = ∫⁻ y, (ENNReal.ofReal M + (Set.Ico 0 yc).indicator
          (fun y => ENNReal.ofReal (c * g y)) y) ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
        rw [lintegral_add_left measurable_const, hconst, hlin]
    _ ≤ _ := by
        apply lintegral_mono_ae
        rw [ae_restrict_iff' measurableSet_Icc]
        exact ae_of_all _ hlow

end Meas

namespace Asm

open Fit Meas
attribute [local instance] Meas.unit_prob Meas.seedLaw_prob

variable {n m : ℕ} (D : Instance n m)

/-! ### Measurability and bounds of the dual pieces -/

lemma choiceAt_DM (ω : Outcome D) (t : Fin m) : DM (fun Y => choiceAt D Y ω t) :=
  DM_bind (Φ := fun (u : Finset (Fin n) × History n m) (Y : Seeds n) => algorithmChoice D Y u.1 t)
    _ (run_DM D ω Finset.univ t.val) (fun u => choice_DM D u.1 t)

lemma lamE_meas (ω : Outcome D) (t : Fin m) : Measurable (fun Y => lamE D Y ω t) := by
  have key : (fun Y => lamE D Y ω t) = fun Y =>
      (fun (o : Option (Fin n)) (Y : Seeds n) => o.elim 0 (fun j => score D Y t j))
        (choiceAt D Y ω t) Y := by
    funext Y; unfold lamE; rcases choiceAt D Y ω t with _ | j <;> rfl
  rw [key]
  refine meas_bind (Φ := fun (o : Option (Fin n)) (Y : Seeds n) => o.elim 0 (fun j => score D Y t j))
    _ (choiceAt_DM D ω t) ?_
  intro o
  rcases o with _ | j
  · exact measurable_const
  · exact score_meas D t j

lemma lamPart_meas (a : Action n m) : Measurable (fun Y => lamPart D Y a) := by
  rcases a with ⟨t, _ | j⟩
  · exact measurable_const
  · show Measurable (fun Y : Seeds n => D.reward j * (1 - g (Y j)))
    unfold g; exact Continuous.measurable (by fun_prop)

lemma lamP_meas (ω : Outcome D) (t : Fin m) : Measurable (fun Y => lamP D Y ω t) := by
  refine meas_bind (Φ := fun (u : Finset (Fin n) × History n m) (Y : Seeds n) =>
      (u.2.map (fun z => if z.1.1 = t then (if z.2 then lamPart D Y z.1 else 0) else 0)).sum)
    _ (run_DM D ω Finset.univ m) ?_
  intro u
  apply list_sum_meas u.2 (fun z Y => if z.1.1 = t then (if z.2 then lamPart D Y z.1 else 0) else 0)
  intro z
  by_cases h1 : z.1.1 = t
  · by_cases h2 : z.2 = true
    · simp only [if_pos h1, if_pos h2]; exact lamPart_meas D z.1
    · simp only [if_pos h1, if_neg h2]; exact measurable_const
  · simp only [if_neg h1]; exact measurable_const

lemma thP_meas (ω : Outcome D) (i : Fin n) : Measurable (fun Y => thP D Y ω i) := by
  refine meas_bind (Φ := fun (u : Finset (Fin n) × History n m) (Y : Seeds n) =>
      (u.2.map (fun z => if z.2 = true ∧ z.1.2 = some i then D.reward i * g (Y i) else 0)).sum)
    _ (run_DM D ω Finset.univ m) ?_
  intro u
  apply list_sum_meas u.2 (fun z Y => if z.2 = true ∧ z.1.2 = some i then D.reward i * g (Y i) else 0)
  intro z
  by_cases h : z.2 = true ∧ z.1.2 = some i
  · simp only [if_pos h]; unfold g; exact Continuous.measurable (by fun_prop)
  · simp only [if_neg h]; exact measurable_const

lemma g_pos (y : ℝ) : 0 < g y := Real.exp_pos _

lemma hist_length (Y : Seeds n) (ω : Outcome D) (S : Finset (Fin n)) :
    ∀ k, (algorithmRun D Y ω S k).2.length ≤ k := by
  intro k
  induction k with
  | zero => simp [algorithmRun]
  | succ k ih =>
    by_cases hk : k < m
    · rw [run_succ D Y ω S k hk]; simp only [List.length_append, List.length_singleton]; omega
    · rw [run_stop D Y ω S k hk]; omega

def RS : ℝ := ∑ j, D.reward j

lemma RS_nonneg : 0 ≤ RS D := Finset.sum_nonneg (fun k _ => D.reward_nonneg k)

lemma reward_le_RS (j : Fin n) : D.reward j ≤ RS D :=
  Finset.single_le_sum (fun k _ => D.reward_nonneg k) (Finset.mem_univ j)

def U (Y : Seeds n) : Prop := ∀ j, Y j ∈ Set.Icc (0:ℝ) 1

lemma U_update (Y0 : Seeds n) (hY0 : U Y0) (i : Fin n) (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    U (Function.update Y0 i y) := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hy
  · rw [Function.update_of_ne hj]; exact hY0 j

lemma lamE_le (Y : Seeds n) (hY : U Y) (ω : Outcome D) (t : Fin m) : lamE D Y ω t ≤ RS D := by
  unfold lamE
  split
  · exact RS_nonneg D
  · rename_i j hc
    have hj := (choice_spec D Y _ t j hc).2.1
    have hp := D.probability_mem _ hj
    have h1 : 1 - g (Y j) ≤ 1 := by linarith [g_pos (Y j)]
    have h2 : 0 ≤ 1 - g (Y j) := by linarith [g_le_one (hY j).2]
    unfold score
    calc D.probability (j, t) * D.reward j * (1 - g (Y j)) ≤ 1 * D.reward j * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hp.2 (D.reward_nonneg j)) h1 h2
          linarith [D.reward_nonneg j]
      _ ≤ RS D := by simpa using reward_le_RS D j

lemma lamP_bounds (Y : Seeds n) (hY : U Y) (ω : Outcome D) (t : Fin m) :
    0 ≤ lamP D Y ω t ∧ lamP D Y ω t ≤ RS D := by
  rw [lamP_eq]
  rcases choiceAt D Y ω t with _ | j
  · rw [show actionBit D ω (t, none) = false by simp [actionBit]]
    simp only [Bool.false_eq_true, if_false]
    exact ⟨le_rfl, RS_nonneg D⟩
  · split_ifs
    · show 0 ≤ D.reward j * (1 - g (Y j)) ∧ D.reward j * (1 - g (Y j)) ≤ RS D
      have h1 : 1 - g (Y j) ≤ 1 := by linarith [g_pos (Y j)]
      have h2 : 0 ≤ 1 - g (Y j) := by linarith [g_le_one (hY j).2]
      refine ⟨mul_nonneg (D.reward_nonneg j) h2, ?_⟩
      calc D.reward j * (1 - g (Y j)) ≤ D.reward j * 1 :=
            mul_le_mul_of_nonneg_left h1 (D.reward_nonneg j)
        _ ≤ RS D := by simpa using reward_le_RS D j
    · exact ⟨le_rfl, RS_nonneg D⟩

lemma thP_bounds (Y : Seeds n) (hY : U Y) (ω : Outcome D) (i : Fin n) :
    0 ≤ thP D Y ω i ∧ thP D Y ω i ≤ m * D.reward i := by
  have hterm : ∀ z : Action n m × Bool,
      0 ≤ (if z.2 = true ∧ z.1.2 = some i then D.reward i * g (Y i) else 0) ∧
      (if z.2 = true ∧ z.1.2 = some i then D.reward i * g (Y i) else 0) ≤ D.reward i := by
    intro z
    split_ifs
    · refine ⟨mul_nonneg (D.reward_nonneg i) (g_pos _).le, ?_⟩
      simpa using mul_le_mul_of_nonneg_left (g_le_one (hY i).2) (D.reward_nonneg i)
    · exact ⟨le_rfl, D.reward_nonneg i⟩
  unfold thP
  refine ⟨list_sum_nonneg _ _ (fun z => (hterm z).1), ?_⟩
  refine (list_sum_le _ _ _ (fun z => (hterm z).2)).trans ?_
  apply mul_le_mul_of_nonneg_right _ (D.reward_nonneg i)
  exact_mod_cast hist_length D Y ω Finset.univ m

lemma int_lamE (ω : Outcome D) (t : Fin m) :
    Integrable (fun Y => lamE D (clamp Y) ω t) (seedLaw n) :=
  integrable_of_bdd _ ((lamE_meas D ω t).comp clamp_meas) (RS D) (fun Y => by
    rw [abs_of_nonneg (lamE_nonneg D _ (fun j => (clamp_unit Y j).2) ω t)]
    exact lamE_le D _ (clamp_unit Y) ω t)

lemma int_lamP (ω : Outcome D) (t : Fin m) :
    Integrable (fun Y => lamP D (clamp Y) ω t) (seedLaw n) :=
  integrable_of_bdd _ ((lamP_meas D ω t).comp clamp_meas) (RS D) (fun Y => by
    rw [abs_of_nonneg (lamP_bounds D _ (clamp_unit Y) ω t).1]
    exact (lamP_bounds D _ (clamp_unit Y) ω t).2)

lemma int_thP (ω : Outcome D) (i : Fin n) :
    Integrable (fun Y => thP D (clamp Y) ω i) (seedLaw n) :=
  integrable_of_bdd _ ((thP_meas D ω i).comp clamp_meas) (m * D.reward i) (fun Y => by
    rw [abs_of_nonneg (thP_bounds D _ (clamp_unit Y) ω i).1]
    exact (thP_bounds D _ (clamp_unit Y) ω i).2)

/-! ### The dual solution (expected-score version of paper eq. (9)) -/

def lam (ω : Outcome D) (t : Fin m) : ℝ := seedAverage (fun Y => lamE D (clamp Y) ω t)

def th (ω : Outcome D) (i : Fin n) : ℝ := seedAverage (fun Y => thP D (clamp Y) ω i)

lemma lam_nonneg : ∀ ω t, 0 ≤ lam D ω t := fun ω t =>
  integral_nonneg fun Y => lamE_nonneg D _ (fun j => (clamp_unit Y j).2) ω t

lemma th_nonneg : ∀ ω i, 0 ≤ th D ω i := fun ω i =>
  integral_nonneg fun Y => (thP_bounds D _ (clamp_unit Y) ω i).1

lemma E_swap (F : Outcome D → Seeds n → ℝ) (hF : ∀ ω, Integrable (F ω) (seedLaw n)) :
    edgeAverage D (fun ω => seedAverage (F ω)) =
      seedAverage (fun Y => edgeAverage D (fun ω => F ω Y)) := by
  simp only [WD.E_def, seedAverage]
  rw [integral_finsetSum _ (fun ω _ => (hF ω).const_mul (pathWeight D ω))]
  exact Finset.sum_congr rfl fun ω _ => (integral_const_mul _ _).symm

/-- Dual objective = algorithm value (paper Lemma 3, averaged). -/
theorem partA : edgeAverage D (fun ω => ∑ t, lam D ω t + ∑ i, th D ω i) = algorithmValue D := by
  have h1 : ∀ ω, seedAverage (fun Y => algorithmReward D Y ω) =
      ∑ t, seedAverage (fun Y => lamP D (clamp Y) ω t) + ∑ i, th D ω i := by
    intro ω
    rw [← seedAverage_clamp (fun Y => algorithmReward D Y ω)]
    simp only [reward_split]
    unfold th seedAverage
    rw [integral_add (integrable_finsetSum _ fun t _ => int_lamP D ω t)
        (integrable_finsetSum _ fun i _ => int_thP D ω i),
      integral_finsetSum _ fun t _ => int_lamP D ω t, integral_finsetSum _ fun i _ => int_thP D ω i]
  unfold algorithmValue
  simp only [h1]
  rw [WD.E_add, WD.E_add]
  congr 1
  rw [E_fsum, E_fsum]
  apply Finset.sum_congr rfl
  intro t _
  unfold lam
  rw [E_swap D _ (fun ω => int_lamP D ω t), E_swap D _ (fun ω => int_lamE D ω t)]
  congr 1
  funext Y
  exact (E_lam D (clamp Y) t).symm

/-! ### Dual feasibility at an edge (paper Lemmas 4-6 and the calculus identity) -/

def Mval (Y0 : Seeds n) (ω1 : Outcome D) (i : Fin n) (t : Fin m) : ℝ :=
  (((algorithmRun D Y0 ω1 (Finset.univ.erase i) t.val).1).filter
    (fun z => (z, t) ∈ D.edges)).fold max 0 (fun z => score D Y0 t z)

lemma Mval_nonneg (Y0 : Seeds n) (ω1 : Outcome D) (i : Fin n) (t : Fin m) :
    0 ≤ Mval D Y0 ω1 i t := by
  unfold Mval; rw [Finset.le_fold_max]; exact Or.inl le_rfl

lemma ptwise (a : Fin n → ℝ) (b : Fin m → ℝ) (hb0 : ∀ t, 0 ≤ b t)
    (hab : ∀ e ∈ D.edges, D.probability e = a e.1 * b e.2)
    (ω1 : Outcome D) (hZ1 : ∀ f : Edge D, D.probability f.val = 0 → ω1 f = false)
    (i : Fin n) (t : Fin m) (hit : (i, t) ∈ D.edges) (hp : 0 < D.probability (i, t))
    (hbit : bit D ω1 (i, t) = true) (Y0 : Seeds n) (hY0 : U Y0) (y : ℝ)
    (hy : y ∈ Set.Icc (0:ℝ) 1) :
    Mval D Y0 ω1 i t ≤ lamE D (Function.update Y0 i y) ω1 t ∧
    (Mval D Y0 ω1 i t < score D (Function.update Y0 i y) t i →
      D.reward i * g y ≤ thP D (Function.update Y0 i y) ω1 i) := by
  have hY' : U (Function.update Y0 i y) := U_update Y0 hY0 i y hy
  have hrun : algorithmRun D Y0 ω1 (Finset.univ.erase i) t.val =
      algorithmRun D (Function.update Y0 i y) ω1 (Finset.univ.erase i) t.val :=
    run_congr_seed D Y0 _ ω1 _ (fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]) t.val
  have hsc : ∀ z ∈ (algorithmRun D Y0 ω1 (Finset.univ.erase i) t.val).1,
      score D (Function.update Y0 i y) t z = score D Y0 t z := by
    intro z hz
    have hzi : z ≠ i := Finset.ne_of_mem_erase (run_sub D Y0 ω1 _ t.val hz)
    simp only [score, Function.update_of_ne hzi]
  constructor
  · unfold Mval
    rw [Finset.fold_max_le]
    refine ⟨lamE_nonneg D _ (fun j => (hY' j).2) ω1 t, ?_⟩
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [← hsc z hz.1]
    have hz' : z ∈ (algorithmRun D (Function.update Y0 i y) ω1 (Finset.univ.erase i) t.val).1 := by
      rw [← hrun]; exact hz.1
    exact lamE_ge D a b hb0 hab _ ω1 hZ1 i t z hz' hz.2
  · intro hlt
    have hgy : g (Function.update Y0 i y i) = g y := by simp
    rw [← hgy]
    refine thP_ge D a b hb0 hab (Function.update Y0 i y) ω1 hZ1 i t hit hp hbit ?_
    intro z hz hzt
    rw [← hrun] at hz
    rw [hsc z hz]
    have hM : score D Y0 t z ≤ Mval D Y0 ω1 i t := by
      have h0 : Mval D Y0 ω1 i t ≤ Mval D Y0 ω1 i t := le_refl _
      unfold Mval at h0 ⊢
      rw [Finset.fold_max_le] at h0
      exact h0.2 z (Finset.mem_filter.mpr ⟨hz, hzt⟩)
    exact lt_of_le_of_lt hM hlt

set_option maxHeartbeats 1000000 in
theorem partB (a : Fin n → ℝ) (b : Fin m → ℝ) (hb0 : ∀ t, 0 ≤ b t)
    (hab : ∀ e ∈ D.edges, D.probability e = a e.1 * b e.2)
    (e : Edge D) (ω : Outcome D) (hZ : ∀ f : Edge D, D.probability f.val = 0 → ω f = false) :
    (1 - Real.exp (-1)) * D.probability e.val * D.reward e.val.1 ≤
      resample D e ω (fun ω' => lam D ω' e.val.2 + th D ω' e.val.1 * indicator ω' e) := by
  obtain ⟨⟨i, t⟩, hit⟩ := e
  dsimp only
  have hlam : ∀ bb, lam D (Function.update ω ⟨(i, t), hit⟩ bb) t = lam D ω t := by
    intro bb; unfold lam; congr 1; funext Y; exact lamE_update D (clamp Y) ω t _ rfl bb
  have hres : resample D ⟨(i, t), hit⟩ ω
      (fun ω' => lam D ω' t + th D ω' i * indicator ω' ⟨(i, t), hit⟩) =
      lam D ω t + D.probability (i, t) * th D (Function.update ω ⟨(i, t), hit⟩ true) i := by
    unfold resample
    simp only [hlam, indicator, Function.update_self, Bool.false_eq_true, if_false, if_true,
      mul_zero, mul_one, add_zero]
    ring
  rw [hres]
  have hp01 := D.probability_mem _ hit
  rcases hp01.1.lt_or_eq with hp | hp
  swap
  · rw [← hp]; simp only [mul_zero, zero_mul, add_zero]; exact lam_nonneg D ω t
  rw [← hlam true]
  set ω1 := Function.update ω ⟨(i, t), hit⟩ true with hω1
  have hZ1 : ∀ f : Edge D, D.probability f.val = 0 → ω1 f = false := by
    intro f hf
    by_cases hfe : f = ⟨(i, t), hit⟩
    · subst hfe; exact absurd hf hp.ne'
    · rw [hω1, Function.update_of_ne hfe]; exact hZ f hf
  have hbit : bit D ω1 (i, t) = true := by
    simp only [bit, dif_pos hit, hω1]; exact Function.update_self _ _ _
  set p := D.probability (i, t) with hpdef
  have hfeq : lam D ω1 t + p * th D ω1 i =
      seedAverage (fun Y => lamE D (clamp Y) ω1 t + p * thP D (clamp Y) ω1 i) := by
    unfold lam th seedAverage
    rw [integral_add (int_lamE D ω1 t) ((int_thP D ω1 i).const_mul p), integral_const_mul]
  rw [hfeq]
  apply tower _ (((lamE_meas D ω1 t).comp clamp_meas).add
      (((thP_meas D ω1 i).comp clamp_meas).const_mul p))
    (fun Y => add_nonneg (lamE_nonneg D _ (fun j => (clamp_unit Y j).2) ω1 t)
      (mul_nonneg hp.le (thP_bounds D _ (clamp_unit Y) ω1 i).1))
    (RS D + p * (m * D.reward i))
    (fun Y => add_le_add (lamE_le D _ (clamp_unit Y) ω1 t)
      (mul_le_mul_of_nonneg_left (thP_bounds D _ (clamp_unit Y) ω1 i).2 hp.le)) i
  intro Y
  have hY0 : U (clamp Y) := clamp_unit Y
  have key := calc5 (Mval D (clamp Y) ω1 i t) (p * D.reward i) (Mval_nonneg D _ _ _ _)
    (mul_nonneg hp.le (D.reward_nonneg i))
    (fun y => lamE D (clamp (Function.update Y i y)) ω1 t +
      p * thP D (clamp (Function.update Y i y)) ω1 i)
    (by
      intro y hy
      try dsimp only
      rw [clamp_update Y i y hy]
      have h1 := (ptwise D a b hb0 hab ω1 hZ1 i t hit hp hbit (clamp Y) hY0 y hy).1
      have h2 := (thP_bounds D _ (U_update _ hY0 i y hy) ω1 i).1
      nlinarith [mul_nonneg hp.le h2])
    (by
      intro y hy hlt
      try dsimp only
      rw [clamp_update Y i y hy]
      have hs : score D (Function.update (clamp Y) i y) t i = p * D.reward i * (1 - g y) := by
        simp [score, hpdef]
      have h1 := (ptwise D a b hb0 hab ω1 hZ1 i t hit hp hbit (clamp Y) hY0 y hy).1
      have h3 := (ptwise D a b hb0 hab ω1 hZ1 i t hit hp hbit (clamp Y) hY0 y hy).2
        (by rw [hs]; linarith)
      nlinarith [mul_le_mul_of_nonneg_left h3 hp.le])
  have e1 : (1 - Real.exp (-1)) * p * D.reward i = p * D.reward i * (1 - Real.exp (-1)) := by ring
  rw [e1]
  exact key

theorem part1 (n m : ℕ) (D : Instance n m) (hd : decomposable D) (ordered : Bool) :
    (1 - Real.exp (-1)) * benchmark D ordered ≤ algorithmValue D := by
  obtain ⟨a, b, _, hb, hab⟩ := hd
  have hα : 0 < 1 - Real.exp (-1) := by
    have h := Real.exp_lt_exp.mpr (show (-1:ℝ) < 0 by norm_num)
    rw [Real.exp_zero] at h; linarith
  have hwd := fun π => WD.weak_duality n m D ordered (1 - Real.exp (-1)) (lam D) (th D)
    (lam_nonneg D) (th_nonneg D) (fun e ω hZ => partB D a b hb hab e ω hZ) π
  unfold benchmark
  rw [mul_comm, ← le_div_iff₀ hα]
  apply csSup_le
  · exact ⟨_, ⟨fun _ => PMF.pure none, rfl⟩⟩
  · rintro _ ⟨π, rfl⟩
    rw [le_div_iff₀ hα, mul_comm]
    rw [← partA D]
    exact hwd π

end Asm


namespace KVV

/-! Part 2 of theorem_1: the Karp-Vazirani-Vazirani upper-triangular instance, averaged over all
relabellings of the resources. Resource `i` has rank `σ.symm i`; arrival `t` is adjacent to `i`
iff `t ≤ rank i`. Potential: `Ψ s x = lam * x / s + Cs s`. -/

def inst (n : ℕ) (σ : Equiv.Perm (Fin n)) : Instance n n where
  edges := Finset.univ.filter (fun e : Fin n × Fin n => e.2 ≤ σ.symm e.1)
  reward := fun _ => 1
  probability := fun _ => 1
  reward_nonneg := fun _ => zero_le_one
  probability_mem := fun _ _ => ⟨zero_le_one, le_rfl⟩

lemma mem_edges {n : ℕ} (σ : Equiv.Perm (Fin n)) (i t : Fin n) :
    (i, t) ∈ (inst n σ).edges ↔ t ≤ σ.symm i := by
  simp [inst]

lemma decomposable_inst (n : ℕ) (σ : Equiv.Perm (Fin n)) : decomposable (inst n σ) :=
  ⟨fun _ => 1, fun _ => 1, fun _ => zero_le_one, fun _ => zero_le_one, fun _ _ => by simp [inst]⟩

lemma pmf_sum_toReal {α : Type} [Fintype α] (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  have h1 : ∑ a, p a = 1 := by
    have := p.tsum_coe
    rwa [tsum_fintype] at this
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a), h1, ENNReal.toReal_one]

/-! ### Benchmark lower bound -/

lemma cont_le {n : ℕ} (σ : Equiv.Perm (Fin n)) (ordered : Bool) (π : RandPolicy n n) :
    ∀ (k : ℕ) (h : History n n), randomizedContinuation (inst n σ) ordered π k h ≤ k := by
  intro k
  induction k with
  | zero => intro h; simp [randomizedContinuation]
  | succ k ih =>
    intro h
    rw [randomizedContinuation]
    calc _ ≤ ∑ a : Option (Action n n), (π h a).toReal * ((k + 1 : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          rcases a with _ | ⟨t, _ | i⟩
          · dsimp only; positivity
          · dsimp only
            split_ifs
            · have e1 : actionProbability (inst n σ) (t, none) = 0 := rfl
              have e2 : actionReward (inst n σ) (t, none) = 0 := rfl
              rw [e1, e2]
              have := ih (h ++ [((t, none), false)]); push_cast; linarith
            · positivity
          · dsimp only
            split_ifs
            · have e1 : actionProbability (inst n σ) (t, some i) = 1 := rfl
              have e2 : actionReward (inst n σ) (t, some i) = 1 := rfl
              rw [e1, e2]
              have := ih (h ++ [((t, some i), true)]); push_cast; linarith
            · positivity
      _ = ((k + 1 : ℕ) : ℝ) := by rw [← Finset.sum_mul, pmf_sum_toReal, one_mul]

def diagPolicy (n : ℕ) (σ : Equiv.Perm (Fin n)) : RandPolicy n n := fun h =>
  if hl : h.length < n then PMF.pure (some (⟨h.length, hl⟩, some (σ ⟨h.length, hl⟩)))
  else PMF.pure none

def diagHist (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ → History n n
  | 0 => []
  | j + 1 => if hj : j < n then diagHist n σ j ++ [((⟨j, hj⟩, some (σ ⟨j, hj⟩)), true)]
      else diagHist n σ j

lemma diagHist_length {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∀ j, j ≤ n → (diagHist n σ j).length = j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih => intro hj; rw [diagHist, dif_pos (by omega)]; simp [ih (by omega)]

lemma diagHist_arr {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∀ j, j ≤ n → ∀ t : Fin n,
      t ∈ ((diagHist n σ j).map (fun z => z.1.1)).toFinset ↔ t.val < j := by
  intro j
  induction j with
  | zero => intro _ t; simp [diagHist]
  | succ j ih =>
    intro hj t
    rw [diagHist, dif_pos (by omega)]
    simp only [List.map_append, List.toFinset_append, Finset.mem_union, ih (by omega) t,
      List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
      Finset.notMem_empty, or_false, Fin.ext_iff]
    omega

lemma diagHist_res {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∀ j, j ≤ n → ∀ i : Fin n,
      i ∈ ((diagHist n σ j).filterMap (fun z => if z.2 then z.1.2 else none)).toFinset ↔
        (σ.symm i).val < j := by
  intro j
  induction j with
  | zero => intro _ i; simp [diagHist]
  | succ j ih =>
    intro hj i
    rw [diagHist, dif_pos (by omega)]
    simp only [List.filterMap_append, List.toFinset_append, Finset.mem_union, ih (by omega) i,
      List.filterMap_cons, List.filterMap_nil, if_true, List.toFinset_cons, List.toFinset_nil,
      Finset.mem_insert, Finset.notMem_empty, or_false]
    constructor
    · rintro (h | h)
      · omega
      · subst h; simp
    · intro h
      by_cases h' : (σ.symm i).val < j
      · exact Or.inl h'
      · right
        have : σ.symm i = ⟨j, by omega⟩ := Fin.ext (show (σ.symm i).val = j by omega)
        rw [← this]; simp

lemma diag_cont {n : ℕ} (σ : Equiv.Perm (Fin n)) (ordered : Bool) :
    ∀ k j, j + k = n →
      randomizedContinuation (inst n σ) ordered (diagPolicy n σ) k (diagHist n σ j) = k := by
  intro k
  induction k with
  | zero => intro j _; simp [randomizedContinuation]
  | succ k ih =>
    intro j hjk
    have hj : j < n := by omega
    have hlen : (diagHist n σ j).length = j := diagHist_length σ j (by omega)
    rw [randomizedContinuation]
    have hpol : diagPolicy n σ (diagHist n σ j) = PMF.pure (some (⟨j, hj⟩, some (σ ⟨j, hj⟩))) := by
      unfold diagPolicy; rw [dif_pos (by omega)]; simp only [hlen]
    rw [hpol, Finset.sum_eq_single (some (⟨j, hj⟩, some (σ ⟨j, hj⟩)))]
    · have hleg : ((⟨j, hj⟩ : Fin n), some (σ ⟨j, hj⟩)) ∈ legalActions (inst n σ) ordered
          (remainingResources (diagHist n σ j)) (remainingArrivals (diagHist n σ j)) := by
        simp only [legalActions, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [remainingArrivals, Finset.mem_sdiff, Finset.mem_univ, true_and,
            diagHist_arr σ j (by omega)]; simp
        · intro _ t ht
          simp only [remainingArrivals, Finset.mem_sdiff, Finset.mem_univ, true_and,
            diagHist_arr σ j (by omega)] at ht
          rw [Fin.le_def]; simp only; omega
        · simp only [remainingResources, Finset.mem_sdiff, Finset.mem_univ, true_and,
            diagHist_res σ j (by omega)]; simp
        · rw [mem_edges]; simp
      dsimp only
      rw [if_pos hleg]
      have hnext : diagHist n σ j ++ [((⟨j, hj⟩, some (σ ⟨j, hj⟩)), true)] = diagHist n σ (j + 1) := by
        rw [diagHist, dif_pos hj]
      rw [hnext, ih (j + 1) (by omega)]
      simp [actionProbability, actionReward, inst]
      ring
    · intro b _ hb
      rw [PMF.pure_apply, if_neg hb]; simp
    · intro h; exact absurd (Finset.mem_univ _) h

theorem benchmark_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) (ordered : Bool) :
    (n : ℝ) ≤ benchmark (inst n σ) ordered := by
  unfold benchmark
  have hb : BddAbove (Set.range (randomizedValue (inst n σ) ordered)) :=
    ⟨n, by rintro _ ⟨π, rfl⟩; exact cont_le σ ordered π n []⟩
  have h1 : randomizedValue (inst n σ) ordered (diagPolicy n σ) = n := by
    unfold randomizedValue
    have := diag_cont σ ordered n 0 (by omega)
    simpa [diagHist] using this
  rw [← h1]
  exact le_csSup hb ⟨_, rfl⟩


/-! ### Online upper bound -/

def comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ' => ∀ r : Fin n, r.val < t → σ' r = σ r)

def S {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => t ≤ (σ.symm i).val)

def Cs (lam : ℝ) : ℕ → ℝ
  | 0 => 0
  | s + 1 => Cs lam s + max 0 (1 - lam / ((s : ℝ) + 1))

def Ψ (lam : ℝ) (s : ℕ) (x : ℝ) : ℝ := lam * x / s + Cs lam s

lemma Cs_nonneg (lam : ℝ) : ∀ s, 0 ≤ Cs lam s := by
  intro s; induction s with
  | zero => simp [Cs]
  | succ s ih => simp only [Cs]; have := le_max_left 0 (1 - lam / ((s : ℝ) + 1)); linarith

lemma card_ge (n t : ℕ) : (Finset.univ.filter (fun r : Fin n => t ≤ r.val)).card = n - t := by
  have : (Finset.univ.filter (fun r : Fin n => t ≤ r.val)).map Fin.valEmbedding = Finset.Ico t n := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨r, hr, rfl⟩; exact ⟨hr, r.isLt⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, h2⟩, h1, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, this, Nat.card_Ico]

lemma card_S {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) : (S σ t).card = n - t := by
  have : S σ t = (Finset.univ.filter (fun r : Fin n => t ≤ r.val)).map σ.toEmbedding := by
    ext i
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    constructor
    · intro h; exact ⟨σ.symm i, h, by simp⟩
    · rintro ⟨r, hr, rfl⟩; simpa using hr
  rw [this, Finset.card_map, card_ge]

/-- agreement on ranks below `t` preserves every rank comparison with `s ≤ t`. -/
lemma rank_iff {n : ℕ} {σ σ' : Equiv.Perm (Fin n)} {t : ℕ} (hσ : σ' ∈ comp σ t)
    (i : Fin n) (s : ℕ) (hs : s ≤ t) : s ≤ (σ'.symm i).val ↔ s ≤ (σ.symm i).val := by
  simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  by_cases h1 : (σ'.symm i).val < t
  · have e := hσ _ h1
    rw [Equiv.apply_symm_apply] at e
    have : σ.symm i = σ'.symm i := by rw [Equiv.symm_apply_eq]; exact e
    rw [this]
  · by_cases h2 : (σ.symm i).val < t
    · exfalso
      have e := hσ _ h2
      rw [Equiv.apply_symm_apply] at e
      have : σ'.symm i = σ.symm i := by rw [Equiv.symm_apply_eq]; exact e.symm
      rw [this] at h1; exact h1 h2
    · omega

lemma S_eq_of_comp {n : ℕ} {σ σ' : Equiv.Perm (Fin n)} {t : ℕ} (hσ : σ' ∈ comp σ t) :
    S σ' t = S σ t := by
  ext i; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  exact rank_iff hσ i t le_rfl

lemma S_succ {n : ℕ} (ρ : Equiv.Perm (Fin n)) (t : ℕ) (ht : t < n) :
    S ρ (t + 1) = (S ρ t).erase (ρ ⟨t, ht⟩) := by
  ext i
  simp only [S, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨?_, by omega⟩
    rintro rfl; simp at h
  · rintro ⟨h1, h2⟩
    have : (ρ.symm i).val ≠ t := by
      intro e; apply h1
      have : ρ.symm i = ⟨t, ht⟩ := Fin.ext e
      rw [← this]; simp
    omega

def swapP {n : ℕ} (σ : Equiv.Perm (Fin n)) (τ : Fin n) (u : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.swap (σ τ) u * σ

lemma swapP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) (ht : t < n) (u : Fin n)
    (hu : u ∈ S σ t) (r : Fin n) (hr : r.val < t) : swapP σ ⟨t, ht⟩ u r = σ r := by
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  unfold swapP
  rw [Equiv.Perm.mul_apply]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro e; have := σ.injective e; rw [Fin.ext_iff] at this; simp at this; omega
  · intro e; rw [← e] at hu; simp at hu; omega

lemma fiber_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) (ht : t < n) (u : Fin n)
    (hu : u ∈ S σ t) :
    (comp σ t).filter (fun σ' => σ' ⟨t, ht⟩ = u) = comp (swapP σ ⟨t, ht⟩ u) (t + 1) := by
  ext σ'
  simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩ r hr
    by_cases hrt : r.val < t
    · rw [h1 r hrt, swapP_lt σ t ht u hu r hrt]
    · have : r = ⟨t, ht⟩ := Fin.ext (by simp only; omega)
      subst this
      rw [h2]; unfold swapP; simp
  · intro h
    refine ⟨fun r hr => ?_, ?_⟩
    · rw [h r (by omega), swapP_lt σ t ht u hu r hr]
    · rw [h ⟨t, ht⟩ (by simp)]; unfold swapP; simp

lemma maps_to {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) (ht : t < n) :
    ∀ σ' ∈ comp σ t, σ' ⟨t, ht⟩ ∈ S σ t := by
  intro σ' hσ
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hlt
  push_neg at hlt
  simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  have e := hσ _ hlt
  rw [Equiv.apply_symm_apply] at e
  have := σ'.injective e
  rw [Fin.ext_iff] at this; simp at this; omega

lemma sum_decomp {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) (ht : t < n)
    (f : Equiv.Perm (Fin n) → ℝ) :
    ∑ σ' ∈ comp σ t, f σ' = ∑ u ∈ S σ t, ∑ σ' ∈ comp (swapP σ ⟨t, ht⟩ u) (t + 1), f σ' := by
  rw [← Finset.sum_fiberwise_of_maps_to (maps_to σ t ht)]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [fiber_eq σ t ht u hu]

lemma swapP_mem {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) (ht : t < n) (u : Fin n)
    (hu : u ∈ S σ t) : swapP σ ⟨t, ht⟩ u ∈ comp σ t := by
  simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun r hr => swapP_lt σ t ht u hu r hr

lemma S_swapP {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) (ht : t < n) (u : Fin n)
    (hu : u ∈ S σ t) : S (swapP σ ⟨t, ht⟩ u) (t + 1) = (S σ t).erase u := by
  rw [S_succ _ t ht, S_eq_of_comp (swapP_mem σ t ht u hu)]
  congr 1; unfold swapP; simp

lemma card_comp {n : ℕ} : ∀ k t, t + k = n → ∀ σ : Equiv.Perm (Fin n),
    (comp σ t).card = k.factorial := by
  intro k
  induction k with
  | zero =>
    intro t htk σ
    have : comp σ t = {σ} := by
      ext σ'
      simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; ext r; rw [h r (by omega)]
      · rintro rfl _ _; rfl
    rw [this]; simp
  | succ k ih =>
    intro t htk σ
    have ht : t < n := by omega
    have := sum_decomp σ t ht (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
    have h2 : ∀ u ∈ S σ t, ((comp (swapP σ ⟨t, ht⟩ u) (t + 1)).card : ℝ) = k.factorial := by
      intro u _; rw [ih (t + 1) (by omega)]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, card_S, nsmul_eq_mul] at this
    have h3 : n - t = k + 1 := by omega
    rw [h3] at this
    rw [Nat.factorial_succ]; exact_mod_cast this

lemma rem_none {n m : ℕ} (h : History n m) (τ : Fin m) :
    remainingResources (h ++ [((τ, none), false)]) = remainingResources h := by
  simp [remainingResources, List.filterMap_append]

lemma rem_some {n m : ℕ} (h : History n m) (τ : Fin m) (i : Fin n) :
    remainingResources (h ++ [((τ, some i), true)]) = (remainingResources h).erase i := by
  ext j
  simp only [remainingResources, List.filterMap_append, List.toFinset_append, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_erase, List.filterMap_cons,
    if_true, List.filterMap_nil, List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
    Finset.notMem_empty, or_false]
  tauto

lemma sum_card_erase {α : Type} [DecidableEq α] (S X : Finset α) :
    ∑ u ∈ S, (((S.erase u) ∩ X).card : ℝ) = ((S.card : ℝ) - 1) * (S ∩ X).card := by
  have h1 : ∀ u ∈ S, (((S.erase u) ∩ X).card : ℝ) =
      ((S ∩ X).card : ℝ) - (if u ∈ S ∩ X then 1 else 0) := by
    intro u _
    rw [Finset.erase_inter, Finset.card_erase_eq_ite]
    split_ifs with h
    · have : 1 ≤ (S ∩ X).card := Finset.card_pos.mpr ⟨u, h⟩
      push_cast [Nat.cast_sub this]; ring
    · simp
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_boole, Finset.filter_mem_eq_inter, ← Finset.inter_assoc, Finset.inter_self]
  ring

lemma reveal_eq {n : ℕ} {σ σ' : Equiv.Perm (Fin n)} {t : ℕ} (hσ : σ' ∈ comp σ t)
    (τ : Fin n) (hτ : τ.val = t) : reveal (inst n σ') τ = reveal (inst n σ) τ := by
  funext s
  unfold reveal
  by_cases hs : s ≤ τ
  · simp only [hs, if_true]
    congr 1; funext i
    have : (i, s) ∈ (inst n σ').edges ↔ (i, s) ∈ (inst n σ).edges := by
      rw [mem_edges, mem_edges, Fin.le_def, Fin.le_def]
      exact rank_iff hσ i s.val (by rw [Fin.le_def] at hs; omega)
    by_cases he : (i, s) ∈ (inst n σ).edges
    · rw [if_pos (this.mpr he), if_pos he]; rfl
    · rw [if_neg (fun h => he (this.mp h)), if_neg he]
  · simp only [hs, if_false]


lemma Ψ_nonneg (lam : ℝ) (hlam : 0 ≤ lam) (s : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Ψ lam s x := by
  unfold Ψ; have := Cs_nonneg lam s; have : 0 ≤ lam * x / s := by positivity
  linarith

lemma cont_succ_eq {n : ℕ} {σ σ' : Equiv.Perm (Fin n)} {t : ℕ} (hσ : σ' ∈ comp σ t) (ht : t < n)
    (A : OnlineRule n n) (k : ℕ) (h : History n n) :
    onlineContinuation (inst n σ') A (k + 1) t h =
      ∑ a : Option (Fin n), (A (fun _ => 1) ⟨t, ht⟩ (reveal (inst n σ) ⟨t, ht⟩) h a).toReal *
        (match a with
         | none => onlineContinuation (inst n σ') A k (t + 1) (h ++ [((⟨t, ht⟩, none), false)])
         | some i => if i ∈ remainingResources h ∧ i ∈ S σ t then
              1 + onlineContinuation (inst n σ') A k (t + 1) (h ++ [((⟨t, ht⟩, some i), true)])
            else onlineContinuation (inst n σ') A k (t + 1) (h ++ [((⟨t, ht⟩, none), false)])) := by
  rw [onlineContinuation, dif_pos ht]
  simp only []
  rw [reveal_eq hσ ⟨t, ht⟩ rfl]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rcases a with _ | i
  · rfl
  · have hiff : (i, (⟨t, ht⟩ : Fin n)) ∈ (inst n σ').edges ↔ i ∈ S σ t := by
      rw [mem_edges, ← S_eq_of_comp hσ]; simp [S, Fin.le_def]
    simp only [hiff]
    split_ifs <;> simp [inst]

set_option maxHeartbeats 1000000 in
theorem main_bound {n : ℕ} (A : OnlineRule n n) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∀ k t : ℕ, t + k = n → ∀ (σ : Equiv.Perm (Fin n)) (h : History n n),
      ∑ σ' ∈ comp σ t, onlineContinuation (inst n σ') A k t h ≤
        (k.factorial : ℝ) * Ψ lam k ((S σ t ∩ remainingResources h).card) := by
  intro k
  induction k with
  | zero =>
    intro t _ σ h
    simp [onlineContinuation, Ψ, Cs]
  | succ k ih =>
    intro t htk σ h
    have ht : t < n := by omega
    have hcardS : ((S σ t).card : ℝ) = k + 1 := by
      rw [card_S]; have : n - t = k + 1 := by omega
      rw [this]; push_cast; ring
    have hΨ : ∀ x, Ψ lam k x = lam / k * x + Cs lam k := fun x => by unfold Ψ; ring
    have hnext : ∀ h' : History n n,
        ∑ σ' ∈ comp σ t, onlineContinuation (inst n σ') A k (t + 1) h' ≤
          (k.factorial : ℝ) * (lam * ((S σ t ∩ remainingResources h').card) +
            (k + 1) * Cs lam k) := by
      intro h'
      rw [sum_decomp σ t ht]
      have hy : (0 : ℝ) ≤ ((S σ t ∩ remainingResources h').card) := Nat.cast_nonneg _
      calc _ ≤ ∑ u ∈ S σ t, (k.factorial : ℝ) *
              Ψ lam k (((S σ t).erase u ∩ remainingResources h').card) := by
            refine Finset.sum_le_sum fun u hu => ?_
            have := ih (t + 1) (by omega) (swapP σ ⟨t, ht⟩ u) h'
            rwa [S_swapP σ t ht u hu] at this
        _ = (k.factorial : ℝ) * (lam / k * ((k : ℝ) * ((S σ t ∩ remainingResources h').card)) +
              (k + 1) * Cs lam k) := by
            simp only [hΨ]
            rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, sum_card_erase,
              Finset.sum_const, nsmul_eq_mul, hcardS]
            ring
        _ ≤ _ := by
            have hle : lam / k * ((k : ℝ) * ((S σ t ∩ remainingResources h').card)) ≤
                lam * ((S σ t ∩ remainingResources h').card) := by
              rcases eq_or_ne (k : ℝ) 0 with hk | hk
              · rw [hk]; simp; positivity
              · rw [← mul_assoc, div_mul_cancel₀ _ hk]
            exact mul_le_mul_of_nonneg_left (add_le_add hle le_rfl) (Nat.cast_nonneg _)
    have hR : ((k + 1).factorial : ℝ) * Ψ lam (k + 1) ((S σ t ∩ remainingResources h).card) =
        (k.factorial : ℝ) * (lam * ((S σ t ∩ remainingResources h).card) +
          (k + 1) * Cs lam (k + 1)) := by
      unfold Ψ; push_cast [Nat.factorial_succ]; field_simp
    have hCs : Cs lam (k + 1) = Cs lam k + max 0 (1 - lam / ((k : ℝ) + 1)) := rfl
    have hfac : (0 : ℝ) ≤ k.factorial := Nat.cast_nonneg _
    -- skip bound
    have hskip : ∑ σ' ∈ comp σ t, onlineContinuation (inst n σ') A k (t + 1)
        (h ++ [((⟨t, ht⟩, none), false)]) ≤
        ((k + 1).factorial : ℝ) * Ψ lam (k + 1) ((S σ t ∩ remainingResources h).card) := by
      refine (hnext _).trans ?_
      rw [hR, rem_none]
      have := le_max_left 0 (1 - lam / ((k : ℝ) + 1))
      have hk1 : (0 : ℝ) ≤ k + 1 := by positivity
      gcongr
      rw [hCs]; linarith
    rw [Finset.sum_congr rfl fun σ' hσ' => cont_succ_eq hσ' ht A k h, Finset.sum_comm]
    simp only [← Finset.mul_sum]
    calc _ ≤ ∑ a : Option (Fin n),
            (A (fun _ => 1) ⟨t, ht⟩ (reveal (inst n σ) ⟨t, ht⟩) h a).toReal *
              (((k + 1).factorial : ℝ) * Ψ lam (k + 1) ((S σ t ∩ remainingResources h).card)) := by
          refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          rcases a with _ | i
          · exact hskip
          · by_cases hc : i ∈ remainingResources h ∧ i ∈ S σ t
            · simp only [hc, and_self, if_true]
              rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
                card_comp (k + 1) t htk σ]
              refine (add_le_add le_rfl (hnext _)).trans ?_
              rw [hR, rem_some, Finset.inter_erase, Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hc.2, hc.1⟩)]
              have h1 : 1 ≤ (S σ t ∩ remainingResources h).card :=
                Finset.card_pos.mpr ⟨i, Finset.mem_inter.mpr ⟨hc.2, hc.1⟩⟩
              push_cast [Nat.cast_sub h1, Nat.factorial_succ]
              rw [hCs]
              have hm := le_max_right 0 (1 - lam / ((k : ℝ) + 1))
              have hk1 : (0 : ℝ) < k + 1 := by positivity
              have e1 : ((k : ℝ) + 1) * (1 - lam / ((k : ℝ) + 1)) = k + 1 - lam := by
                field_simp
              have e2 : ((k : ℝ) + 1) * (1 - lam / ((k : ℝ) + 1)) ≤
                  ((k : ℝ) + 1) * max 0 (1 - lam / ((k : ℝ) + 1)) :=
                mul_le_mul_of_nonneg_left hm hk1.le
              nlinarith
            · simp only [hc, if_false]
              exact hskip
      _ = _ := by rw [← Finset.sum_mul, pmf_sum_toReal, one_mul]

/-! ### The numeric bound on `Cs` -/

def G (lam x : ℝ) : ℝ := if x ≤ lam then 0 else x - lam - lam * Real.log (x / lam)

lemma G_nonneg (lam : ℝ) (hlam : 0 ≤ lam) (x : ℝ) : 0 ≤ G lam x := by
  unfold G
  split_ifs with h
  · exact le_rfl
  · push_neg at h
    rcases eq_or_lt_of_le hlam with h0 | h0
    · subst h0; simp; linarith
    · have := Real.log_le_sub_one_of_pos (div_pos (h0.trans h) h0)
      have h2 : lam * Real.log (x / lam) ≤ lam * (x / lam - 1) := mul_le_mul_of_nonneg_left this hlam
      rw [mul_sub, mul_div_cancel₀ _ h0.ne'] at h2
      linarith

lemma G_step (lam : ℝ) (hlam : 0 ≤ lam) (j : ℝ) (hj : 1 ≤ j) :
    max 0 (1 - lam / j) ≤ G lam (j + 1) - G lam j := by
  have hj0 : 0 < j := by linarith
  by_cases hA : j ≤ lam
  · have hGj : G lam j = 0 := by unfold G; rw [if_pos hA]
    have hneg : 1 - lam / j ≤ 0 := by
      have : 1 ≤ lam / j := by rw [le_div_iff₀ hj0]; linarith
      linarith
    rw [max_eq_left hneg, hGj, sub_zero]
    exact G_nonneg lam hlam _
  · push_neg at hA
    have hGj : G lam j = j - lam - lam * Real.log (j / lam) := by unfold G; rw [if_neg (by linarith)]
    have hGj1 : G lam (j + 1) = j + 1 - lam - lam * Real.log ((j + 1) / lam) := by
      unfold G; rw [if_neg (by linarith)]
    have key : lam * (Real.log ((j + 1) / lam) - Real.log (j / lam)) ≤ lam / j := by
      rcases eq_or_lt_of_le hlam with h0 | h0
      · subst h0; simp
      · rw [← Real.log_div (by positivity) (by positivity)]
        have e : (j + 1) / lam / (j / lam) = 1 + 1 / j := by field_simp
        rw [e]
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / j by positivity)
        have h3 : lam * Real.log (1 + 1 / j) ≤ lam * (1 + 1 / j - 1) :=
          mul_le_mul_of_nonneg_left this hlam
        have e2 : lam * (1 + 1 / j - 1) = lam / j := by rw [add_sub_cancel_left, mul_one_div]
        linarith
    have hpos : 0 ≤ 1 - lam / j := by
      have : lam / j < 1 := by rw [div_lt_one hj0]; exact hA
      linarith
    rw [max_eq_right hpos, hGj, hGj1]
    nlinarith

lemma Cs_le_G (lam : ℝ) (hlam : 0 ≤ lam) : ∀ s : ℕ, Cs lam s ≤ G lam ((s : ℝ) + 1) - G lam 1 := by
  intro s
  induction s with
  | zero => simp [Cs]
  | succ s ih =>
    have := G_step lam hlam ((s : ℝ) + 1) (by have := (Nat.cast_nonneg s : (0 : ℝ) ≤ s); linarith)
    simp only [Cs]
    push_cast
    linarith

lemma Ψ_nn_le (n : ℕ) (hn : 0 < n) :
    Ψ ((n : ℝ) * Real.exp (-1)) n n ≤ (1 - Real.exp (-1)) * n + 1 := by
  set lam := (n : ℝ) * Real.exp (-1) with hlam_def
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  have he1 : Real.exp (-1) < 1 := by
    have := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num); rwa [Real.exp_zero] at this
  have hlam : 0 < lam := by positivity
  have hΨ : Ψ lam n n = lam + Cs lam n := by
    unfold Ψ; rw [mul_div_assoc, div_self hn'.ne', mul_one]
  have hC := Cs_le_G lam hlam.le n
  have hG1 := G_nonneg lam hlam.le 1
  have hlt : ¬ ((n : ℝ) + 1 ≤ lam) := by
    push_neg; have : lam < n := by rw [hlam_def]; nlinarith
    linarith
  have hGn : G lam ((n : ℝ) + 1) = (n : ℝ) + 1 - lam - lam * Real.log (((n : ℝ) + 1) / lam) := by
    unfold G; rw [if_neg hlt]
  have hlog : 1 ≤ Real.log (((n : ℝ) + 1) / lam) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    rw [le_div_iff₀ hlam, hlam_def, ← mul_assoc, mul_comm (Real.exp 1), mul_assoc,
      ← Real.exp_add]
    norm_num
  have : lam * 1 ≤ lam * Real.log (((n : ℝ) + 1) / lam) := mul_le_mul_of_nonneg_left hlog hlam.le
  rw [hΨ]
  have : (1 - Real.exp (-1)) * n = n - lam := by rw [hlam_def]; ring
  linarith

theorem online_exists {n : ℕ} (hn : 0 < n) (A : OnlineRule n n) :
    ∃ σ : Equiv.Perm (Fin n), onlineValue (inst n σ) A ≤ (1 - Real.exp (-1)) * n + 1 := by
  set lam := (n : ℝ) * Real.exp (-1)
  have hlam : 0 ≤ lam := by positivity
  have hmain := main_bound A lam hlam n 0 (by omega) 1 []
  have hcomp : comp (1 : Equiv.Perm (Fin n)) 0 = Finset.univ := by
    ext σ; simp [comp]
  have hS : (S (1 : Equiv.Perm (Fin n)) 0 ∩ remainingResources ([] : History n n)).card = n := by
    have : S (1 : Equiv.Perm (Fin n)) 0 ∩ remainingResources ([] : History n n) = Finset.univ := by
      ext i; simp [S, remainingResources]
    rw [this, Finset.card_univ, Fintype.card_fin]
  rw [hcomp, hS] at hmain
  have hB := Ψ_nn_le n hn
  have hsum : ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), onlineValue (inst n σ) A ≤
      ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), ((1 - Real.exp (-1)) * n + 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _))
    simpa [onlineValue] using hmain
  obtain ⟨σ, _, hσ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨σ, hσ⟩

theorem part2 : ∀ (ε : ℝ), 0 < ε → ∀ A : OnlineFamily,
      ∃ (n m : ℕ) (D : Instance n m), decomposable D ∧
        0 < benchmark D true ∧ 0 < benchmark D false ∧
        onlineValue D (A n m) ≤ (1 - Real.exp (-1) + ε) * benchmark D true ∧
        onlineValue D (A n m) ≤ (1 - Real.exp (-1) + ε) * benchmark D false := by
  intro ε hε A
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hn : 0 < N + 1 := Nat.succ_pos N
  obtain ⟨σ, hσ⟩ := online_exists hn (A (N + 1) (N + 1))
  have he1 : Real.exp (-1) < 1 := by
    have := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num); rwa [Real.exp_zero] at this
  have hn' : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; have := (Nat.cast_nonneg N : (0:ℝ) ≤ N); linarith
  have hkey : (1 - Real.exp (-1)) * ((N + 1 : ℕ) : ℝ) + 1 ≤
      (1 - Real.exp (-1) + ε) * ((N + 1 : ℕ) : ℝ) := by
    have : 1 ≤ ε * ((N + 1 : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hε] at hN; push_cast; nlinarith
    nlinarith
  have hc : 0 ≤ 1 - Real.exp (-1) + ε := by linarith
  have hbt := benchmark_ge σ true
  have hbf := benchmark_ge σ false
  refine ⟨N + 1, N + 1, inst (N + 1) σ, decomposable_inst _ σ, by linarith, by linarith, ?_, ?_⟩
  · exact hσ.trans (hkey.trans (mul_le_mul_of_nonneg_left hbt hc))
  · exact hσ.trans (hkey.trans (mul_le_mul_of_nonneg_left hbf hc))
end KVV

end StochasticRewardMatching.Decomposable

open StochasticRewardMatching.Decomposable in
theorem solution :
    (∀ (n m : ℕ) (D : Instance n m), decomposable D →
      (1 - Real.exp (-1)) * benchmark D true ≤ algorithmValue D ∧
      (1 - Real.exp (-1)) * benchmark D false ≤ algorithmValue D) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ A : OnlineFamily,
      ∃ (n m : ℕ) (D : Instance n m), decomposable D ∧
        0 < benchmark D true ∧ 0 < benchmark D false ∧
        onlineValue D (A n m) ≤ (1 - Real.exp (-1) + ε) * benchmark D true ∧
        onlineValue D (A n m) ≤ (1 - Real.exp (-1) + ε) * benchmark D false) := by
  exact ⟨fun n m D hd => ⟨Asm.part1 n m D hd true, Asm.part1 n m D hd false⟩, KVV.part2⟩

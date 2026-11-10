-- Prove2me | solution 1 for SmartExpediteAudit.PolicyM.theorem_1_full
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T10:18:03.407302+00:00
-- url     : https://prove2.me/submissions/040ea887-1952-47ee-8f12-eab7b9eeb56d

import Mathlib
import Definitions.Def_SmartExpediteAudit_PolicyM_Transient
import Theorems.Thm_SmartExpedite_PolicyM_theorem_1
import Theorems.Thm_SmartExpediteAudit_lazy_chain_tendsto_stationary
import Theorems.Thm_SmartExpediteAudit_PolicyM_transient_semigroup
import Theorems.Thm_SmartExpediteAudit_PolicyM_transient_generator

set_option autoImplicit false

open Filter SmartExpedite.PolicyM
open scoped Topology NNReal

namespace SEFull

open SmartExpediteAudit.PolicyM MarkovMixing

section Generic

variable {V : Type*} [Countable V] [DecidableEq V]

lemma hasSum_swap {ι W : Type*} {f : ι × W → ℝ} {a : ℝ} (h : HasSum f a) :
    HasSum (fun p : W × ι => f p.swap) a := by
  have h2 := (Equiv.prodComm W ι).hasSum_iff.2 h
  exact h2

lemma rowmix {ι W : Type*} (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw : HasSum w 1) (Q : ι → W → ℝ) (hQ0 : ∀ i y, 0 ≤ Q i y) (hQ : ∀ i, HasSum (Q i) 1) :
    HasSum (fun y => ∑' i, w i * Q i y) 1 := by
  have hrow : ∀ i, HasSum (fun y => w i * Q i y) (w i) := fun i => by
    have h := (hQ i).mul_left (w i)
    rwa [mul_one] at h
  have hG0 : (0 : ι × W → ℝ) ≤ fun p => w p.1 * Q p.1 p.2 :=
    Pi.le_def.2 (fun p => by simp only [Pi.zero_apply]; exact mul_nonneg (hw0 _) (hQ0 _ _))
  have hGs : Summable (fun p : ι × W => w p.1 * Q p.1 p.2) := by
    refine (summable_prod_of_nonneg hG0).2 ⟨fun i => (hrow i).summable, ?_⟩
    have h : (fun i => ∑' y, w i * Q i y) = w := funext fun i => (hrow i).tsum_eq
    rw [h]; exact hw.summable
  have hG1 : HasSum (fun p : ι × W => w p.1 * Q p.1 p.2) 1 := by
    have h := hGs.hasSum.prod_fiberwise hrow
    rw [hw.unique h]; exact hGs.hasSum
  refine (hasSum_swap hG1).prod_fiberwise (fun y => ?_)
  exact (Summable.of_nonneg_of_le (fun i => mul_nonneg (hw0 i) (hQ0 i y))
    (fun i => mul_le_of_le_one_right (hw0 i) (le_hasSum (hQ i) y (fun j _ => hQ0 i j)))
    hw.summable).hasSum

lemma stoch_le_one {P : V → V → ℝ} (hP : IsStochasticC P) (x y : V) : P x y ≤ 1 :=
  le_hasSum (hP.2 x) y (fun j _ => hP.1 x j)

lemma stoch_comp {A B : V → V → ℝ} (hA : IsStochasticC A) (hB : IsStochasticC B) :
    IsStochasticC (fun x y => ∑' z, A x z * B z y) :=
  ⟨fun x y => tsum_nonneg (fun z => mul_nonneg (hA.1 x z) (hB.1 z y)),
   fun x => rowmix (A x) (hA.1 x) (hA.2 x) B hB.1 hB.2⟩

lemma stepPow_succ (P : V → V → ℝ) (r : ℕ) (x y : V) :
    stepPow P (r + 1) x y = ∑' z, stepPow P r x z * P z y := rfl

lemma stepPow_zero (P : V → V → ℝ) (x y : V) :
    stepPow P 0 x y = if y = x then 1 else 0 := rfl

lemma stepPow_one (P : V → V → ℝ) (x n : V) : stepPow P 1 x n = P x n := by
  rw [stepPow_succ, tsum_eq_single x (fun z hz => by rw [stepPow_zero, if_neg hz, zero_mul])]
  rw [stepPow_zero, if_pos rfl, one_mul]

lemma stoch_stepPow {P : V → V → ℝ} (hP : IsStochasticC P) (r : ℕ) :
    IsStochasticC (stepPow P r) := by
  induction r with
  | zero =>
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · rw [stepPow_zero]; split_ifs <;> norm_num
    · show HasSum (fun y => if y = x then (1 : ℝ) else 0) 1
      exact hasSum_ite_eq x (1 : ℝ)
  | succ r ih => exact stoch_comp ih hP

lemma tsum_assoc3 {P : V → V → ℝ} (hP : IsStochasticC P) (a : V → ℝ) (ha0 : ∀ y, 0 ≤ a y)
    (ha : Summable a) (g : V → ℝ) (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1) :
    ∑' z, (∑' y, a y * P y z) * g z = ∑' y, a y * ∑' z, P y z * g z := by
  have hf0 : ∀ y z, 0 ≤ a y * P y z * g z := fun y z =>
    mul_nonneg (mul_nonneg (ha0 y) (hP.1 y z)) (hg0 z)
  have hfle : ∀ y z, a y * P y z * g z ≤ a y * P y z := fun y z =>
    mul_le_of_le_one_right (mul_nonneg (ha0 y) (hP.1 y z)) (hg1 z)
  have hrow : ∀ y, Summable (fun z => a y * P y z) := fun y => (hP.2 y).summable.mul_left _
  have hsum : Summable (Function.uncurry fun y z => a y * P y z * g z) := by
    have h2 : Summable (fun p : V × V => a p.1 * P p.1 p.2) := by
      rw [summable_prod_of_nonneg (fun p => mul_nonneg (ha0 _) (hP.1 _ _))]
      refine ⟨hrow, ?_⟩
      have : (fun y => ∑' z, a y * P y z) = a := by
        funext y; rw [tsum_mul_left, (hP.2 y).tsum_eq, mul_one]
      rw [this]; exact ha
    exact Summable.of_nonneg_of_le (fun p => hf0 p.1 p.2) (fun p => hfle p.1 p.2) h2
  have h1 : ∀ y, Summable (fun z => a y * P y z * g z) := fun y =>
    Summable.of_nonneg_of_le (hf0 y) (hfle y) (hrow y)
  have h2 : ∀ z, Summable (fun y => a y * P y z * g z) := fun z =>
    Summable.of_nonneg_of_le (fun y => hf0 y z)
      (fun y => (hfle y z).trans (mul_le_of_le_one_right (ha0 y) (stoch_le_one hP y z))) ha
  calc ∑' z, (∑' y, a y * P y z) * g z = ∑' z, ∑' y, a y * P y z * g z := by
        congr 1; funext z; rw [tsum_mul_right]
    _ = ∑' y, ∑' z, a y * P y z * g z := hsum.tsum_comm' h1 h2
    _ = ∑' y, a y * ∑' z, P y z * g z := by
        congr 1; funext y; rw [← tsum_mul_left]; congr 1; funext z; ring

/-- Chapman–Kolmogorov for the step powers. -/
lemma stepPow_add {P : V → V → ℝ} (hP : IsStochasticC P) (a b : ℕ) (x n : V) :
    stepPow P (a + b) x n = ∑' y, stepPow P a x y * stepPow P b y n := by
  induction b generalizing n with
  | zero =>
    have : (fun y => stepPow P a x y * stepPow P 0 y n) =
        fun y => if y = n then stepPow P a x n else 0 := by
      funext y
      rw [stepPow_zero]
      by_cases h : y = n
      · subst h; simp
      · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
    rw [this, tsum_ite_eq]; rfl
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 from rfl, stepPow_succ]
    simp_rw [ih]
    rw [tsum_assoc3 (stoch_stepPow hP b) (stepPow P a x) (fun y => (stoch_stepPow hP a).1 x y)
      ((stoch_stepPow hP a).2 x).summable (fun z => P z n) (fun z => hP.1 z n)
      (fun z => stoch_le_one hP z n)]
    rfl

end Generic

section Model

variable {K : ℕ} {u : ℕ → ℕ → ℕ∞} {lam : ℝ} {mu : ℕ → ℝ}

lemma rate_nonneg (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (a b : Fin K → ℕ) : 0 ≤ rate K u lam mu a b := by
  unfold rate
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · split_ifs <;> linarith
  · refine Finset.sum_nonneg (fun m hm => ?_)
    rw [Finset.mem_Icc] at hm
    split_ifs
    · exact (hmu m hm.1 (by omega)).le
    · exact le_rfl
  · split_ifs
    · exact (hmu K hK le_rfl).le
    · exact le_rfl

lemma rate_hasSum (hK : 1 ≤ K) (a : Fin K → ℕ) :
    HasSum (rate K u lam mu a) (outRate K lam mu a) := by
  have h1 : HasSum (fun b : Fin K → ℕ => if b = a + ev K (arrNode K u a) then lam else 0) lam :=
    hasSum_ite_eq _ _
  have h2 : HasSum (fun b : Fin K → ℕ => ∑ m ∈ Finset.Icc 1 (K - 1),
      if 0 < occ a m ∧ b = a - ev K m + ev K (expNode K u m a) then mu m else 0)
      (∑ m ∈ Finset.Icc 1 (K - 1), if 0 < occ a m then mu m else 0) := by
    refine hasSum_sum (fun m _ => ?_)
    by_cases h : 0 < occ a m
    · simpa [h] using hasSum_ite_eq (a - ev K m + ev K (expNode K u m a)) (mu m)
    · simpa [h] using (hasSum_zero : HasSum (fun _ : Fin K → ℕ => (0 : ℝ)) 0)
  have h3 : HasSum (fun b : Fin K → ℕ => if 0 < occ a K ∧ b = a - ev K K then mu K else 0)
      (if 0 < occ a K then mu K else 0) := by
    by_cases h : 0 < occ a K
    · simpa [h] using hasSum_ite_eq (a - ev K K) (mu K)
    · simpa [h] using (hasSum_zero : HasSum (fun _ : Fin K → ℕ => (0 : ℝ)) 0)
  have := (h1.add h2).add h3
  convert this using 1
  · rfl
  unfold outRate
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp only [Nat.add_sub_cancel]
  ring

lemma sumMu_nonneg (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k) :
    0 ≤ ∑ k ∈ Finset.Icc 1 K, mu k :=
  Finset.sum_nonneg (fun k hk => by rw [Finset.mem_Icc] at hk; exact (hmu k hk.1 hk.2).le)

lemma outRate_le (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k) (a : Fin K → ℕ) :
    outRate K lam mu a ≤ lam + ∑ k ∈ Finset.Icc 1 K, mu k := by
  unfold outRate
  have : ∑ k ∈ Finset.Icc 1 K, (if 0 < occ a k then mu k else 0) ≤
      ∑ k ∈ Finset.Icc 1 K, mu k :=
    Finset.sum_le_sum (fun k hk => by
      rw [Finset.mem_Icc] at hk
      split_ifs
      · exact le_rfl
      · exact (hmu k hk.1 hk.2).le)
  linarith

lemma clock_pos (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k) :
    0 < clockRate K lam mu := by
  unfold clockRate; have := sumMu_nonneg hmu; linarith

lemma rate_le_clock (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (a b : Fin K → ℕ) : rate K u lam mu a b ≤ clockRate K lam mu := by
  have h1 := le_hasSum (rate_hasSum (u := u) (lam := lam) (mu := mu) hK a) b
    (fun j _ => rate_nonneg hK hlam hmu a j)
  have h2 := outRate_le (lam := lam) hmu a
  have h3 := sumMu_nonneg hmu
  unfold clockRate; linarith

lemma uniformStep_stoch (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k) :
    IsStochasticC (uniformStep K u lam mu) := by
  have hc := clock_pos hlam hmu
  have hle : ∀ a, outRate K lam mu a / clockRate K lam mu ≤ 1 / 2 := fun a => by
    rw [div_le_iff₀ hc]
    have := outRate_le (lam := lam) hmu a
    unfold clockRate; linarith
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · unfold uniformStep
    have h1 := div_nonneg (rate_nonneg (u := u) hK hlam hmu x y) hc.le
    split_ifs
    · linarith [hle x]
    · linarith
  · have h1 := (rate_hasSum (u := u) (lam := lam) (mu := mu) hK x).div_const (clockRate K lam mu)
    have h2 : HasSum (fun y : Fin K → ℕ =>
        if x = y then 1 - outRate K lam mu x / clockRate K lam mu else 0)
        (1 - outRate K lam mu x / clockRate K lam mu) := by
      have := hasSum_ite_eq x (1 - outRate K lam mu x / clockRate K lam mu)
      convert this using 2 with y
      by_cases h : y = x
      · subst h; simp
      · rw [if_neg (Ne.symm h), if_neg h]
    have h3 := h1.add h2
    rw [show outRate K lam mu x / clockRate K lam mu +
      (1 - outRate K lam mu x / clockRate K lam mu) = 1 by ring] at h3
    exact h3

lemma uniformStep_diag (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (x : Fin K → ℕ) : 1 / 2 ≤ uniformStep K u lam mu x x := by
  have hc := clock_pos hlam hmu
  have hle : outRate K lam mu x / clockRate K lam mu ≤ 1 / 2 := by
    rw [div_le_iff₀ hc]
    have := outRate_le (lam := lam) hmu x
    unfold clockRate; linarith
  unfold uniformStep
  rw [if_pos rfl]
  have h1 := div_nonneg (rate_nonneg (u := u) hK hlam hmu x x) hc.le
  linarith

lemma poissonMass_nonneg (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (t : ℝ≥0) (r : ℕ) : 0 ≤ poissonMass K lam mu t r := by
  unfold poissonMass
  have hc := clock_pos hlam hmu
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le
    (pow_nonneg (mul_nonneg hc.le t.coe_nonneg) _)) (Nat.cast_nonneg _)

lemma poissonMass_hasSum (t : ℝ≥0) : HasSum (poissonMass K lam mu t) 1 := by
  have h := NormedSpace.expSeries_div_hasSum_exp (clockRate K lam mu * (t : ℝ))
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-(clockRate K lam mu * (t : ℝ))))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  have hf : poissonMass K lam mu t = fun r => Real.exp (-(clockRate K lam mu * (t : ℝ))) *
      ((clockRate K lam mu * (t : ℝ)) ^ r / (r.factorial : ℝ)) := by
    funext r; unfold poissonMass; ring
  rw [hf]; exact h2

lemma transient_hasSum (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (t : ℝ≥0) (x n : Fin K → ℕ) :
    HasSum (fun r => poissonMass K lam mu t r *
      stepPow (uniformStep K u lam mu) r x n) (transient K u lam mu t x n) := by
  have hP := stoch_stepPow (uniformStep_stoch (u := u) hK hlam hmu)
  exact (Summable.of_nonneg_of_le
    (fun r => mul_nonneg (poissonMass_nonneg hlam hmu t r) ((hP r).1 x n))
    (fun r => mul_le_of_le_one_right (poissonMass_nonneg hlam hmu t r) (stoch_le_one (hP r) x n))
    (poissonMass_hasSum t).summable).hasSum

lemma transient_stoch (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (t : ℝ≥0) : IsStochasticC (transient K u lam mu t) := by
  have hP := stoch_stepPow (uniformStep_stoch (u := u) hK hlam hmu)
  exact ⟨fun x n => tsum_nonneg (fun r =>
      mul_nonneg (poissonMass_nonneg hlam hmu t r) ((hP r).1 x n)),
    fun x => rowmix (poissonMass K lam mu t) (poissonMass_nonneg hlam hmu t)
      (poissonMass_hasSum t) (fun r => stepPow (uniformStep K u lam mu) r x)
      (fun r => (hP r).1 x) (fun r => (hP r).2 x)⟩

lemma transient_zero (x n : Fin K → ℕ) :
    transient K u lam mu 0 x n = if x = n then 1 else 0 := by
  have h : ∀ r, poissonMass K lam mu 0 r = if r = 0 then 1 else 0 := fun r => by
    unfold poissonMass; rcases r with _ | r <;> simp
  unfold transient
  simp only [h, ite_mul, one_mul, zero_mul]
  rw [tsum_ite_eq, stepPow_zero]
  by_cases hxn : x = n
  · subst hxn; simp
  · rw [if_neg (Ne.symm hxn), if_neg hxn]

lemma SM_closed (hreach : {n : Fin K → ℕ | Relation.ReflTransGen
      (fun a b => 0 < rate K u lam mu a b) 0 n} = SM K u)
    {z n : Fin K → ℕ} (hz : z ∈ SM K u) (h : 0 < rate K u lam mu z n) : n ∈ SM K u := by
  rw [← hreach] at hz ⊢
  exact Relation.ReflTransGen.tail hz h

lemma uniformStep_out (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hreach : {n : Fin K → ℕ | Relation.ReflTransGen
      (fun a b => 0 < rate K u lam mu a b) 0 n} = SM K u)
    {z n : Fin K → ℕ} (hz : z ∈ SM K u) (hn : n ∉ SM K u) :
    uniformStep K u lam mu z n = 0 := by
  have hzn : z ≠ n := fun h : z = n => hn (by rw [← h]; exact hz)
  have hr : rate K u lam mu z n = 0 :=
    le_antisymm (not_lt.mp (fun h => hn (SM_closed hreach hz h))) (rate_nonneg hK hlam hmu z n)
  unfold uniformStep; rw [if_neg hzn, hr]; simp

lemma stepPow_out (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hreach : {n : Fin K → ℕ | Relation.ReflTransGen
      (fun a b => 0 < rate K u lam mu a b) 0 n} = SM K u)
    {x : Fin K → ℕ} (hx : x ∈ SM K u) (r : ℕ) :
    ∀ n, n ∉ SM K u → stepPow (uniformStep K u lam mu) r x n = 0 := by
  induction r with
  | zero => intro n hn; rw [stepPow_zero, if_neg (fun h : n = x => hn (by rw [h]; exact hx))]
  | succ r ih =>
    intro n hn
    rw [stepPow_succ]
    have : ∀ z, stepPow (uniformStep K u lam mu) r x z * uniformStep K u lam mu z n = 0 :=
      fun z => by
        by_cases hz : z ∈ SM K u
        · rw [uniformStep_out hK hlam hmu hreach hz hn, mul_zero]
        · rw [ih z hz, zero_mul]
    simp [this]

lemma weight_pos (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k) (n : Fin K → ℕ) :
    0 < weight K lam mu n := by
  unfold weight
  exact Finset.prod_pos (fun k hk => by
    rw [Finset.mem_Icc] at hk; exact pow_pos (div_pos hlam (hmu k hk.1 hk.2)) _)

lemma piM_nonneg (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hG : 0 < normG K u lam mu) (n : Fin K → ℕ) : 0 ≤ piM K u lam mu n := by
  unfold piM
  exact div_nonneg (Set.indicator_nonneg (fun m _ => (weight_pos hlam hmu m).le) n) hG.le

lemma piM_pos (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hG : 0 < normG K u lam mu) {n : Fin K → ℕ} (hn : n ∈ SM K u) : 0 < piM K u lam mu n := by
  unfold piM
  rw [Set.indicator_of_mem hn]
  exact div_pos (weight_pos hlam hmu n) hG

/-- Global balance for the rates gives stationarity of the uniformized kernel. -/
lemma stationary (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (π : (Fin K → ℕ) → ℝ) (hπ0 : ∀ n, 0 ≤ π n) (hπ : Summable π)
    (hbal : ∀ n, π n * outRate K lam mu n = ∑' m, π m * rate K u lam mu m n)
    (n : Fin K → ℕ) :
    HasSum (fun m => π m * uniformStep K u lam mu m n) (π n) := by
  have hc := clock_pos hlam hmu
  have hs : Summable (fun m => π m * rate K u lam mu m n) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (hπ0 m) (rate_nonneg hK hlam hmu m n))
      (fun m => mul_le_mul_of_nonneg_left (rate_le_clock hK hlam hmu m n) (hπ0 m))
      (hπ.mul_right (clockRate K lam mu))
  have h1 := hs.hasSum.div_const (clockRate K lam mu)
  have key := h1.add (hasSum_ite_eq n (π n * (1 - outRate K lam mu n / clockRate K lam mu)))
  have hf : (fun m => π m * uniformStep K u lam mu m n) = fun m =>
      π m * rate K u lam mu m n / clockRate K lam mu +
        (if m = n then π n * (1 - outRate K lam mu n / clockRate K lam mu) else 0) := by
    funext m
    unfold uniformStep
    by_cases h : m = n
    · subst h; rw [if_pos rfl, if_pos rfl]; ring
    · rw [if_neg h, if_neg h]; ring
  have hv : π n = (∑' m, π m * rate K u lam mu m n) / clockRate K lam mu +
      π n * (1 - outRate K lam mu n / clockRate K lam mu) := by
    rw [← hbal n]; field_simp; ring
  rw [← hf, ← hv] at key
  exact key

end Model

/-- Mixing a convergent `[0,1]`-sequence by distributions whose point masses vanish. -/
lemma mix_tendsto {ι : Type*} {l : Filter ι} {a : ℕ → ℝ} {L : ℝ} (ha : Tendsto a atTop (𝓝 L))
    (ha0 : ∀ r, 0 ≤ a r) (ha1 : ∀ r, a r ≤ 1) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    {p : ι → ℕ → ℝ} (hp0 : ∀ t r, 0 ≤ p t r) (hp1 : ∀ t, HasSum (p t) 1)
    (hpr : ∀ r, Tendsto (fun t => p t r) l (𝓝 0)) :
    Tendsto (fun t => ∑' r, p t r * a r) l (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 ha (ε / 2) (by linarith)
  have hfin : Tendsto (fun t => ∑ r ∈ Finset.range R, p t r) l (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range R) (fun r _ => hpr r)
  filter_upwards [Metric.tendsto_nhds.1 hfin (ε / 2) (by linarith)] with t ht
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg (fun r _ => hp0 t r))] at ht
  have hsa : HasSum (fun r => p t r * a r) (∑' r, p t r * a r) :=
    (Summable.of_nonneg_of_le (fun r => mul_nonneg (hp0 t r) (ha0 r))
      (fun r => mul_le_of_le_one_right (hp0 t r) (ha1 r)) (hp1 t).summable).hasSum
  have hd : HasSum (fun r => p t r * a r - p t r * L) (∑' r, p t r * a r - 1 * L) :=
    hsa.sub ((hp1 t).mul_right L)
  rw [one_mul] at hd
  have hf1 : HasSum (fun r => if r < R then p t r else 0) (∑ r ∈ Finset.range R, p t r) := by
    have h : HasSum (fun r => if r < R then p t r else 0)
        (∑ r ∈ Finset.range R, (if r < R then p t r else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun r hr => if_neg (by simpa using hr))
    rwa [Finset.sum_congr rfl (fun r hr => if_pos (Finset.mem_range.1 hr))] at h
  have hg := hf1.add ((hp1 t).mul_right (ε / 2))
  rw [one_mul] at hg
  have hpt : ∀ r, |p t r * a r - p t r * L| ≤ (if r < R then p t r else 0) + p t r * (ε / 2) := by
    intro r
    rw [← mul_sub, abs_mul, abs_of_nonneg (hp0 t r)]
    have h0 := hp0 t r
    by_cases hr : r < R
    · rw [if_pos hr]
      have : |a r - L| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ha0 r, ha1 r]
      nlinarith [mul_le_mul_of_nonneg_left this h0]
    · rw [if_neg hr, zero_add]
      have h2 := hR r (by omega)
      rw [Real.dist_eq] at h2
      exact mul_le_mul_of_nonneg_left h2.le h0
  have hup := hasSum_le (fun r => (abs_le.1 (hpt r)).2) hd hg
  have hlo := hasSum_le (fun r => (abs_le.1 (hpt r)).1) hg.neg hd
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith


section Glue

variable {K : ℕ} {u : ℕ → ℕ → ℕ∞} {lam : ℝ} {mu : ℕ → ℝ}

lemma poissonMass_tendsto (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k) (r : ℕ) :
    Tendsto (fun t : ℝ≥0 => poissonMass K lam mu t r) atTop (𝓝 0) := by
  have hc := clock_pos hlam hmu
  have hco : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    tendsto_atTop_atTop_of_monotone NNReal.coe_mono
      (fun b => ⟨b.toNNReal, Real.le_coe_toNNReal b⟩)
  have h1 : Tendsto (fun t : ℝ≥0 => clockRate K lam mu * (t : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hc hco
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero r).comp h1).div_const (r.factorial : ℝ)
  rw [zero_div] at h2
  refine h2.congr (fun t => ?_)
  simp only [Function.comp, poissonMass]
  ring

lemma uniformStep_pos_of_rate (hK : 1 ≤ K) (hlam : 0 < lam)
    (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k) {a b : Fin K → ℕ}
    (h : 0 < rate K u lam mu a b) : 0 < uniformStep K u lam mu a b := by
  have hc := clock_pos hlam hmu
  have hle := outRate_le (lam := lam) hmu a
  have hs := sumMu_nonneg hmu
  have hite : 0 ≤ (if a = b then 1 - outRate K lam mu a / clockRate K lam mu else 0) := by
    split_ifs
    · rw [sub_nonneg, div_le_one hc]; unfold clockRate; linarith
    · exact le_rfl
  unfold uniformStep
  exact add_pos_of_pos_of_nonneg (div_pos h hc) hite

lemma piM_out {n : Fin K → ℕ} (hn : n ∉ SM K u) : piM K u lam mu n = 0 := by
  unfold piM; rw [Set.indicator_of_notMem hn, zero_div]

lemma path_lift (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hreach : {n : Fin K → ℕ | Relation.ReflTransGen
      (fun a b => 0 < rate K u lam mu a b) 0 n} = SM K u)
    (hG : 0 < normG K u lam mu) {n : Fin K → ℕ} (hn : n ∈ SM K u) :
    Relation.ReflTransGen
      (fun a b => 0 < piM K u lam mu a ∧ 0 < uniformStep K u lam mu a b) 0 n := by
  have h : Relation.ReflTransGen (fun a b => 0 < rate K u lam mu a b) 0 n := by
    rw [← hreach] at hn; exact hn
  clear hn
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    have hb : b ∈ SM K u := by rw [← hreach]; exact hab
    exact Relation.ReflTransGen.tail ih
      ⟨piM_pos hlam hmu hG hb, uniformStep_pos_of_rate hK hlam hmu hbc⟩

lemma transient_tendsto (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hreach : {n : Fin K → ℕ | Relation.ReflTransGen
      (fun a b => 0 < rate K u lam mu a b) 0 n} = SM K u)
    (hG : 0 < normG K u lam mu) (h1 : HasSum (piM K u lam mu) 1)
    (hbal : ∀ n, piM K u lam mu n * outRate K lam mu n =
      ∑' m, piM K u lam mu m * rate K u lam mu m n)
    (hconv : ∀ (P : (Fin K → ℕ) → (Fin K → ℕ) → ℝ) (π : (Fin K → ℕ) → ℝ),
      IsStochasticC P → (∀ y, 0 ≤ π y) → HasSum π 1 → (∀ z, ∑' y, π y * P y z = π z) →
      (∀ z, 1 / 2 ≤ P z z) → ∀ o, (∀ n, 0 < π n →
        Relation.ReflTransGen (fun a b => 0 < π a ∧ 0 < P a b) o n) →
      ∀ x, 0 < π x → ∀ n, Tendsto (fun r => stepPow P r x n) atTop (𝓝 (π n)))
    {x : Fin K → ℕ} (hx : x ∈ SM K u) (n : Fin K → ℕ) :
    Tendsto (fun t : ℝ≥0 => transient K u lam mu t x n) atTop (nhds (piM K u lam mu n)) := by
  have hP := uniformStep_stoch (u := u) hK hlam hmu
  have h0 := piM_nonneg (u := u) hlam hmu hG
  have hstat : ∀ z, ∑' y, piM K u lam mu y * uniformStep K u lam mu y z = piM K u lam mu z :=
    fun z => (stationary hK hlam hmu _ h0 h1.summable hbal z).tsum_eq
  have hpath : ∀ m, 0 < piM K u lam mu m → Relation.ReflTransGen
      (fun a b => 0 < piM K u lam mu a ∧ 0 < uniformStep K u lam mu a b) 0 m := by
    intro m hm
    by_cases hmS : m ∈ SM K u
    · exact path_lift hK hlam hmu hreach hG hmS
    · rw [piM_out hmS] at hm; exact absurd hm (lt_irrefl 0)
  have ha := hconv _ _ hP h0 h1 hstat (uniformStep_diag hK hlam hmu) 0 hpath x
    (piM_pos hlam hmu hG hx) n
  have hstep := stoch_stepPow hP
  show Tendsto (fun t : ℝ≥0 => ∑' r, poissonMass K lam mu t r *
    stepPow (uniformStep K u lam mu) r x n) atTop _
  exact mix_tendsto (p := fun t r => poissonMass K lam mu t r) ha
    (fun r => (hstep r).1 x n) (fun r => stoch_le_one (hstep r) x n) (h0 n)
    (le_hasSum h1 n (fun m _ => h0 m)) (fun t r => poissonMass_nonneg hlam hmu t r)
    (fun t => poissonMass_hasSum t) (fun r => poissonMass_tendsto hlam hmu r)

end Glue

open SmartExpediteAudit.PolicyM in
theorem assemble (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ)
    (hK : 1 ≤ K) (hlam : 0 < lam)
    (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hT1 : {n : Fin K → ℕ | Relation.ReflTransGen
      (fun a b => 0 < rate K u lam mu a b) 0 n} = SM K u ∧
    (lam < mu K →
      (∀ i, 1 ≤ i → i ≤ K - 1 → u 0 i ≠ ⊤) →
      Summable ((SM K u).indicator (weight K lam mu)) ∧
      0 < normG K u lam mu ∧
      HasSum (piM K u lam mu) 1 ∧
      ∀ n, piM K u lam mu n * outRate K lam mu n =
        ∑' m, piM K u lam mu m * rate K u lam mu m n))
    (hconv : ∀ (P : (Fin K → ℕ) → (Fin K → ℕ) → ℝ) (π : (Fin K → ℕ) → ℝ),
      IsStochasticC P → (∀ y, 0 ≤ π y) → HasSum π 1 → (∀ z, ∑' y, π y * P y z = π z) →
      (∀ z, 1 / 2 ≤ P z z) → ∀ o, (∀ n, 0 < π n →
        Relation.ReflTransGen (fun a b => 0 < π a ∧ 0 < P a b) o n) →
      ∀ x, 0 < π x → ∀ n, Tendsto (fun r => stepPow P r x n) atTop (𝓝 (π n)))
    (hsemi : ∀ s t x n, HasSum (fun y : Fin K → ℕ =>
      transient K u lam mu s x y * transient K u lam mu t y n)
        (transient K u lam mu (s + t) x n))
    (hgen : ∀ x n, Tendsto
      (fun t : ℝ≥0 =>
        (transient K u lam mu t x n - (if x = n then 1 else 0)) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (rate K u lam mu x n -
        if x = n then outRate K lam mu x else 0))) :
    {n : Fin K → ℕ | Relation.ReflTransGen
      (fun a b => 0 < rate K u lam mu a b) 0 n} = SM K u ∧
    0 < clockRate K lam mu ∧
    MarkovMixing.IsStochasticC (uniformStep K u lam mu) ∧
    (∀ r, MarkovMixing.IsStochasticC
      (MarkovMixing.stepPow (uniformStep K u lam mu) r)) ∧
    (∀ r x n, Summable (fun y : Fin K → ℕ =>
      MarkovMixing.stepPow (uniformStep K u lam mu) r x y *
        uniformStep K u lam mu y n)) ∧
    (∀ t, HasSum (poissonMass K lam mu t) 1) ∧
    (∀ t x n, HasSum (fun r => poissonMass K lam mu t r *
      MarkovMixing.stepPow (uniformStep K u lam mu) r x n)
        (transient K u lam mu t x n)) ∧
    (∀ t, MarkovMixing.IsStochasticC (transient K u lam mu t)) ∧
    (∀ x n, transient K u lam mu 0 x n = if x = n then 1 else 0) ∧
    (∀ s t x n, HasSum (fun y : Fin K → ℕ =>
      transient K u lam mu s x y * transient K u lam mu t y n)
        (transient K u lam mu (s + t) x n)) ∧
    (∀ x n, Tendsto
      (fun t : ℝ≥0 =>
        (transient K u lam mu t x n - (if x = n then 1 else 0)) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (rate K u lam mu x n -
        if x = n then outRate K lam mu x else 0))) ∧
    (∀ x ∈ SM K u, ∀ n, n ∉ SM K u →
      ∀ t, transient K u lam mu t x n = 0) ∧
    ((lam < mu K) →
      (∀ i, 1 ≤ i → i < K → u 0 i ≠ ⊤) →
      Summable ((SM K u).indicator (weight K lam mu)) ∧
      0 < normG K u lam mu ∧
      (∀ n, 0 ≤ piM K u lam mu n) ∧
      HasSum (piM K u lam mu) 1 ∧
      (∀ n ∈ SM K u, piM K u lam mu n =
        (∏ k ∈ Finset.Icc 1 K, (lam / mu k) ^ occ n k) / normG K u lam mu) ∧
      (∀ n, n ∉ SM K u → piM K u lam mu n = 0) ∧
      ∀ x ∈ SM K u, ∀ n : Fin K → ℕ,
        Tendsto (fun t : ℝ≥0 => transient K u lam mu t x n)
          atTop (nhds (piM K u lam mu n))) := by
  obtain ⟨hreach, hstab⟩ := hT1
  have hP := uniformStep_stoch (u := u) hK hlam hmu
  refine ⟨hreach, clock_pos hlam hmu, hP, stoch_stepPow hP, ?_, fun t => poissonMass_hasSum t,
    transient_hasSum hK hlam hmu, transient_stoch hK hlam hmu, transient_zero, hsemi, hgen,
    ?_, ?_⟩
  · intro r x n
    exact Summable.of_nonneg_of_le
      (fun y => mul_nonneg ((stoch_stepPow hP r).1 x y) (hP.1 y n))
      (fun y => mul_le_of_le_one_right ((stoch_stepPow hP r).1 x y) (stoch_le_one hP y n))
      ((stoch_stepPow hP r).2 x).summable
  · intro x hx n hn t
    have hz : ∀ r, poissonMass K lam mu t r * stepPow (uniformStep K u lam mu) r x n = 0 :=
      fun r => by rw [stepPow_out hK hlam hmu hreach hx r n hn, mul_zero]
    show ∑' r, poissonMass K lam mu t r * stepPow (uniformStep K u lam mu) r x n = 0
    simp [hz]
  · intro hlt hu0
    have hu' : ∀ i, 1 ≤ i → i ≤ K - 1 → u 0 i ≠ ⊤ := fun i hi1 hi2 => hu0 i hi1 (by omega)
    obtain ⟨hsum, hG, h1, hbal⟩ := hstab hlt hu'
    refine ⟨hsum, hG, piM_nonneg hlam hmu hG, h1, ?_, fun n hn => piM_out hn,
      fun x hx n => transient_tendsto hK hlam hmu hreach hG h1 hbal hconv hx n⟩
    intro n hn
    unfold piM
    rw [Set.indicator_of_mem hn]
    rfl

end SEFull

open SmartExpediteAudit.PolicyM in
theorem solution (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ)
    (hK : 1 ≤ K) (hlam : 0 < lam)
    (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (hu : IsPolicyParam K u) (hA : AssumptionA K u) :
    {n : Fin K → ℕ | Relation.ReflTransGen
      (fun a b => 0 < rate K u lam mu a b) 0 n} = SM K u ∧
    0 < clockRate K lam mu ∧
    MarkovMixing.IsStochasticC (uniformStep K u lam mu) ∧
    (∀ r, MarkovMixing.IsStochasticC
      (MarkovMixing.stepPow (uniformStep K u lam mu) r)) ∧
    (∀ r x n, Summable (fun y : Fin K → ℕ =>
      MarkovMixing.stepPow (uniformStep K u lam mu) r x y *
        uniformStep K u lam mu y n)) ∧
    (∀ t, HasSum (poissonMass K lam mu t) 1) ∧
    (∀ t x n, HasSum (fun r => poissonMass K lam mu t r *
      MarkovMixing.stepPow (uniformStep K u lam mu) r x n)
        (transient K u lam mu t x n)) ∧
    (∀ t, MarkovMixing.IsStochasticC (transient K u lam mu t)) ∧
    (∀ x n, transient K u lam mu 0 x n = if x = n then 1 else 0) ∧
    (∀ s t x n, HasSum (fun y : Fin K → ℕ =>
      transient K u lam mu s x y * transient K u lam mu t y n)
        (transient K u lam mu (s + t) x n)) ∧
    (∀ x n, Tendsto
      (fun t : ℝ≥0 =>
        (transient K u lam mu t x n - (if x = n then 1 else 0)) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (rate K u lam mu x n -
        if x = n then outRate K lam mu x else 0))) ∧
    (∀ x ∈ SM K u, ∀ n, n ∉ SM K u →
      ∀ t, transient K u lam mu t x n = 0) ∧
    ((lam < mu K) →
      (∀ i, 1 ≤ i → i < K → u 0 i ≠ ⊤) →
      Summable ((SM K u).indicator (weight K lam mu)) ∧
      0 < normG K u lam mu ∧
      (∀ n, 0 ≤ piM K u lam mu n) ∧
      HasSum (piM K u lam mu) 1 ∧
      (∀ n ∈ SM K u, piM K u lam mu n =
        (∏ k ∈ Finset.Icc 1 K, (lam / mu k) ^ occ n k) / normG K u lam mu) ∧
      (∀ n, n ∉ SM K u → piM K u lam mu n = 0) ∧
      ∀ x ∈ SM K u, ∀ n : Fin K → ℕ,
        Tendsto (fun t : ℝ≥0 => transient K u lam mu t x n)
          atTop (nhds (piM K u lam mu n))) := by
  exact SEFull.assemble K u lam mu hK hlam hmu
    (SmartExpedite.PolicyM.theorem_1 K u lam mu hK hlam hmu hu hA)
    (fun P π a b c d e o f x g n =>
      SmartExpediteAudit.lazy_chain_tendsto_stationary P π a b c d e o f x g n)
    (SmartExpediteAudit.PolicyM.transient_semigroup K u lam mu hK hlam hmu)
    (SmartExpediteAudit.PolicyM.transient_generator K u lam mu hK hlam hmu)

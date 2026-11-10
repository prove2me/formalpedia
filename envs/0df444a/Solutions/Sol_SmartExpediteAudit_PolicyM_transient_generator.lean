-- Prove2me | solution 1 for SmartExpediteAudit.PolicyM.transient_generator
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T09:58:18.817593+00:00
-- url     : https://prove2.me/submissions/63ec7dcc-8ff0-4746-85aa-6430eec26b7a

import Mathlib
import Definitions.Def_SmartExpediteAudit_PolicyM_Transient

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

end Model

section Semi

variable {K : ℕ} {u : ℕ → ℕ → ℕ∞} {lam : ℝ} {mu : ℕ → ℝ}

lemma transient_bounds (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (t : ℝ≥0) (x n : Fin K → ℕ) :
    poissonMass K lam mu t 0 * stepPow (uniformStep K u lam mu) 0 x n +
      poissonMass K lam mu t 1 * uniformStep K u lam mu x n ≤ transient K u lam mu t x n ∧
    transient K u lam mu t x n ≤ 1 - poissonMass K lam mu t 0 - poissonMass K lam mu t 1 +
      (poissonMass K lam mu t 0 * stepPow (uniformStep K u lam mu) 0 x n +
      poissonMass K lam mu t 1 * uniformStep K u lam mu x n) := by
  have hPr := stoch_stepPow (uniformStep_stoch (u := u) hK hlam hmu)
  have hT := transient_hasSum (u := u) hK hlam hmu t x n
  have hp0 := poissonMass_nonneg (K := K) hlam hmu t
  constructor
  · have h := sum_le_hasSum (Finset.range 2) (fun r _ => mul_nonneg (hp0 r) ((hPr r).1 x n)) hT
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, stepPow_one] at h
    exact h
  · have h2 := (poissonMass_hasSum (K := K) (lam := lam) (mu := mu) t).sub hT
    have h := sum_le_hasSum (Finset.range 2) (fun r _ => by
      have := stoch_le_one (hPr r) x n
      have := hp0 r
      show 0 ≤ poissonMass K lam mu t r -
        poissonMass K lam mu t r * stepPow (uniformStep K u lam mu) r x n
      nlinarith) h2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, stepPow_one] at h
    linarith

lemma transient_gen (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k)
    (x n : Fin K → ℕ) :
    Tendsto (fun t : ℝ≥0 =>
        (transient K u lam mu t x n - (if x = n then 1 else 0)) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (rate K u lam mu x n - if x = n then outRate K lam mu x else 0)) := by
  have hc := clock_pos hlam hmu
  have hL : rate K u lam mu x n - (if x = n then outRate K lam mu x else 0) =
      clockRate K lam mu * (uniformStep K u lam mu x n - if x = n then 1 else 0) := by
    have hc' := hc.ne'
    unfold uniformStep
    split_ifs <;> field_simp <;> ring
  have hS0 : stepPow (uniformStep K u lam mu) 0 x n = if x = n then 1 else 0 := by
    rw [stepPow_zero]; by_cases h : x = n
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  have hP0 : 0 ≤ uniformStep K u lam mu x n := (uniformStep_stoch (u := u) hK hlam hmu).1 x n
  have hP1 : uniformStep K u lam mu x n ≤ 1 := stoch_le_one (uniformStep_stoch (u := u) hK hlam hmu) x n
  have hδ0 : (0:ℝ) ≤ if x = n then 1 else 0 := by split_ifs <;> norm_num
  have hδ1 : (if x = n then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  rw [hL, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ?_
    (g := fun t : ℝ≥0 => 2 * clockRate K lam mu ^ 2 * (t : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have htp : (0:ℝ) < t := by exact_mod_cast (show (0:ℝ≥0) < t from ht)
    obtain ⟨hlo, hhi⟩ := transient_bounds (u := u) hK hlam hmu t x n
    have he0 : poissonMass K lam mu t 0 = Real.exp (-(clockRate K lam mu * t)) := by
      unfold poissonMass; simp
    have he1 : poissonMass K lam mu t 1 =
        Real.exp (-(clockRate K lam mu * t)) * (clockRate K lam mu * t) := by
      unfold poissonMass; simp
    rw [hS0, he0, he1] at hlo hhi
    generalize transient K u lam mu t x n = T at hlo hhi ⊢
    generalize uniformStep K u lam mu x n = P at hlo hhi hP0 hP1 ⊢
    generalize (if x = n then (1:ℝ) else 0) = δ at hlo hhi hδ0 hδ1 ⊢
    generalize clockRate K lam mu = c at hlo hhi hc ⊢
    generalize (t : ℝ) = τ at hlo hhi htp ⊢
    have hU0 : 0 ≤ c * τ := mul_nonneg hc.le htp.le
    have he0' : 0 ≤ Real.exp (-(c * τ)) := (Real.exp_pos _).le
    have hea : 1 - c * τ ≤ Real.exp (-(c * τ)) := by
      have := Real.add_one_le_exp (-(c * τ)); linarith
    have heb : Real.exp (-(c * τ)) * (1 + c * τ) ≤ 1 := by
      have h1 := Real.add_one_le_exp (c * τ)
      have h2 : Real.exp (-(c * τ)) * Real.exp (c * τ) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      nlinarith [mul_le_mul_of_nonneg_left h1 he0']
    generalize Real.exp (-(c * τ)) = e at hlo hhi he0' hea heb
    have hec : e ≤ 1 - c * τ + (c * τ) ^ 2 := by
      nlinarith [mul_nonneg hU0 (sq_nonneg (c * τ))]
    have he1' : e ≤ 1 := by nlinarith [mul_nonneg he0' hU0]
    have k1 : 0 ≤ (e - (1 - c * τ)) * (1 + c * τ) := mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ (1 - δ) * (e - 1 + c * τ) := mul_nonneg (by linarith) (by linarith)
    have k3 : 0 ≤ (c * τ) * P * (1 - e) := mul_nonneg (mul_nonneg hU0 hP0) (by linarith)
    have k4 : 0 ≤ δ * (e - 1 + c * τ) := mul_nonneg hδ0 (by linarith)
    have k5 : 0 ≤ (c * τ) * P * (e - (1 - c * τ)) := mul_nonneg (mul_nonneg hU0 hP0) (by linarith)
    have k6 : 0 ≤ (c * τ) ^ 2 * (1 - P) := mul_nonneg (sq_nonneg _) (by linarith)
    have hrw : (T - δ) / τ - c * (P - δ) = (T - δ - τ * (c * (P - δ))) / τ := by
      field_simp
    rw [Real.norm_eq_abs, hrw, abs_div, abs_of_pos htp, div_le_iff₀ htp, abs_le]
    constructor <;> nlinarith [k1, k2, k3, k4, k5, k6, hec, hlo, hhi, sq_nonneg (c * τ)]
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      ((by fun_prop : Continuous fun t : ℝ≥0 => 2 * clockRate K lam mu ^ 2 * (t : ℝ)).tendsto' 0 0
        (by simp))

end Semi

end SEFull

open SmartExpediteAudit.PolicyM in
theorem solution (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ)
    (hK : 1 ≤ K) (hlam : 0 < lam) (hmu : ∀ k, 1 ≤ k → k ≤ K → 0 < mu k) :
    ∀ x n, Filter.Tendsto
      (fun t : ℝ≥0 =>
        (transient K u lam mu t x n - (if x = n then 1 else 0)) / (t : ℝ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (rate K u lam mu x n -
        if x = n then outRate K lam mu x else 0)) := by
  intro x n
  exact SEFull.transient_gen hK hlam hmu x n

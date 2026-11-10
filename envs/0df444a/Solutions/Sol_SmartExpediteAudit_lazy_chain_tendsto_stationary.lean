-- Prove2me | solution 1 for SmartExpediteAudit.lazy_chain_tendsto_stationary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T09:48:32.156892+00:00
-- url     : https://prove2.me/submissions/d430a7f3-5ae1-4aee-b8e3-1ec3c85c3532

import Mathlib
import Definitions.Def_mm_countable

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Filter
open scoped Topology

namespace SEFullM

open MarkovMixing

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
/-- Hypotheses of the discrete convergence argument. -/
structure CSetup (P : V → V → ℝ) (π : V → ℝ) (x : V) : Prop where
  hP : IsStochasticC P
  h0 : ∀ y, 0 ≤ π y
  h1 : HasSum π 1
  hstat : ∀ z, ∑' y, π y * P y z = π z
  hx : 0 < π x

lemma pi_summable_mul {π : V → ℝ} (hπ0 : ∀ y, 0 ≤ π y) (hπ : Summable π) {Q : V → V → ℝ}
    (hQ : IsStochasticC Q) (z : V) : Summable (fun y => π y * Q y z) :=
  Summable.of_nonneg_of_le (fun y => mul_nonneg (hπ0 y) (hQ.1 y z))
    (fun y => mul_le_of_le_one_right (hπ0 y) (stoch_le_one hQ y z)) hπ

lemma stat_pow {P : V → V → ℝ} {π : V → ℝ} (hP : IsStochasticC P) (hπ0 : ∀ y, 0 ≤ π y)
    (hπ : Summable π) (hstat : ∀ z, ∑' y, π y * P y z = π z) (r : ℕ) (z : V) :
    ∑' y, π y * stepPow P r y z = π z := by
  induction r generalizing z with
  | zero =>
    rw [tsum_eq_single z (fun y hy => by rw [stepPow_zero, if_neg (Ne.symm hy), mul_zero])]
    rw [stepPow_zero, if_pos rfl, mul_one]
  | succ r ih =>
    have h := tsum_assoc3 hP π hπ0 hπ (fun w => stepPow P r w z)
      (fun w => (stoch_stepPow hP r).1 w z) (fun w => stoch_le_one (stoch_stepPow hP r) w z)
    simp_rw [hstat] at h
    rw [ih z] at h
    calc ∑' y, π y * stepPow P (r + 1) y z
        = ∑' y, π y * ∑' w, P y w * stepPow P r w z := by
          congr 1; funext y
          rw [show r + 1 = 1 + r from Nat.add_comm r 1, stepPow_add hP 1 r y z]
          simp_rw [stepPow_one]
      _ = π z := h.symm

noncomputable def fr (P : V → V → ℝ) (π : V → ℝ) (x : V) (r : ℕ) (y : V) : ℝ :=
  stepPow P r x y / π y

section S
variable {P : V → V → ℝ} {π : V → ℝ} {x : V}

lemma CSetup.mass_le (S : CSetup P π x) (r : ℕ) (y : V) : π x * stepPow P r x y ≤ π y := by
  have h := (pi_summable_mul S.h0 S.h1.summable (stoch_stepPow S.hP r) y).hasSum
  rw [stat_pow S.hP S.h0 S.h1.summable S.hstat r y] at h
  exact le_hasSum h x (fun j _ => mul_nonneg (S.h0 j) ((stoch_stepPow S.hP r).1 j y))

lemma CSetup.mass_eq (S : CSetup P π x) (r : ℕ) (y : V) :
    stepPow P r x y = π y * fr P π x r y := by
  unfold fr
  by_cases hy : π y = 0
  · have h1 := S.mass_le r y
    have h2 := (stoch_stepPow S.hP r).1 x y
    rw [hy] at h1 ⊢
    have : stepPow P r x y ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith [mul_pos S.hx hc]
    rw [zero_mul]; linarith
  · field_simp

lemma CSetup.fr_nonneg (S : CSetup P π x) (r : ℕ) (y : V) : 0 ≤ fr P π x r y :=
  div_nonneg ((stoch_stepPow S.hP r).1 x y) (S.h0 y)

lemma CSetup.fr_le (S : CSetup P π x) (r : ℕ) (y : V) : fr P π x r y ≤ 1 / π x := by
  unfold fr
  by_cases hy : π y = 0
  · rw [hy, div_zero]; exact (div_pos one_pos S.hx).le
  · have hyp : 0 < π y := lt_of_le_of_ne (S.h0 y) (Ne.symm hy)
    rw [div_le_div_iff₀ hyp S.hx]
    have := S.mass_le r y
    linarith

lemma CSetup.fr_succ (S : CSetup P π x) (r : ℕ) (z : V) :
    π z * fr P π x (r + 1) z = ∑' y, π y * P y z * fr P π x r y := by
  rw [← S.mass_eq, stepPow_succ]
  congr 1; funext y; rw [S.mass_eq r y]; ring

lemma CSetup.W_hasSum (S : CSetup P π x) :
    HasSum (fun p : V × V => π p.1 * P p.1 p.2) 1 := by
  have hrow : ∀ i, HasSum (fun y => π i * P i y) (π i) := fun i => by
    have h := (S.hP.2 i).mul_left (π i)
    rwa [mul_one] at h
  have hG0 : (0 : V × V → ℝ) ≤ fun p => π p.1 * P p.1 p.2 :=
    Pi.le_def.2 (fun p => by simp only [Pi.zero_apply]; exact mul_nonneg (S.h0 _) (S.hP.1 _ _))
  have hGs : Summable (fun p : V × V => π p.1 * P p.1 p.2) := by
    refine (summable_prod_of_nonneg hG0).2 ⟨fun i => (hrow i).summable, ?_⟩
    have h : (fun i => ∑' y, π i * P i y) = π := funext fun i => (hrow i).tsum_eq
    rw [h]; exact S.h1.summable
  have h := hGs.hasSum.prod_fiberwise hrow
  rw [S.h1.unique h]; exact hGs.hasSum

lemma CSetup.sumW (S : CSetup P π x) {g : V × V → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg0 : ∀ p, 0 ≤ g p) (hgle : ∀ p, g p ≤ C * (π p.1 * P p.1 p.2)) :
    Summable g ∧ (∀ y, Summable fun z => g (y, z)) ∧ (∀ z, Summable fun y => g (y, z)) := by
  refine ⟨Summable.of_nonneg_of_le hg0 hgle (S.W_hasSum.summable.mul_left C), fun y => ?_, fun z => ?_⟩
  · exact Summable.of_nonneg_of_le (fun z => hg0 _)
      (fun z => (hgle (y, z)).trans (le_of_eq (by ring))) ((S.hP.2 y).summable.mul_left (C * π y))
  · exact Summable.of_nonneg_of_le (fun y => hg0 _)
      (fun y => (hgle (y, z)).trans (mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (S.h0 y) (stoch_le_one S.hP y z)) hC))
      (S.h1.summable.mul_left C)

lemma tsum_swap2 {g : V × V → ℝ} (hg : Summable g) (h2 : ∀ z, Summable fun y => g (y, z)) :
    ∑' p, g p = ∑' z, ∑' y, g (y, z) := by
  rw [← (Equiv.prodComm V V).tsum_eq g]
  exact ((Equiv.prodComm V V).summable_iff.2 hg).tsum_prod' h2

lemma scal {w a b B : ℝ} (hw : 0 ≤ w) (ha0 : 0 ≤ a) (haB : a ≤ B) (hb0 : 0 ≤ b) (hbB : b ≤ B) :
    w * a ^ 2 ≤ B ^ 2 * w ∧ w * b ^ 2 ≤ B ^ 2 * w ∧ w * a * b ≤ B ^ 2 * w ∧
      w * (a - b) ^ 2 ≤ B ^ 2 * w := by
  have h1 : a ^ 2 ≤ B ^ 2 := by nlinarith
  have h2 : b ^ 2 ≤ B ^ 2 := by nlinarith
  have h3 : a * b ≤ B ^ 2 := by nlinarith
  have h4 : (a - b) ^ 2 ≤ B ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left h1 hw]
  · nlinarith [mul_le_mul_of_nonneg_left h2 hw]
  · nlinarith [mul_le_mul_of_nonneg_left h3 hw]
  · nlinarith [mul_le_mul_of_nonneg_left h4 hw]

/-- The Dirichlet functional `D r = Σ π f_r²`. -/
noncomputable def Dr (P : V → V → ℝ) (π : V → ℝ) (x : V) (r : ℕ) : ℝ :=
  ∑' y, π y * fr P π x r y ^ 2

noncomputable def Er (P : V → V → ℝ) (π : V → ℝ) (x : V) (r : ℕ) : ℝ :=
  ∑' p : V × V, π p.1 * P p.1 p.2 * (fr P π x r p.1 - fr P π x (r + 1) p.2) ^ 2

lemma CSetup.E_eq (S : CSetup P π x) (r : ℕ) : Er P π x r = Dr P π x r - Dr P π x (r + 1) := by
  set B := 1 / π x with hB
  have hB0 : 0 ≤ B := (div_pos one_pos S.hx).le
  have hW : ∀ p : V × V, 0 ≤ π p.1 * P p.1 p.2 := fun p => mul_nonneg (S.h0 _) (S.hP.1 _ _)
  have hsc := fun (p : V × V) => scal (hW p) (S.fr_nonneg r p.1) (S.fr_le r p.1)
    (S.fr_nonneg (r + 1) p.2) (S.fr_le (r + 1) p.2)
  have hf0 := S.fr_nonneg
  obtain ⟨ha, ha1, -⟩ := S.sumW (g := fun p => π p.1 * P p.1 p.2 * fr P π x r p.1 ^ 2)
    (sq_nonneg B) (fun p => mul_nonneg (hW p) (sq_nonneg _)) (fun p => (hsc p).1)
  obtain ⟨hb, -, hb2⟩ := S.sumW (g := fun p => π p.1 * P p.1 p.2 * fr P π x (r + 1) p.2 ^ 2)
    (sq_nonneg B) (fun p => mul_nonneg (hW p) (sq_nonneg _)) (fun p => (hsc p).2.1)
  obtain ⟨hc, -, hc2⟩ := S.sumW
    (g := fun p => π p.1 * P p.1 p.2 * fr P π x r p.1 * fr P π x (r + 1) p.2)
    (sq_nonneg B) (fun p => mul_nonneg (mul_nonneg (hW p) (hf0 _ _)) (hf0 _ _))
    (fun p => (hsc p).2.2.1)
  have hA : ∑' p : V × V, π p.1 * P p.1 p.2 * fr P π x r p.1 ^ 2 = Dr P π x r := by
    rw [ha.tsum_prod' ha1]; unfold Dr; congr 1; funext y
    have : (fun z => π (y, z).1 * P (y, z).1 (y, z).2 * fr P π x r (y, z).1 ^ 2) =
        fun z => (π y * fr P π x r y ^ 2) * P y z := by funext z; simp only; ring
    rw [this, tsum_mul_left, (S.hP.2 y).tsum_eq, mul_one]
  have hBB : ∑' p : V × V, π p.1 * P p.1 p.2 * fr P π x (r + 1) p.2 ^ 2 = Dr P π x (r + 1) := by
    rw [tsum_swap2 hb hb2]; unfold Dr; congr 1; funext z
    have : (fun y => π (y, z).1 * P (y, z).1 (y, z).2 * fr P π x (r + 1) (y, z).2 ^ 2) =
        fun y => (π y * P y z) * fr P π x (r + 1) z ^ 2 := by funext y; simp only
    rw [this, tsum_mul_right, S.hstat z]
  have hCC : ∑' p : V × V, π p.1 * P p.1 p.2 * fr P π x r p.1 * fr P π x (r + 1) p.2 =
      Dr P π x (r + 1) := by
    rw [tsum_swap2 hc hc2]; unfold Dr; congr 1; funext z
    have : (fun y => π (y, z).1 * P (y, z).1 (y, z).2 * fr P π x r (y, z).1 * fr P π x (r + 1) (y, z).2) =
        fun y => (π y * P y z * fr P π x r y) * fr P π x (r + 1) z := by funext y; simp only
    rw [this, tsum_mul_right, ← S.fr_succ]; ring
  have hE : (fun p : V × V => π p.1 * P p.1 p.2 * (fr P π x r p.1 - fr P π x (r + 1) p.2) ^ 2) =
      fun p => (π p.1 * P p.1 p.2 * fr P π x r p.1 ^ 2 +
        π p.1 * P p.1 p.2 * fr P π x (r + 1) p.2 ^ 2) -
        2 * (π p.1 * P p.1 p.2 * fr P π x r p.1 * fr P π x (r + 1) p.2) := by
    funext p; ring
  unfold Er
  rw [hE, (ha.add hb).tsum_sub (hc.mul_left 2), ha.tsum_add hb, tsum_mul_left, hA, hBB, hCC]
  ring

lemma CSetup.E_nonneg (S : CSetup P π x) (r : ℕ) : 0 ≤ Er P π x r :=
  tsum_nonneg (fun p => mul_nonneg (mul_nonneg (S.h0 _) (S.hP.1 _ _)) (sq_nonneg _))

lemma CSetup.E_tendsto (S : CSetup P π x) : Tendsto (Er P π x) atTop (𝓝 0) := by
  have hD0 : ∀ r, 0 ≤ Dr P π x r := fun r =>
    tsum_nonneg (fun y => mul_nonneg (S.h0 y) (sq_nonneg _))
  have htel : ∀ N, ∑ r ∈ Finset.range N, Er P π x r = Dr P π x 0 - Dr P π x N := by
    intro N; induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, S.E_eq]; ring
  have hs : Summable (Er P π x) := summable_of_sum_range_le S.E_nonneg (c := Dr P π x 0)
    (fun N => by rw [htel]; linarith [hD0 N])
  exact hs.tendsto_atTop_zero

lemma CSetup.edge (S : CSetup P π x) {y z : V} (hW : 0 < π y * P y z) :
    Tendsto (fun r => fr P π x r y - fr P π x (r + 1) z) atTop (𝓝 0) := by
  set B := 1 / π x
  have hB0 : 0 ≤ B := (div_pos one_pos S.hx).le
  have hW0 : ∀ p : V × V, 0 ≤ π p.1 * P p.1 p.2 := fun p => mul_nonneg (S.h0 _) (S.hP.1 _ _)
  have hterm : ∀ r, π y * P y z * (fr P π x r y - fr P π x (r + 1) z) ^ 2 ≤ Er P π x r := by
    intro r
    obtain ⟨hs, -, -⟩ := S.sumW
      (g := fun p => π p.1 * P p.1 p.2 * (fr P π x r p.1 - fr P π x (r + 1) p.2) ^ 2)
      (sq_nonneg B) (fun p => mul_nonneg (hW0 p) (sq_nonneg _))
      (fun p => (scal (hW0 p) (S.fr_nonneg r p.1) (S.fr_le r p.1)
        (S.fr_nonneg (r + 1) p.2) (S.fr_le (r + 1) p.2)).2.2.2)
    exact le_hasSum hs.hasSum (y, z) (fun p _ => mul_nonneg (hW0 p) (sq_nonneg _))
  have h1 : Tendsto (fun r => π y * P y z * (fr P π x r y - fr P π x (r + 1) z) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun r => mul_nonneg hW.le (sq_nonneg _)) hterm S.E_tendsto
  have h2 : Tendsto (fun r => (fr P π x r y - fr P π x (r + 1) z) ^ 2) atTop (𝓝 0) := by
    have := h1.div_const (π y * P y z)
    rw [zero_div] at this
    exact this.congr (fun r => mul_div_cancel_left₀ _ hW.ne')
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at h3
  refine squeeze_zero_norm (fun r => le_of_eq ?_) h3
  simp only [Function.comp_apply, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

lemma CSetup.path (S : CSetup P π x) (hlazy : ∀ z, 1 / 2 ≤ P z z) {o n : V}
    (h : Relation.ReflTransGen (fun a b => 0 < π a ∧ 0 < P a b) o n) :
    Tendsto (fun r => fr P π x r n - fr P π x r o) atTop (𝓝 0) := by
  induction h with
  | refl => simp only [sub_self]; exact tendsto_const_nhds
  | @tail a b _ hab ih =>
    have hb : 0 < π b := by
      have h := le_hasSum (pi_summable_mul S.h0 S.h1.summable S.hP b).hasSum a
        (fun j _ => mul_nonneg (S.h0 j) (S.hP.1 j b))
      rw [S.hstat b] at h
      exact lt_of_lt_of_le (mul_pos hab.1 hab.2) h
    have h1 := S.edge (mul_pos hab.1 hab.2)
    have h2 := S.edge (y := b) (z := b) (mul_pos hb (by linarith [hlazy b]))
    convert (ih.sub h1).add h2 using 2 <;> ring

lemma CSetup.sum_fr (S : CSetup P π x) (r : ℕ) : ∑' n, π n * fr P π x r n = 1 := by
  have h := ((stoch_stepPow S.hP r).2 x).tsum_eq
  rw [← h]; congr 1; funext n; rw [S.mass_eq r n]

theorem CSetup.conv (S : CSetup P π x) (hlazy : ∀ z, 1 / 2 ≤ P z z) (o : V)
    (hpath : ∀ n, 0 < π n → Relation.ReflTransGen (fun a b => 0 < π a ∧ 0 < P a b) o n)
    (n : V) : Tendsto (fun r => stepPow P r x n) atTop (𝓝 (π n)) := by
  set B := 1 / π x
  have hdiff : ∀ m, Tendsto (fun r => π m * (fr P π x r o - fr P π x r m)) atTop (𝓝 0) := by
    intro m
    by_cases hm : π m = 0
    · simp only [hm, zero_mul]; exact tendsto_const_nhds
    · have hmp : 0 < π m := lt_of_le_of_ne (S.h0 m) (Ne.symm hm)
      have := (S.path hlazy (hpath m hmp)).const_mul (-(π m))
      rw [mul_zero] at this
      exact this.congr (fun r => by ring)
  have hdom := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun r m => π m * (fr P π x r o - fr P π x r m)) (g := fun _ => (0 : ℝ))
    (bound := fun m => π m * B) (S.h1.summable.mul_right B) hdiff
    (Eventually.of_forall (fun r m => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (S.h0 m)]
      refine mul_le_mul_of_nonneg_left ?_ (S.h0 m)
      rw [abs_le]
      have := S.fr_nonneg r o; have := S.fr_nonneg r m
      have := S.fr_le r o; have := S.fr_le r m
      constructor <;> linarith))
  simp only [tsum_zero] at hdom
  have hval : ∀ r, ∑' m, π m * (fr P π x r o - fr P π x r m) = fr P π x r o - 1 := by
    intro r
    have hs1 : Summable (fun m => π m * fr P π x r o) := S.h1.summable.mul_right _
    have hs2 : Summable (fun m => π m * fr P π x r m) :=
      Summable.of_nonneg_of_le (fun m => mul_nonneg (S.h0 m) (S.fr_nonneg r m))
        (fun m => mul_le_mul_of_nonneg_left (S.fr_le r m) (S.h0 m)) (S.h1.summable.mul_right B)
    simp_rw [mul_sub]
    rw [hs1.tsum_sub hs2, tsum_mul_right, S.h1.tsum_eq, one_mul, S.sum_fr]
  simp_rw [hval] at hdom
  have ho : Tendsto (fun r => fr P π x r o) atTop (𝓝 1) := by
    have := hdom.add_const 1
    rw [zero_add] at this
    exact this.congr (fun r => by ring)
  by_cases hn : π n = 0
  · have : ∀ r, stepPow P r x n = 0 := fun r => by rw [S.mass_eq r n, hn, zero_mul]
    simp only [this, hn]; exact tendsto_const_nhds
  · have hnp : 0 < π n := lt_of_le_of_ne (S.h0 n) (Ne.symm hn)
    have h := ((S.path hlazy (hpath n hnp)).add ho).const_mul (π n)
    rw [zero_add, mul_one] at h
    refine h.congr (fun r => ?_)
    rw [S.mass_eq r n]; ring

end S

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

end Generic

end SEFullM

open SEFullM in
/-- Convergence to equilibrium for a lazy chain with an invariant distribution. -/
theorem solution {V : Type*} [Countable V] [DecidableEq V]
    (P : V → V → ℝ) (π : V → ℝ) (hP : MarkovMixing.IsStochasticC P)
    (hπ0 : ∀ y, 0 ≤ π y) (hπ1 : HasSum π 1)
    (hstat : ∀ z, ∑' y, π y * P y z = π z)
    (hlazy : ∀ z, 1 / 2 ≤ P z z) (o : V)
    (hpath : ∀ n, 0 < π n →
      Relation.ReflTransGen (fun a b => 0 < π a ∧ 0 < P a b) o n)
    (x : V) (hx : 0 < π x) (n : V) :
    Filter.Tendsto (fun r => MarkovMixing.stepPow P r x n) Filter.atTop (nhds (π n)) := by
  exact SEFullM.CSetup.conv ⟨hP, hπ0, hπ1, hstat, hx⟩ hlazy o hpath n

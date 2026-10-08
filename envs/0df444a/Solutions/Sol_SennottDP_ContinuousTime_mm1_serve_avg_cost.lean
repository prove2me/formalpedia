-- Prove2me | solution 1 for SennottDP.ContinuousTime.mm1_serve_avg_cost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T18:50:09.614669+00:00
-- url     : https://prove2.me/submissions/3f97fcaf-7950-40df-802d-c4e6e623f91f

import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_MM1

open scoped ENNReal
open MeasureTheory ProbabilityTheory Filter Topology

namespace SennottDP.ContinuousTime

lemma mm1d_exp_mean {r : ℝ} (hr : 0 < r) :
    ∫⁻ s, ENNReal.ofReal s ∂(expMeasure r) = ENNReal.ofReal (1 / r) := by
  unfold expMeasure gammaMeasure
  have hm : Measurable (gammaPDF 1 r) := (measurable_gammaPDFReal 1 r).ennreal_ofReal
  have hid : Measurable (fun s : ℝ => ENNReal.ofReal s) := measurable_id.ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hm hid]
  have h1 : ∀ x, (gammaPDF 1 r * fun s => ENNReal.ofReal s) x =
      (Set.Ioi (0:ℝ)).indicator (fun x => ENNReal.ofReal (r * (x ^ ((2:ℝ) - 1) * Real.exp (-(r * x))))) x := by
    intro x
    simp only [Pi.mul_apply]
    by_cases hx : 0 < x
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hx)]
      have : gammaPDF 1 r x = exponentialPDF r x := rfl
      rw [this, exponentialPDF_of_nonneg hx.le, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      norm_num; ring
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      rw [ENNReal.ofReal_of_nonpos (by linarith), mul_zero]
  simp_rw [h1]
  rw [lintegral_indicator measurableSet_Ioi]
  have hint : ∫ x in Set.Ioi (0:ℝ), r * (x ^ ((2:ℝ) - 1) * Real.exp (-(r * x))) = 1 / r := by
    rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hr]
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num [Real.Gamma_two]
    field_simp
  rw [integral_eq_lintegral_of_nonneg_ae] at hint
  · have hne : (∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (r * (x ^ ((2:ℝ) - 1) * Real.exp (-(r * x))))) ≠ ⊤ := by
      intro h; rw [h] at hint; simp at hint; exact absurd hint (by positivity)
    rw [← hint, ENNReal.ofReal_toReal hne]
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ (fun x (hx : 0 < x) ↦ by positivity)
  · exact (by fun_prop : Measurable fun x : ℝ => r * (x ^ ((2:ℝ) - 1) * Real.exp (-(r * x)))).aestronglyMeasurable

section general
variable {S Act : Type}

noncomputable def mm1dStep (Ψ : CTMDC S Act) (e : S → Act) (f : S → ℝ≥0∞) (i : S) : ℝ≥0∞ :=
  ∑' j, Ψ.P i (e i) j * f j

noncomputable def mm1dPhi (Ψ : CTMDC S Act) (e : S → Act) (F : S → ℝ≥0∞) : ℕ → S → ℝ≥0∞
  | 0, _ => 0
  | n + 1, i => F i + mm1dStep Ψ e (mm1dPhi Ψ e F n) i

noncomputable def mm1dQ (Ψ : CTMDC S Act) (e : S → Act) (g : S → ℝ≥0∞) : ℕ → S → ℝ≥0∞
  | 0, i => g i
  | n + 1, i => mm1dStep Ψ e (mm1dQ Ψ e g n) i

lemma mm1d_step_add (Ψ : CTMDC S Act) (e : S → Act) (f g : S → ℝ≥0∞) (i : S) :
    mm1dStep Ψ e (fun j => f j + g j) i = mm1dStep Ψ e f i + mm1dStep Ψ e g i := by
  simp only [mm1dStep, mul_add]; exact ENNReal.tsum_add

lemma mm1d_step_mono (Ψ : CTMDC S Act) (e : S → Act) {f g : S → ℝ≥0∞} (h : ∀ j, f j ≤ g j)
    (i : S) : mm1dStep Ψ e f i ≤ mm1dStep Ψ e g i :=
  ENNReal.tsum_le_tsum fun j => by gcongr; exact h j

lemma mm1d_step_const_mul (Ψ : CTMDC S Act) (e : S → Act) (k : ℝ≥0∞) (f : S → ℝ≥0∞) (i : S) :
    mm1dStep Ψ e (fun j => k * f j) i = k * mm1dStep Ψ e f i := by
  simp only [mm1dStep]; rw [← ENNReal.tsum_mul_left]; congr 1; funext j; ring

lemma mm1d_step_sum (Ψ : CTMDC S Act) (e : S → Act) (f : ℕ → S → ℝ≥0∞) (n : ℕ) (i : S) :
    mm1dStep Ψ e (fun j => ∑ m ∈ Finset.range n, f m j) i =
      ∑ m ∈ Finset.range n, mm1dStep Ψ e (f m) i := by
  simp only [mm1dStep, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

lemma mm1d_phi_const_mul (Ψ : CTMDC S Act) (e : S → Act) (k : ℝ≥0∞) (F : S → ℝ≥0∞) :
    ∀ n i, mm1dPhi Ψ e (fun j => k * F j) n i = k * mm1dPhi Ψ e F n i := by
  intro n; induction n with
  | zero => intro i; simp [mm1dPhi]
  | succ n ih =>
    intro i
    simp only [mm1dPhi]
    rw [show mm1dPhi Ψ e (fun j => k * F j) n = fun j => k * mm1dPhi Ψ e F n j from funext ih,
      mm1d_step_const_mul, mul_add]

lemma mm1d_phi_sum (Ψ : CTMDC S Act) (e : S → Act) (F : S → ℝ≥0∞) :
    ∀ n i, mm1dPhi Ψ e F n i = ∑ m ∈ Finset.range n, mm1dQ Ψ e F m i := by
  intro n; induction n with
  | zero => intro i; simp [mm1dPhi]
  | succ n ih =>
    intro i
    simp only [mm1dPhi]
    rw [show mm1dPhi Ψ e F n = fun j => ∑ m ∈ Finset.range n, mm1dQ Ψ e F m j from funext ih,
      mm1d_step_sum, Finset.sum_range_succ']
    simp only [mm1dQ]; ring

lemma mm1d_tele (Ψ : CTMDC S Act) (e : S → Act) (A B g : S → ℝ≥0∞)
    (h : ∀ i, A i + mm1dStep Ψ e g i ≤ B i + g i) :
    ∀ n i, mm1dPhi Ψ e A n i + mm1dQ Ψ e g n i ≤ mm1dPhi Ψ e B n i + g i := by
  intro n; induction n with
  | zero => intro i; simp [mm1dPhi, mm1dQ]
  | succ n ih =>
    intro i
    simp only [mm1dPhi, mm1dQ]
    calc A i + mm1dStep Ψ e (mm1dPhi Ψ e A n) i + mm1dStep Ψ e (mm1dQ Ψ e g n) i
        = A i + mm1dStep Ψ e (fun j => mm1dPhi Ψ e A n j + mm1dQ Ψ e g n j) i := by
          rw [mm1d_step_add]; ring
      _ ≤ A i + mm1dStep Ψ e (fun j => mm1dPhi Ψ e B n j + g j) i := by
          gcongr; exact mm1d_step_mono Ψ e ih i
      _ = (A i + mm1dStep Ψ e g i) + mm1dStep Ψ e (mm1dPhi Ψ e B n) i := by
          rw [mm1d_step_add]; ring
      _ ≤ (B i + g i) + mm1dStep Ψ e (mm1dPhi Ψ e B n) i := add_le_add (h i) le_rfl
      _ = B i + mm1dStep Ψ e (mm1dPhi Ψ e B n) i + g i := by ring

lemma mm1d_tele' (Ψ : CTMDC S Act) (e : S → Act) (A B g : S → ℝ≥0∞)
    (h : ∀ i, B i + g i ≤ A i + mm1dStep Ψ e g i) :
    ∀ n i, mm1dPhi Ψ e B n i + g i ≤ mm1dPhi Ψ e A n i + mm1dQ Ψ e g n i := by
  intro n; induction n with
  | zero => intro i; simp [mm1dPhi, mm1dQ]
  | succ n ih =>
    intro i
    simp only [mm1dPhi, mm1dQ]
    calc B i + mm1dStep Ψ e (mm1dPhi Ψ e B n) i + g i
        = (B i + g i) + mm1dStep Ψ e (mm1dPhi Ψ e B n) i := by ring
      _ ≤ (A i + mm1dStep Ψ e g i) + mm1dStep Ψ e (mm1dPhi Ψ e B n) i := add_le_add (h i) le_rfl
      _ = A i + mm1dStep Ψ e (fun j => mm1dPhi Ψ e B n j + g j) i := by
          rw [mm1d_step_add]; ring
      _ ≤ A i + mm1dStep Ψ e (fun j => mm1dPhi Ψ e A n j + mm1dQ Ψ e g n j) i := by
          gcongr; exact mm1d_step_mono Ψ e ih i
      _ = A i + mm1dStep Ψ e (mm1dPhi Ψ e A n) i + mm1dStep Ψ e (mm1dQ Ψ e g n) i := by
          rw [mm1d_step_add]; ring

lemma mm1d_stat (Ψ : CTMDC S Act) (e : S → Act) (he : ∀ i, e i ∈ Ψ.A i)
    (hν : ∀ i, 0 < Ψ.ν i (e i)) (f : S → Act → ℝ → ℝ≥0∞) :
    ∀ n k sa t i, CTMDC.expectedSum (Ψ.ofStationary e he) f n k sa t i =
      mm1dPhi Ψ e (fun i => ∫⁻ s, f i (e i) s ∂(expMeasure (Ψ.ν i (e i)))) n i := by
  intro n; induction n with
  | zero => intros; simp [CTMDC.expectedSum, mm1dPhi]
  | succ n ih =>
    intro k sa t i
    simp only [CTMDC.expectedSum]
    simp only [ih]
    simp only [mm1dPhi, CTMDC.ofStationary]
    rw [Finset.sum_eq_single (e i)]
    · have := isProbabilityMeasure_expMeasure (hν i)
      simp only [if_true, one_mul]
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      rfl
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (he i) h

end general


section chain

lemma mm1d_step_mm1 (lam a : ℝ) (rates : Finset ℝ) (c : ℝ → ℝ) (hold : ℕ → ℝ)
    (hlam : 0 < lam) (ha0 : 0 < a) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (i : ℕ) :
    mm1dStep (mm1 lam rates c hold) (fun i => if i = 0 then 0 else a)
      (fun j => ENNReal.ofReal (f j)) i =
    ENNReal.ofReal (if i = 0 then f 1 else lam / (lam + a) * f (i + 1) + a / (lam + a) * f (i - 1)) := by
  unfold mm1dStep
  rcases i with _ | k
  · simp [mm1]
  · have hfun : (fun j => (mm1 lam rates c hold).P (k + 1)
        ((fun i => if i = 0 then (0:ℝ) else a) (k + 1)) j * ENNReal.ofReal (f j)) =
        fun j => (if j = k + 2 then ENNReal.ofReal (lam / (lam + a)) * ENNReal.ofReal (f (k + 2)) else 0)
          + (if j = k then ENNReal.ofReal (a / (lam + a)) * ENNReal.ofReal (f k) else 0) := by
      funext j
      simp only [mm1, Nat.add_one_ne_zero, if_false]
      by_cases h1 : j = k + 2
      · subst h1; simp
      · by_cases h2 : j = k
        · rw [h2]; have h5 : ¬ (k = k + 1 + 1) := by omega
          simp [h5]
        · have h3 : ¬ j = k + 1 + 1 := by omega
          have h4 : ¬ j + 1 = k + 1 := by omega
          simp [h1, h2, h3, h4]
    rw [hfun, ENNReal.tsum_add, tsum_ite_eq, tsum_ite_eq]
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    have hs : 0 < lam + a := by linarith
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by have := hf (k+2); positivity) (by have := hf k; positivity)]

lemma mm1d_ofReal_ineq {x y z u : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hu : 0 ≤ u)
    (h : x + y ≤ z + u) :
    ENNReal.ofReal x + ENNReal.ofReal y ≤ ENNReal.ofReal z + ENNReal.ofReal u := by
  rw [← ENNReal.ofReal_add hx hy, ← ENNReal.ofReal_add hz hu]; exact ENNReal.ofReal_le_ofReal h

lemma mm1d_phi_const (lam a : ℝ) (rates : Finset ℝ) (c : ℝ → ℝ) (hold : ℕ → ℝ)
    (hlam : 0 < lam) (ha0 : 0 < a) (k : ℝ) (hk : 0 ≤ k) :
    ∀ n i, mm1dPhi (mm1 lam rates c hold) (fun i => if i = 0 then 0 else a)
      (fun _ => ENNReal.ofReal k) n i = n * ENNReal.ofReal k := by
  intro n; induction n with
  | zero => intro i; simp [mm1dPhi]
  | succ n ih =>
    intro i
    simp only [mm1dPhi]
    rw [show mm1dPhi (mm1 lam rates c hold) (fun i => if i = 0 then 0 else a)
      (fun _ => ENNReal.ofReal k) n = fun _ => ENNReal.ofReal (n * k) from funext fun j => by
        rw [ih, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]]
    rw [mm1d_step_mm1 lam a rates c hold hlam ha0 _ (fun _ => by positivity)]
    have hs : 0 < lam + a := by linarith
    have : (if i = 0 then (n:ℝ) * k else lam / (lam + a) * (n * k) + a / (lam + a) * (n * k))
        = n * k := by
      split_ifs
      · rfl
      · field_simp
    rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    push_cast; ring

noncomputable def mm1dW (α β : ℝ) (n : ℕ) : ℝ := α * ((n:ℝ) * ((n:ℝ) - 1)) / 2 + β * n

lemma mm1d_nn (n : ℕ) : (0:ℝ) ≤ (n:ℝ) * ((n:ℝ) - 1) := by
  rcases n with _ | n
  · simp
  · push_cast; nlinarith

lemma mm1d_W_nn {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) : 0 ≤ mm1dW α β n := by
  unfold mm1dW; have := mm1d_nn n; positivity

lemma mm1d_poisson (lam H a ca : ℝ) (hlam : 0 < lam) (hla : lam < a) (i : ℕ) :
    let nu : ℝ := if i = 0 then lam else lam + a
    let gr : ℝ := if i = 0 then 0 else ca + H * i
    let W := mm1dW (H / (a - lam)) (ca / a + H / (a - lam))
    gr * (1 / nu) + (if i = 0 then W 1 else lam / (lam + a) * W (i + 1) + a / (lam + a) * W (i - 1))
      = (lam / a * ca + H * (lam / a) / (1 - lam / a)) * (1 / nu) + W i := by
  intro nu gr W
  have ha0 : 0 < a := by linarith
  have h1 : a - lam ≠ 0 := by linarith
  have h2 : 1 - lam / a = (a - lam) / a := by field_simp
  rcases i with _ | k
  · simp only [nu, gr, W, mm1dW, if_true]
    rw [h2]; push_cast; field_simp; ring
  · simp only [nu, gr, W, mm1dW, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [h2]; push_cast
    have hs : lam + a ≠ 0 := by linarith
    field_simp; ring

lemma mm1d_lyap (lam a α β : ℝ) (hlam : 0 < lam) (hla : lam < a) (hα : 0 ≤ α) (hβ : 0 ≤ β) (i : ℕ) :
    let κ : ℝ := (α + 1) / (3 * ((a - lam) / (lam + a)))
    let V : ℕ → ℝ := fun n => κ * (n:ℝ) ^ 3
    mm1dW α β i + (if i = 0 then V 1 else lam / (lam + a) * V (i + 1) + a / (lam + a) * V (i - 1))
      ≤ ((β + 3 * κ) ^ 2 / 4 + κ) + V i := by
  intro κ V
  have ha0 : 0 < a := by linarith
  have hs : 0 < lam + a := by linarith
  have hd : 0 < (a - lam) / (lam + a) := div_pos (by linarith) hs
  have hκ : 0 ≤ κ := by positivity
  have hκd : 3 * ((a - lam) / (lam + a)) * κ = α + 1 := by
    have h1 : a - lam ≠ 0 := by linarith
    simp only [κ]; field_simp
  rcases i with _ | k
  · simp only [V, mm1dW, if_true]; push_cast; nlinarith [sq_nonneg (β + 3 * κ)]
  · simp only [V, mm1dW, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    push_cast
    set x : ℝ := (k:ℝ) + 1 with hx
    have hk : (k:ℝ) = x - 1 := by rw [hx]; ring
    have hx1 : 1 ≤ x := by rw [hx]; have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith
    set p := lam / (lam + a) with hp
    set q := a / (lam + a) with hq
    set d := (a - lam) / (lam + a) with hdd
    have hpq : p + q = 1 := by rw [hp, hq]; field_simp
    have hpq' : p - q = -d := by rw [hp, hq, hdd]; field_simp; ring
    have key : p * (κ * (x + 1) ^ 3) + q * (κ * (x - 1) ^ 3) =
        κ * x ^ 3 + κ * (3 * x ^ 2 * (p - q) + 3 * x + (p - q)) := by
      have : q = 1 - p := by linarith
      rw [this]; ring
    rw [hk, key, hpq']
    have hW : α * (x * (x - 1)) / 2 ≤ α * x ^ 2 := by nlinarith
    nlinarith [sq_nonneg (x - (β + 3 * κ) / 2), mul_nonneg hκ hd.le]


theorem mm1d_core (lam H a : ℝ) (rates : Finset ℝ) (c : ℝ → ℝ) (hlam : 0 < lam)
    (hca : 0 ≤ c a) (hH : 0 < H) (ha : a ∈ rates) (hla : lam < a) (i : ℕ) :
    CTMDC.avgCost (mm1Serve lam rates c (fun k => H * k) a ha) i =
      ENNReal.ofReal (lam / a * c a + H * (lam / a) / (1 - lam / a)) := by
  have ha0 : 0 < a := by linarith
  have hs : 0 < lam + a := by linarith
  have hla' : 0 < 1 - lam / a := by rw [sub_pos, div_lt_one ha0]; exact hla
  set Jr := lam / a * c a + H * (lam / a) / (1 - lam / a) with hJr
  have hJr0 : 0 ≤ Jr := by positivity
  set Ψ := mm1 lam rates c (fun k : ℕ => H * (k:ℝ)) with hΨ
  set e : ℕ → ℝ := fun i => if i = 0 then 0 else a with he_def
  have he : ∀ i, e i ∈ Ψ.A i := by intro i; by_cases h : i = 0 <;> simp [Ψ, e, mm1, h, ha]
  set nu : ℕ → ℝ := fun i => if i = 0 then lam else lam + a with hnu
  set gr : ℕ → ℝ := fun i => if i = 0 then 0 else c a + H * i with hgr
  have hν : ∀ i, Ψ.ν i (e i) = nu i := by intro i; by_cases h : i = 0 <;> simp [Ψ, e, nu, mm1, h]
  have hνpos : ∀ i, 0 < Ψ.ν i (e i) := by intro i; rw [hν]; simp only [nu]; split_ifs <;> linarith
  have hnupos : ∀ i, 0 < nu i := fun i => hν i ▸ hνpos i
  have hgr0 : ∀ i, 0 ≤ gr i := by intro i; simp only [gr]; split_ifs <;> positivity
  set FT : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (1 / nu i) with hFT
  set FC : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (gr i * (1 / nu i)) with hFC
  have hFT' : (fun i => ∫⁻ s, ENNReal.ofReal s ∂(expMeasure (Ψ.ν i (e i)))) = FT := by
    funext i; rw [mm1d_exp_mean (hνpos i), hν]
  have hFC' : (fun i => ∫⁻ s, Ψ.periodCost i (e i) s ∂(expMeasure (Ψ.ν i (e i)))) = FC := by
    funext i
    have hpc : ∀ s, Ψ.periodCost i (e i) s = ENNReal.ofReal (gr i) * ENNReal.ofReal s := by
      intro s; by_cases h : i = 0 <;> simp [CTMDC.periodCost, Ψ, mm1, e, gr, h]
    simp_rw [hpc]
    rw [lintegral_const_mul (f := fun s : ℝ => ENNReal.ofReal s) _ (measurable_id.ennreal_ofReal : Measurable fun s : ℝ => ENNReal.ofReal s), mm1d_exp_mean (hνpos i), hν,
      ← ENNReal.ofReal_mul (hgr0 i)]
  have hθ : mm1Serve lam rates c (fun k => H * k) a ha = Ψ.ofStationary e he := rfl
  have hcost : ∀ n, CTMDC.expCostN (mm1Serve lam rates c (fun k => H * k) a ha) n i =
      mm1dPhi Ψ e FC n i := by
    intro n; rw [hθ, CTMDC.expCostN, mm1d_stat Ψ e he hνpos, hFC']
  have htime : ∀ n, CTMDC.expTimeN (mm1Serve lam rates c (fun k => H * k) a ha) n i =
      mm1dPhi Ψ e FT n i := by
    intro n; rw [hθ, CTMDC.expTimeN, mm1d_stat Ψ e he hνpos, hFT']
  unfold CTMDC.avgCost
  simp_rw [hcost, htime]
  -- step formula
  have hstep : ∀ (f : ℕ → ℝ), (∀ j, 0 ≤ f j) → ∀ j, mm1dStep Ψ e (fun j => ENNReal.ofReal (f j)) j =
      ENNReal.ofReal (if j = 0 then f 1 else lam / (lam + a) * f (j + 1) + a / (lam + a) * f (j - 1)) :=
    fun f hf j => mm1d_step_mm1 lam a rates c _ hlam ha0 f hf j
  have hphic : ∀ k : ℝ, 0 ≤ k → ∀ n j, mm1dPhi Ψ e (fun _ => ENNReal.ofReal k) n j = n * ENNReal.ofReal k :=
    fun k hk => mm1d_phi_const lam a rates c _ hlam ha0 k hk
  set α := H / (a - lam) with hα
  set β := c a / a + H / (a - lam) with hβ
  have hα0 : 0 ≤ α := div_nonneg hH.le (by linarith)
  have hβ0 : 0 ≤ β := by
    have : 0 ≤ H / (a - lam) := div_nonneg hH.le (by linarith)
    positivity
  set W := mm1dW α β with hW
  have hW0 : ∀ j, 0 ≤ W j := mm1d_W_nn hα0 hβ0
  set w : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (W j) with hw
  set J := ENNReal.ofReal Jr with hJ
  set T := fun n => mm1dPhi Ψ e FT n i with hT
  set C := fun n => mm1dPhi Ψ e FC n i with hC
  set r := fun n => mm1dQ Ψ e w n i with hr
  have hJFT : (fun j => J * FT j) = fun j => ENNReal.ofReal (Jr * (1 / nu j)) := by
    funext j; simp only [J, FT]; rw [ENNReal.ofReal_mul hJr0]
  have hpois : ∀ j, FC j + mm1dStep Ψ e w j = J * FT j + w j := by
    intro j
    have h := mm1d_poisson lam H a (c a) hlam hla j
    dsimp only at h
    have h2 := congrFun hJFT j
    rw [h2]
    simp only [FC, w]
    rw [hstep W hW0 j, ← ENNReal.ofReal_add (mul_nonneg (hgr0 j) (by have := hnupos j; positivity))
      (by split_ifs <;> first | exact hW0 _ | (have := hW0 (j+1); have := hW0 (j-1); positivity)),
      ← ENNReal.ofReal_add (mul_nonneg hJr0 (by have := hnupos j; positivity)) (hW0 j)]
    congr 1
  have hup : ∀ n : ℕ, C n + r n ≤ J * T n + w i := by
    intro n
    have := mm1d_tele Ψ e FC (fun j => J * FT j) w (fun j => (hpois j).le) n i
    rwa [mm1d_phi_const_mul] at this
  have hlo : ∀ n : ℕ, J * T n + w i ≤ C n + r n := by
    intro n
    have := mm1d_tele' Ψ e FC (fun j => J * FT j) w (fun j => (hpois j).ge) n i
    rwa [mm1d_phi_const_mul] at this
  set μr := 1 / (lam + a) with hμr
  have hμr0 : 0 < μr := by positivity
  set μ := ENNReal.ofReal μr with hμ
  have hμ0 : μ ≠ 0 := by simp [μ, hμr0]
  have hμtop : μ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hTlo : ∀ n : ℕ, (n : ℝ≥0∞) * μ ≤ T n := by
    intro n
    have := mm1d_tele Ψ e (fun _ => μ) FT (fun _ => 0) (fun j => by
      simp only [mm1dStep, mul_zero, tsum_zero, add_zero, FT, μ]
      apply ENNReal.ofReal_le_ofReal
      simp only [μr, nu]; split_ifs
      · exact one_div_le_one_div_of_le hlam (by linarith)
      · exact le_rfl) n i
    rw [hphic μr hμr0.le] at this
    exact le_trans le_self_add (by simpa using this)
  have hThi : ∀ n : ℕ, T n ≤ n * ENNReal.ofReal (1 / lam) := by
    intro n
    have := mm1d_tele Ψ e FT (fun _ => ENNReal.ofReal (1 / lam)) (fun _ => 0) (fun j => by
      simp only [mm1dStep, mul_zero, tsum_zero, add_zero, FT]
      apply ENNReal.ofReal_le_ofReal
      simp only [nu]; split_ifs
      · exact le_rfl
      · exact one_div_le_one_div_of_le hlam (by linarith)) n i
    rw [hphic _ (by positivity)] at this
    exact le_trans le_self_add (by simpa using this)
  have hTtop : ∀ n : ℕ, T n ≠ ⊤ := fun n => ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) ENNReal.ofReal_ne_top) (hThi n)
  have hTpos : ∀ n : ℕ, 1 ≤ n → T n ≠ 0 := by
    intro n hn h
    have := hTlo n
    rw [h, nonpos_iff_eq_zero, mul_eq_zero] at this
    rcases this with h1 | h1
    · simp at h1; omega
    · exact hμ0 h1
  have hwtop : w i ≠ ⊤ := ENNReal.ofReal_ne_top
  apply le_antisymm
  · -- upper bound
    have hbound : ∀ᶠ n : ℕ in atTop, C n / T n ≤ J + w i / μ * (n : ℝ≥0∞)⁻¹ := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      apply ENNReal.div_le_of_le_mul
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by simp; omega
      calc C n ≤ J * T n + w i := le_trans le_self_add (hup n)
        _ = J * T n + w i / μ * ((n : ℝ≥0∞)⁻¹ * ((n : ℝ≥0∞) * μ)) := by
          rw [← mul_assoc ((n : ℝ≥0∞)⁻¹), ENNReal.inv_mul_cancel hn0 (ENNReal.natCast_ne_top n),
            one_mul, ENNReal.div_mul_cancel hμ0 hμtop]
        _ ≤ J * T n + w i / μ * ((n : ℝ≥0∞)⁻¹ * T n) := by gcongr; exact hTlo n
        _ = (J + w i / μ * (n : ℝ≥0∞)⁻¹) * T n := by ring
    have hlim : Tendsto (fun n : ℕ => J + w i / μ * (n : ℝ≥0∞)⁻¹) atTop (𝓝 J) := by
      have := (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
        (Or.inr (ENNReal.div_ne_top hwtop hμ0) : (0:ℝ≥0∞) ≠ 0 ∨ w i / μ ≠ ⊤)).const_add J
      simpa using this
    calc limsup (fun n => C n / T n) atTop
        ≤ limsup (fun n : ℕ => J + w i / μ * (n : ℝ≥0∞)⁻¹) atTop := limsup_le_limsup hbound
      _ = J := hlim.limsup_eq
  · -- lower bound
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    rw [← tsub_le_iff_right]
    apply le_limsup_of_frequently_le'
    rw [frequently_atTop]
    intro N
    set K := (β + 3 * ((α + 1) / (3 * ((a - lam) / (lam + a))))) ^ 2 / 4 +
      (α + 1) / (3 * ((a - lam) / (lam + a))) with hK
    set κ := (α + 1) / (3 * ((a - lam) / (lam + a))) with hκ
    have hκ0 : 0 ≤ κ := by
      have : 0 < (a - lam) / (lam + a) := div_pos (by linarith) hs
      positivity
    have hK0 : 0 ≤ K := by positivity
    set V : ℕ → ℝ := fun n => κ * (n:ℝ) ^ 3 with hV
    have hV0 : ∀ j, 0 ≤ V j := fun j => by positivity
    have hly : ∀ n : ℕ, mm1dPhi Ψ e w n i + mm1dQ Ψ e (fun j => ENNReal.ofReal (V j)) n i ≤
        n * ENNReal.ofReal K + ENNReal.ofReal (V i) := by
      intro n
      have := mm1d_tele Ψ e w (fun _ => ENNReal.ofReal K) (fun j => ENNReal.ofReal (V j)) (fun j => by
        rw [hstep V hV0 j]
        exact mm1d_ofReal_ineq (hW0 j) (by split_ifs <;> positivity) hK0 (hV0 j)
          (mm1d_lyap lam a α β hlam hla hα0 hβ0 j)) n i
      rwa [hphic K hK0] at this
    set R := ENNReal.ofReal (V i) + 2 * ENNReal.ofReal K with hR
    have hRtop : R ≠ ⊤ := by simp [R, ENNReal.mul_eq_top]
    have hεμ0 : (ε : ℝ≥0∞) * μ ≠ 0 := mul_ne_zero (by simpa using hε.ne') hμ0
    have hεμtop : (ε : ℝ≥0∞) * μ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hμtop
    obtain ⟨M0, hM0⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hRtop hεμ0)
    set M := max M0 (max N 1) with hM
    have hM1 : 1 ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
    have hMN : N ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
    have hRM : R ≤ M * ((ε : ℝ≥0∞) * μ) := by
      calc R = R / ((ε : ℝ≥0∞) * μ) * ((ε : ℝ≥0∞) * μ) := (ENNReal.div_mul_cancel hεμ0 hεμtop).symm
        _ ≤ M0 * ((ε : ℝ≥0∞) * μ) := by gcongr
        _ ≤ M * ((ε : ℝ≥0∞) * μ) := by gcongr; exact_mod_cast le_max_left _ _
    -- pigeonhole
    have hsum : ∑ m ∈ Finset.Ico M (2 * M), r m ≤ ∑ m ∈ Finset.Ico M (2 * M), R := by
      rw [Finset.sum_const, Nat.card_Ico, show 2 * M - M = M by omega, nsmul_eq_mul]
      calc ∑ m ∈ Finset.Ico M (2 * M), r m ≤ ∑ m ∈ Finset.range (2 * M), r m :=
            Finset.sum_le_sum_of_subset (fun x hx => by simp at hx ⊢; omega)
        _ = mm1dPhi Ψ e w (2 * M) i := (mm1d_phi_sum Ψ e w (2 * M) i).symm
        _ ≤ mm1dPhi Ψ e w (2 * M) i + mm1dQ Ψ e (fun j => ENNReal.ofReal (V j)) (2 * M) i :=
            le_self_add
        _ ≤ ((2 * M : ℕ) : ℝ≥0∞) * ENNReal.ofReal K + ENNReal.ofReal (V i) := hly _
        _ ≤ M * R := by
            rw [hR, mul_add]; push_cast
            have h1 : ENNReal.ofReal (V i) ≤ (M : ℝ≥0∞) * ENNReal.ofReal (V i) :=
              le_mul_of_one_le_left (zero_le) (by exact_mod_cast hM1)
            calc 2 * (M : ℝ≥0∞) * ENNReal.ofReal K + ENNReal.ofReal (V i)
                = ENNReal.ofReal (V i) + (M : ℝ≥0∞) * (2 * ENNReal.ofReal K) := by ring
              _ ≤ (M : ℝ≥0∞) * ENNReal.ofReal (V i) + (M : ℝ≥0∞) * (2 * ENNReal.ofReal K) :=
                  add_le_add h1 le_rfl
    obtain ⟨m, hm, hrm⟩ := ENNReal.exists_le_of_sum_le ⟨M, by simp; omega⟩ hsum
    simp only [Finset.mem_Ico] at hm
    refine ⟨m, by omega, ?_⟩
    have hT0 := hTpos m (by omega)
    have hTt := hTtop m
    have hrε : r m ≤ ε * T m := by
      calc r m ≤ R := hrm
        _ ≤ M * ((ε : ℝ≥0∞) * μ) := hRM
        _ ≤ m * ((ε : ℝ≥0∞) * μ) := by gcongr; exact_mod_cast hm.1
        _ = ε * (m * μ) := by ring
        _ ≤ ε * T m := by gcongr; exact hTlo m
    rw [ENNReal.le_div_iff_mul_le (Or.inl hT0) (Or.inl hTt), ENNReal.sub_mul (fun _ _ => hTt),
      tsub_le_iff_right]
    calc J * T m ≤ J * T m + w i := le_self_add
      _ ≤ C m + r m := hlo m
      _ ≤ C m + ε * T m := by gcongr

end chain

end SennottDP.ContinuousTime

open SennottDP.ContinuousTime


theorem solution (lam H a : ℝ) (rates : Finset ℝ) (c : ℝ → ℝ) (hlam : 0 < lam)
    (hrates : ∀ b ∈ rates, 0 < b) (hc : ∀ b ∈ rates, 0 ≤ c b) (hH : 0 < H)
    (ha : a ∈ rates) (hla : lam < a) :
    ∀ i, CTMDC.avgCost (mm1Serve lam rates c (fun k => H * k) a ha) i =
      ENNReal.ofReal (lam / a * c a + H * (lam / a) / (1 - lam / a)) := by
  exact fun i => mm1d_core lam H a rates c hlam (hc a ha) hH ha hla i

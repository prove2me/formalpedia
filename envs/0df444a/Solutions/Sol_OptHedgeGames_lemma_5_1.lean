-- Prove2me | solution 1 for OptHedgeGames.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T19:50:22.540545+00:00
-- url     : https://prove2.me/submissions/85568592-2083-4dd2-83bf-f1f8c3dceea8

import Mathlib
import Definitions.Def_OptHedgeGames_TwoPlayerRun
import Theorems.Thm_OptHedgeGames_lemma_A_2

open scoped Matrix

namespace SolOHG51

open OptHedgeGames

variable {n : ℕ}

lemma Z_pos {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) (x : Fin n → ℝ) :
    0 < ∑ c, p c * Real.exp (x c) := by
  obtain ⟨a, ha⟩ : ∃ a, 0 < p a := by
    by_contra h
    push_neg at h
    have : ∑ a, p a ≤ 0 := Finset.sum_nonpos fun a _ => h a
    linarith [hp.2]
  calc 0 < p a * Real.exp (x a) := mul_pos ha (Real.exp_pos _)
    _ ≤ ∑ c, p c * Real.exp (x c) :=
      Finset.single_le_sum (f := fun c => p c * Real.exp (x c))
        (fun c _ => mul_nonneg (hp.1 c) (Real.exp_pos _).le) (Finset.mem_univ a)

/-- Tilting preserves positive probability vectors. -/
lemma tilt_good {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) (hpos : ∀ a, 0 < p a)
    (x : Fin n → ℝ) : tilt p x ∈ stdSimplex ℝ (Fin n) ∧ ∀ a, 0 < tilt p x a := by
  have hZ := Z_pos hp x
  refine ⟨⟨fun a => ?_, ?_⟩, fun a => ?_⟩
  · unfold tilt; exact div_nonneg (mul_nonneg (hp.1 a) (Real.exp_pos _).le) hZ.le
  · unfold tilt; rw [← Finset.sum_div, div_self hZ.ne']
  · unfold tilt; exact div_pos (mul_pos (hpos a) (Real.exp_pos _)) hZ

lemma uniform_good (hn : 1 ≤ n) : uniform n ∈ stdSimplex ℝ (Fin n) ∧ ∀ a, 0 < uniform n a := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨⟨fun a => ?_, ?_⟩, fun a => ?_⟩
  · unfold uniform; positivity
  · unfold uniform; simp; field_simp
  · unfold uniform; positivity

lemma state_good (hn : 1 ≤ n) (G : Game n) (η : ℝ) (t : ℕ) :
    ((G.state η t).x1 ∈ stdSimplex ℝ (Fin n) ∧ ∀ a, 0 < (G.state η t).x1 a) ∧
    ((G.state η t).x2 ∈ stdSimplex ℝ (Fin n) ∧ ∀ a, 0 < (G.state η t).x2 a) := by
  induction t with
  | zero => exact ⟨uniform_good hn, uniform_good hn⟩
  | succ k ih =>
    exact ⟨tilt_good ih.1.1 ih.1.2 _, tilt_good ih.2.1 ih.2.2 _⟩

lemma mulVec_mem (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ a b, M a b ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) (a : Fin n) :
    0 ≤ (M *ᵥ x) a ∧ (M *ᵥ x) a ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  constructor
  · exact Finset.sum_nonneg fun b _ => mul_nonneg (hM a b).1 (hx.1 b)
  · calc ∑ b, M a b * x b ≤ ∑ b, 1 * x b :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hM a b).2 (hx.1 b)
      _ = 1 := by simp [hx.2]

lemma l1_mem (hn : 1 ≤ n) (G : Game n) (η : ℝ) (t : ℕ) (a : Fin n) :
    0 ≤ G.l1 η t a ∧ G.l1 η t a ≤ 1 := by
  cases t with
  | zero => simp [Game.l1]
  | succ k =>
    simp only [Game.l1]
    exact mulVec_mem G.A G.A_mem _ (state_good hn G η _).2.1 a

lemma x1_good (hn : 1 ≤ n) (G : Game n) (η : ℝ) (t : ℕ) :
    G.x1 η t ∈ stdSimplex ℝ (Fin n) ∧ ∀ a, 0 < G.x1 η t a :=
  (state_good hn G η _).1

/-- The update rule written with the loss vectors. -/
lemma x1_succ (G : Game n) (η : ℝ) (t : ℕ) (ht : 1 ≤ t) :
    G.x1 η (t + 1) = tilt (G.x1 η t) (fun a => -η * (2 * G.l1 η t a - G.l1 η (t - 1) a)) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp only [Game.x1, Nat.add_sub_cancel]
  rw [Game.state]
  simp only
  congr 1
  funext a
  congr 2
  cases k with
  | zero => first | rfl | simp [Game.state]
  | succ j => first | rfl | simp [Game.state, Game.x2]

lemma var_nonneg (p v : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) : 0 ≤ var p v :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hp.1 a) (sq_nonneg _)

lemma var_le_sum (q v : Fin n → ℝ) (hq1 : ∑ a, q a = 1) (c : ℝ) :
    var q v ≤ ∑ a, q a * (v a - c) ^ 2 := by
  unfold var
  have e : ∀ a, q a * (v a - c) ^ 2 = q a * (v a - ∑ c, q c * v c) ^ 2 +
      (2 * ((∑ c, q c * v c) - c)) * (q a * v a) -
      (((∑ c, q c * v c) - c) * ((∑ c, q c * v c) + c)) * q a := fun a => by ring
  rw [Finset.sum_congr rfl fun a _ => e a, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hq1]
  nlinarith [sq_nonneg ((∑ c, q c * v c) - c)]

/-- Variance of a `[0, 1]`-valued vector is at most `1/4`. -/
lemma var_le_quarter (q v : Fin n → ℝ) (hq : q ∈ stdSimplex ℝ (Fin n))
    (hv : ∀ a, 0 ≤ v a ∧ v a ≤ 1) : var q v ≤ 1 / 4 := by
  refine le_trans (var_le_sum q v hq.2 (1 / 2)) ?_
  calc ∑ a, q a * (v a - 1 / 2) ^ 2 ≤ ∑ a, q a * (1 / 4) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          (by nlinarith [hv a]) (hq.1 a)
    _ = 1 / 4 := by rw [← Finset.sum_mul, hq.2, one_mul]

lemma wcs (q x y : Fin n → ℝ) (hq0 : ∀ a, 0 ≤ q a) :
    ∑ a, q a * x a * y a ≤
      Real.sqrt (∑ a, q a * x a ^ 2) * Real.sqrt (∑ a, q a * y a ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => Real.sqrt (q a) * x a)
    (fun a => Real.sqrt (q a) * y a)
  have e1 : ∀ a, Real.sqrt (q a) * x a * (Real.sqrt (q a) * y a) = q a * x a * y a := fun a => by
    rw [show Real.sqrt (q a) * x a * (Real.sqrt (q a) * y a) =
      (Real.sqrt (q a) * Real.sqrt (q a)) * x a * y a by ring, Real.mul_self_sqrt (hq0 a)]
  have e2 : ∀ (u : Fin n → ℝ) a, (Real.sqrt (q a) * u a) ^ 2 = q a * u a ^ 2 := fun u a => by
    rw [mul_pow, Real.sq_sqrt (hq0 a)]
  simp only [e1, e2] at h
  have hA : 0 ≤ ∑ a, q a * x a ^ 2 := Finset.sum_nonneg fun a _ => mul_nonneg (hq0 a) (sq_nonneg _)
  rw [← Real.sqrt_mul hA]
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt h)

/-- `‖αu + βw‖_p ≤ |α|‖u‖_p + |β|‖w‖_p`. -/
lemma vnorm_comb (p u w : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) (α β : ℝ) :
    vnorm p (fun a => α * u a + β * w a) ≤ |α| * vnorm p u + |β| * vnorm p w := by
  set mu := ∑ c, p c * u c
  set mw := ∑ c, p c * w c
  have hmean : ∑ c, p c * (α * u c + β * w c) = α * mu + β * mw := by
    simp only [mu, mw, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  set U : Fin n → ℝ := fun a => α * (u a - mu)
  set W : Fin n → ℝ := fun a => β * (w a - mw)
  have hvar : var p (fun a => α * u a + β * w a) = ∑ a, p a * (U a + W a) ^ 2 := by
    unfold var
    rw [hmean]
    exact Finset.sum_congr rfl fun a _ => by simp only [U, W]; ring
  have hU : ∑ a, p a * U a ^ 2 = |α| ^ 2 * var p u := by
    unfold var
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by simp only [U]; rw [sq_abs]; ring
  have hW : ∑ a, p a * W a ^ 2 = |β| ^ 2 * var p w := by
    unfold var
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by simp only [W]; rw [sq_abs]; ring
  have hcs := wcs p U W hp.1
  have hexp : ∑ a, p a * (U a + W a) ^ 2 =
      ∑ a, p a * U a ^ 2 + ∑ a, p a * W a ^ 2 + 2 * ∑ a, p a * U a * W a := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hvu := var_nonneg p u hp
  have hvw := var_nonneg p w hp
  unfold vnorm
  rw [hvar, hexp, hU, hW]
  rw [hU, hW] at hcs
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _),
    Real.sqrt_sq (abs_nonneg _)] at hcs
  have hR : 0 ≤ |α| * Real.sqrt (var p u) + |β| * Real.sqrt (var p w) := by positivity
  rw [Real.sqrt_le_left hR]
  have s1 := Real.sq_sqrt hvu
  have s2 := Real.sq_sqrt hvw
  nlinarith [hcs]

lemma osc_le (hn : 1 ≤ n) (z : Fin n → ℝ) (lo hi : ℝ) (hz : ∀ a, lo ≤ z a ∧ z a ≤ hi) :
    osc z ≤ hi - lo := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold osc
  have h1 : (⨆ a, z a) ≤ hi := ciSup_le fun a => (hz a).2
  have h2 : lo ≤ ⨅ a, z a := le_ciInf fun a => (hz a).1
  linarith

end SolOHG51

open OptHedgeGames SolOHG51 in
theorem solution {n : ℕ} (hn : 1 ≤ n) (G : Game n) (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 100) :
    (∀ t : ℕ, 1 ≤ t →
      (∀ a, Real.exp (-(3 * η)) ≤ G.x1 η (t + 1) a / G.x1 η t a ∧
        G.x1 η (t + 1) a / G.x1 η t a ≤ Real.exp (3 * η)) ∧
      l1Norm (G.x1 η (t + 1) - G.x1 η t) ≤ 3 * η * (G.v η t + G.v η (t - 1))) ∧
    (∀ T : ℕ, 1 ≤ T →
      ∑ t ∈ Finset.Icc 1 T, var (G.x1 η t) (G.l1 η t) ≤
        Real.exp (3 * η) * cumVariance (G.x1 η) (G.l1 η) T + 1 / 4) := by
  -- the tilt vector of round `t` and its oscillation
  set zt : ℕ → Fin n → ℝ := fun t a => -η * (2 * G.l1 η t a - G.l1 η (t - 1) a) with hzt
  have hosc : ∀ t, osc (zt t) ≤ 3 * η := by
    intro t
    have := osc_le hn (zt t) (-2 * η) η (fun a => by
      have h1 := l1_mem hn G η t a
      have h2 := l1_mem hn G η (t - 1) a
      simp only [hzt]
      constructor <;> nlinarith)
    linarith
  have hA2 : ∀ t, 1 ≤ t → _ := fun t (ht : 1 ≤ t) =>
    OptHedgeGames.lemma_A_2 (G.x1 η t) (x1_good hn G η t).1 (zt t) (3 * η) (hosc t)
  have hstep : ∀ t, 1 ≤ t → G.x1 η (t + 1) = tilt (G.x1 η t) (zt t) := fun t ht =>
    x1_succ G η t ht
  -- variance transfer between consecutive rounds
  have hvar_up : ∀ t, 1 ≤ t → ∀ w : Fin n → ℝ,
      var (G.x1 η (t + 1)) w ≤ Real.exp (3 * η) * var (G.x1 η t) w := by
    intro t ht w
    rw [hstep t ht]
    exact ((hA2 t ht).2.1 w).2
  have hvar_down : ∀ t, 1 ≤ t → ∀ w : Fin n → ℝ,
      var (G.x1 η t) w ≤ Real.exp (3 * η) * var (G.x1 η (t + 1)) w := by
    intro t ht w
    rw [hstep t ht]
    have h := ((hA2 t ht).2.1 w).1
    have h2 : Real.exp (3 * η) * Real.exp (-(3 * η)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc var (G.x1 η t) w = Real.exp (3 * η) * (Real.exp (-(3 * η)) * var (G.x1 η t) w) := by
          rw [← mul_assoc, h2, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have he3 : Real.exp (3 * η) ≤ 3 := by
    have : Real.exp (3 * η) ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
    have h1 := Real.exp_one_lt_d9
    norm_num at h1
    linarith
  have he32 : 2 * Real.exp (3 * η / 2) ≤ 3 := by
    have h := Real.exp_bound_div_one_sub_of_interval (x := 3 * η / 2) (by positivity)
      (by linarith)
    have h2 : 1 / (1 - 3 * η / 2) ≤ 3 / 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  refine ⟨fun t ht => ⟨fun a => ?_, ?_⟩, fun T hT => ?_⟩
  -- ratio bounds
  · have hpos := (x1_good hn G η t).2 a
    rw [hstep t ht]
    exact (hA2 t ht).1 a hpos
  -- (33)
  · have h3 := (hA2 t ht).2.2.1
    rw [← hstep t ht] at h3
    -- bound `‖z‖_{x_t}`
    have hz : vnorm (G.x1 η t) (zt t) ≤
        η * (2 * G.v η t + Real.exp (3 * η / 2) * G.v η (t - 1)) := by
      have hc := vnorm_comb (G.x1 η t) (G.l1 η t) (G.l1 η (t - 1)) (x1_good hn G η t).1
        (-2 * η) η
      have hfun : (fun a => -2 * η * G.l1 η t a + η * G.l1 η (t - 1) a) = zt t := by
        funext a; simp only [hzt]; ring
      rw [hfun] at hc
      have hvt : vnorm (G.x1 η t) (G.l1 η t) = G.v η t := by
        obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
        rfl
      have hvt1 : vnorm (G.x1 η t) (G.l1 η (t - 1)) ≤ Real.exp (3 * η / 2) * G.v η (t - 1) := by
        rcases Nat.lt_or_ge t 2 with h | h
        · have : t = 1 := by omega
          subst this
          simp [vnorm, var, Game.l1, Game.v]
        · obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
          have hv := hvar_up (k + 1) (by omega) (G.l1 η (k + 1))
          simp only [show k + 2 - 1 = k + 1 by omega]
          show Real.sqrt (var (G.x1 η (k + 1 + 1)) (G.l1 η (k + 1))) ≤
            Real.exp (3 * η / 2) * Real.sqrt (var (G.x1 η (k + 1)) (G.l1 η (k + 1)))
          calc _ ≤ Real.sqrt (Real.exp (3 * η) * var (G.x1 η (k + 1)) (G.l1 η (k + 1))) :=
                Real.sqrt_le_sqrt hv
            _ = _ := by
                rw [Real.sqrt_mul (Real.exp_pos _).le]
                congr 1
                rw [show 3 * η = 3 * η / 2 + 3 * η / 2 by ring, Real.exp_add,
                  Real.sqrt_mul_self (Real.exp_pos _).le]
                ring_nf
      rw [abs_of_neg (by linarith), abs_of_pos hη] at hc
      rw [hvt] at hc
      nlinarith [hc, hvt1]
    have hv0 : 0 ≤ G.v η t := by
      obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
      exact Real.sqrt_nonneg _
    have hv1 : 0 ≤ G.v η (t - 1) := by
      cases h : t - 1 with
      | zero => simp [Game.v]
      | succ k => exact Real.sqrt_nonneg _
    have hE : 0 < Real.exp (3 * η / 2) := Real.exp_pos _
    have hEE : Real.exp (3 * η / 2) * Real.exp (3 * η / 2) = Real.exp (3 * η) := by
      rw [← Real.exp_add]; ring_nf
    calc l1Norm (G.x1 η (t + 1) - G.x1 η t)
        ≤ Real.exp (3 * η / 2) * vnorm (G.x1 η t) (zt t) := h3
      _ ≤ Real.exp (3 * η / 2) * (η * (2 * G.v η t + Real.exp (3 * η / 2) * G.v η (t - 1))) :=
          mul_le_mul_of_nonneg_left hz hE.le
      _ = η * ((2 * Real.exp (3 * η / 2)) * G.v η t +
            (Real.exp (3 * η / 2) * Real.exp (3 * η / 2)) * G.v η (t - 1)) := by ring
      _ ≤ η * (3 * G.v η t + 3 * G.v η (t - 1)) := by
          rw [hEE]
          apply mul_le_mul_of_nonneg_left _ hη.le
          nlinarith
      _ = 3 * η * (G.v η t + G.v η (t - 1)) := by ring
  -- (34)
  · have key : ∀ T, 1 ≤ T →
        ∑ t ∈ Finset.Icc 1 T, var (G.x1 η t) (G.l1 η t) ≤
          Real.exp (3 * η) * cumVariance (G.x1 η) (G.l1 η) T + var (G.x1 η T) (G.l1 η T) := by
      intro T hT
      induction T, hT using Nat.le_induction with
      | base =>
        simp only [cumVariance, Finset.Icc_self, Finset.sum_singleton, Nat.sub_self]
        have : var (G.x1 η 1) (G.l1 η 0) = 0 := by simp [var, Game.l1]
        rw [this, mul_zero, zero_add]
      | succ k hk ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        unfold cumVariance at ih ⊢
        rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
        have := hvar_down k hk (G.l1 η k)
        nlinarith [this, ih]
    have hq := var_le_quarter (G.x1 η T) (G.l1 η T) (x1_good hn G η T).1
      (fun a => l1_mem hn G η T a)
    linarith [key T hT]

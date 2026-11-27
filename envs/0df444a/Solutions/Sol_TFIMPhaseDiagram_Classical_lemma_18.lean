-- Prove2me | solution 1 for TFIMPhaseDiagram.Classical.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:03:52.645593+00:00
-- url     : https://prove2.me/submissions/9d26d6d1-7de3-4507-a92a-89f226a57ffd

import Definitions.Def_TFIMPhaseDiagram_Classical_cycles

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical.ChainAux
open TFIMPhaseDiagram.Classical

/-- weighted expectation -/
def wE {Ω : Type} [Fintype Ω] (W f : Ω → ℝ) : ℝ := (∑ x, W x * f x) / ∑ x, W x
def wcov {Ω : Type} [Fintype Ω] (W f g : Ω → ℝ) : ℝ :=
  wE W (fun x => f x * g x) - wE W f * wE W g

lemma covariance_normalize {Ω : Type} [Fintype Ω] (W f g : Ω → ℝ) :
    covariance (normalize W) f g = wcov W f g := by
  unfold covariance normalize wcov wE
  simp only [Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl; intro x _; ring
  · congr 1 <;> (apply Finset.sum_congr rfl; intro x _; ring)

lemma wE_equiv {Ω Ω' : Type} [Fintype Ω] [Fintype Ω'] (e : Ω' ≃ Ω) (W f : Ω → ℝ) :
    wE (W ∘ e) (f ∘ e) = wE W f := by
  unfold wE
  simp only [Function.comp]
  rw [Equiv.sum_comp e (fun x => W x * f x), Equiv.sum_comp e W]

lemma wcov_equiv {Ω Ω' : Type} [Fintype Ω] [Fintype Ω'] (e : Ω' ≃ Ω) (W f g : Ω → ℝ) :
    wcov (W ∘ e) (f ∘ e) (g ∘ e) = wcov W f g := by
  unfold wcov
  rw [wE_equiv, wE_equiv, ← wE_equiv e W (fun x => f x * g x)]
  rfl

lemma wE_smul {Ω : Type} [Fintype Ω] (c : ℝ) (hc : c ≠ 0) (W f : Ω → ℝ) :
    wE (fun x => c * W x) f = wE W f := by
  unfold wE
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ hc]

lemma wcov_smul {Ω : Type} [Fintype Ω] (c : ℝ) (hc : c ≠ 0) (W f g : Ω → ℝ) :
    wcov (fun x => c * W x) f g = wcov W f g := by
  unfold wcov; rw [wE_smul c hc, wE_smul c hc, wE_smul c hc]

lemma wE_le_one {Ω : Type} [Fintype Ω] (W f : Ω → ℝ) (hW : ∀ x, 0 < W x) [Nonempty Ω]
    (hf : ∀ x, |f x| ≤ 1) : |wE W f| ≤ 1 := by
  unfold wE
  have hS : 0 < ∑ x, W x := Finset.sum_pos (fun x _ => hW x) Finset.univ_nonempty
  rw [abs_div, abs_of_pos hS, div_le_one hS]
  calc |∑ x, W x * f x| ≤ ∑ x, |W x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, W x := by
      apply Finset.sum_le_sum; intro x _
      rw [abs_mul, abs_of_pos (hW x)]
      exact mul_le_of_le_one_right (hW x).le (hf x)

lemma var_spin {Ω : Type} [Fintype Ω] [Nonempty Ω] (W f : Ω → ℝ) (hW : ∀ x, 0 < W x)
    (hf : ∀ x, f x = 1 ∨ f x = -1) : |wcov W f f| ≤ 1 := by
  have hsq : wE W (fun x => f x * f x) = 1 := by
    unfold wE
    have hS : 0 < ∑ x, W x := Finset.sum_pos (fun x _ => hW x) Finset.univ_nonempty
    have : ∀ x, W x * (f x * f x) = W x := by
      intro x; rcases hf x with h | h <;> rw [h] <;> ring
    simp only [this]; exact div_self hS.ne'
  have hE := wE_le_one W f hW (fun x => by rcases hf x with h | h <;> rw [h] <;> norm_num)
  unfold wcov; rw [hsq]
  rw [abs_le] at hE ⊢
  constructor <;> nlinarith

lemma sum4 (x : Bool × Bool → ℝ) : ∑ s, x s =
    x (false,false) + x (false,true) + x (true,false) + x (true,true) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]; ring

lemma cov4 (x : Bool × Bool → ℝ) (hS : ∑ s, x s ≠ 0) :
    covariance (normalize x) (fun s => spin s.1) (fun s => spin s.2) =
      4 * (x (false,false) * x (true,true) - x (false,true) * x (true,false)) / (∑ s, x s)^2 := by
  have e1 : covariance (normalize x) (fun s => spin s.1) (fun s => spin s.2) =
      (x (false,false) - x (false,true) - x (true,false) + x (true,true)) / (∑ s, x s) -
      ((x (false,false) + x (false,true) - x (true,false) - x (true,true)) / (∑ s, x s)) *
      ((x (false,false) - x (false,true) + x (true,false) - x (true,true)) / (∑ s, x s)) := by
    simp only [covariance, normalize, Fintype.sum_prod_type, Fintype.sum_bool, spin]
    simp
    ring
  rw [e1, sum4]; rw [sum4] at hS
  field_simp
  ring

lemma tanh_u (J : ℝ) : Real.tanh J = (Real.exp J ^ 2 - 1) / (Real.exp J ^ 2 + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  have := Real.exp_pos J
  field_simp


lemma spin_pm (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b <;> simp [spin]

end TFIMPhaseDiagram.Classical.ChainAux

namespace TFIMPhaseDiagram.Classical.CycleAux
open TFIMPhaseDiagram.Classical TFIMPhaseDiagram.Classical.ChainAux

lemma four_bound (A B C D u : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hu : 0 < u) (hAD : A * D = u ^ 4 * (B * C)) :
    |4 * (A * D - B * C) / (A + B + C + D) ^ 2| ≤ |(u ^ 2 - 1) / (u ^ 2 + 1)| := by
  set Q := B * C
  have hQ : 0 < Q := mul_pos hB hC
  have k1 : (A + D)^2 ≥ 4 * u^4 * Q := by nlinarith [sq_nonneg (A - D)]
  have k2 : (B + C)^2 ≥ 4 * Q := by nlinarith [sq_nonneg (B - C)]
  have k3 : (A + D) * (B + C) ≥ 4 * u^2 * Q := by
    have : (4 * u^2 * Q)^2 ≤ ((A + D) * (B + C))^2 := by
      rw [mul_pow]; nlinarith [mul_le_mul k1 k2 (by positivity) (by positivity)]
    exact (sq_le_sq₀ (by positivity) (by positivity)).1 this
  have kS : 4 * Q * (u^2 + 1)^2 ≤ (A + B + C + D)^2 := by nlinarith
  have hnum : |4 * (A * D - Q)| = 4 * Q * |u^2 - 1| * (u^2 + 1) := by
    rw [hAD, show 4 * (u ^ 4 * Q - Q) = (4 * Q * (u^2+1)) * (u^2 - 1) by ring, abs_mul,
      abs_of_pos (by positivity)]; ring
  rw [abs_div, abs_div, hnum, abs_of_pos (by positivity : (0:ℝ) < (A+B+C+D)^2),
    abs_of_pos (by positivity : (0:ℝ) < u^2 + 1)]
  calc 4 * Q * |u ^ 2 - 1| * (u ^ 2 + 1) / (A + B + C + D) ^ 2
      ≤ 4 * Q * |u ^ 2 - 1| * (u ^ 2 + 1) / (4 * Q * (u^2 + 1)^2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) kS
    _ = |u ^ 2 - 1| / (u ^ 2 + 1) := by field_simp

/-- two-spin covariance bound with an explicit Ising form. -/
lemma two_spin (J a b : ℝ) :
    |wcov (fun p : Bool × Bool => Real.exp (J * spin p.1 * spin p.2 + a * spin p.1 + b * spin p.2))
      (fun p => spin p.1) (fun p => spin p.2)| ≤ |Real.tanh J| := by
  set x : Bool × Bool → ℝ := fun p => Real.exp (J * spin p.1 * spin p.2 + a * spin p.1 + b * spin p.2)
  have hpos : ∀ s, 0 < x s := fun s => Real.exp_pos _
  have hS : ∑ s, x s ≠ 0 := (Finset.sum_pos (fun s _ => hpos s) Finset.univ_nonempty).ne'
  rw [← covariance_normalize, cov4 x hS, sum4, tanh_u]
  apply four_bound _ _ _ _ _ (hpos _) (hpos _) (hpos _) (hpos _) (Real.exp_pos J)
  simp only [x, spin, Bool.false_eq_true, if_false, if_true]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1; push_cast; ring

/-- cosh product identity -/
lemma cosh_prod (x h : ℝ) : Real.cosh (x + h) * Real.cosh (-x + h) = Real.cosh x ^ 2 + Real.sinh h ^ 2 := by
  rw [Real.cosh_add, Real.cosh_add, Real.cosh_neg, Real.sinh_neg]
  have h1 := Real.cosh_sq_sub_sinh_sq x
  have h2 := Real.cosh_sq_sub_sinh_sq h
  nlinarith [h1, h2]

/-- the effective coupling after summing out a middle spin. -/
lemma elim_bound (K1 K2 h u : ℝ) (hu : 0 < u)
    (hu4 : u ^ 4 * ((Real.exp (K1 - K2 + h) + Real.exp (-(K1 - K2 + h))) *
        (Real.exp (-K1 + K2 + h) + Real.exp (-(-K1 + K2 + h)))) =
      (Real.exp (K1 + K2 + h) + Real.exp (-(K1 + K2 + h))) *
        (Real.exp (-K1 - K2 + h) + Real.exp (-(-K1 - K2 + h)))) :
    |(u ^ 2 - 1) / (u ^ 2 + 1)| ≤ |Real.tanh K1| * |Real.tanh K2| := by
  have e2 : ∀ y, Real.exp y + Real.exp (-y) = 2 * Real.cosh y := by
    intro y; rw [Real.cosh_eq]; ring
  rw [e2, e2, e2, e2] at hu4
  set X := Real.cosh (K1 + K2) ^ 2
  set Y := Real.cosh (K1 - K2) ^ 2
  set c := Real.sinh h ^ 2
  have hP : 2 * Real.cosh (K1 + K2 + h) * (2 * Real.cosh (-K1 - K2 + h)) = 4 * (X + c) := by
    rw [show -K1 - K2 + h = -(K1 + K2) + h by ring, mul_mul_mul_comm, cosh_prod]; ring
  have hQ : 2 * Real.cosh (K1 - K2 + h) * (2 * Real.cosh (-K1 + K2 + h)) = 4 * (Y + c) := by
    rw [show -K1 + K2 + h = -(K1 - K2) + h by ring, mul_mul_mul_comm, cosh_prod]; ring
  rw [hP, hQ] at hu4
  have hc : 0 ≤ c := sq_nonneg _
  have hX : 0 < X := by positivity
  have hY : 0 < Y := by positivity
  set m := Real.cosh (K1 + K2) * Real.cosh (K1 - K2)
  have hm : 0 < m := mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
  have hmXY : m ^ 2 = X * Y := by simp only [m, X, Y]; ring
  set v := 4 * (Y + c) * u ^ 2
  have hv : 0 ≤ v := by positivity
  have hv2 : v ^ 2 = 4 * (X + c) * (4 * (Y + c)) := by
    simp only [v]; rw [← hu4]; ring
  have hvm : 4 * m ≤ v := by
    have : (4 * m) ^ 2 ≤ v ^ 2 := by rw [hv2]; nlinarith [mul_nonneg hc hc]
    exact (sq_le_sq₀ (by positivity) hv).1 this
  -- identities for cosh sums
  have hsum : Real.cosh (K1 + K2) + Real.cosh (K1 - K2) = 2 * Real.cosh K1 * Real.cosh K2 := by
    rw [Real.cosh_add, Real.cosh_sub]; ring
  have hdiff : Real.cosh (K1 + K2) - Real.cosh (K1 - K2) = 2 * Real.sinh K1 * Real.sinh K2 := by
    rw [Real.cosh_add, Real.cosh_sub]; ring
  have hXY : X - Y = (2 * Real.sinh K1 * Real.sinh K2) * (2 * Real.cosh K1 * Real.cosh K2) := by
    rw [← hsum, ← hdiff]; simp only [X, Y]; ring
  have hden : 4 * (Y + c) * (u ^ 2 + 1) ^ 2 ≥ 16 * (Real.cosh K1 * Real.cosh K2) ^ 2 := by
    have : 4 * (Y + c) * (u ^ 2 + 1) ^ 2 = 4 * (X + c) + 4 * (Y + c) + 2 * v := by
      have : 4 * (Y + c) * u ^ 4 = 4 * (X + c) := by linarith
      simp only [v]; nlinarith
    rw [this]
    have : (Real.cosh (K1 + K2) + Real.cosh (K1 - K2)) ^ 2 = X + Y + 2 * m := by
      simp only [X, Y, m]; ring
    rw [hsum] at this
    nlinarith
  have hYc : 0 < 4 * (Y + c) := by positivity
  have key : |(u ^ 2 - 1) / (u ^ 2 + 1)| = 4 * |X - Y| / (4 * (Y + c) * (u ^ 2 + 1) ^ 2) := by
    have : 4 * (X - Y) = 4 * (Y + c) * (u ^ 2 - 1) * (u ^ 2 + 1) := by
      have : 4 * (Y + c) * u ^ 4 = 4 * (X + c) := by linarith
      nlinarith
    rw [show 4 * |X - Y| = |4 * (X - Y)| by rw [abs_mul]; norm_num, this, abs_mul, abs_mul,
      abs_of_pos hYc, abs_of_pos (by positivity : (0:ℝ) < u ^ 2 + 1), abs_div,
      abs_of_pos (by positivity : (0:ℝ) < u ^ 2 + 1)]
    field_simp
  rw [key, hXY, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, abs_div, abs_div,
    abs_of_pos (Real.cosh_pos K1), abs_of_pos (Real.cosh_pos K2)]
  have c1 := Real.cosh_pos K1; have c2 := Real.cosh_pos K2
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
    abs_of_pos (by positivity : (0:ℝ) < 2 * Real.cosh K1), abs_of_pos c2]
  have hs : 0 ≤ |Real.sinh K1| * |Real.sinh K2| := by positivity
  calc 4 * (2 * |Real.sinh K1| * |Real.sinh K2| * (2 * Real.cosh K1 * Real.cosh K2)) *
        (Real.cosh K1 * Real.cosh K2)
      = (|Real.sinh K1| * |Real.sinh K2|) * (16 * (Real.cosh K1 * Real.cosh K2) ^ 2) := by ring
    _ ≤ (|Real.sinh K1| * |Real.sinh K2|) * (4 * (Y + c) * (u ^ 2 + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hden hs


def cycW {n : ℕ} (K w : Fin n → ℝ) (s : Spins n) : ℝ :=
  Real.exp ((∑ k, K k * spin (s k) * spin (s (next k))) + ∑ k, w k * spin (s k))

lemma cycW_pos {n : ℕ} (K w : Fin n → ℝ) (s : Spins n) : 0 < cycW K w s := Real.exp_pos _

lemma next_eq {N : ℕ} (k : Fin (N+1)) : next k = k + 1 := by
  ext; simp [next, Fin.val_add]

lemma next_rot {N : ℕ} (m : Fin (N+1)) :
    next (finRotate (N+1) m) = finRotate (N+1) (next m) := by
  simp [next_eq, finRotate_apply]

lemma cycW_rot {N : ℕ} (K w : Fin (N+1) → ℝ) (s : Spins (N+1)) :
    cycW K w (fun l => s ((finRotate (N+1)).symm l)) =
      cycW (K ∘ finRotate (N+1)) (w ∘ finRotate (N+1)) s := by
  unfold cycW
  congr 1
  congr 1
  · rw [← Equiv.sum_comp (finRotate (N+1))]
    apply Finset.sum_congr rfl; intro m _
    dsimp only
    rw [next_rot, Equiv.symm_apply_apply, Equiv.symm_apply_apply]; rfl
  · rw [← Equiv.sum_comp (finRotate (N+1))]
    apply Finset.sum_congr rfl; intro m _
    simp

def rotE (N : ℕ) : Spins (N+1) ≃ Spins (N+1) where
  toFun s := fun l => s ((finRotate (N+1)).symm l)
  invFun s := fun l => s (finRotate (N+1) l)
  left_inv s := by funext l; simp
  right_inv s := by funext l; simp

lemma rot_cov {N : ℕ} (K w : Fin (N+1) → ℝ) (i j : Fin (N+1)) :
    wcov (cycW K w) (fun s => spin (s (finRotate (N+1) i))) (fun s => spin (s (finRotate (N+1) j))) =
      wcov (cycW (K ∘ finRotate (N+1)) (w ∘ finRotate (N+1)))
        (fun s => spin (s i)) (fun s => spin (s j)) := by
  rw [← wcov_equiv (rotE N)]
  congr 1
  · funext s; exact cycW_rot K w s
  · funext s; simp [rotE]
  · funext s; simp [rotE]

lemma wcov_symm {Ω : Type} [Fintype Ω] (W f g : Ω → ℝ) : wcov W f g = wcov W g f := by
  unfold wcov
  rw [mul_comm (wE W f)]
  congr 2; funext x; ring

lemma wE_marg {Ω : Type} [Fintype Ω] (W : Bool × Ω → ℝ) (h : Ω → ℝ) :
    wE W (fun p => h p.2) = wE (fun x => ∑ b, W (b, x)) h := by
  unfold wE
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm,
    Finset.sum_comm (f := fun b x => W (b, x))]
  congr 1
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_mul]

lemma wcov_marg {Ω : Type} [Fintype Ω] (W : Bool × Ω → ℝ) (f g : Ω → ℝ) :
    wcov W (fun p => f p.2) (fun p => g p.2) = wcov (fun x => ∑ b, W (b, x)) f g := by
  unfold wcov
  rw [wE_marg, wE_marg, ← wE_marg W (fun x => f x * g x)]

/-- two-spin positive weight representation (Prop 19 (i)). -/
lemma pair_rep (r : Bool × Bool → ℝ) (hr : ∀ s, 0 < r s) :
    ∃ C J v1 v2 : ℝ, 0 < C ∧ (∀ s, r s = C * Real.exp (J * spin s.1 * spin s.2 + v1 * spin s.1 +
      v2 * spin s.2)) ∧ Real.exp J ^ 4 * (r (false,true) * r (true,false)) =
        r (false,false) * r (true,true) := by
  have h1 := hr (false,false); have h2 := hr (false,true)
  have h3 := hr (true,false); have h4 := hr (true,true)
  set la := Real.log (r (false,false)); set lb := Real.log (r (false,true))
  set lc := Real.log (r (true,false)); set ld := Real.log (r (true,true))
  refine ⟨Real.exp ((1/4) * (la + lb + lc + ld)), (1/4) * (la + ld - lb - lc),
    (1/4) * (la + lb - lc - ld), (1/4) * (la + lc - lb - ld), Real.exp_pos _, ?_, ?_⟩
  · rintro ⟨_ | _, _ | _⟩ <;>
    · rw [← Real.exp_add]
      conv_lhs => rw [← Real.exp_log (hr _)]
      congr 1; simp [spin, la, lb, lc, ld]; ring
  · rw [← Real.exp_nat_mul]
    conv_rhs => rw [← Real.exp_log h1, ← Real.exp_log h4]
    conv_lhs => rw [← Real.exp_log h2, ← Real.exp_log h3]
    simp only [← Real.exp_add]; congr 1; push_cast; ring

/-- the bound function -/
def Fb (x y : ℝ) : ℝ := (x + y) / (1 + x * y)

lemma Fb_symm (x y : ℝ) : Fb x y = Fb y x := by unfold Fb; ring_nf

lemma Fb_mono (x y y' : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy' : 0 ≤ y') (hyy : y' ≤ y) :
    Fb x y' ≤ Fb x y := by
  unfold Fb
  have hy : 0 ≤ y := le_trans hy' hyy
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hyy) (sub_nonneg.2 (mul_le_one₀ hx1 hx0 hx1))]

lemma abs_tanh_le_one (x : ℝ) : |Real.tanh x| ≤ 1 := by
  rw [abs_le]; exact ⟨(Real.neg_one_lt_tanh x).le, (Real.tanh_lt_one x).le⟩

lemma tanh_add' (a b : ℝ) : Real.tanh (a + b) =
    (Real.tanh a + Real.tanh b) / (1 + Real.tanh a * Real.tanh b) := by
  have ca := Real.cosh_pos a; have cb := Real.cosh_pos b
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    Real.sinh_add, Real.cosh_add]
  have : Real.cosh a * Real.cosh b + Real.sinh a * Real.sinh b ≠ 0 := by
    rw [← Real.cosh_add]; exact (Real.cosh_pos _).ne'
  field_simp

lemma tanh_add_le (a b : ℝ) : |Real.tanh (a + b)| ≤ Fb |Real.tanh a| |Real.tanh b| := by
  rw [tanh_add']
  set x := Real.tanh a; set y := Real.tanh b
  have hx := abs_tanh_le_one a; have hy := abs_tanh_le_one b
  have hx' : |x| < 1 := by rw [abs_lt]; exact ⟨Real.neg_one_lt_tanh a, Real.tanh_lt_one a⟩
  have hy' : |y| < 1 := by rw [abs_lt]; exact ⟨Real.neg_one_lt_tanh b, Real.tanh_lt_one b⟩
  have hxy : |x * y| < 1 := by rw [abs_mul]; nlinarith [abs_nonneg x, abs_nonneg y]
  have hden : 0 < 1 + x * y := by rw [abs_lt] at hxy; linarith
  unfold Fb
  rw [abs_div, abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
  rcases le_total 0 (x * y) with h | h
  · have : |x| * |y| = x * y := by rw [← abs_mul, abs_of_nonneg h]
    rw [this]
    nlinarith [abs_add_le x y]
  · have : |x| * |y| = -(x * y) := by rw [← abs_mul, abs_of_nonpos h]
    rw [this]
    rcases le_total 0 x with hx0 | hx0 <;> rcases le_total 0 y with hy0 | hy0
    · have : x * y = 0 := le_antisymm h (mul_nonneg hx0 hy0)
      nlinarith [abs_add_le x y]
    · rw [abs_of_nonneg hx0, abs_of_nonpos hy0] at *
      have hx2 : x * x ≤ 1 := by nlinarith
      have hy2 : y * y ≤ 1 := by nlinarith
      rcases abs_cases (x + y) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;>
        nlinarith [mul_nonneg (neg_nonneg.2 hy0) (sub_nonneg.2 hx2),
          mul_nonneg hx0 (sub_nonneg.2 hy2)]
    · rw [abs_of_nonpos hx0, abs_of_nonneg hy0] at *
      have hx2 : x * x ≤ 1 := by nlinarith
      have hy2 : y * y ≤ 1 := by nlinarith
      rcases abs_cases (x + y) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;>
        nlinarith [mul_nonneg (neg_nonneg.2 hx0) (sub_nonneg.2 hy2),
          mul_nonneg hy0 (sub_nonneg.2 hx2)]
    · have : x * y = 0 := le_antisymm h (mul_nonneg_of_nonpos_of_nonpos hx0 hy0)
      nlinarith [abs_add_le x y]


lemma next_cc {N : ℕ} (m : Fin N) :
    next (m.castSucc.castSucc : Fin (N+2)) = m.succ.castSucc := by
  ext; simp only [next, Fin.val_castSucc, Fin.val_succ]; exact Nat.mod_eq_of_lt (by omega)
lemma next_cl {N : ℕ} : next ((Fin.last N).castSucc : Fin (N+2)) = Fin.last (N+1) := by
  ext; simp only [next, Fin.val_castSucc, Fin.val_last]; exact Nat.mod_eq_of_lt (by omega)
lemma next_last {N : ℕ} : next (Fin.last N : Fin (N+1)) = 0 := by
  ext; simp [next]
lemma next_c {N : ℕ} (m : Fin N) : next (m.castSucc : Fin (N+1)) = m.succ := by
  ext; simp only [next, Fin.val_castSucc, Fin.val_succ]; exact Nat.mod_eq_of_lt (by omega)

lemma elim_step {N : ℕ} (hN : 1 ≤ N) (K w : Fin (N+2) → ℝ) :
    ∃ (K'' w'' : Fin (N+1) → ℝ) (C : ℝ), 0 < C ∧
      (∀ s' : Spins (N+1), ∑ b, cycW K w (Fin.snoc s' b) = C * cycW K'' w'' s') ∧
      (∀ m : Fin N, K'' m.castSucc = K m.castSucc.castSucc) ∧
      |Real.tanh (K'' (Fin.last N))| ≤
        |Real.tanh (K (Fin.last N).castSucc)| * |Real.tanh (K (Fin.last (N+1)))| := by
  set K1 := K (Fin.last N).castSucc
  set K2 := K (Fin.last (N+1))
  set h := w (Fin.last (N+1))
  set ρ : Bool × Bool → ℝ := fun p => ∑ b : Bool,
    Real.exp (K1 * spin p.1 * spin b + K2 * spin b * spin p.2 + h * spin b)
  have hρ : ∀ p, 0 < ρ p := fun p => Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  obtain ⟨C, J, v1, v2, hC, hrep, hu4⟩ := pair_rep ρ hρ
  refine ⟨Fin.snoc (fun m : Fin N => K m.castSucc.castSucc) J,
    fun l => w l.castSucc + (if l = Fin.last N then v1 else 0) + (if l = 0 then v2 else 0),
    C, hC, ?_, ?_, ?_⟩
  · intro s'
    have hdecomp : ∀ b, cycW K w (Fin.snoc s' b) =
        Real.exp ((∑ m : Fin N, K m.castSucc.castSucc * spin (s' m.castSucc) * spin (s' m.succ)) +
          ∑ l : Fin (N+1), w l.castSucc * spin (s' l)) *
        Real.exp (K1 * spin (s' (Fin.last N)) * spin b + K2 * spin b * spin (s' 0) + h * spin b) := by
      intro b
      unfold cycW
      rw [← Real.exp_add]; congr 1
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [next_cc, next_cl, next_last, Fin.snoc_castSucc, Fin.snoc_last]
      have h0 : (0 : Fin (N+2)) = (0 : Fin (N+1)).castSucc := rfl
      rw [h0, Fin.snoc_castSucc]
      ring
    simp only [hdecomp, ← Finset.mul_sum]
    have hρv : ∑ b : Bool, Real.exp (K1 * spin (s' (Fin.last N)) * spin b + K2 * spin b * spin (s' 0)
        + h * spin b) = ρ (s' (Fin.last N), s' 0) := rfl
    rw [hρv, hrep]
    unfold cycW
    rw [mul_left_comm, ← Real.exp_add]; congr 2
    have hE : ∑ k, Fin.snoc (α := fun _ => ℝ) (fun m : Fin N => K m.castSucc.castSucc) J k *
        spin (s' k) * spin (s' (next k)) =
        ∑ m : Fin N, K m.castSucc.castSucc * spin (s' m.castSucc) * spin (s' m.succ) +
          J * spin (s' (Fin.last N)) * spin (s' 0) := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, next_c, next_last]
    have hF : ∑ k : Fin (N+1), ((w k.castSucc + if k = Fin.last N then v1 else 0) +
        if k = 0 then v2 else 0) * spin (s' k) =
        ∑ k : Fin (N+1), w k.castSucc * spin (s' k) + v1 * spin (s' (Fin.last N)) +
          v2 * spin (s' 0) := by
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    simp only []
    rw [hE, hF]
    ring
  · intro m; simp
  · simp only [Fin.snoc_last]
    rw [tanh_u]
    apply elim_bound K1 K2 h (Real.exp J) (Real.exp_pos J)
    have e : ∀ x y : ℝ, Real.exp x + Real.exp y = Real.exp x + Real.exp y := fun _ _ => rfl
    convert hu4 using 2 <;> simp only [ρ, Fintype.sum_bool, spin, if_true, if_false,
      Bool.false_eq_true] <;> ring_nf


lemma abs_prod_tanh_le_one {ι : Type} (s : Finset ι) (f : ι → ℝ) :
    |∏ k ∈ s, Real.tanh (f k)| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun k _ => abs_nonneg _) (fun k _ => abs_tanh_le_one _)

lemma base2 (K w : Fin 2 → ℝ) :
    |wcov (cycW K w) (fun s => spin (s 0)) (fun s => spin (s 1))| ≤
      Fb |arcProduct K 0 1| |otherArcProduct K 0 1| := by
  have harc : arcProduct K 0 1 = Real.tanh (K 0) := by
    simp [arcProduct, Finset.prod_filter, Fin.prod_univ_two]
  have hoth : otherArcProduct K 0 1 = Real.tanh (K 1) := by
    simp [otherArcProduct, Finset.prod_filter, Fin.prod_univ_two]
  rw [harc, hoth]
  rw [← wcov_equiv (finTwoArrowEquiv Bool).symm]
  have hW : (cycW K w ∘ (finTwoArrowEquiv Bool).symm) = fun p : Bool × Bool =>
      Real.exp ((K 0 + K 1) * spin p.1 * spin p.2 + w 0 * spin p.1 + w 1 * spin p.2) := by
    funext p
    simp only [Function.comp, cycW, Fin.sum_univ_two]
    have h0 : next (0 : Fin 2) = 1 := rfl
    have h1 : next (1 : Fin 2) = 0 := rfl
    rw [h0, h1]
    simp [finTwoArrowEquiv]
    ring_nf
  rw [hW]
  have e1 : ((fun s : Spins 2 => spin (s 0)) ∘ (finTwoArrowEquiv Bool).symm) = fun p => spin p.1 := by
    funext p; simp [finTwoArrowEquiv]
  have e2 : ((fun s : Spins 2 => spin (s 1)) ∘ (finTwoArrowEquiv Bool).symm) = fun p => spin p.2 := by
    funext p; simp [finTwoArrowEquiv]
  rw [e1, e2]
  exact (two_spin _ _ _).trans (tanh_add_le _ _)


lemma arc0_castSucc {N : ℕ} (K : Fin (N+3) → ℝ) (K'' : Fin (N+2) → ℝ)
    (hK : ∀ m : Fin (N+1), K'' m.castSucc = K m.castSucc.castSucc)
    (j : Fin (N+3)) (j' : Fin (N+2)) (hjj : j'.val = j.val) (hj : j.val < N + 2) :
    arcProduct K'' 0 j' = arcProduct K 0 j ∧
    otherArcProduct K'' 0 j' = (∏ m : Fin (N+1), if j.val ≤ m.val then Real.tanh (K m.castSucc.castSucc) else 1) *
      Real.tanh (K'' (Fin.last (N+1))) ∧
    otherArcProduct K 0 j = (∏ m : Fin (N+1), if j.val ≤ m.val then Real.tanh (K m.castSucc.castSucc) else 1) *
      (Real.tanh (K (Fin.last (N+1)).castSucc) * Real.tanh (K (Fin.last (N+2)))) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold arcProduct
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_castSucc (n := N+1),
      Fin.prod_univ_castSucc (n := N+2), Fin.prod_univ_castSucc (n := N+1)]
    simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, zero_le, true_and, hK, hjj]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring
  · unfold otherArcProduct
    rw [Finset.prod_filter, Fin.prod_univ_castSucc (n := N+1)]
    simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, Nat.not_lt_zero, false_or, hK, hjj]
    rw [if_pos (by omega)]
  · unfold otherArcProduct
    rw [Finset.prod_filter, Fin.prod_univ_castSucc (n := N+2), Fin.prod_univ_castSucc (n := N+1)]
    simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, Nat.not_lt_zero, false_or]
    rw [if_pos (by omega), if_pos (by omega)]
    ring

theorem cyc0 (N : ℕ) : ∀ (K w : Fin (N+2) → ℝ) (j : Fin (N+2)), 0 < j.val →
    |wcov (cycW K w) (fun s => spin (s 0)) (fun s => spin (s j))| ≤
      Fb |arcProduct K 0 j| |otherArcProduct K 0 j| := by
  induction N with
  | zero =>
    intro K w j hj
    have : j = 1 := Fin.ext (by have := j.isLt; simp; omega)
    subst this
    exact base2 K w
  | succ N ih =>
    have nonlast : ∀ (K w : Fin (N+3) → ℝ) (j : Fin (N+3)), 0 < j.val → j.val < N + 2 →
        |wcov (cycW K w) (fun s => spin (s 0)) (fun s => spin (s j))| ≤
          Fb |arcProduct K 0 j| |otherArcProduct K 0 j| := by
      intro K w j hj0 hj
      obtain ⟨K'', w'', C, hC, hsum, hK, htanh⟩ := elim_step (N := N+1) (by omega) K w
      set j' : Fin (N+2) := ⟨j.val, hj⟩
      set E := Fin.snocEquiv (fun _ : Fin (N+3) => Bool)
      rw [← wcov_equiv E]
      have e0 : ((fun s : Spins (N+3) => spin (s 0)) ∘ E) = fun p => spin (p.2 0) := by
        funext p
        show spin (Fin.snoc (α := fun _ => Bool) p.2 p.1 0) = _
        rw [show (0 : Fin (N+3)) = (0 : Fin (N+2)).castSucc from rfl, Fin.snoc_castSucc]
      have ej : ((fun s : Spins (N+3) => spin (s j)) ∘ E) = fun p => spin (p.2 j') := by
        funext p
        show spin (Fin.snoc (α := fun _ => Bool) p.2 p.1 j) = _
        rw [show j = j'.castSucc from Fin.ext rfl, Fin.snoc_castSucc]
      have eW : (cycW K w ∘ E) = fun p => cycW K w (Fin.snoc p.2 p.1) := rfl
      rw [e0, ej, eW, wcov_marg (fun p : Bool × Spins (N+2) => cycW K w (Fin.snoc p.2 p.1))
        (fun x => spin (x 0)) (fun x => spin (x j'))]
      simp only [hsum]
      rw [wcov_smul C hC.ne']
      have hIH := ih K'' w'' j' hj0
      obtain ⟨h1, h2, h3⟩ := arc0_castSucc K K'' hK j j' rfl hj
      rw [h1] at hIH
      refine hIH.trans (Fb_mono _ _ _ (abs_nonneg _) (abs_prod_tanh_le_one _ _) (abs_nonneg _) ?_)
      rw [h2, h3, abs_mul, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left htanh (abs_nonneg _)
    intro K w j hj0
    by_cases hj : j.val < N + 2
    · exact nonlast K w j hj0 hj
    have hjl : j = Fin.last (N+2) := Fin.ext (by have := j.isLt; simp; omega)
    subst hjl
    set σ := finRotate (N+3)
    have hrot := rot_cov (K ∘ σ.symm) (w ∘ σ.symm) 0 (Fin.last (N+2))
    have hKK : (K ∘ σ.symm) ∘ σ = K := by funext x; simp
    have hww : (w ∘ σ.symm) ∘ σ = w := by funext x; simp
    rw [hKK, hww] at hrot
    have hs0 : σ 0 = 1 := by simp [σ, finRotate_apply]
    have hsl : σ (Fin.last (N+2)) = 0 := by simp [σ, finRotate_last]
    rw [hs0, hsl] at hrot
    rw [← hrot, wcov_symm]
    have hb := nonlast (K ∘ σ.symm) (w ∘ σ.symm) 1 (by simp) (by simp)
    refine hb.trans (le_of_eq ?_)
    rw [Fb_symm]
    congr 2
    · -- other arc of rotated = arc of original
      unfold otherArcProduct arcProduct
      rw [Finset.prod_filter, Finset.prod_filter, ← Equiv.prod_comp σ]
      apply Finset.prod_congr rfl; intro m _
      simp only [Function.comp, Equiv.symm_apply_apply, Fin.val_zero, zero_le, true_and,
        Nat.not_lt_zero, false_or, Fin.val_last]
      have : (1 : Fin (N+3)).val ≤ (σ m).val ↔ m.val < N + 2 := by
        simp only [σ, finRotate_apply, Fin.val_add, Fin.val_one]
        have := m.isLt
        constructor
        · intro h; by_contra hc
          have hm : m.val = N + 2 := by omega
          rw [hm] at h; simp at h
        · intro h; rw [Nat.mod_eq_of_lt (by omega)]; omega
      simp only [this]
    · have hA : arcProduct (K ∘ σ.symm) 0 1 = Real.tanh (K (Fin.last (N+2))) := by
        unfold arcProduct
        rw [Finset.prod_filter, Fin.prod_univ_succ]
        have h1 : ∀ i : Fin (N+2), ¬ ((0 : Fin (N+3)).val ≤ i.succ.val ∧ i.succ.val < (1 : Fin (N+3)).val) :=
          fun i => by simp
        simp only [h1, if_false, Finset.prod_const_one, mul_one]
        rw [if_pos (by simp)]
        have : σ.symm 0 = Fin.last (N+2) := by
          rw [Equiv.symm_apply_eq]; simp [σ, finRotate_last]
        simp [this]
      have hB : otherArcProduct K 0 (Fin.last (N+2)) = Real.tanh (K (Fin.last (N+2))) := by
        unfold otherArcProduct
        rw [Finset.prod_filter, Fin.prod_univ_castSucc (n := N+2)]
        have h2 : ∀ i : Fin (N+2), ¬ (i.castSucc.val < (0 : Fin (N+3)).val ∨
            (Fin.last (N+2)).val ≤ i.castSucc.val) := fun i => by
          have := i.isLt; simp
        simp only [h2, if_false, Finset.prod_const_one, one_mul]
        rw [if_pos (Or.inr le_rfl)]
      rw [hA, hB]


lemma rot_val {N : ℕ} (k : Fin (N+2)) :
    (finRotate (N+2) k).val = if k.val < N + 1 then k.val + 1 else 0 := by
  rw [finRotate_apply, Fin.val_add, Fin.val_one]
  have := k.isLt
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · have : k.val = N + 1 := by omega
    rw [this, show N + 1 + 1 = N + 2 by ring, Nat.mod_self]

theorem cyc_gen (N : ℕ) : ∀ (i : ℕ) (K w : Fin (N+2) → ℝ) (a c : Fin (N+2)), a.val = i → a < c →
    |wcov (cycW K w) (fun s => spin (s a)) (fun s => spin (s c))| ≤
      Fb |arcProduct K a c| |otherArcProduct K a c| := by
  intro i
  induction i with
  | zero =>
    intro K w a c ha hac
    have : a = 0 := Fin.ext ha
    subst this
    exact cyc0 N K w c (by rw [Fin.lt_def] at hac; simpa using hac)
  | succ i ih =>
    intro K w a c ha hac
    set σ := finRotate (N+2)
    have hc : c.val < N + 2 := c.isLt
    rw [Fin.lt_def] at hac
    set a₀ : Fin (N+2) := ⟨i, by omega⟩
    set c₀ : Fin (N+2) := ⟨c.val - 1, by omega⟩
    have hσa : σ a₀ = a := Fin.ext (by rw [rot_val]; simp only [a₀]; split_ifs <;> omega)
    have hσc : σ c₀ = c := Fin.ext (by rw [rot_val]; simp only [c₀]; split_ifs <;> omega)
    have hrot := rot_cov K w a₀ c₀
    rw [hσa, hσc] at hrot
    rw [hrot]
    have hb := ih (K ∘ σ) (w ∘ σ) a₀ c₀ rfl (by rw [Fin.lt_def]; simp [a₀, c₀]; omega)
    refine hb.trans (le_of_eq ?_)
    congr 2
    · unfold arcProduct
      rw [Finset.prod_filter, Finset.prod_filter, ← Equiv.prod_comp σ (fun m =>
        if a.val ≤ m.val ∧ m.val < c.val then Real.tanh (K m) else 1)]
      apply Finset.prod_congr rfl; intro k _
      simp only [Function.comp, σ, rot_val, a₀, c₀]
      have := k.isLt
      split_ifs <;> first | rfl | omega
    · unfold otherArcProduct
      rw [Finset.prod_filter, Finset.prod_filter, ← Equiv.prod_comp σ (fun m =>
        if m.val < a.val ∨ c.val ≤ m.val then Real.tanh (K m) else 1)]
      apply Finset.prod_congr rfl; intro k _
      simp only [Function.comp, σ, rot_val, a₀, c₀]
      have := k.isLt
      split_ifs <;> first | rfl | omega


lemma cycleProb_finite {n : ℕ} (K w : Fin n → ℝ) :
    cycleProb K (fun k => Field.finite (w k)) = normalize (cycW K w) := by
  have : cycleWeight K (fun k => Field.finite (w k)) = cycW K w := by
    funext s
    have hc : compatible (fun k => Field.finite (w k)) s := by intro k; trivial
    unfold cycleWeight cycleEnergy fieldEnergy cycW
    rw [if_pos hc]
  unfold cycleProb; rw [this]

lemma tanh_le_tanh {x y : ℝ} (h : x ≤ y) : Real.tanh x ≤ Real.tanh y := by
  rw [tanh_u, tanh_u]
  have hx := Real.exp_pos x; have hy := Real.exp_pos y
  have hxy : Real.exp x ^ 2 ≤ Real.exp y ^ 2 := by
    have := Real.exp_le_exp.2 h; nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma abs_tanh_le {x b : ℝ} (h : |x| ≤ b) : |Real.tanh x| ≤ Real.tanh b := by
  have h0 : Real.tanh 0 = 0 := Real.tanh_zero
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg (by rw [← h0]; exact tanh_le_tanh hx)]
    exact tanh_le_tanh (le_trans (le_abs_self x) h)
  · rw [abs_of_nonpos (by rw [← h0]; exact tanh_le_tanh hx), ← Real.tanh_neg]
    exact tanh_le_tanh (le_trans (neg_le_abs x) h)

lemma card_arc {M : ℕ} (i j : Fin M) (hij : i ≤ j) :
    (Finset.univ.filter (fun k : Fin M => i.val ≤ k.val ∧ k.val < j.val)).card = j.val - i.val := by
  have hsub : Finset.univ.filter (fun k : Fin M => k.val < i.val) ⊆
      Finset.univ.filter (fun k : Fin M => k.val < j.val) := by
    intro k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Fin.le_def] at hij; omega
  have : Finset.univ.filter (fun k : Fin M => i.val ≤ k.val ∧ k.val < j.val) =
      Finset.univ.filter (fun k : Fin M => k.val < j.val) \
        Finset.univ.filter (fun k : Fin M => k.val < i.val) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]; omega
  rw [this, Finset.card_sdiff_of_subset hsub, Fin.card_filter_val_lt, Fin.card_filter_val_lt]
  have := i.isLt; have := j.isLt
  rw [min_eq_right this.le, min_eq_right (by omega)]

lemma card_other {M : ℕ} (i j : Fin M) (hij : i ≤ j) :
    (Finset.univ.filter (fun k : Fin M => k.val < i.val ∨ j.val ≤ k.val)).card =
      M - (j.val - i.val) := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin M)))
    (fun k : Fin M => i.val ≤ k.val ∧ k.val < j.val)
  rw [card_arc i j hij, Finset.card_univ, Fintype.card_fin] at h
  have : Finset.univ.filter (fun k : Fin M => ¬ (i.val ≤ k.val ∧ k.val < j.val)) =
      Finset.univ.filter (fun k : Fin M => k.val < i.val ∨ j.val ≤ k.val) := by
    apply Finset.filter_congr; intro k _; omega
  rw [this] at h
  omega

lemma prod_bound {ι : Type} (s : Finset ι) (K : ι → ℝ) (b : ℝ) (hK : ∀ k, |K k| ≤ b) :
    |∏ k ∈ s, Real.tanh (K k)| ≤ Real.tanh b ^ s.card := by
  rw [Finset.abs_prod, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k _ => abs_tanh_le (hK k))

theorem lemma18 (M : ℕ) (hM : 3 ≤ M) (K : Fin M → ℝ) (w : Fin M → ℝ)
    (b : ℝ) (hb : 0 < b) (hK : ∀ k, |K k| ≤ b) (i j : Fin M) (hij : i ≤ j) :
  |spinCov (cycleProb K (fun k => .finite (w k))) i j| ≤
    (|arcProduct K i j| + |otherArcProduct K i j|) / (1 + |∏ k, Real.tanh (K k)|) ∧
  (|arcProduct K i j| + |otherArcProduct K i j|) / (1 + |∏ k, Real.tanh (K k)|) ≤
    ((Real.tanh b)^(j.val-i.val) + (Real.tanh b)^(M-(j.val-i.val))) /
      (1 + (Real.tanh b)^M) := by
  have hall : ∏ k, Real.tanh (K k) = arcProduct K i j * otherArcProduct K i j := by
    unfold arcProduct otherArcProduct
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun k : Fin M => i.val ≤ k.val ∧ k.val < j.val)]
    congr 1
    apply Finset.prod_congr (Finset.filter_congr (fun k _ => by omega)) (fun _ _ => rfl)
  have hF : (|arcProduct K i j| + |otherArcProduct K i j|) / (1 + |∏ k, Real.tanh (K k)|) =
      Fb |arcProduct K i j| |otherArcProduct K i j| := by
    unfold Fb; rw [hall, abs_mul]
  rw [hF]
  set a := Real.tanh b
  have ha0 : 0 ≤ a := by
    have := abs_tanh_le (show |(0:ℝ)| ≤ b by simp; exact hb.le); simpa using (abs_nonneg _).trans this
  have ha1 : a ≤ 1 := (le_abs_self _).trans (abs_tanh_le_one b)
  constructor
  · unfold spinCov
    rw [cycleProb_finite, covariance_normalize]
    rcases eq_or_lt_of_le hij with h | h
    · subst h
      have hA : arcProduct K i i = 1 := by
        unfold arcProduct
        rw [Finset.filter_false_of_mem (fun k _ => by omega), Finset.prod_empty]
      rw [hA, abs_one]
      have : Fb 1 |otherArcProduct K i i| = 1 := by
        unfold Fb; rw [one_mul]; exact div_self (by positivity)
      rw [this]
      exact var_spin _ _ (cycW_pos K w) (fun s => spin_pm _)
    · obtain ⟨N, rfl⟩ : ∃ N, M = N + 2 := ⟨M - 2, by omega⟩
      exact cyc_gen N i.val K w i j rfl h
  · have hA : |arcProduct K i j| ≤ a ^ (j.val - i.val) := by
      have := prod_bound (Finset.univ.filter (fun k : Fin M => i.val ≤ k.val ∧ k.val < j.val)) K b hK
      rwa [card_arc i j hij] at this
    have hB : |otherArcProduct K i j| ≤ a ^ (M - (j.val - i.val)) := by
      have := prod_bound (Finset.univ.filter (fun k : Fin M => k.val < i.val ∨ j.val ≤ k.val)) K b hK
      rwa [card_other i j hij] at this
    have hAle : |arcProduct K i j| ≤ 1 := abs_prod_tanh_le_one _ _
    have hpow1 : a ^ (M - (j.val - i.val)) ≤ 1 := pow_le_one₀ ha0 ha1
    calc Fb |arcProduct K i j| |otherArcProduct K i j|
        ≤ Fb |arcProduct K i j| (a ^ (M - (j.val - i.val))) :=
          Fb_mono _ _ _ (abs_nonneg _) hAle (abs_nonneg _) hB
      _ = Fb (a ^ (M - (j.val - i.val))) |arcProduct K i j| := Fb_symm _ _
      _ ≤ Fb (a ^ (M - (j.val - i.val))) (a ^ (j.val - i.val)) :=
          Fb_mono _ _ _ (pow_nonneg ha0 _) hpow1 (abs_nonneg _) hA
      _ = (a ^ (j.val - i.val) + a ^ (M - (j.val - i.val))) / (1 + a ^ M) := by
          unfold Fb
          have hd : j.val - i.val ≤ M := by have := j.isLt; omega
          rw [← pow_add, show M - (j.val - i.val) + (j.val - i.val) = M by omega, add_comm]

end TFIMPhaseDiagram.Classical.CycleAux

open TFIMPhaseDiagram.Classical in
theorem solution (M : ℕ) (hM : 3 ≤ M) (K : Fin M → ℝ) (w : Fin M → ℝ)
    (b : ℝ) (hb : 0 < b) (hK : ∀ k, |K k| ≤ b) (i j : Fin M) (hij : i ≤ j) :
  |spinCov (cycleProb K (fun k => .finite (w k))) i j| ≤
    (|arcProduct K i j| + |otherArcProduct K i j|) / (1 + |∏ k, Real.tanh (K k)|) ∧
  (|arcProduct K i j| + |otherArcProduct K i j|) / (1 + |∏ k, Real.tanh (K k)|) ≤
    ((Real.tanh b)^(j.val-i.val) + (Real.tanh b)^(M-(j.val-i.val))) /
      (1 + (Real.tanh b)^M) :=
  TFIMPhaseDiagram.Classical.CycleAux.lemma18 M hM K w b hb hK i j hij

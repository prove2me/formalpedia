-- Prove2me | solution 1 for ReflNewton.LocalQuad.theorem_13
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T13:25:56.661607+00:00
-- url     : https://prove2.me/submissions/7e6ca16f-afec-48ab-986b-1426a8f8da0f

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_ReflNewton_LocalQuad_Setting

set_option autoImplicit false

namespace RNQ827

open ReflNewton.FirstOrder ReflNewton.LocalQuad Filter Topology

lemma abs_coord_le {n : ℕ} (w : E n) (i : Fin n) : |w i| ≤ ‖w‖ := by
  have := PiLp.norm_apply_le w i
  simpa [Real.norm_eq_abs] using this

lemma norm_le_of_coord {n : ℕ} (w : E n) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i, |w i| ≤ B) :
    ‖w‖ ≤ n * B := by
  have h1 : ‖w‖ ^ 2 ≤ (n * B) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin n, B ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      _ = n * B ^ 2 := by simp
      _ ≤ (n * B) ^ 2 := by
          rw [mul_pow]
          have : (n:ℝ) ≤ (n:ℝ) ^ 2 := by
            rcases Nat.eq_zero_or_pos n with h0 | h0
            · simp [h0]
            · have : (1:ℝ) ≤ n := by exact_mod_cast h0
              nlinarith
          nlinarith [sq_nonneg B]
  have : 0 ≤ (n:ℝ) * B := mul_nonneg (Nat.cast_nonneg n) hB
  nlinarith [norm_nonneg w]

lemma norm_le_norm_of_coord {n : ℕ} (a b : E n) (h : ∀ i, |a i| ≤ |b i|) : ‖a‖ ≤ ‖b‖ := by
  have h1 : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum; intro i _
    simp only [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
  nlinarith [norm_nonneg a, norm_nonneg b]

lemma ereal_toReal_le {a : EReal} {c : ℝ} (ha : a ≠ ⊥) (h : a ≤ (c : EReal)) : a.toReal ≤ c := by
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top c) h
  rw [← EReal.coe_toReal ha' ha] at h
  exact EReal.coe_le_coe_iff.mp h

lemma ereal_le_toReal {b : EReal} {c : ℝ} (hb : b ≠ ⊤) (h : (c : EReal) ≤ b) : c ≤ b.toReal := by
  have hb' : b ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) h
  rw [← EReal.coe_toReal hb hb'] at h
  exact EReal.coe_le_coe_iff.mp h

lemma ereal_toReal_lt {a : EReal} {c : ℝ} (ha : a ≠ ⊥) (h : a < (c : EReal)) : a.toReal < c := by
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top c) h.le
  rw [← EReal.coe_toReal ha' ha] at h
  exact EReal.coe_lt_coe_iff.mp h

lemma ereal_lt_toReal {b : EReal} {c : ℝ} (hb : b ≠ ⊤) (h : (c : EReal) < b) : c < b.toReal := by
  have hb' : b ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) h.le
  rw [← EReal.coe_toReal hb hb'] at h
  exact EReal.coe_lt_coe_iff.mp h

lemma tri_le (P t s : ℝ) (hP : 0 < P) (ht : 0 ≤ t) (hs0 : 0 ≤ s) (hs1 : s ≤ P / 2) :
    |min (P * Int.fract (t / P)) (P - P * Int.fract (t / P)) - s| ≤ |t - s| := by
  have hf0 := Int.fract_nonneg (t / P)
  have hf1 := Int.fract_lt_one (t / P)
  have hPt : P * (t / P) = t := by field_simp
  have hfe : P * Int.fract (t / P) = t - P * (⌊t / P⌋ : ℝ) := by
    unfold Int.fract; rw [mul_sub, hPt]
  have hm0 : (0:ℤ) ≤ ⌊t / P⌋ := Int.floor_nonneg.mpr (div_nonneg ht hP.le)
  have hw0 : 0 ≤ P * Int.fract (t / P) := mul_nonneg hP.le hf0
  have hw1 : P * Int.fract (t / P) < P := by nlinarith
  rcases (show ⌊t / P⌋ = 0 ∨ 1 ≤ ⌊t / P⌋ by omega) with h0 | h1
  · rw [h0] at hfe
    simp only [Int.cast_zero, mul_zero, sub_zero] at hfe
    rw [hfe]
    rw [hfe] at hw1
    rcases le_total t (P - t) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, abs_of_nonneg (by linarith : 0 ≤ t - s), abs_le]
      constructor <;> linarith
  · have h1' : (1:ℝ) ≤ ⌊t / P⌋ := by exact_mod_cast h1
    have htP : P ≤ t := by nlinarith
    rw [abs_of_nonneg (by linarith : 0 ≤ t - s), abs_le]
    have hmin0 : 0 ≤ min (P * Int.fract (t / P)) (P - P * Int.fract (t / P)) :=
      le_min hw0 (by linarith)
    have hmin1 : min (P * Int.fract (t / P)) (P - P * Int.fract (t / P)) ≤ P / 2 := by
      rcases le_total (P * Int.fract (t / P)) (P / 2) with h | h
      · exact (min_le_left _ _).trans h
      · exact (min_le_right _ _).trans (by linarith)
    constructor <;> linarith

lemma reflectCoord_le (a b : EReal) (c y : ℝ) (ha : a ≤ (c : EReal)) (hb : (c : EReal) ≤ b) :
    |reflectCoord a b y - c| ≤ |y - c| := by
  unfold reflectCoord
  by_cases ha' : a = ⊥
  · rw [if_pos ha']
    by_cases hb' : b = ⊤
    · rw [if_pos hb']
    · rw [if_neg hb']
      have hbc : c ≤ b.toReal := ereal_le_toReal hb' hb
      split_ifs with hy
      · exact le_rfl
      · rw [not_le] at hy
        rw [abs_of_nonneg (by linarith : 0 ≤ y - c), abs_le]
        constructor <;> linarith
  · rw [if_neg ha']
    have hac : a.toReal ≤ c := ereal_toReal_le ha' ha
    by_cases hb' : b = ⊤
    · rw [if_pos hb']
      split_ifs with hy
      · exact le_rfl
      · rw [not_le] at hy
        rw [abs_of_nonpos (by linarith : y - c ≤ 0), abs_le]
        constructor <;> linarith
    · rw [if_neg hb']
      have hbc : c ≤ b.toReal := ereal_le_toReal hb' hb
      simp only
      have key : |(y - a.toReal)| - (c - a.toReal) ≤ |y - c| ∧
          (c - a.toReal) - |(y - a.toReal)| ≤ |y - c| := by
        have h1 := abs_sub_abs_le_abs_sub (y - a.toReal) (c - a.toReal)
        have h2 := abs_sub_abs_le_abs_sub (c - a.toReal) (y - a.toReal)
        rw [abs_of_nonneg (by linarith : 0 ≤ c - a.toReal)] at h1 h2
        have e1 : y - a.toReal - (c - a.toReal) = y - c := by ring
        have e2 : c - a.toReal - (y - a.toReal) = -(y - c) := by ring
        rw [e1] at h1; rw [e2, abs_neg] at h2
        exact ⟨h1, h2⟩
      rcases eq_or_lt_of_le (show 0 ≤ 2 * (b.toReal - a.toReal) by linarith) with hP | hP
      · rw [← hP]
        have hab : a.toReal = c := by linarith
        simp only [zero_mul, sub_zero, min_self, zero_add, hab, sub_self, abs_zero]
        exact abs_nonneg _
      · have h := tri_le (2 * (b.toReal - a.toReal)) |y - a.toReal| (c - a.toReal) hP
          (abs_nonneg _) (by linarith) (by linarith)
        have e3 : min (2 * (b.toReal - a.toReal) * Int.fract (|y - a.toReal| / (2 * (b.toReal - a.toReal))))
            (2 * (b.toReal - a.toReal) -
              2 * (b.toReal - a.toReal) * Int.fract (|y - a.toReal| / (2 * (b.toReal - a.toReal))))
            + a.toReal - c =
            min (2 * (b.toReal - a.toReal) * Int.fract (|y - a.toReal| / (2 * (b.toReal - a.toReal))))
            (2 * (b.toReal - a.toReal) -
              2 * (b.toReal - a.toReal) * Int.fract (|y - a.toReal| / (2 * (b.toReal - a.toReal))))
            - (c - a.toReal) := by ring
        rw [e3]
        refine h.trans ?_
        rw [abs_le]; constructor <;> linarith [key.1, key.2]

lemma reflect_norm_le {n : ℕ} (l u : Fin n → EReal) (c y : E n)
    (hc : c ∈ LewisTorczon.BoundPS.box l u) : ‖reflect l u y - c‖ ≤ ‖y - c‖ := by
  apply norm_le_norm_of_coord
  intro i
  show |reflectCoord (l i) (u i) (y i) - c i| ≤ |y i - c i|
  exact reflectCoord_le _ _ _ _ (hc i).1 (hc i).2

lemma classify {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (xs : E n)
    (hnd : IsNondegenerate l u f xs) (hsos : SecondOrderSufficient l u f xs) (i : Fin n) :
    (gradient f xs i = 0 ∧ i ∈ freeSet l u xs) ∨
    (gradient f xs i < 0 ∧ u i ≠ ⊤ ∧ xs i = (u i).toReal) ∨
    (0 < gradient f xs i ∧ l i ≠ ⊥ ∧ xs i = (l i).toReal) := by
  have h0 : |vCoord (l i) (u i) (xs i) (gradient f xs i)| * gradient f xs i = 0 := by
    have := congrArg (fun w : E n => w i) hsos.2.1
    first
      | exact this
      | simpa [dSqG, vVec] using this
  rcases lt_trichotomy (gradient f xs i) 0 with hg | hg | hg
  · right; left
    have hv : vCoord (l i) (u i) (xs i) (gradient f xs i) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact abs_eq_zero.mp h
      · exact absurd h hg.ne
    unfold vCoord at hv
    rw [if_pos hg] at hv
    by_cases hb : u i = ⊤
    · rw [if_pos hb] at hv; norm_num at hv
    · rw [if_neg hb] at hv
      exact ⟨hg, hb, by linarith⟩
  · left; exact ⟨hg, hnd i hg⟩
  · right; right
    have hv : vCoord (l i) (u i) (xs i) (gradient f xs i) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact abs_eq_zero.mp h
      · exact absurd h hg.ne'
    unfold vCoord at hv
    rw [if_neg (not_lt.mpr hg.le)] at hv
    by_cases ha : l i = ⊥
    · rw [if_pos ha] at hv; norm_num at hv
    · rw [if_neg ha] at hv
      exact ⟨hg, ha, by linarith⟩

lemma free_gap (a b : EReal) (c : ℝ) (h1 : a < (c : EReal)) (h2 : (c : EReal) < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ (a = ⊥ ∨ a.toReal + 2 * δ ≤ c) ∧ (b = ⊤ ∨ c + 2 * δ ≤ b.toReal) := by
  have hA : a = ⊥ ∨ a.toReal < c := by
    by_cases ha' : a = ⊥
    · exact Or.inl ha'
    · exact Or.inr (ereal_toReal_lt ha' h1)
  have hB : b = ⊤ ∨ c < b.toReal := by
    by_cases hb' : b = ⊤
    · exact Or.inl hb'
    · exact Or.inr (ereal_lt_toReal hb' h2)
  obtain ⟨p, hp, hpA, hpB⟩ : ∃ p : ℝ, 0 < p ∧ (a = ⊥ ∨ a.toReal + p ≤ c) ∧
      (b = ⊤ ∨ c + p ≤ b.toReal) := by
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact ⟨1, one_pos, Or.inl hA, Or.inl hB⟩
    · exact ⟨b.toReal - c, by linarith, Or.inl hA, Or.inr (by linarith)⟩
    · exact ⟨c - a.toReal, by linarith, Or.inr (by linarith), Or.inl hB⟩
    · exact ⟨min (c - a.toReal) (b.toReal - c), lt_min (by linarith) (by linarith),
        Or.inr (by linarith [min_le_left (c - a.toReal) (b.toReal - c)]),
        Or.inr (by linarith [min_le_right (c - a.toReal) (b.toReal - c)])⟩
  refine ⟨min 1 (p / 2), lt_min one_pos (by linarith), min_le_left _ _, ?_, ?_⟩
  · rcases hpA with h | h
    · exact Or.inl h
    · right; linarith [min_le_right 1 (p / 2)]
  · rcases hpB with h | h
    · exact Or.inl h
    · right; linarith [min_le_right 1 (p / 2)]

lemma vCoord_lower (a b : EReal) (c xi gi δ : ℝ) (hδ : 0 < δ)
    (ha : a = ⊥ ∨ a.toReal + 2 * δ ≤ c) (hb : b = ⊤ ∨ c + 2 * δ ≤ b.toReal) (hδ1 : δ ≤ 1)
    (hx : |xi - c| ≤ δ) : δ ≤ |vCoord a b xi gi| := by
  have hx' := abs_le.mp hx
  unfold vCoord
  by_cases hg : gi < 0
  · rw [if_pos hg]
    by_cases hb' : b = ⊤
    · rw [if_pos hb', abs_neg, abs_one]; exact hδ1
    · rw [if_neg hb']
      rcases hb with hb | hb
      · exact absurd hb hb'
      · rw [abs_of_neg (by linarith)]; linarith
  · rw [if_neg hg]
    by_cases ha' : a = ⊥
    · rw [if_pos ha', abs_one]; exact hδ1
    · rw [if_neg ha']
      rcases ha with ha | ha
      · exact absurd ha ha'
      · rw [abs_of_pos (by linarith)]; linarith

lemma vCoord_abs_le (a b : EReal) (xi gi : ℝ) :
    |vCoord a b xi gi| ≤ 1 + |xi - a.toReal| + |xi - b.toReal| := by
  have h1 := abs_nonneg (xi - a.toReal)
  have h2 := abs_nonneg (xi - b.toReal)
  unfold vCoord
  split_ifs
  · rw [abs_neg, abs_one]; linarith
  · linarith
  · rw [abs_one]; linarith
  · linarith

lemma jv_abs_le {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (x : E n) (i : Fin n) :
    |jvDg l u f x i| ≤ |gradient f x i| := by
  by_cases h : finiteBound l u f x i
  · simp [jvDg, h]
  · simp [jvDg, h]

lemma free_alg (V J hd gi di δ : ℝ) (hδ : 0 < δ) (hV : δ ≤ |V|) (hJ : |J| ≤ |gi|)
    (h : |V| * hd + J * di = -(|V| * gi)) : |hd + gi| ≤ |gi| * |di| / δ := by
  have h1 : |V| * (hd + gi) = -(J * di) := by linarith
  have h2 : |V| * |hd + gi| = |J| * |di| := by
    have := congrArg abs h1
    rwa [abs_mul, abs_abs, abs_neg, abs_mul] at this
  rw [le_div_iff₀ hδ]
  have h3 : |hd + gi| * δ ≤ |hd + gi| * |V| := mul_le_mul_of_nonneg_left hV (abs_nonneg _)
  have h4 : |J| * |di| ≤ |gi| * |di| := mul_le_mul_of_nonneg_right hJ (abs_nonneg _)
  linarith

lemma act_alg (ei hd gi di γ : ℝ) (hγ : 0 < γ) (hg : γ ≤ |gi|)
    (h : ei * hd + gi * di = -(ei * gi)) : |di + ei| ≤ |ei| * |hd| / γ := by
  have h1 : gi * (di + ei) = -(ei * hd) := by linarith
  have h2 : |gi| * |di + ei| = |ei| * |hd| := by
    have := congrArg abs h1
    rwa [abs_mul, abs_neg, abs_mul] at this
  rw [le_div_iff₀ hγ]
  have h3 : |di + ei| * γ ≤ |di + ei| * |gi| := mul_le_mul_of_nonneg_left hg (abs_nonneg _)
  linarith

lemma fin1 (a K e dn : ℝ) (ha : 0 ≤ a) (hK : a ≤ K) (he : 0 ≤ e) (hd : 0 ≤ dn) :
    a * (e * dn) ≤ K * (e ^ 2 + e * dn) := by
  nlinarith [mul_nonneg he hd, mul_nonneg (sub_nonneg.mpr hK) (mul_nonneg he hd),
    mul_nonneg (ha.trans hK) (sq_nonneg e)]

lemma comb3 (X P Q R e dn A B C : ℝ) (he : 0 ≤ e) (hd : 0 ≤ dn) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hP : |P| ≤ A * (e * dn)) (hQ : |Q| ≤ B * e ^ 2) (hR : |R| ≤ B * (e * dn))
    (hX : X = P - Q - R) : |X| ≤ (A + B + C) * (e ^ 2 + e * dn) := by
  have h1 : 0 ≤ e * dn := mul_nonneg he hd
  have h2 : 0 ≤ e ^ 2 := sq_nonneg e
  obtain ⟨p1, p2⟩ := abs_le.mp hP
  obtain ⟨q1, q2⟩ := abs_le.mp hQ
  obtain ⟨r1, r2⟩ := abs_le.mp hR
  rw [hX, abs_le]
  constructor <;> nlinarith [mul_nonneg hA h2, mul_nonneg hC h2, mul_nonneg hC h1]

lemma grad_diff {n : ℕ} (f : E n → ℝ) (D : Set (E n)) (hDo : IsOpen D)
    (hf : ContDiffOn ℝ 2 f D) {y : E n} (hy : y ∈ D) : DifferentiableAt ℝ (gradient f) y := by
  have h1 : ContDiffAt ℝ 2 f y := hf.contDiffAt (hDo.mem_nhds hy)
  have h2 : ContDiffAt ℝ 1 (fderiv ℝ f) y := h1.fderiv_right (by norm_num)
  have h3 : ContDiffAt ℝ 1 (gradient f) y := by
    have : gradient f = fun x => (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ f x) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ (E n)).symm.contDiff.contDiffAt.comp y h2
  exact h3.differentiableAt (by norm_num)

lemma analytic {n : ℕ} (f : E n → ℝ) (D : Set (E n)) (hDo : IsOpen D)
    (hf : ContDiffOn ℝ 2 f D) (xs : E n) (hxs : xs ∈ D)
    (hLip : ∃ κ r₀ : ℝ, 0 < r₀ ∧ ∀ x ∈ Metric.ball xs r₀, ‖hess f x - hess f xs‖ ≤ κ * ‖x - xs‖) :
    ∃ ε > 0, ∃ κ' ≥ 0, ∀ x, ‖x - xs‖ < ε →
      ‖x - xs‖ ≤ 1 ∧ ‖hess f x - hess f xs‖ ≤ κ' * ‖x - xs‖ ∧
      ‖gradient f x - gradient f xs - hess f xs (x - xs)‖ ≤ κ' * ‖x - xs‖ ^ 2 ∧
      ‖gradient f x - gradient f xs‖ ≤ (‖hess f xs‖ + κ') * ‖x - xs‖ ∧
      ‖hess f x‖ ≤ ‖hess f xs‖ + κ' := by
  obtain ⟨κ, r₀, hr₀, hL⟩ := hLip
  obtain ⟨rD, hrD, hbD⟩ := Metric.isOpen_iff.mp hDo xs hxs
  refine ⟨min (min 1 r₀) rD, lt_min (lt_min one_pos hr₀) hrD, |κ|, abs_nonneg _, fun x hx => ?_⟩
  have hx1 : ‖x - xs‖ < 1 := lt_of_lt_of_le hx (le_trans (min_le_left _ _) (min_le_left _ _))
  have hxr : ‖x - xs‖ < r₀ := lt_of_lt_of_le hx (le_trans (min_le_left _ _) (min_le_right _ _))
  have hxD : ‖x - xs‖ < rD := lt_of_lt_of_le hx (min_le_right _ _)
  have hHy : ∀ y : E n, ‖y - xs‖ < r₀ → ‖hess f y - hess f xs‖ ≤ |κ| * ‖y - xs‖ := fun y hy =>
    (hL y (by rw [Metric.mem_ball, dist_eq_norm]; exact hy)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self κ) (norm_nonneg _))
  have h1 := hHy x hxr
  have hsub : ∀ y ∈ Metric.closedBall xs ‖x - xs‖, y ∈ D ∧ ‖y - xs‖ < r₀ := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    exact ⟨hbD (by rw [Metric.mem_ball, dist_eq_norm]; linarith), by linarith⟩
  have hder : ∀ y ∈ Metric.closedBall xs ‖x - xs‖,
      HasFDerivWithinAt (fun z => gradient f z - hess f xs z) (hess f y - hess f xs)
        (Metric.closedBall xs ‖x - xs‖) y := by
    intro y hy
    have hd := (grad_diff f D hDo hf (hsub y hy).1).hasFDerivAt
    exact (hd.sub (hess f xs).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ y ∈ Metric.closedBall xs ‖x - xs‖, ‖hess f y - hess f xs‖ ≤ |κ| * ‖x - xs‖ := by
    intro y hy
    have hy' := hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy'
    exact (hHy y (hsub y hy).2).trans (mul_le_mul_of_nonneg_left hy' (abs_nonneg _))
  have hmv := (convex_closedBall xs ‖x - xs‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hder
    hbound (Metric.mem_closedBall_self (norm_nonneg _))
    (by rw [Metric.mem_closedBall, dist_eq_norm])
  have h2 : ‖gradient f x - gradient f xs - hess f xs (x - xs)‖ ≤ |κ| * ‖x - xs‖ ^ 2 := by
    have : gradient f x - gradient f xs - hess f xs (x - xs) =
        (gradient f x - hess f xs x) - (gradient f xs - hess f xs xs) := by
      rw [map_sub]; abel
    rw [this, sq, ← mul_assoc]; exact hmv
  have he0 := norm_nonneg (x - xs)
  have hκ0 := abs_nonneg κ
  refine ⟨hx1.le, h1, h2, ?_, ?_⟩
  · have h3 : ‖gradient f x - gradient f xs‖ ≤
        ‖hess f xs (x - xs)‖ + ‖gradient f x - gradient f xs - hess f xs (x - xs)‖ := by
      have := norm_add_le (hess f xs (x - xs)) (gradient f x - gradient f xs - hess f xs (x - xs))
      rwa [add_sub_cancel] at this
    have h4 := (hess f xs).le_opNorm (x - xs)
    have h5 : |κ| * ‖x - xs‖ ^ 2 ≤ |κ| * ‖x - xs‖ := by
      apply mul_le_mul_of_nonneg_left _ hκ0; nlinarith
    nlinarith
  · have h3 : ‖hess f x‖ ≤ ‖hess f xs‖ + ‖hess f x - hess f xs‖ := by
      have := norm_add_le (hess f xs) (hess f x - hess f xs)
      rwa [add_sub_cancel] at this
    have h5 : |κ| * ‖x - xs‖ ≤ |κ| := by
      have := mul_le_mul_of_nonneg_left hx1.le hκ0; linarith
    linarith

noncomputable def Tmap {n : ℕ} (m : Fin n → ℝ) (A : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n where
  toFun w := WithLp.toLp 2 (fun i => m i * A w i + (1 - m i) * w i)
  map_add' a b := by ext i; simp; ring
  map_smul' c a := by ext i; simp; ring

lemma Tmap_apply {n : ℕ} (m : Fin n → ℝ) (A : E n →L[ℝ] E n) (w : E n) (i : Fin n) :
    (Tmap m A w) i = m i * A w i + (1 - m i) * w i := rfl

lemma Tmap_inj {n : ℕ} (S : Set (Fin n)) (m : Fin n → ℝ) (hm1 : ∀ i ∈ S, m i = 1)
    (hm0 : ∀ i ∉ S, m i = 0) (A : E n →L[ℝ] E n)
    (hpos : ∀ w : E n, w ≠ 0 → (∀ i ∉ S, w i = 0) → 0 < inner ℝ (A w) w) :
    Function.Injective (Tmap m A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have hc : ∀ i, m i * A w i + (1 - m i) * w i = 0 := fun i => by
    rw [← Tmap_apply, hw]; rfl
  have hA : ∀ i ∉ S, w i = 0 := fun i hi => by
    have := hc i; rw [hm0 i hi] at this; simpa using this
  have hB : ∀ i ∈ S, A w i = 0 := fun i hi => by
    have := hc i; rw [hm1 i hi] at this; simpa using this
  by_contra hne
  have h1 := hpos w hne hA
  have h0 : inner ℝ (A w) w = 0 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero; intro i _
    by_cases hi : i ∈ S
    · simp [hB i hi]
    · simp [hA i hi]
  linarith

lemma Tmap_bound {n : ℕ} (m : Fin n → ℝ) (A : E n →L[ℝ] E n) (hinj : Function.Injective (Tmap m A)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w, ‖w‖ ≤ K * ‖Tmap m A w‖ := by
  let T := LinearEquiv.ofInjectiveEndo (Tmap m A) hinj
  let Tc : E n →L[ℝ] E n := LinearMap.toContinuousLinearMap (T.symm : E n →ₗ[ℝ] E n)
  refine ⟨‖Tc‖, norm_nonneg _, fun w => ?_⟩
  have h1 : T w = Tmap m A w := rfl
  have h2 : Tc (Tmap m A w) = w := by
    rw [← h1]
    show T.symm (T w) = w
    exact T.symm_apply_apply w
  calc ‖w‖ = ‖Tc (Tmap m A w)‖ := by rw [h2]
    _ ≤ ‖Tc‖ * ‖Tmap m A w‖ := Tc.le_opNorm _


lemma newton_rel {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (x dh : E n)
    (hb : bHat l u f x dh = -dG l u f x) (i : Fin n) :
    |vVec l u f x i| * hess f x (WithLp.toLp 2 fun j => Real.sqrt |vVec l u f x j| * dh j) i
      + jvDg l u f x i * (WithLp.toLp 2 fun j => Real.sqrt |vVec l u f x j| * dh j : E n) i
      = -(|vVec l u f x i| * gradient f x i) := by
  have h : Real.sqrt |vVec l u f x i| *
        hess f x (WithLp.toLp 2 fun j => Real.sqrt |vVec l u f x j| * dh j) i
      + jvDg l u f x i * dh i = -(Real.sqrt |vVec l u f x i| * gradient f x i) := by
    have := congrArg (fun w : E n => w i) hb
    first
      | exact this
      | simpa [bHat, dG] using this
  have hs := Real.mul_self_sqrt (abs_nonneg (vVec l u f x i))
  rw [PiLp.toLp_apply]
  linear_combination (Real.sqrt |vVec l u f x i|) * h -
    (hess f x (WithLp.toLp 2 fun j => Real.sqrt |vVec l u f x j| * dh j) i + gradient f x i) * hs

set_option maxHeartbeats 1000000 in
lemma coord_bound {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (xs : E n)
    (hnd : IsNondegenerate l u f xs) (hsos : SecondOrderSufficient l u f xs)
    (ε κ' : ℝ) (hε : 0 < ε) (hκ : 0 ≤ κ')
    (hA : ∀ x, ‖x - xs‖ < ε →
      ‖x - xs‖ ≤ 1 ∧ ‖hess f x - hess f xs‖ ≤ κ' * ‖x - xs‖ ∧
      ‖gradient f x - gradient f xs - hess f xs (x - xs)‖ ≤ κ' * ‖x - xs‖ ^ 2 ∧
      ‖gradient f x - gradient f xs‖ ≤ (‖hess f xs‖ + κ') * ‖x - xs‖ ∧
      ‖hess f x‖ ≤ ‖hess f xs‖ + κ')
    (m : Fin n → ℝ) (hm1 : ∀ i ∈ freeSet l u xs, m i = 1) (hm0 : ∀ i ∉ freeSet l u xs, m i = 0)
    (i : Fin n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ ρ > 0, ∀ x : E n, ‖x - xs‖ < ρ → x ∈ intBox l u →
      (∀ d : E n, |vVec l u f x i| * hess f x d i + jvDg l u f x i * d i =
          -(|vVec l u f x i| * gradient f x i) →
        |m i * hess f xs (x + d - xs) i + (1 - m i) * (x + d - xs) i| ≤
          K * (‖x - xs‖ ^ 2 + ‖x - xs‖ * ‖d‖)) ∧
      |dSqG l u f x i| ≤ K * ‖x - xs‖ := by
  have hL : 0 ≤ ‖hess f xs‖ + κ' := add_nonneg (norm_nonneg _) hκ
  rcases classify l u f xs hnd hsos i with ⟨hg0, hfree⟩ | ⟨hgneg, hui, hxu⟩ | ⟨hgpos, hli, hxl⟩
  · -- free coordinate
    obtain ⟨δ, hδ, hδ1, hδa, hδb⟩ := free_gap (l i) (u i) (xs i) hfree.1 hfree.2
    have hVb0 : 0 ≤ 3 + |xs i - (l i).toReal| + |xs i - (u i).toReal| := by positivity
    have hA0 : 0 ≤ (‖hess f xs‖ + κ') / δ := div_nonneg hL hδ.le
    refine ⟨(‖hess f xs‖ + κ') / δ + κ' +
        (3 + |xs i - (l i).toReal| + |xs i - (u i).toReal|) * (‖hess f xs‖ + κ'),
      add_nonneg (add_nonneg hA0 hκ) (mul_nonneg hVb0 hL), min ε δ, lt_min hε hδ,
      fun x hx hxint => ?_⟩
    have hxε : ‖x - xs‖ < ε := lt_of_lt_of_le hx (min_le_left _ _)
    obtain ⟨he1, hH, hρ, hgL, hHn⟩ := hA x hxε
    have he0 := norm_nonneg (x - xs)
    have hei : |x i - xs i| ≤ δ := by
      have := abs_coord_le (x - xs) i
      rw [PiLp.sub_apply] at this
      linarith [min_le_right ε δ]
    have hgi : |gradient f x i| ≤ (‖hess f xs‖ + κ') * ‖x - xs‖ := by
      have := abs_coord_le (gradient f x - gradient f xs) i
      rw [PiLp.sub_apply, hg0, sub_zero] at this
      linarith
    have hv : δ ≤ |vVec l u f x i| :=
      vCoord_lower (l i) (u i) (xs i) (x i) _ δ hδ hδa hδb hδ1 hei
    refine ⟨fun d hrel => ?_, ?_⟩
    · have h1 := free_alg (vVec l u f x i) (jvDg l u f x i) (hess f x d i) (gradient f x i) (d i) δ
        hδ hv (jv_abs_le l u f x i) hrel
      rw [hm1 i hfree, one_mul, sub_self, zero_mul, add_zero]
      have hd0 := norm_nonneg d
      refine comb3 _ (hess f x d i + gradient f x i)
        ((gradient f x - gradient f xs - hess f xs (x - xs)) i)
        (((hess f x - hess f xs) d) i) ‖x - xs‖ ‖d‖ ((‖hess f xs‖ + κ') / δ) κ'
        ((3 + |xs i - (l i).toReal| + |xs i - (u i).toReal|) * (‖hess f xs‖ + κ'))
        he0 hd0 hA0 hκ (mul_nonneg hVb0 hL) ?_ ?_ ?_ ?_
      · refine h1.trans ?_
        have h2 : |gradient f x i| * |d i| / δ ≤ (‖hess f xs‖ + κ') * ‖x - xs‖ * ‖d‖ / δ := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hgi (abs_coord_le d i) (abs_nonneg _) (mul_nonneg hL he0))
            (inv_nonneg.mpr hδ.le)
        refine h2.trans (le_of_eq ?_)
        ring
      · exact (abs_coord_le _ i).trans hρ
      · refine (abs_coord_le _ i).trans ?_
        refine ((hess f x - hess f xs).le_opNorm d).trans ?_
        have := mul_le_mul_of_nonneg_right hH hd0
        linarith [this]
      · have : x + d - xs = (x - xs) + d := by abel
        rw [this, map_add]
        simp only [PiLp.add_apply, PiLp.sub_apply, ContinuousLinearMap.sub_apply, hg0]
        ring
    · show |(|vVec l u f x i| * gradient f x i)| ≤ _
      rw [abs_mul, abs_abs]
      have hvb : |vVec l u f x i| ≤ 3 + |xs i - (l i).toReal| + |xs i - (u i).toReal| := by
        have h1 := vCoord_abs_le (l i) (u i) (x i) (gradient f x i)
        have h2 := abs_sub_le (x i) (xs i) (l i).toReal
        have h3 := abs_sub_le (x i) (xs i) (u i).toReal
        show |vCoord (l i) (u i) (x i) (gradient f x i)| ≤ _
        linarith
      calc |vVec l u f x i| * |gradient f x i|
          ≤ (3 + |xs i - (l i).toReal| + |xs i - (u i).toReal|) *
              ((‖hess f xs‖ + κ') * ‖x - xs‖) :=
            mul_le_mul hvb hgi (abs_nonneg _) hVb0
        _ ≤ _ := by
          have : 0 ≤ ((‖hess f xs‖ + κ') / δ + κ') * ‖x - xs‖ :=
            mul_nonneg (add_nonneg hA0 hκ) he0
          linarith
  · -- active at the upper bound
    have hnf : i ∉ freeSet l u xs := fun h => by
      have := ereal_lt_toReal hui h.2; linarith
    have hγ : 0 < -(gradient f xs i) / 2 := by linarith
    have hA0 : 0 ≤ (‖hess f xs‖ + κ') / (-(gradient f xs i) / 2) := div_nonneg hL hγ.le
    refine ⟨(‖hess f xs‖ + κ') / (-(gradient f xs i) / 2) + |gradient f xs i| + (‖hess f xs‖ + κ'),
      add_nonneg (add_nonneg hA0 (abs_nonneg _)) hL,
      min ε ((-(gradient f xs i) / 2) / (‖hess f xs‖ + κ' + 1)),
      lt_min hε (div_pos hγ (by linarith)), fun x hx hxint => ?_⟩
    have hxε : ‖x - xs‖ < ε := lt_of_lt_of_le hx (min_le_left _ _)
    obtain ⟨he1, hH, hρ, hgL, hHn⟩ := hA x hxε
    have he0 := norm_nonneg (x - xs)
    have hgi : |gradient f x i - gradient f xs i| ≤ (‖hess f xs‖ + κ') * ‖x - xs‖ := by
      have := abs_coord_le (gradient f x - gradient f xs) i
      rw [PiLp.sub_apply] at this; linarith
    have hLe : (‖hess f xs‖ + κ') * ‖x - xs‖ < -(gradient f xs i) / 2 := by
      have h1 : ‖x - xs‖ < (-(gradient f xs i) / 2) / (‖hess f xs‖ + κ' + 1) :=
        lt_of_lt_of_le hx (min_le_right _ _)
      rw [lt_div_iff₀ (by linarith)] at h1
      nlinarith
    obtain ⟨a1, a2⟩ := abs_le.mp hgi
    have hgx : gradient f x i < 0 := by linarith
    have hgx2 : -(gradient f xs i) / 2 ≤ |gradient f x i| := by rw [abs_of_neg hgx]; linarith
    have hxlt : x i < (u i).toReal := ereal_lt_toReal hui (hxint i).2
    have hei : x i - xs i < 0 := by rw [hxu]; linarith
    have hv : vVec l u f x i = x i - xs i := by
      show vCoord (l i) (u i) (x i) (gradient f x i) = _
      unfold vCoord; rw [if_pos hgx, if_neg hui, hxu]
    have hJ : jvDg l u f x i = -(gradient f x i) := by
      have hfb : finiteBound l u f x i := Or.inl ⟨hgx, hui⟩
      simp [jvDg, hfb, abs_of_neg hgx]
    have b1 : |x i - xs i| ≤ ‖x - xs‖ := by
      have := abs_coord_le (x - xs) i; rwa [PiLp.sub_apply] at this
    refine ⟨fun d hrel => ?_, ?_⟩
    · rw [hm0 i hnf, zero_mul, sub_zero, one_mul, zero_add]
      rw [hv, hJ, abs_of_neg hei] at hrel
      have hrel' : (x i - xs i) * hess f x d i + gradient f x i * d i =
          -((x i - xs i) * gradient f x i) := by linarith
      have h1 := act_alg (x i - xs i) (hess f x d i) (gradient f x i) (d i) _ hγ hgx2 hrel'
      have hcoord : (x + d - xs) i = d i + (x i - xs i) := by
        simp only [PiLp.sub_apply, PiLp.add_apply]; ring
      rw [hcoord]
      have b2 : |hess f x d i| ≤ (‖hess f xs‖ + κ') * ‖d‖ :=
        (abs_coord_le _ i).trans (((hess f x).le_opNorm d).trans
          (mul_le_mul_of_nonneg_right hHn (norm_nonneg _)))
      have b3 : |x i - xs i| * |hess f x d i| / (-(gradient f xs i) / 2) ≤
          (‖hess f xs‖ + κ') / (-(gradient f xs i) / 2) * (‖x - xs‖ * ‖d‖) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have := mul_le_mul b1 b2 (abs_nonneg _) he0
        have hi : 0 ≤ (-(gradient f xs i) / 2)⁻¹ := inv_nonneg.mpr hγ.le
        calc |x i - xs i| * |hess f x d i| * (-(gradient f xs i) / 2)⁻¹
            ≤ ‖x - xs‖ * ((‖hess f xs‖ + κ') * ‖d‖) * (-(gradient f xs i) / 2)⁻¹ :=
              mul_le_mul_of_nonneg_right this hi
          _ = _ := by ring
      refine (h1.trans b3).trans (fin1 _ _ _ _ hA0 ?_ he0 (norm_nonneg d))
      have := abs_nonneg (gradient f xs i)
      linarith
    · show |(|vVec l u f x i| * gradient f x i)| ≤ _
      rw [abs_mul, abs_abs, hv]
      have b2 : |gradient f x i| ≤ |gradient f xs i| + (‖hess f xs‖ + κ') := by
        have h1 := abs_sub_abs_le_abs_sub (gradient f x i) (gradient f xs i)
        have h2 : (‖hess f xs‖ + κ') * ‖x - xs‖ ≤ ‖hess f xs‖ + κ' := by nlinarith
        linarith
      calc |x i - xs i| * |gradient f x i| ≤ ‖x - xs‖ * (|gradient f xs i| + (‖hess f xs‖ + κ')) :=
            mul_le_mul b1 b2 (abs_nonneg _) he0
        _ ≤ _ := by
          have : 0 ≤ (‖hess f xs‖ + κ') / (-(gradient f xs i) / 2) * ‖x - xs‖ :=
            mul_nonneg hA0 he0
          linarith
  · -- active at the lower bound
    have hnf : i ∉ freeSet l u xs := fun h => by
      have := ereal_toReal_lt hli h.1; linarith
    have hγ : 0 < gradient f xs i / 2 := by linarith
    have hA0 : 0 ≤ (‖hess f xs‖ + κ') / (gradient f xs i / 2) := div_nonneg hL hγ.le
    refine ⟨(‖hess f xs‖ + κ') / (gradient f xs i / 2) + |gradient f xs i| + (‖hess f xs‖ + κ'),
      add_nonneg (add_nonneg hA0 (abs_nonneg _)) hL,
      min ε ((gradient f xs i / 2) / (‖hess f xs‖ + κ' + 1)),
      lt_min hε (div_pos hγ (by linarith)), fun x hx hxint => ?_⟩
    have hxε : ‖x - xs‖ < ε := lt_of_lt_of_le hx (min_le_left _ _)
    obtain ⟨he1, hH, hρ, hgL, hHn⟩ := hA x hxε
    have he0 := norm_nonneg (x - xs)
    have hgi : |gradient f x i - gradient f xs i| ≤ (‖hess f xs‖ + κ') * ‖x - xs‖ := by
      have := abs_coord_le (gradient f x - gradient f xs) i
      rw [PiLp.sub_apply] at this; linarith
    have hLe : (‖hess f xs‖ + κ') * ‖x - xs‖ < gradient f xs i / 2 := by
      have h1 : ‖x - xs‖ < (gradient f xs i / 2) / (‖hess f xs‖ + κ' + 1) :=
        lt_of_lt_of_le hx (min_le_right _ _)
      rw [lt_div_iff₀ (by linarith)] at h1
      nlinarith
    obtain ⟨a1, a2⟩ := abs_le.mp hgi
    have hgx : 0 < gradient f x i := by linarith
    have hgx2 : gradient f xs i / 2 ≤ |gradient f x i| := by rw [abs_of_pos hgx]; linarith
    have hxgt : (l i).toReal < x i := ereal_toReal_lt hli (hxint i).1
    have hei : 0 < x i - xs i := by rw [hxl]; linarith
    have hv : vVec l u f x i = x i - xs i := by
      show vCoord (l i) (u i) (x i) (gradient f x i) = _
      unfold vCoord; rw [if_neg (not_lt.mpr hgx.le), if_neg hli, hxl]
    have hJ : jvDg l u f x i = gradient f x i := by
      have hfb : finiteBound l u f x i := Or.inr ⟨hgx.le, hli⟩
      simp [jvDg, hfb, abs_of_pos hgx]
    have b1 : |x i - xs i| ≤ ‖x - xs‖ := by
      have := abs_coord_le (x - xs) i; rwa [PiLp.sub_apply] at this
    refine ⟨fun d hrel => ?_, ?_⟩
    · rw [hm0 i hnf, zero_mul, sub_zero, one_mul, zero_add]
      rw [hv, hJ, abs_of_pos hei] at hrel
      have h1 := act_alg (x i - xs i) (hess f x d i) (gradient f x i) (d i) _ hγ hgx2 hrel
      have hcoord : (x + d - xs) i = d i + (x i - xs i) := by
        simp only [PiLp.sub_apply, PiLp.add_apply]; ring
      rw [hcoord]
      have b2 : |hess f x d i| ≤ (‖hess f xs‖ + κ') * ‖d‖ :=
        (abs_coord_le _ i).trans (((hess f x).le_opNorm d).trans
          (mul_le_mul_of_nonneg_right hHn (norm_nonneg _)))
      have b3 : |x i - xs i| * |hess f x d i| / (gradient f xs i / 2) ≤
          (‖hess f xs‖ + κ') / (gradient f xs i / 2) * (‖x - xs‖ * ‖d‖) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have := mul_le_mul b1 b2 (abs_nonneg _) he0
        have hi : 0 ≤ (gradient f xs i / 2)⁻¹ := inv_nonneg.mpr hγ.le
        calc |x i - xs i| * |hess f x d i| * (gradient f xs i / 2)⁻¹
            ≤ ‖x - xs‖ * ((‖hess f xs‖ + κ') * ‖d‖) * (gradient f xs i / 2)⁻¹ :=
              mul_le_mul_of_nonneg_right this hi
          _ = _ := by ring
      refine (h1.trans b3).trans (fin1 _ _ _ _ hA0 ?_ he0 (norm_nonneg d))
      have := abs_nonneg (gradient f xs i)
      linarith
    · show |(|vVec l u f x i| * gradient f x i)| ≤ _
      rw [abs_mul, abs_abs, hv]
      have b2 : |gradient f x i| ≤ |gradient f xs i| + (‖hess f xs‖ + κ') := by
        have h1 := abs_sub_abs_le_abs_sub (gradient f x i) (gradient f xs i)
        have h2 : (‖hess f xs‖ + κ') * ‖x - xs‖ ≤ ‖hess f xs‖ + κ' := by nlinarith
        linarith
      calc |x i - xs i| * |gradient f x i| ≤ ‖x - xs‖ * (|gradient f xs i| + (‖hess f xs‖ + κ')) :=
            mul_le_mul b1 b2 (abs_nonneg _) he0
        _ ≤ _ := by
          have : 0 ≤ (‖hess f xs‖ + κ') / (gradient f xs i / 2) * ‖x - xs‖ :=
            mul_nonneg hA0 he0
          linarith

lemma core {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (xs : E n)
    (hnd : IsNondegenerate l u f xs) (hsos : SecondOrderSufficient l u f xs)
    (ε κ' : ℝ) (hε : 0 < ε) (hκ : 0 ≤ κ')
    (hA : ∀ x, ‖x - xs‖ < ε →
      ‖x - xs‖ ≤ 1 ∧ ‖hess f x - hess f xs‖ ≤ κ' * ‖x - xs‖ ∧
      ‖gradient f x - gradient f xs - hess f xs (x - xs)‖ ≤ κ' * ‖x - xs‖ ^ 2 ∧
      ‖gradient f x - gradient f xs‖ ≤ (‖hess f xs‖ + κ') * ‖x - xs‖ ∧
      ‖hess f x‖ ≤ ‖hess f xs‖ + κ') :
    ∃ A0 Q ε' : ℝ, 0 ≤ A0 ∧ 0 ≤ Q ∧ 0 < ε' ∧ ∀ x : E n, ‖x - xs‖ < ε' → x ∈ intBox l u →
      (∀ d : E n, (∀ i, |vVec l u f x i| * hess f x d i + jvDg l u f x i * d i =
          -(|vVec l u f x i| * gradient f x i)) →
        ‖x + d - xs‖ ≤ A0 * (‖x - xs‖ ^ 2 + ‖x - xs‖ * ‖d‖)) ∧
      ‖dSqG l u f x‖ ≤ Q * ‖x - xs‖ := by
  classical
  let m : Fin n → ℝ := fun i => if i ∈ freeSet l u xs then 1 else 0
  have hm1 : ∀ i ∈ freeSet l u xs, m i = 1 := fun i hi => if_pos hi
  have hm0 : ∀ i ∉ freeSet l u xs, m i = 0 := fun i hi => if_neg hi
  have hcb := fun i => coord_bound l u f xs hnd hsos ε κ' hε hκ hA m hm1 hm0 i
  choose K hK0 ρ hρ hKb using hcb
  have hev : ∀ᶠ x in 𝓝 xs, ∀ i, ‖x - xs‖ < ρ i := by
    rw [Filter.eventually_all]; intro i
    filter_upwards [Metric.ball_mem_nhds xs (hρ i)] with x hx
    rwa [Metric.mem_ball, dist_eq_norm] at hx
  obtain ⟨ε', hε', hε'b⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨KT, hKT0, hKT⟩ := Tmap_bound m (hess f xs)
    (Tmap_inj (freeSet l u xs) m hm1 hm0 (hess f xs) hsos.2.2)
  have hKs0 : 0 ≤ ∑ j, K j := Finset.sum_nonneg (fun j _ => hK0 j)
  have hKs : ∀ i, K i ≤ ∑ j, K j := fun i =>
    Finset.single_le_sum (fun j _ => hK0 j) (Finset.mem_univ i)
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨KT * (n * ∑ j, K j), n * ∑ j, K j, ε', mul_nonneg hKT0 (mul_nonneg hn0 hKs0),
    mul_nonneg hn0 hKs0, hε', fun x hx hxint => ?_⟩
  have hxρ : ∀ i, ‖x - xs‖ < ρ i := hε'b (show dist x xs < ε' by rwa [dist_eq_norm])
  refine ⟨fun d hrel => ?_, ?_⟩
  · have hpos : 0 ≤ ‖x - xs‖ ^ 2 + ‖x - xs‖ * ‖d‖ := by positivity
    have hc : ∀ i, |(Tmap m (hess f xs) (x + d - xs)) i| ≤
        (∑ j, K j) * (‖x - xs‖ ^ 2 + ‖x - xs‖ * ‖d‖) := by
      intro i
      rw [Tmap_apply]
      exact ((hKb i x (hxρ i) hxint).1 d (hrel i)).trans
        (mul_le_mul_of_nonneg_right (hKs i) hpos)
    calc ‖x + d - xs‖ ≤ KT * ‖Tmap m (hess f xs) (x + d - xs)‖ := hKT _
      _ ≤ KT * (n * ((∑ j, K j) * (‖x - xs‖ ^ 2 + ‖x - xs‖ * ‖d‖))) :=
          mul_le_mul_of_nonneg_left (norm_le_of_coord _ _ (mul_nonneg hKs0 hpos) hc) hKT0
      _ = KT * (n * ∑ j, K j) * (‖x - xs‖ ^ 2 + ‖x - xs‖ * ‖d‖) := by ring
  · have hc : ∀ i, |dSqG l u f x i| ≤ (∑ j, K j) * ‖x - xs‖ := fun i =>
      ((hKb i x (hxρ i) hxint).2).trans (mul_le_mul_of_nonneg_right (hKs i) (norm_nonneg _))
    calc ‖dSqG l u f x‖ ≤ n * ((∑ j, K j) * ‖x - xs‖) :=
          norm_le_of_coord _ _ (mul_nonneg hKs0 (norm_nonneg _)) hc
      _ = n * (∑ j, K j) * ‖x - xs‖ := by ring

end RNQ827

open ReflNewton.LocalQuad in
theorem solution {n : ℕ} (l u : Fin n → EReal)
    (hl : ∀ i, l i ≠ ⊤) (hu : ∀ i, u i ≠ ⊥) (hlu : l ≤ u)
    (f : ReflNewton.FirstOrder.E n → ℝ) (D : Set (ReflNewton.FirstOrder.E n)) (hDo : IsOpen D)
    (hFD : LewisTorczon.BoundPS.box l u ⊆ D) (hf : ContDiffOn ℝ 2 f D)
    (xstar : ReflNewton.FirstOrder.E n) (hnd : IsNondegenerate l u f xstar)
    (hsos : SecondOrderSufficient l u f xstar)
    (hLip : ∃ κ r₀ : ℝ, 0 < r₀ ∧
      ∀ x ∈ Metric.ball xstar r₀,
        ‖hess f x - hess f xstar‖ ≤ κ * ‖x - xstar‖)
    (χα : ℝ) (hχ : 0 ≤ χα) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ,
      ∀ (x : ℕ → ReflNewton.FirstOrder.E n) (α : ℕ → ℝ),
        IsLocalNewtonRun l u f χα x α →
        x 0 ∈ Metric.ball xstar r →
        (∀ k, x k ∈ ReflNewton.FirstOrder.intBox l u) ∧
        (∀ k, ‖x (k + 1) - xstar‖ ≤ C * ‖x k - xstar‖ ^ 2) ∧
        Filter.Tendsto x Filter.atTop (nhds xstar) := by
  classical
  have hxsD : xstar ∈ D := hFD hsos.1
  obtain ⟨ε, hε, κ', hκ, hA⟩ := RNQ827.analytic f D hDo hf xstar hxsD hLip
  obtain ⟨A0, Q, ε', hA0, hQ, hε', hcore⟩ := RNQ827.core l u f xstar hnd hsos ε κ' hε hκ hA
  have hχQ : 0 ≤ χα * Q := mul_nonneg hχ hQ
  have hC0 : 0 ≤ 4 * A0 + χα * Q * (4 * A0 + 1) := by nlinarith
  set C := 4 * A0 + χα * Q * (4 * A0 + 1) with hC
  have hden : 0 < 4 * (A0 + C + 1) := by linarith
  set r := min (min ε' 1) (1 / (4 * (A0 + C + 1))) with hr
  have hr0 : 0 < r := lt_min (lt_min hε' one_pos) (div_pos one_pos hden)
  have hr1 : r ≤ ε' := le_trans (min_le_left _ _) (min_le_left _ _)
  have hr2 : r ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hr3 : r * (4 * (A0 + C + 1)) ≤ 1 := by
    have h := min_le_right (min ε' 1) (1 / (4 * (A0 + C + 1)))
    rw [← hr, le_div_iff₀ hden] at h
    exact h
  have hAr : A0 * r ≤ 1 / 4 := by nlinarith [mul_nonneg hC0 hr0.le]
  have hCr : C * r ≤ 1 / 4 := by nlinarith [mul_nonneg hA0 hr0.le]
  refine ⟨r, hr0, C, fun x α hrun hx0 => ?_⟩
  have hint : ∀ k, x k ∈ ReflNewton.FirstOrder.intBox l u := by
    intro k
    cases k with
    | zero => exact hrun.1
    | succ k =>
      obtain ⟨dh, _, hrest⟩ := hrun.2 k
      obtain ⟨_, hmem, hnext⟩ := hrest
      rw [hnext]; exact hmem
  have step : ∀ k, ‖x k - xstar‖ < r → ‖x (k + 1) - xstar‖ ≤ C * ‖x k - xstar‖ ^ 2 := by
    intro k hk
    obtain ⟨dh, hb, hrest⟩ := hrun.2 k
    obtain ⟨hα, hmem, hnext⟩ := hrest
    have hrel := RNQ827.newton_rel l u f (x k) dh hb
    obtain ⟨hcd, hcq⟩ := hcore (x k) (lt_of_lt_of_le hk hr1) (hint k)
    have hW := hcd _ hrel
    set d : ReflNewton.FirstOrder.E n :=
      WithLp.toLp 2 fun j => Real.sqrt |ReflNewton.FirstOrder.vVec l u f (x k) j| * dh j with hd
    set e := ‖x k - xstar‖ with he
    have he0 : 0 ≤ e := norm_nonneg _
    have hAe : A0 * e ≤ 1 / 4 := by nlinarith [mul_le_mul_of_nonneg_left hk.le hA0]
    have hdn : ‖d‖ ≤ ‖x k + d - xstar‖ + e := by
      have h : d = (x k + d - xstar) - (x k - xstar) := by abel
      calc ‖d‖ = ‖(x k + d - xstar) - (x k - xstar)‖ := by rw [← h]
        _ ≤ ‖x k + d - xstar‖ + ‖x k - xstar‖ := norm_sub_le _ _
    have hW0 := norm_nonneg (x k + d - xstar)
    have hd0 := norm_nonneg d
    have hW2 : ‖x k + d - xstar‖ ≤ 4 * A0 * e ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hdn (mul_nonneg hA0 he0)
      have h2 := mul_le_mul_of_nonneg_right hAe hW0
      nlinarith
    have hdn2 : ‖d‖ ≤ (4 * A0 + 1) * e := by
      have h1 : e ^ 2 ≤ e := by nlinarith [lt_of_lt_of_le hk hr2]
      have h2 : 4 * A0 * e ^ 2 ≤ 4 * A0 * e := mul_le_mul_of_nonneg_left h1 (by linarith)
      nlinarith
    have hα' : |α k - 1| ≤ χα * Q * e := by
      refine hα.trans ?_
      have := mul_le_mul_of_nonneg_left hcq hχ
      linarith [this]
    have hy : ‖x k + α k • d - xstar‖ ≤ C * e ^ 2 := by
      have hsplit : x k + α k • d - xstar = (x k + d - xstar) + (α k - 1) • d := by
        rw [sub_smul, one_smul]; abel
      rw [hsplit]
      calc ‖(x k + d - xstar) + (α k - 1) • d‖
          ≤ ‖x k + d - xstar‖ + ‖(α k - 1) • d‖ := norm_add_le _ _
        _ = ‖x k + d - xstar‖ + |α k - 1| * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 4 * A0 * e ^ 2 + (χα * Q * e) * ((4 * A0 + 1) * e) :=
            add_le_add hW2 (mul_le_mul hα' hdn2 hd0 (mul_nonneg hχQ he0))
        _ = C * e ^ 2 := by rw [hC]; ring
    rw [hnext]
    have hR : x k + ReflNewton.FirstOrder.reflPath l u (x k) d (α k) =
        ReflNewton.FirstOrder.reflect l u (x k + α k • d) := by
      simp [ReflNewton.FirstOrder.reflPath]
    rw [hR]
    exact (RNQ827.reflect_norm_le l u xstar _ hsos.1).trans hy
  have hall : ∀ k, ‖x k - xstar‖ < r ∧ ‖x k - xstar‖ ≤ (1 / 2) ^ k * ‖x 0 - xstar‖ := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, by simp⟩
      rw [Metric.mem_ball, dist_eq_norm] at hx0; exact hx0
    | succ k ih =>
      have h1 := step k ih.1
      have h0 := norm_nonneg (x k - xstar)
      have hCe : C * ‖x k - xstar‖ ≤ 1 / 4 :=
        le_trans (mul_le_mul_of_nonneg_left ih.1.le hC0) hCr
      have h2 : C * ‖x k - xstar‖ ^ 2 ≤ ‖x k - xstar‖ / 4 := by
        have := mul_le_mul_of_nonneg_right hCe h0
        nlinarith
      refine ⟨by linarith [ih.1], ?_⟩
      rw [pow_succ]
      nlinarith [ih.2]
  refine ⟨hint, fun k => step k (hall k).1, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => (hall k).2) ?_
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num : (1:ℝ) / 2 < 1)).mul_const ‖x 0 - xstar‖
  rw [zero_mul] at h
  exact h

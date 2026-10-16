-- Prove2me | solution 1 for TaitTobin.Outerplanar.B_empty
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T16:21:51.685128+00:00
-- url     : https://prove2.me/submissions/a4bef9b6-c2d1-40f6-a3d6-dff127c1b19e

import Mathlib
import Definitions.Def_TaitTobin_Outerplanar_Setting
import Theorems.Thm_TaitTobin_Outerplanar_outerplanar_facts
set_option autoImplicit false

open Matrix in
theorem wk9_transpose {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    Aᵀ = A := by
  rw [← conjTranspose_eq_transpose_of_trivial]; exact hA

open Matrix in
theorem wk9_parseval {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (x y : n → ℝ) :
    x ⬝ᵥ y = ∑ j, (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ x) *
      (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ y) := by
  have := hA.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at this
  rw [dotProduct_comm x y, ← this]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [dotProduct_comm y]

open Matrix in
theorem wk9_eigdot {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (j : n) (x : n → ℝ) :
    WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ (A *ᵥ x) =
      hA.eigenvalues j * (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, wk9_transpose hA, dotProduct_comm,
    hA.mulVec_eigenvectorBasis, dotProduct_smul, smul_eq_mul, dotProduct_comm]

open Matrix in
theorem wk9_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (h : 0 < Fintype.card n) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ hA.eigenvalues₀ ⟨0, h⟩ * (x ⬝ᵥ x) := by
  rw [wk9_parseval hA x (A *ᵥ x), wk9_parseval hA x x, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [wk9_eigdot]
  have hj : hA.eigenvalues j ≤ hA.eigenvalues₀ ⟨0, h⟩ := by
    unfold Matrix.IsHermitian.eigenvalues
    exact hA.eigenvalues₀_antitone (by rw [Fin.le_def]; exact Nat.zero_le _)
  nlinarith [mul_le_mul_of_nonneg_right hj
    (mul_self_nonneg (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ x))]

open Matrix in
theorem wk9_exists {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (h : 0 < Fintype.card n) :
    ∃ v : n → ℝ, v ⬝ᵥ v = 1 ∧ A *ᵥ v = hA.eigenvalues₀ ⟨0, h⟩ • v := by
  obtain ⟨j, hj⟩ : ∃ j : n, j = (Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨0, h⟩ :=
    ⟨_, rfl⟩
  refine ⟨WithLp.ofLp (hA.eigenvectorBasis j), ?_, ?_⟩
  · have horth := orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal j j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at horth
    simpa using horth
  · rw [hA.mulVec_eigenvectorBasis]
    congr 1
    rw [hj]
    simp only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]

open Matrix in
theorem wk9_quad {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = ∑ i, ∑ j, (if G.Adj i j then x i * x j else 0) := by
  simp only [dotProduct, mulVec, SimpleGraph.adjMatrix_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  split_ifs <;> ring

open Matrix in
theorem wk9_row {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) (i : V) :
    (G.adjMatrix ℝ *ᵥ x) i = ∑ j, (if G.Adj i j then x j else 0) := by
  simp only [mulVec, dotProduct, SimpleGraph.adjMatrix_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> ring

open Matrix in
theorem wk9_eq {n : Type*} [Fintype n] (A : Matrix n n ℝ) (hsym : Aᵀ = A) (lam : ℝ)
    (H : ∀ y : n → ℝ, y ⬝ᵥ (A *ᵥ y) ≤ lam * (y ⬝ᵥ y)) (x : n → ℝ)
    (hx : x ⬝ᵥ (A *ᵥ x) = lam * (x ⬝ᵥ x)) : A *ᵥ x = lam • x := by
  obtain ⟨w, hw⟩ : ∃ w, w = A *ᵥ x - lam • x := ⟨_, rfl⟩
  have hsymd : ∀ u z : n → ℝ, u ⬝ᵥ (A *ᵥ z) = z ⬝ᵥ (A *ᵥ u) := by
    intro u z
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
  have hp : w ⬝ᵥ (A *ᵥ x) - lam * (w ⬝ᵥ x) = w ⬝ᵥ w := by
    conv_rhs => rw [hw]
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    conv_lhs => rw [hw]
  have hK := H w
  have hnn : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
  have key : ∀ t : ℝ, 2 * t * (w ⬝ᵥ w) + t ^ 2 * (w ⬝ᵥ (A *ᵥ w) - lam * (w ⬝ᵥ w)) ≤ 0 := by
    intro t
    have h1 := H (x + t • w)
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul] at h1
    rw [hsymd x w, dotProduct_comm x w] at h1
    have e1 : t * (w ⬝ᵥ (A *ᵥ x)) - lam * (t * (w ⬝ᵥ x)) = t * (w ⬝ᵥ w) := by
      rw [← hp]; ring
    nlinarith [h1, hx, e1]
  have hw0 : w ⬝ᵥ w = 0 := by
    by_contra hne
    have hpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne hnn (Ne.symm hne)
    obtain ⟨K, hKd⟩ : ∃ K, K = lam * (w ⬝ᵥ w) - w ⬝ᵥ (A *ᵥ w) := ⟨_, rfl⟩
    have hK0 : 0 ≤ K := by linarith
    have h2 := key ((w ⬝ᵥ w) / (K + 1))
    have hK1 : 0 < K + 1 := by linarith
    have e : (w ⬝ᵥ w) / (K + 1) * (K + 1) = w ⬝ᵥ w := div_mul_cancel₀ _ hK1.ne'
    obtain ⟨t, ht⟩ : ∃ t, t = (w ⬝ᵥ w) / (K + 1) := ⟨_, rfl⟩
    rw [← ht] at h2 e
    have htpos : 0 < t := by rw [ht]; positivity
    have : w ⬝ᵥ (A *ᵥ w) - lam * (w ⬝ᵥ w) = -K := by linarith
    rw [this] at h2
    nlinarith [mul_pos htpos hpos, mul_pos htpos htpos]
  have : w = 0 := dotProduct_self_eq_zero.mp hw0
  rw [hw] at this
  exact sub_eq_zero.mp this

section TTSpec

open WangKangXue.SpectralTuran Matrix

-- Quadratic form bound.
open Classical in
theorem tt_Q_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hV : 0 < Fintype.card V) (x : V → ℝ) :
    (∑ i, ∑ j, (if G.Adj i j then x i * x j else 0)) ≤ specRad G * ∑ i, x i * x i := by
  have h := wk9_le (G.isHermitian_adjMatrix ℝ) hV x
  rw [wk9_quad] at h
  unfold specRad
  rw [dif_pos hV]
  simpa [dotProduct] using h

end TTSpec

section TTFanGeom

-- Sorted chord geometry on the parabola y = x^2.
theorem tt_L1 (a b c d s t : ℝ) (hab : a < b) (hcd : c < d) (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1) (hX : a + s * (b - a) = c + t * (d - c))
    (hY : a ^ 2 + s * (b ^ 2 - a ^ 2) = c ^ 2 + t * (d ^ 2 - c ^ 2)) :
    (a = c ∧ b = d) ∨ (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b) := by
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = a + s * (b - a) := ⟨_, rfl⟩
  have hXc : X = c + t * (d - c) := by rw [hXd]; exact hX
  have haX : a < X := by rw [hXd]; nlinarith
  have hXb : X < b := by rw [hXd]; nlinarith
  have hcX : c < X := by rw [hXc]; nlinarith
  have hXd' : X < d := by rw [hXc]; nlinarith
  have h1 : (X - a) * (b - X) = (a ^ 2 + s * (b ^ 2 - a ^ 2)) - X ^ 2 := by
    rw [hXd]; ring
  have h2 : (X - c) * (d - X) = (c ^ 2 + t * (d ^ 2 - c ^ 2)) - X ^ 2 := by
    rw [hXc]; ring
  have hf : (X - a) * (b - X) = (X - c) * (d - X) := by rw [h1, h2, hY]
  -- alpha = a + b - c - d
  have hell : (a + b - c - d) * X = a * b - c * d := by nlinarith [hf]
  have hA : (c - a) * (b - c) = (a + b - c - d) * (c - X) := by
    have : (c - a) * (b - c) = (a + b - c - d) * c - (a * b - c * d) := by ring
    rw [this, ← hell]; ring
  have hB : (d - a) * (b - d) = (a + b - c - d) * (d - X) := by
    have : (d - a) * (b - d) = (a + b - c - d) * d - (a * b - c * d) := by ring
    rw [this, ← hell]; ring
  by_cases hα : a + b - c - d = 0
  · rw [hα, zero_mul] at hA hB
    left
    have hc : c = a ∨ c = b := by
      rcases mul_eq_zero.1 hA with h | h
      · left; linarith
      · right; linarith
    have hd : d = a ∨ d = b := by
      rcases mul_eq_zero.1 hB with h | h
      · left; linarith
      · right; linarith
    rcases hc with hc | hc <;> rcases hd with hd | hd
    · exfalso; linarith
    · exact ⟨hc.symm, hd.symm⟩
    · exfalso; linarith
    · exfalso; linarith
  · have hneg : ((c - a) * (b - c)) * ((d - a) * (b - d)) < 0 := by
      rw [hA, hB]
      have : (a + b - c - d) * (c - X) * ((a + b - c - d) * (d - X)) =
          (a + b - c - d) ^ 2 * ((c - X) * (d - X)) := by ring
      rw [this]
      have hp : 0 < (a + b - c - d) ^ 2 := by positivity
      have hq : (c - X) * (d - X) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
      exact mul_neg_of_pos_of_neg hp hq
    rcases mul_neg_iff.1 hneg with ⟨hApos, hBneg⟩ | ⟨hAneg, hBpos⟩
    · right; left
      have h1 : a < c ∧ c < b := by
        rcases mul_pos_iff.1 hApos with ⟨x, y⟩ | ⟨x, y⟩
        · exact ⟨by linarith, by linarith⟩
        · exfalso; linarith
      refine ⟨h1.1, h1.2, ?_⟩
      by_contra hcon
      push Not at hcon
      have : 0 ≤ (d - a) * (b - d) := mul_nonneg (by linarith) (by linarith)
      linarith
    · right; right
      have h1 : a < d ∧ d < b := by
        rcases mul_pos_iff.1 hBpos with ⟨x, y⟩ | ⟨x, y⟩
        · exact ⟨by linarith, by linarith⟩
        · exfalso; linarith
      refine ⟨?_, h1.1, h1.2⟩
      by_contra hcon
      push Not at hcon
      have : 0 ≤ (c - a) * (b - c) := mul_nonneg (by linarith) (by linarith)
      linarith

end TTFanGeom

section TTFan

open RobertsonSeymour1986.GM5 TaitTobin.Outerplanar

theorem tt_L2 (p q r u s t : ℝ) (hpq : p ≠ q) (hru : r ≠ u) (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1) (hX : p + s * (q - p) = r + t * (u - r))
    (hY : p ^ 2 + s * (q ^ 2 - p ^ 2) = r ^ 2 + t * (u ^ 2 - r ^ 2)) :
    (p = r ∧ q = u) ∨ (p = u ∧ q = r) ∨
    (min p q < min r u ∧ min r u < max p q ∧ max p q < max r u) ∨
    (min r u < min p q ∧ min p q < max r u ∧ max r u < max p q) := by
  rcases lt_or_gt_of_ne hpq with h1 | h1 <;> rcases lt_or_gt_of_ne hru with h2 | h2
  · rcases tt_L1 p q r u s t h1 h2 hs0 hs1 ht0 ht1 hX hY with ⟨e1, e2⟩ | h | h
    · exact Or.inl ⟨e1, e2⟩
    · rw [min_eq_left h1.le, max_eq_right h1.le, min_eq_left h2.le, max_eq_right h2.le]
      exact Or.inr (Or.inr (Or.inl h))
    · rw [min_eq_left h1.le, max_eq_right h1.le, min_eq_left h2.le, max_eq_right h2.le]
      exact Or.inr (Or.inr (Or.inr h))
  · rcases tt_L1 p q u r s (1 - t) h1 h2 hs0 hs1 (by linarith) (by linarith)
      (by linear_combination hX) (by linear_combination hY) with ⟨e1, e2⟩ | h | h
    · exact Or.inr (Or.inl ⟨e1, e2⟩)
    · rw [min_eq_left h1.le, max_eq_right h1.le, min_eq_right h2.le, max_eq_left h2.le]
      exact Or.inr (Or.inr (Or.inl h))
    · rw [min_eq_left h1.le, max_eq_right h1.le, min_eq_right h2.le, max_eq_left h2.le]
      exact Or.inr (Or.inr (Or.inr h))
  · rcases tt_L1 q p r u (1 - s) t h1 h2 (by linarith) (by linarith) ht0 ht1
      (by linear_combination hX) (by linear_combination hY) with ⟨e1, e2⟩ | h | h
    · exact Or.inr (Or.inl ⟨e2, e1⟩)
    · rw [min_eq_right h1.le, max_eq_left h1.le, min_eq_left h2.le, max_eq_right h2.le]
      exact Or.inr (Or.inr (Or.inl h))
    · rw [min_eq_right h1.le, max_eq_left h1.le, min_eq_left h2.le, max_eq_right h2.le]
      exact Or.inr (Or.inr (Or.inr h))
  · rcases tt_L1 q p u r (1 - s) (1 - t) h1 h2 (by linarith) (by linarith) (by linarith)
      (by linarith) (by linear_combination hX) (by linear_combination hY) with ⟨e1, e2⟩ | h | h
    · exact Or.inl ⟨e2, e1⟩
    · rw [min_eq_right h1.le, max_eq_left h1.le, min_eq_right h2.le, max_eq_left h2.le]
      exact Or.inr (Or.inr (Or.inl h))
    · rw [min_eq_right h1.le, max_eq_left h1.le, min_eq_right h2.le, max_eq_left h2.le]
      exact Or.inr (Or.inr (Or.inr h))

theorem tt_inter_nat (n1 n1' n2 n2' : ℕ)
    (h1 : n1 ≠ n1' ∧ (n1 = 0 ∨ n1' = 0 ∨ n1 + 1 = n1' ∨ n1' + 1 = n1))
    (h2 : n2 ≠ n2' ∧ (n2 = 0 ∨ n2' = 0 ∨ n2 + 1 = n2' ∨ n2' + 1 = n2)) :
    ¬ (min (n1 : ℝ) n1' < min (n2 : ℝ) n2' ∧ min (n2 : ℝ) n2' < max (n1 : ℝ) n1' ∧
        max (n1 : ℝ) n1' < max (n2 : ℝ) n2') ∧
    ¬ (min (n2 : ℝ) n2' < min (n1 : ℝ) n1' ∧ min (n1 : ℝ) n1' < max (n2 : ℝ) n2' ∧
        max (n2 : ℝ) n2' < max (n1 : ℝ) n1') := by
  simp only [← Nat.cast_min, ← Nat.cast_max, Nat.cast_lt]
  omega

/-- The point of the parabola `y = x²` with abscissa `t`. -/
def ttQ (t : ℝ) : ℝ × ℝ := (t, t ^ 2)

/-- The straight segment from `p` to `q` as a path. -/
def ttSeg (p q : ℝ × ℝ) : Path p q where
  toFun t := p + (t : ℝ) • (q - p)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem ttSeg_apply (p q : ℝ × ℝ) (t : unitInterval) :
    ttSeg p q t = p + (t : ℝ) • (q - p) := rfl

/-- Abscissa of a fan vertex: the hub is at `0`, path vertex `b` at `b + 1`. -/
def ttTau {m : ℕ} : Fin 1 ⊕ Fin m → ℕ
  | Sum.inl _ => 0
  | Sum.inr b => (b : ℕ) + 1

def ttVx {m : ℕ} (v : Fin 1 ⊕ Fin m) : ℝ × ℝ := ttQ ((ttTau v : ℕ) : ℝ)

theorem tt_tau_inj {m : ℕ} : Function.Injective (ttTau (m := m)) := by
  intro v w h
  rcases v with a | b <;> rcases w with c | d
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · simp [ttTau] at h
  · simp [ttTau] at h
  · simp only [ttTau, add_left_inj] at h
    exact congrArg Sum.inr (Fin.ext h)

theorem tt_vx_inj {m : ℕ} : Function.Injective (ttVx (m := m)) := by
  intro v w h
  apply tt_tau_inj
  have := congrArg Prod.fst h
  simp only [ttVx, ttQ] at this
  exact_mod_cast this

theorem tt_fan_adj {m : ℕ} {v w : Fin 1 ⊕ Fin m}
    (h : (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)).Adj v w) :
    ttTau v ≠ ttTau w ∧ (ttTau v = 0 ∨ ttTau w = 0 ∨ ttTau v + 1 = ttTau w ∨
      ttTau w + 1 = ttTau v) := by
  rcases v with a | b <;> rcases w with c | d
  · have h' : (⊤ : SimpleGraph (Fin 1)).Adj a c := h
    exact absurd (Subsingleton.elim a c) h'.ne
  · exact ⟨by simp [ttTau], Or.inl rfl⟩
  · exact ⟨by simp [ttTau], Or.inr (Or.inl rfl)⟩
  · have h' : (SimpleGraph.pathGraph m).Adj b d := h
    rw [SimpleGraph.pathGraph_adj] at h'
    simp only [ttTau]
    omega

theorem tt_unit_cases (s : unitInterval) : s = 0 ∨ s = 1 ∨ (0 < (s : ℝ) ∧ (s : ℝ) < 1) := by
  rcases eq_or_lt_of_le s.2.1 with h | h
  · left; exact Subtype.ext h.symm
  rcases eq_or_lt_of_le s.2.2 with h' | h'
  · right; left; exact Subtype.ext h'
  · right; right; exact ⟨h, h'⟩

theorem tt_seg_fst (a b : ℝ) (t : unitInterval) :
    (ttSeg (ttQ a) (ttQ b) t).1 = a + (t : ℝ) * (b - a) := by
  rw [ttSeg_apply]; simp [ttQ]

theorem tt_seg_snd (a b : ℝ) (t : unitInterval) :
    (ttSeg (ttQ a) (ttQ b) t).2 = a ^ 2 + (t : ℝ) * (b ^ 2 - a ^ 2) := by
  rw [ttSeg_apply]; simp [ttQ]

theorem tt_inside (p q z t : ℝ) (hpq : p ≠ q) (ht0 : 0 < t) (ht1 : t < 1)
    (hx : p + t * (q - p) = z) (hy : p ^ 2 + t * (q ^ 2 - p ^ 2) = z ^ 2) : False := by
  have h1 : t * (1 - t) * (q - p) ^ 2 = 0 := by
    rw [← hx] at hy
    nlinarith [hy]
  have hne : q - p ≠ 0 := sub_ne_zero.2 hpq.symm
  have h2 : 0 < t * (1 - t) * (q - p) ^ 2 := by
    have : 0 < 1 - t := by linarith
    positivity
  linarith

theorem tt_seg_above (a b : ℝ) (t : unitInterval) :
    ((ttSeg (ttQ a) (ttQ b) t).1) ^ 2 ≤ (ttSeg (ttQ a) (ttQ b) t).2 := by
  rw [tt_seg_fst, tt_seg_snd]
  have h0 : 0 ≤ (t : ℝ) := t.2.1
  have h1 : (t : ℝ) ≤ 1 := t.2.2
  nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), sq_nonneg (b - a),
    mul_nonneg (mul_nonneg h0 (sub_nonneg.2 h1)) (sq_nonneg (b - a))]

end TTFan

section TTFanDraw

open RobertsonSeymour1986.GM5 TaitTobin.Outerplanar

theorem tt_vx_fst {m : ℕ} (z : Fin 1 ⊕ Fin m) : (ttVx z).1 = ((ttTau z : ℕ) : ℝ) := rfl
theorem tt_vx_snd {m : ℕ} (z : Fin 1 ⊕ Fin m) : (ttVx z).2 = ((ttTau z : ℕ) : ℝ) ^ 2 := rfl

theorem tt_segV_fst {m : ℕ} (v w : Fin 1 ⊕ Fin m) (t : unitInterval) :
    (ttSeg (ttVx v) (ttVx w) t).1 =
      ((ttTau v : ℕ) : ℝ) + (t : ℝ) * (((ttTau w : ℕ) : ℝ) - ((ttTau v : ℕ) : ℝ)) :=
  tt_seg_fst _ _ t

theorem tt_segV_snd {m : ℕ} (v w : Fin 1 ⊕ Fin m) (t : unitInterval) :
    (ttSeg (ttVx v) (ttVx w) t).2 =
      ((ttTau v : ℕ) : ℝ) ^ 2 + (t : ℝ) * (((ttTau w : ℕ) : ℝ) ^ 2 - ((ttTau v : ℕ) : ℝ) ^ 2) :=
  tt_seg_snd _ _ t

theorem tt_seg_inj (p q : ℝ × ℝ) (hne : p ≠ q) : Function.Injective (ttSeg p q) := by
  intro s t hst
  simp only [ttSeg_apply, add_right_inj] at hst
  exact Subtype.ext (smul_left_injective ℝ (sub_ne_zero.2 hne.symm) hst)

theorem tt_not_vertex_inside {m : ℕ} {x y : Fin 1 ⊕ Fin m}
    (k : (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)).Adj x y)
    (z : Fin 1 ⊕ Fin m) (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    ttSeg (ttVx x) (ttVx y) t ≠ ttVx z := by
  intro hz
  obtain ⟨hxy, -⟩ := tt_fan_adj k
  have hpq : ((ttTau x : ℕ) : ℝ) ≠ ((ttTau y : ℕ) : ℝ) := by exact_mod_cast hxy
  have hx := congrArg Prod.fst hz
  have hy := congrArg Prod.snd hz
  rw [tt_segV_fst, tt_vx_fst] at hx
  rw [tt_segV_snd, tt_vx_snd] at hy
  exact tt_inside _ _ _ (t : ℝ) hpq ht0 ht1 hx hy

theorem tt_avoid {m : ℕ} {v w : Fin 1 ⊕ Fin m}
    (h : (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)).Adj v w)
    (t : unitInterval) (z : Fin 1 ⊕ Fin m) (hz : ttSeg (ttVx v) (ttVx w) t = ttVx z) :
    z = v ∨ z = w := by
  rcases tt_unit_cases t with rfl | rfl | ⟨h0, h1⟩
  · left
    rw [Path.source] at hz
    exact (tt_vx_inj hz).symm
  · right
    rw [Path.target] at hz
    exact (tt_vx_inj hz).symm
  · exact absurd hz (tt_not_vertex_inside h z t h0 h1)

theorem tt_meet {m : ℕ} {v w x y : Fin 1 ⊕ Fin m}
    (h : (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)).Adj v w)
    (k : (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)).Adj x y)
    (s t : unitInterval)
    (hst : ttSeg (ttVx v) (ttVx w) s = ttSeg (ttVx x) (ttVx y) t) :
    (v = x ∧ w = y) ∨ (v = y ∧ w = x) ∨ ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) := by
  have hX := congrArg Prod.fst hst
  have hY := congrArg Prod.snd hst
  rw [tt_segV_fst, tt_segV_fst] at hX
  rw [tt_segV_snd, tt_segV_snd] at hY
  obtain ⟨hvw, hvw'⟩ := tt_fan_adj h
  obtain ⟨hxy, hxy'⟩ := tt_fan_adj k
  have hpq : ((ttTau v : ℕ) : ℝ) ≠ ((ttTau w : ℕ) : ℝ) := by exact_mod_cast hvw
  have hru : ((ttTau x : ℕ) : ℝ) ≠ ((ttTau y : ℕ) : ℝ) := by exact_mod_cast hxy
  rcases tt_unit_cases s with hs | hs | ⟨hs0, hs1⟩ <;>
    rcases tt_unit_cases t with ht | ht | ⟨ht0, ht1⟩
  · exact Or.inr (Or.inr ⟨Or.inl hs, Or.inl ht⟩)
  · exact Or.inr (Or.inr ⟨Or.inl hs, Or.inr ht⟩)
  · exfalso
    have e : ttSeg (ttVx v) (ttVx w) s = ttVx v := by rw [hs]; exact Path.source _
    exact tt_not_vertex_inside k v t ht0 ht1 (hst.symm.trans e)
  · exact Or.inr (Or.inr ⟨Or.inr hs, Or.inl ht⟩)
  · exact Or.inr (Or.inr ⟨Or.inr hs, Or.inr ht⟩)
  · exfalso
    have e : ttSeg (ttVx v) (ttVx w) s = ttVx w := by rw [hs]; exact Path.target _
    exact tt_not_vertex_inside k w t ht0 ht1 (hst.symm.trans e)
  · exfalso
    have e : ttSeg (ttVx x) (ttVx y) t = ttVx x := by rw [ht]; exact Path.source _
    exact tt_not_vertex_inside h x s hs0 hs1 (hst.trans e)
  · exfalso
    have e : ttSeg (ttVx x) (ttVx y) t = ttVx y := by rw [ht]; exact Path.target _
    exact tt_not_vertex_inside h y s hs0 hs1 (hst.trans e)
  · rcases tt_L2 _ _ _ _ (s : ℝ) (t : ℝ) hpq hru hs0 hs1 ht0 ht1 hX hY with
      ⟨e1, e2⟩ | ⟨e1, e2⟩ | h3 | h3
    · exact Or.inl ⟨tt_tau_inj (by exact_mod_cast e1), tt_tau_inj (by exact_mod_cast e2)⟩
    · exact Or.inr (Or.inl ⟨tt_tau_inj (by exact_mod_cast e1), tt_tau_inj (by exact_mod_cast e2)⟩)
    · exact absurd h3 (tt_inter_nat _ _ _ _ ⟨hvw, hvw'⟩ ⟨hxy, hxy'⟩).1
    · exact absurd h3 (tt_inter_nat _ _ _ _ ⟨hvw, hvw'⟩ ⟨hxy, hxy'⟩).2

noncomputable def ttFanDraw (m : ℕ) :
    PlaneDrawing (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)) where
  vertex := ttVx
  vertex_injective := tt_vx_inj
  arc := fun {v w} _ => ttSeg (ttVx v) (ttVx w)
  arc_injective := fun {v w} h =>
    tt_seg_inj _ _ (fun e => (SimpleGraph.ne_of_adj _ h) (tt_vx_inj e))
  arc_reverse := by
    intro v w h
    apply Path.ext
    funext t
    show ttSeg (ttVx w) (ttVx v) t = ttSeg (ttVx v) (ttVx w) (unitInterval.symm t)
    rw [ttSeg_apply, ttSeg_apply, unitInterval.coe_symm_eq]
    ext <;> simp <;> ring
  arc_avoids_vertices := fun {v w} h t z hz => tt_avoid h t z hz
  arcs_meet_only_at_endpoints := fun {v w x y} h k s t hst => tt_meet h k s t hst

theorem tt_fan_above {m : ℕ} (z : ℝ × ℝ) (hz : z ∈ drawingImage (ttFanDraw m)) :
    z.1 ^ 2 ≤ z.2 := by
  rcases hz with ⟨a, rfl⟩ | hz
  · exact le_of_eq (by simp [ttFanDraw, ttVx, ttQ])
  · simp only [Set.mem_iUnion, Set.mem_range] at hz
    obtain ⟨a, b, h, t, rfl⟩ := hz
    exact tt_seg_above _ _ t

theorem tt_fan_outer (m : ℕ) :
    IsOuterplanar (join (⊤ : SimpleGraph (Fin 1)) (SimpleGraph.pathGraph m)) := by
  refine ⟨ttFanDraw m, fun v => ?_⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t0 : ℝ := ((ttTau v : ℕ) : ℝ) with ht0
  set b : ℝ × ℝ := (t0, t0 ^ 2 - ε / 2) with hb
  let Ray : Set (ℝ × ℝ) := ({t0} : Set ℝ) ×ˢ Set.Iic (t0 ^ 2 - ε / 2)
  have hbRay : b ∈ Ray := ⟨rfl, Set.mem_Iic.2 le_rfl⟩
  have hRsub : Ray ⊆ (drawingImage (ttFanDraw m))ᶜ := by
    intro z hz hz'
    have h1 := tt_fan_above z hz'
    have h2 : z.1 = t0 := hz.1
    have h3 : z.2 ≤ t0 ^ 2 - ε / 2 := hz.2
    rw [h2] at h1
    linarith
  have hRpre : IsPreconnected Ray := (convex_singleton t0 |>.prod (convex_Iic _)).isPreconnected
  refine ⟨b, ⟨hRsub hbRay, ?_⟩, ?_⟩
  · intro hbdd
    have h1 : Bornology.IsBounded Ray :=
      hbdd.subset (hRpre.subset_connectedComponentIn hbRay hRsub)
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 h1
    have hmem : (t0, min (t0 ^ 2 - ε / 2) (-C - 1)) ∈ Ray :=
      ⟨rfl, Set.mem_Iic.2 (min_le_left _ _)⟩
    have := hC _ hmem
    have h2 : |min (t0 ^ 2 - ε / 2) (-C - 1)| ≤ ‖(t0, min (t0 ^ 2 - ε / 2) (-C - 1))‖ := by
      simpa using norm_snd_le (t0, min (t0 ^ 2 - ε / 2) (-C - 1))
    have h3 : min (t0 ^ 2 - ε / 2) (-C - 1) ≤ -C - 1 := min_le_right _ _
    have h4 := neg_abs_le (min (t0 ^ 2 - ε / 2) (-C - 1))
    linarith
  · rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · simp [hb, ttFanDraw, ttVx, ttQ, ht0, hε]
    · simp only [hb, ttFanDraw, ttVx, ttQ, Real.dist_eq, ht0]
      rw [show ((ttTau v : ℕ) : ℝ) ^ 2 - (((ttTau v : ℕ) : ℝ) ^ 2 - ε / 2) = ε / 2 by ring,
        abs_of_pos (by linarith)]
      linarith

end TTFanDraw

section TTIso

open WangKangXue.SpectralTuran

open Matrix in
theorem wkx_quad_iso {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    {G : SimpleGraph V} {G' : SimpleGraph V'} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (e : G ≃g G') (v : V → ℝ) :
    (v ∘ e.symm) ⬝ᵥ (G'.adjMatrix ℝ *ᵥ (v ∘ e.symm)) = v ⬝ᵥ (G.adjMatrix ℝ *ᵥ v) := by
  rw [wk9_quad, wk9_quad]
  symm
  refine Fintype.sum_equiv e.toEquiv _ _ (fun i => ?_)
  refine Fintype.sum_equiv e.toEquiv _ _ (fun j => ?_)
  have h : G'.Adj (e i) (e j) ↔ G.Adj i j := e.map_adj_iff
  by_cases hij : G.Adj i j
  · simp [Function.comp, hij, h.2 hij]
  · simp [hij, mt h.1 hij]

open Matrix in
theorem wkx_dot_iso {V V' : Type*} [Fintype V] [Fintype V'] (e : V ≃ V') (v : V → ℝ) :
    (v ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = v ⬝ᵥ v := by
  simp only [dotProduct]
  symm
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

open Matrix in
theorem wkx_specRad_le_of_iso {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V']
    [DecidableEq V'] {G : SimpleGraph V} {G' : SimpleGraph V'} (e : G ≃g G') :
    specRad G ≤ specRad G' := by
  classical
  unfold specRad
  by_cases h : 0 < Fintype.card V
  · have h' : 0 < Fintype.card V' := by rw [← e.card_eq]; exact h
    rw [dif_pos h, dif_pos h']
    obtain ⟨v, hvv, hv⟩ := wk9_exists (G.isHermitian_adjMatrix ℝ) h
    have hle := wk9_le (G'.isHermitian_adjMatrix ℝ) h' (v ∘ e.symm)
    have h2 : (v ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = 1 := by
      rw [show (v ∘ e.symm) = v ∘ e.toEquiv.symm from rfl, wkx_dot_iso, hvv]
    rw [wkx_quad_iso e v, h2, hv, dotProduct_smul, smul_eq_mul, hvv] at hle
    simpa using hle
  · have h' : ¬ 0 < Fintype.card V' := by rw [← e.card_eq]; exact h
    rw [dif_neg h, dif_neg h']

theorem wkx_specRad_eq_of_iso {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V']
    [DecidableEq V'] {G : SimpleGraph V} {G' : SimpleGraph V'} (e : G ≃g G') :
    specRad G = specRad G' :=
  le_antisymm (wkx_specRad_le_of_iso e) (wkx_specRad_le_of_iso e.symm)

end TTIso

section ofhelpers

open RobertsonSeymour1986.GM5 TaitTobin.Outerplanar

/-- the drawing of `G.comap g` obtained from a drawing of `G` (injective `g`) -/
def ofComapDraw {V W : Type} {G : SimpleGraph W} (g : V → W) (hg : Function.Injective g)
    (D : PlaneDrawing G) : PlaneDrawing (G.comap g) where
  vertex v := D.vertex (g v)
  vertex_injective := D.vertex_injective.comp hg
  arc h := D.arc h
  arc_injective h := D.arc_injective h
  arc_reverse h := D.arc_reverse h
  arc_avoids_vertices := by
    intro v w h t x hx
    rcases D.arc_avoids_vertices h t (g x) hx with h1 | h1
    · exact Or.inl (hg h1)
    · exact Or.inr (hg h1)
  arcs_meet_only_at_endpoints := by
    intro v w x y h k s t hst
    rcases D.arcs_meet_only_at_endpoints h k s t hst with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
    · exact Or.inl ⟨hg h1, hg h2⟩
    · exact Or.inr (Or.inl ⟨hg h1, hg h2⟩)
    · exact Or.inr (Or.inr h1)

theorem of_comap_img {V W : Type} {G : SimpleGraph W} (g : V → W) (hg : Function.Injective g)
    (D : PlaneDrawing G) : drawingImage (ofComapDraw g hg D) ⊆ drawingImage D := by
  intro z hz
  rcases hz with ⟨v, rfl⟩ | hz
  · exact Or.inl ⟨g v, rfl⟩
  · simp only [Set.mem_iUnion, Set.mem_range] at hz
    obtain ⟨a, b, h, t, rfl⟩ := hz
    refine Or.inr ?_
    simp only [Set.mem_iUnion, Set.mem_range]
    exact ⟨g a, g b, h, t, rfl⟩

/-- outerplanarity pulls back along an injective map of vertices -/
theorem of_comap {V W : Type} (G : SimpleGraph W) (g : V → W)
    (hg : Function.Injective g) (hG : IsOuterplanar G) : IsOuterplanar (G.comap g) := by
  obtain ⟨D, hD⟩ := hG
  refine ⟨ofComapDraw g hg D, fun v => ?_⟩
  have hsub := of_comap_img g hg D
  have hface : outerFace D ⊆ outerFace (ofComapDraw g hg D) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    refine ⟨fun h => hp1 (hsub h), fun hb => hp2 ?_⟩
    exact hb.subset (connectedComponentIn_mono p (Set.compl_subset_compl.2 hsub))
  exact closure_mono hface (hD (g v))

theorem of_inj5 {n : ℕ} (p q a b c : Fin n) (hpq : p ≠ q) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (hcp : c ≠ p) (hcq : c ≠ q) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    Function.Injective (Sum.elim ![p, q] ![a, b, c] : Fin 2 ⊕ Fin 3 → Fin n) := by
  intro s t h
  rcases s with i | j <;> rcases t with k | l <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
  · fin_cases i <;> fin_cases k <;> simp_all [eq_comm]
  · fin_cases i <;> fin_cases l <;> simp_all [eq_comm]
  · fin_cases j <;> fin_cases k <;> simp_all [eq_comm]
  · fin_cases j <;> fin_cases l <;> simp_all [eq_comm]

open Classical in
/-- two distinct vertices of an outerplanar graph have at most two common neighbours -/
theorem of_common_le {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G)
    (p q : Fin n) (hpq : p ≠ q) :
    (Finset.univ.filter (fun y : Fin n => G.Adj p y ∧ G.Adj q y)).card ≤ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 hcon
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  have hn : 2 ≤ n := by
    have h1 := p.isLt
    have h2 := q.isLt
    have h3 : p.val ≠ q.val := fun h => hpq (Fin.ext h)
    omega
  have hf := of_inj5 p q a b c hpq (G.ne_of_adj ha.1).symm (G.ne_of_adj ha.2).symm
    (G.ne_of_adj hb.1).symm (G.ne_of_adj hb.2).symm (G.ne_of_adj hc.1).symm
    (G.ne_of_adj hc.2).symm hab hac hbc
  have hadj : ∀ i : Fin 2, ∀ j : Fin 3, G.Adj (![p, q] i) (![a, b, c] j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact ha.1
    · exact hb.1
    · exact hc.1
    · exact ha.2
    · exact hb.2
    · exact hc.2
  apply (TaitTobin.Outerplanar.outerplanar_facts hn G hG).2
  refine ⟨⟨⟨Sum.elim ![p, q] ![a, b, c], ?_⟩, hf⟩⟩
  intro s t h
  rcases s with i | j <;> rcases t with k | l
  · simp at h
  · exact hadj i l
  · exact (hadj k j).symm
  · simp at h

end ofhelpers

section BQFan

open Classical WangKangXue.SpectralTuran TaitTobin.Outerplanar

theorem bq_ll {n : ℕ} (i j : Fin 1) : (fan n).Adj (Sum.inl i) (Sum.inl j) ↔ False := by
  constructor
  · intro h
    have h' : (⊤ : SimpleGraph (Fin 1)).Adj i j := h
    exact (SimpleGraph.top_adj i j).1 h' (Subsingleton.elim i j)
  · intro h; exact h.elim

theorem bq_lr {n : ℕ} (i : Fin 1) (j : Fin (n - 1)) :
    (fan n).Adj (Sum.inl i) (Sum.inr j) ↔ True := Iff.rfl

theorem bq_rl {n : ℕ} (i : Fin 1) (j : Fin (n - 1)) :
    (fan n).Adj (Sum.inr j) (Sum.inl i) ↔ True := Iff.rfl

theorem bq_rr {n : ℕ} (i j : Fin (n - 1)) :
    (fan n).Adj (Sum.inr i) (Sum.inr j) ↔ (SimpleGraph.pathGraph (n - 1)).Adj i j := Iff.rfl

theorem bq_path_row (m : ℕ) (b : Fin m) :
    (if b.val + 1 < m then (1:ℝ) else 0) + (if 0 < b.val then (1:ℝ) else 0) ≤
      ∑ c : Fin m, (if (SimpleGraph.pathGraph m).Adj b c then (1:ℝ) else 0) := by
  have h0 : ∀ c : Fin m, 0 ≤ (if (SimpleGraph.pathGraph m).Adj b c then (1:ℝ) else 0) := by
    intro c; split_ifs <;> norm_num
  by_cases h1 : b.val + 1 < m <;> by_cases h2 : 0 < b.val
  · have hc1 : (SimpleGraph.pathGraph m).Adj b ⟨b.val + 1, h1⟩ := by
      rw [SimpleGraph.pathGraph_adj]; left; rfl
    have hc2 : (SimpleGraph.pathGraph m).Adj b ⟨b.val - 1, by omega⟩ := by
      rw [SimpleGraph.pathGraph_adj]; right; show b.val - 1 + 1 = b.val; omega
    have hne : (⟨b.val + 1, h1⟩ : Fin m) ≠ ⟨b.val - 1, by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    have := Finset.add_le_sum (f := fun c => if (SimpleGraph.pathGraph m).Adj b c then (1:ℝ) else 0)
      (fun c _ => h0 c) (Finset.mem_univ _) (Finset.mem_univ _) hne
    simp only [if_pos hc1, if_pos hc2] at this
    rw [if_pos h1, if_pos h2]
    exact this
  · have hc1 : (SimpleGraph.pathGraph m).Adj b ⟨b.val + 1, h1⟩ := by
      rw [SimpleGraph.pathGraph_adj]; left; rfl
    have := Finset.single_le_sum (f := fun c => if (SimpleGraph.pathGraph m).Adj b c then (1:ℝ) else 0)
      (fun c _ => h0 c) (Finset.mem_univ (⟨b.val + 1, h1⟩ : Fin m))
    simp only [if_pos hc1] at this
    rw [if_pos h1, if_neg h2, add_zero]
    exact this
  · have hc2 : (SimpleGraph.pathGraph m).Adj b ⟨b.val - 1, by omega⟩ := by
      rw [SimpleGraph.pathGraph_adj]; right; show b.val - 1 + 1 = b.val; omega
    have := Finset.single_le_sum (f := fun c => if (SimpleGraph.pathGraph m).Adj b c then (1:ℝ) else 0)
      (fun c _ => h0 c) (Finset.mem_univ (⟨b.val - 1, by omega⟩ : Fin m))
    simp only [if_pos hc2] at this
    rw [if_neg h1, if_pos h2, zero_add]
    exact this
  · rw [if_neg h1, if_neg h2, add_zero]
    exact Finset.sum_nonneg (fun c _ => h0 c)

theorem bq_count_succ (m : ℕ) (hm : 1 ≤ m) :
    ∑ b : Fin m, (if b.val + 1 < m then (1:ℝ) else 0) = (m:ℝ) - 1 := by
  rw [Finset.sum_boole]
  have e : (Finset.univ.filter (fun b : Fin m => b.val + 1 < m)) =
      Finset.univ.erase (⟨m - 1, by omega⟩ : Fin m) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, and_true]
    have := b.isLt
    constructor
    · intro h h'
      have := congrArg Fin.val h'
      simp only at this
      omega
    · intro h
      by_contra h''
      apply h
      ext
      simp only
      omega
  rw [e, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
    Nat.cast_sub hm]
  simp

theorem bq_count_pos (m : ℕ) (hm : 1 ≤ m) :
    ∑ b : Fin m, (if 0 < b.val then (1:ℝ) else 0) = (m:ℝ) - 1 := by
  rw [Finset.sum_boole]
  have e : (Finset.univ.filter (fun b : Fin m => 0 < b.val)) =
      Finset.univ.erase (⟨0, by omega⟩ : Fin m) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, and_true]
    constructor
    · intro h h'
      have := congrArg Fin.val h'
      simp only at this
      omega
    · intro h
      by_contra h''
      apply h
      ext
      simp only
      omega
  rw [e, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
    Nat.cast_sub hm]
  simp

theorem bq_path_sum (m : ℕ) (hm : 1 ≤ m) :
    2 * ((m:ℝ) - 1) ≤
      ∑ b : Fin m, ∑ c : Fin m, (if (SimpleGraph.pathGraph m).Adj b c then (1:ℝ) else 0) := by
  have h := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin m))) => bq_path_row m b)
  rw [Finset.sum_add_distrib, bq_count_succ m hm, bq_count_pos m hm] at h
  linarith

theorem bq_fan_quad (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    2 * ((n:ℝ) - 1) * a + 2 * ((n:ℝ) - 2) ≤
      ∑ i, ∑ j, (if (fan n).Adj i j then
        (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin (n - 1) => (1:ℝ)) i) *
          (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin (n - 1) => (1:ℝ)) j) else 0) := by
  have hm : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hl : ∀ i : Fin 1, ∑ j, (if (fan n).Adj (Sum.inl i) j then
      (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin (n - 1) => (1:ℝ)) (Sum.inl i)) *
        (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin (n - 1) => (1:ℝ)) j) else 0) =
      ((n:ℝ) - 1) * a := by
    intro i
    rw [Fintype.sum_sum_type]
    simp only [bq_ll, bq_lr, if_false, if_true, Sum.elim_inl, Sum.elim_inr, mul_one,
      Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [hm]
  have hr : ∀ b : Fin (n - 1), ∑ j, (if (fan n).Adj (Sum.inr b) j then
      (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin (n - 1) => (1:ℝ)) (Sum.inr b)) *
        (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin (n - 1) => (1:ℝ)) j) else 0) =
      a + ∑ c : Fin (n - 1), (if (SimpleGraph.pathGraph (n - 1)).Adj b c then (1:ℝ) else 0) := by
    intro b
    rw [Fintype.sum_sum_type]
    simp only [bq_rl, bq_rr, if_true, Sum.elim_inl, Sum.elim_inr, one_mul, mul_one,
      Fin.sum_univ_one]
  rw [Fintype.sum_sum_type]
  rw [Finset.sum_congr rfl (fun i _ => hl i), Finset.sum_congr rfl (fun b _ => hr b)]
  rw [Finset.sum_add_distrib]
  have hp := bq_path_sum (n - 1) (by omega)
  rw [hm] at hp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_one,
    one_mul]
  rw [hm]
  linarith

theorem bq_fan_lower (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    2 * ((n:ℝ) - 1) * a + 2 * ((n:ℝ) - 2) ≤ specRad (fan n) * (a ^ 2 + ((n:ℝ) - 1)) := by
  have hV : 0 < Fintype.card (Fin 1 ⊕ Fin (n - 1)) := by simp
  have hQ := tt_Q_le (fan n) hV (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin (n - 1) => (1:ℝ)))
  have hm : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hyy : ∑ i, (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin (n - 1) => (1:ℝ)) i) *
      (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin (n - 1) => (1:ℝ)) i) = a ^ 2 + ((n:ℝ) - 1) := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hm]
    ring
  rw [hyy] at hQ
  exact le_trans (bq_fan_quad n hn a) hQ

theorem bq_fan_le_max {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n))
    (hG : IsSpecMax IsOuterplanar G) : specRad (fan n) ≤ specRad G := by
  have hc : Fintype.card (Fin n) = Fintype.card (Fin 1 ⊕ Fin (n - 1)) := by simp; omega
  obtain ⟨e, -⟩ : ∃ e : Fin n ≃ (Fin 1 ⊕ Fin (n - 1)), True :=
    ⟨Fintype.equivOfCardEq hc, trivial⟩
  have hB : IsOuterplanar ((fan n).comap e) :=
    of_comap (fan n) e e.injective (tt_fan_outer (n - 1))
  have iso : (fan n).comap e ≃g fan n := { toEquiv := e, map_rel_iff' := Iff.rfl }
  rw [← wkx_specRad_eq_of_iso iso]
  exact hG.2 _ hB

end BQFan


section BQGraph

open Classical WangKangXue.SpectralTuran TaitTobin.Outerplanar

theorem bq_row {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (l : ℝ)
    (h : (G.adjMatrix ℝ).mulVec v = l • v) (i : Fin n) :
    ∑ j, (if G.Adj i j then v j else 0) = l * v i := by
  have := congrFun h i
  simpa [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, ite_mul] using this

theorem bq_eig {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (l : ℝ)
    (h : (G.adjMatrix ℝ).mulVec v = l • v) (Z : Finset (Fin n)) :
    l * ∑ z ∈ Z, v z = ∑ u, (∑ z ∈ Z, if G.Adj u z then (1:ℝ) else 0) * v u := by
  have hrow : ∀ i, ∑ j, (if G.Adj i j then v j else 0) = l * v i := bq_row G v l h
  rw [Finset.mul_sum]
  calc ∑ z ∈ Z, l * v z = ∑ z ∈ Z, ∑ j, (if G.Adj z j then v j else 0) :=
        Finset.sum_congr rfl (fun z _ => (hrow z).symm)
    _ = ∑ j, ∑ z ∈ Z, (if G.Adj z j then v j else 0) := Finset.sum_comm
    _ = ∑ u, (∑ z ∈ Z, if G.Adj u z then (1:ℝ) else 0) * v u := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        by_cases hz : G.Adj z j
        · have hz' : G.Adj j z := hz.symm
          simp [hz, hz']
        · have hz' : ¬ G.Adj j z := fun h' => hz h'.symm
          simp [hz, hz']

/-- the common neighbours of two distinct vertices, as a filter of a neighbourhood -/
theorem bq_common {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G) (u w : Fin n)
    (huw : u ≠ w) : ((Finset.univ.filter (G.Adj u)).filter (G.Adj w)).card ≤ 2 := by
  refine le_trans (Finset.card_le_card ?_) (of_common_le G hG u w huw)
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  exact hz

theorem bq_cnt_le {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G) (u w : Fin n)
    (huw : u ≠ w) :
    (∑ z ∈ Finset.univ.filter (G.Adj u), if G.Adj w z then (1:ℝ) else 0) ≤ 2 := by
  rw [Finset.sum_boole]
  have := bq_common G hG u w huw
  exact_mod_cast this

/-- `λ² v_u ≤ d_u v_u + 2 (Σ v - v_u)` (two vertices have at most two common neighbours) -/
theorem bq_sq {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G) (v : Fin n → ℝ)
    (l : ℝ) (h : (G.adjMatrix ℝ).mulVec v = l • v) (hv0 : ∀ i, 0 ≤ v i) (u : Fin n) :
    l * (l * v u) ≤ ((Finset.univ.filter (G.Adj u)).card : ℝ) * v u +
      2 * (∑ w, v w - v u) := by
  have hr := bq_row G v l h u
  have hZs : ∑ z ∈ Finset.univ.filter (G.Adj u), v z = l * v u := by
    rw [Finset.sum_filter]; exact hr
  have he := bq_eig G v l h (Finset.univ.filter (G.Adj u))
  rw [hZs] at he
  rw [he]
  have hpt : ∀ w, (∑ z ∈ Finset.univ.filter (G.Adj u), if G.Adj w z then (1:ℝ) else 0) * v w ≤
      (if w = u then (((Finset.univ.filter (G.Adj u)).card : ℝ) - 2) * v u else 0) +
        2 * v w := by
    intro w
    by_cases hw : w = u
    · subst hw
      have e : (∑ z ∈ Finset.univ.filter (G.Adj w), if G.Adj w z then (1:ℝ) else 0) =
          ((Finset.univ.filter (G.Adj w)).card : ℝ) := by
        rw [Finset.sum_boole, Finset.filter_filter]
        congr 2
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_self]
      rw [e, if_pos rfl]
      linarith
    · rw [if_neg hw, zero_add]
      exact mul_le_mul_of_nonneg_right (bq_cnt_le G hG u w (Ne.symm hw)) (hv0 w)
  have hsum := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin n))) => hpt w)
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  rw [← Finset.mul_sum] at hsum
  linarith

theorem bq_S {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G)
    (v : Fin n → ℝ) (l : ℝ) (h : (G.adjMatrix ℝ).mulVec v = l • v)
    (hv1 : ∀ i, v i ≤ 1) : l * ∑ w, v w ≤ 4 * (n : ℝ) := by
  have he := bq_eig G v l h Finset.univ
  rw [he]
  have hD0 : ∀ u, 0 ≤ (∑ z ∈ (Finset.univ : Finset (Fin n)), if G.Adj u z then (1:ℝ) else 0) :=
    fun u => Finset.sum_nonneg (fun z _ => by split_ifs <;> norm_num)
  have h1 : ∑ u, (∑ z ∈ (Finset.univ : Finset (Fin n)), if G.Adj u z then (1:ℝ) else 0) * v u ≤
      ∑ u, (∑ z ∈ (Finset.univ : Finset (Fin n)), if G.Adj u z then (1:ℝ) else 0) :=
    Finset.sum_le_sum (fun u _ => by
      have := mul_le_mul_of_nonneg_left (hv1 u) (hD0 u)
      linarith)
  have hdeg : ∀ u, (∑ z ∈ (Finset.univ : Finset (Fin n)), if G.Adj u z then (1:ℝ) else 0) =
      (G.degree u : ℝ) := by
    intro u
    rw [Finset.sum_boole, ← SimpleGraph.card_neighborFinset_eq_degree]
    congr 2
    ext z
    simp
  have h2 : ∑ u, (∑ z ∈ (Finset.univ : Finset (Fin n)), if G.Adj u z then (1:ℝ) else 0) =
      ((∑ u, G.degree u : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun u _ => hdeg u)
  have hh := G.sum_degrees_eq_twice_card_edges
  have hE := (TaitTobin.Outerplanar.outerplanar_facts hn G hG).1
  have hE' : G.edgeFinset.card ≤ 2 * n - 3 := by convert hE
  have h3 : (∑ u, G.degree u : ℕ) ≤ 4 * n := by omega
  have h4 : ((∑ u, G.degree u : ℕ) : ℝ) ≤ 4 * (n : ℝ) := by exact_mod_cast h3
  linarith

/-- local edge count: `Σ_{y ∈ T} |N(y) ∩ T| ≤ 4 |T|` -/
theorem bq_local_nat {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G)
    (T : Finset (Fin n)) : ∑ y ∈ T, (T.filter (fun z => G.Adj y z)).card ≤ 4 * T.card := by
  by_cases hT : 2 ≤ T.card
  · let g : Fin T.card → Fin n := fun i => T.orderEmbOfFin rfl i
    have hg : Function.Injective g := (T.orderEmbOfFin rfl).injective
    have hrange : ∀ y, y ∈ T ↔ ∃ i, g i = y := by
      intro y
      have := Finset.range_orderEmbOfFin T (rfl : T.card = T.card)
      constructor
      · intro hy
        have : y ∈ Set.range (T.orderEmbOfFin rfl) := by rw [this]; exact hy
        exact this
      · rintro ⟨i, rfl⟩
        exact Finset.orderEmbOfFin_mem T rfl i
    have houter := of_comap G g hg hG
    obtain ⟨hE, -⟩ := TaitTobin.Outerplanar.outerplanar_facts hT (G.comap g) houter
    have himg : T = Finset.univ.image g := by
      ext y; simp only [Finset.mem_image, Finset.mem_univ, true_and]; exact hrange y
    set d : Fin n → ℕ := fun y => (T.filter (fun z => G.Adj y z)).card with hd
    have hdeg : ∀ i, (G.comap g).degree i = d (g i) := by
      intro i
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
      simp only [hd]
      refine Finset.card_bij (fun j _ => g j) ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.comap_adj] at hj
        exact Finset.mem_filter.2 ⟨(hrange _).2 ⟨j, rfl⟩, hj⟩
      · intro j _ k _ h; exact hg h
      · intro y hy
        obtain ⟨hyT, hy2⟩ := Finset.mem_filter.1 hy
        obtain ⟨j, rfl⟩ := (hrange y).1 hyT
        exact ⟨j, by simpa using hy2, rfl⟩
    have hsum : ∑ i, (G.comap g).degree i = ∑ y ∈ T, d y := by
      calc ∑ i, (G.comap g).degree i = ∑ i, d (g i) := Finset.sum_congr rfl (fun i _ => hdeg i)
        _ = ∑ y ∈ Finset.univ.image g, d y := (Finset.sum_image (fun a _ b _ h => hg h)).symm
        _ = ∑ y ∈ T, d y := congrArg (fun s => ∑ y ∈ s, d y) himg.symm
    have hhand := SimpleGraph.sum_degrees_eq_twice_card_edges (G.comap g)
    have hE' : (G.comap g).edgeFinset.card ≤ 2 * T.card - 3 := by convert hE
    show ∑ y ∈ T, d y ≤ 4 * T.card
    omega
  · have h0 : ∀ y ∈ T, (T.filter (fun z => G.Adj y z)).card = 0 := by
      intro y hy
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z hz hyz
      have := Finset.card_le_one.1 (by omega) y hy z hz
      exact G.ne_of_adj hyz this
    rw [Finset.sum_eq_zero h0]
    omega

theorem bq_local {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G)
    (T : Finset (Fin n)) :
    ∑ y ∈ T, (∑ z ∈ T, if G.Adj y z then (1:ℝ) else 0) ≤ 4 * (T.card : ℝ) := by
  have h := bq_local_nat G hG T
  have e : ∀ y, (∑ z ∈ T, if G.Adj y z then (1:ℝ) else 0) =
      ((T.filter (fun z => G.Adj y z)).card : ℝ) := fun y => by rw [Finset.sum_boole]
  rw [Finset.sum_congr rfl (fun y _ => e y)]
  have h' : ((∑ y ∈ T, (T.filter (fun z => G.Adj y z)).card : ℕ) : ℝ) ≤ ((4 * T.card : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  exact h'

/-- `Σ_u f u = f x + Σ_{N(x)} f + Σ_B f` with `B` the non-neighbours of `x` other than `x` -/
theorem bq_part {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n) (f : Fin n → ℝ) :
    ∑ u, f u = f x + ∑ u ∈ Finset.univ.filter (G.Adj x), f u +
      ∑ u ∈ Finset.univ.filter (fun z => z ≠ x ∧ ¬ G.Adj x z), f u := by
  rw [Finset.sum_filter, Finset.sum_filter]
  have hpt : ∀ u, f u = (if u = x then f u else 0) + (if G.Adj x u then f u else 0) +
      (if u ≠ x ∧ ¬ G.Adj x u then f u else 0) := by
    intro u
    by_cases h1 : u = x
    · subst h1
      simp
    · by_cases h2 : G.Adj x u
      · simp [h1, h2]
      · simp [h1, h2]
  calc ∑ u, f u = ∑ u, ((if u = x then f u else 0) + (if G.Adj x u then f u else 0) +
        (if u ≠ x ∧ ¬ G.Adj x u then f u else 0)) := Finset.sum_congr rfl (fun u _ => hpt u)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]

theorem bq_deg_pair {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G) (u x : Fin n)
    (hu : u ≠ x) :
    ((Finset.univ.filter (G.Adj u)).card : ℝ) + ((Finset.univ.filter (G.Adj x)).card : ℝ) ≤
      (n : ℝ) + 2 := by
  have h1 := Finset.card_union_add_card_inter (Finset.univ.filter (G.Adj u))
    (Finset.univ.filter (G.Adj x))
  have h2 : ((Finset.univ.filter (G.Adj u)) ∪ (Finset.univ.filter (G.Adj x))).card ≤ n := by
    calc _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  have h3 : ((Finset.univ.filter (G.Adj u)) ∩ (Finset.univ.filter (G.Adj x))).card ≤ 2 := by
    refine le_trans (Finset.card_le_card ?_) (of_common_le G hG u x hu)
    intro z hz
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hz
  have h4 : (Finset.univ.filter (G.Adj u)).card + (Finset.univ.filter (G.Adj x)).card ≤ n + 2 := by
    omega
  exact_mod_cast h4

/-- every vertex other than `x` has `λ² v_u ≤ (n + 2 - d_x) + 2 Σ v` -/
theorem bq_vertex {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G) (v : Fin n → ℝ)
    (l : ℝ) (h : (G.adjMatrix ℝ).mulVec v = l • v) (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1)
    (x u : Fin n) (hu : u ≠ x) :
    l * (l * v u) ≤ ((n : ℝ) + 2 - ((Finset.univ.filter (G.Adj x)).card : ℝ)) +
      2 * ∑ w, v w := by
  have h1 := bq_sq G hG v l h hv0 u
  have h2 := bq_deg_pair G hG u x hu
  have h3 : ((Finset.univ.filter (G.Adj u)).card : ℝ) * v u ≤
      ((Finset.univ.filter (G.Adj u)).card : ℝ) :=
    mul_le_of_le_one_right (Nat.cast_nonneg _) (hv1 u)
  have h4 := hv0 u
  linarith

/-- the weighted degree of `B` is at most `6 |B|` -/
theorem bq_DB_sum {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G) (x : Fin n) :
    ∑ u, (∑ z ∈ Finset.univ.filter (fun z => z ≠ x ∧ ¬ G.Adj x z),
        if G.Adj u z then (1:ℝ) else 0) ≤
      6 * ((Finset.univ.filter (fun z => z ≠ x ∧ ¬ G.Adj x z)).card : ℝ) := by
  set B := Finset.univ.filter (fun z => z ≠ x ∧ ¬ G.Adj x z) with hB
  set N := Finset.univ.filter (G.Adj x) with hN
  have hp : ∑ u, (∑ z ∈ B, if G.Adj u z then (1:ℝ) else 0) =
      (∑ z ∈ B, if G.Adj x z then (1:ℝ) else 0) +
        ∑ u ∈ N, (∑ z ∈ B, if G.Adj u z then (1:ℝ) else 0) +
          ∑ u ∈ B, (∑ z ∈ B, if G.Adj u z then (1:ℝ) else 0) :=
    bq_part G x (fun u => ∑ z ∈ B, if G.Adj u z then (1:ℝ) else 0)
  have hx0 : (∑ z ∈ B, if G.Adj x z then (1:ℝ) else 0) = 0 := by
    refine Finset.sum_eq_zero (fun z hz => ?_)
    have : z ≠ x ∧ ¬ G.Adj x z := by simpa [hB] using hz
    rw [if_neg this.2]
  have hBB := bq_local G hG B
  have hNB : ∑ u ∈ N, (∑ z ∈ B, if G.Adj u z then (1:ℝ) else 0) ≤ 2 * (B.card : ℝ) := by
    rw [Finset.sum_comm]
    have hz : ∀ z ∈ B, (∑ u ∈ N, if G.Adj u z then (1:ℝ) else 0) ≤ 2 := by
      intro z hz
      have hzx : z ≠ x := by
        have : z ≠ x ∧ ¬ G.Adj x z := by simpa [hB] using hz
        exact this.1
      have e : (∑ u ∈ N, if G.Adj u z then (1:ℝ) else 0) =
          (∑ u ∈ N, if G.Adj z u then (1:ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun u _ => ?_)
        by_cases h1 : G.Adj u z
        · rw [if_pos h1, if_pos h1.symm]
        · rw [if_neg h1, if_neg (fun h => h1 h.symm)]
      rw [e]
      exact bq_cnt_le G hG x z (Ne.symm hzx)
    calc ∑ z ∈ B, (∑ u ∈ N, if G.Adj u z then (1:ℝ) else 0) ≤ ∑ z ∈ B, (2:ℝ) :=
          Finset.sum_le_sum hz
      _ = 2 * (B.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hp, hx0]
  linarith

/-- `λ³ β ≤ 6 |B| K` when every vertex other than `x` has `λ² v_u ≤ K` -/
theorem bq_beta {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G) (v : Fin n → ℝ)
    (l : ℝ) (h : (G.adjMatrix ℝ).mulVec v = l • v) (x : Fin n) (K : ℝ) (hK0 : 0 ≤ K)
    (hvert : ∀ u, u ≠ x → l * (l * v u) ≤ K) :
    l * l * (l * ∑ z ∈ Finset.univ.filter (fun z => z ≠ x ∧ ¬ G.Adj x z), v z) ≤
      6 * ((Finset.univ.filter (fun z => z ≠ x ∧ ¬ G.Adj x z)).card : ℝ) * K := by
  set B := Finset.univ.filter (fun z => z ≠ x ∧ ¬ G.Adj x z) with hB
  have he := bq_eig G v l h B
  rw [he, Finset.mul_sum]
  have hD0 : ∀ u, 0 ≤ (∑ z ∈ B, if G.Adj u z then (1:ℝ) else 0) :=
    fun u => Finset.sum_nonneg (fun z _ => by split_ifs <;> norm_num)
  have hpt : ∀ u, l * l * ((∑ z ∈ B, if G.Adj u z then (1:ℝ) else 0) * v u) ≤
      (∑ z ∈ B, if G.Adj u z then (1:ℝ) else 0) * K := by
    intro u
    by_cases hu : u = x
    · rw [hu]
      have hx0 : (∑ z ∈ B, if G.Adj x z then (1:ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero (fun z hz => ?_)
        have : z ≠ x ∧ ¬ G.Adj x z := by simpa [hB] using hz
        rw [if_neg this.2]
      rw [hx0]; simp
    · have := mul_le_mul_of_nonneg_left (hvert u hu) (hD0 u)
      calc l * l * ((∑ z ∈ B, if G.Adj u z then (1:ℝ) else 0) * v u) =
            (∑ z ∈ B, if G.Adj u z then (1:ℝ) else 0) * (l * (l * v u)) := by ring
        _ ≤ _ := this
  calc ∑ u, l * l * ((∑ z ∈ B, if G.Adj u z then (1:ℝ) else 0) * v u) ≤
        ∑ u, (∑ z ∈ B, if G.Adj u z then (1:ℝ) else 0) * K := Finset.sum_le_sum (fun u _ => hpt u)
    _ = (∑ u, (∑ z ∈ B, if G.Adj u z then (1:ℝ) else 0)) * K := by rw [Finset.sum_mul]
    _ ≤ (6 * (B.card : ℝ)) * K := mul_le_mul_of_nonneg_right (bq_DB_sum G hG x) hK0

end BQGraph


section BQMain

open Classical WangKangXue.SpectralTuran TaitTobin.Outerplanar

/-- the final inequality chain (all quantities real; `n = t²`, `P = t (t - 1)`) -/
theorem bq_arith (t P L S d b β K : ℝ) (ht : 2000 ≤ t) (hPeq : P = t ^ 2 - t)
    (hfan : t ^ 3 - t - 1 ≤ L * P) (hS0 : 0 ≤ S) (hSL : L * S ≤ 4 * t ^ 2)
    (hx2 : L * L ≤ d + 2 * (S - 1)) (hcnt : t ^ 2 = 1 + d + b) (hSs : S = 1 + L + β)
    (hb1 : 1 ≤ b) (hβ0 : 0 ≤ β) (hK : K = (t ^ 2 + 2 - d) + 2 * S)
    (hβK : L * L * (L * β) ≤ 6 * b * K) : False := by
  have ht0 : 0 < t := by linarith
  have h5 : 1000 * t ≤ P := by rw [hPeq]; nlinarith
  have hP : 0 < P := by linarith
  have htP : t * P = t ^ 3 - t ^ 2 := by rw [hPeq]; ring
  -- L ≥ t
  have hq : 0 < t ^ 2 - t - 1 := by nlinarith
  have hLt : t ≤ L := by
    by_contra hc
    push Not at hc
    have h1 : L * P < t * P := mul_lt_mul_of_pos_right hc hP
    linarith
  -- (L - 1)² ≥ t² - 1/500
  have h1 : t * P - 1 ≤ (L - 1) * P := by
    have e : (L - 1) * P = L * P - P := by ring
    rw [e]
    linarith
  have h2 : 0 ≤ t * P - 1 := by nlinarith
  have h3 : (t * P - 1) ^ 2 ≤ ((L - 1) * P) ^ 2 := pow_le_pow_left₀ h2 h1 2
  have h6 : 2 * t * P ≤ P ^ 2 / 500 := by nlinarith
  have e1 : ((L - 1) * P) ^ 2 = (L - 1) ^ 2 * P ^ 2 := by ring
  have e2 : (t * P - 1) ^ 2 = t ^ 2 * P ^ 2 - 2 * t * P + 1 := by ring
  have h4 : (t ^ 2 - 1 / 500) * P ^ 2 ≤ (L - 1) ^ 2 * P ^ 2 := by
    have e3 : (t ^ 2 - 1 / 500) * P ^ 2 = t ^ 2 * P ^ 2 - P ^ 2 / 500 := by ring
    rw [e3]
    linarith
  have hL1 : t ^ 2 - 1 / 500 ≤ (L - 1) ^ 2 := le_of_mul_le_mul_right h4 (pow_pos hP 2)
  -- S ≤ 4t
  have hSt : S ≤ 4 * t := by
    have h7 : t * S ≤ L * S := mul_le_mul_of_nonneg_right hLt hS0
    have h8 : t * S ≤ t * (4 * t) := by nlinarith
    exact le_of_mul_le_mul_left h8 ht0
  have hL2 : t * t ≤ L * L := mul_self_le_mul_self ht0.le hLt
  have ht2 : t ^ 2 = t * t := by ring
  -- |B| ≤ 8t, K ≤ 16t
  have hb : b ≤ 8 * t := by linarith
  have hKb : K ≤ 16 * t := by linarith
  have hK0 : 0 ≤ K := by linarith
  -- t β ≤ 768
  have h9 : b * K ≤ (8 * t) * (16 * t) := mul_le_mul hb hKb hK0 (by linarith)
  have h10 : t * β ≤ L * β := mul_le_mul_of_nonneg_right hLt hβ0
  have h11 : t * t * (t * β) ≤ L * L * (L * β) :=
    mul_le_mul hL2 h10 (mul_nonneg ht0.le hβ0) (mul_self_nonneg L)
  have h12 : t * t * (t * β) ≤ t * t * 768 := by nlinarith
  have hβt : t * β ≤ 768 := le_of_mul_le_mul_left h12 (mul_pos ht0 ht0)
  -- (L - 1)² ≤ t² - 1 + 2β
  have h13 : (L - 1) ^ 2 ≤ t ^ 2 - 1 + 2 * β := by
    have e4 : (L - 1) ^ 2 = L * L - 2 * L + 1 := by ring
    rw [e4]
    linarith
  have h14 : 499 / 1000 ≤ β := by linarith
  have h15 : 0 ≤ (t - 2000) * (β - 499 / 1000) := mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem bq_main {n : ℕ} (hn : 4000000 ≤ n) (G : SimpleGraph (Fin n))
    (hG : IsSpecMax IsOuterplanar G) (v : Fin n → ℝ)
    (hv : (G.adjMatrix ℝ).mulVec v = specRad G • v) (hpos : ∀ i, 0 < v i)
    (hle : ∀ i, v i ≤ 1) (x : Fin n) (hx : v x = 1) (y : Fin n) (hyx : y ≠ x) :
    G.Adj x y := by
  by_contra hxy
  have hGo : IsOuterplanar G := hG.1
  have hv0 : ∀ i, 0 ≤ v i := fun i => (hpos i).le
  have hn2 : 2 ≤ n := by omega
  -- t = √n
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.sqrt n := ⟨_, rfl⟩
  have ht2 : t ^ 2 = (n : ℝ) := by rw [ht]; exact Real.sq_sqrt (Nat.cast_nonneg n)
  have hnr : (4000000 : ℝ) ≤ n := by exact_mod_cast hn
  have ht0 : 2000 ≤ t := by
    rw [ht]; apply Real.le_sqrt_of_sq_le; linarith [show (2000:ℝ) ^ 2 = 4000000 by norm_num]
  -- the fan comparison
  have hfl := bq_fan_lower n hn2 (t - 1)
  have hfm := bq_fan_le_max (by omega) G hG
  have hX : 0 ≤ (t - 1) ^ 2 + ((n : ℝ) - 1) := by nlinarith [sq_nonneg (t - 1)]
  have hfm' := mul_le_mul_of_nonneg_right hfm hX
  have hfan : t ^ 3 - t - 1 ≤ specRad G * (t ^ 2 - t) := by
    rw [← ht2] at hfl hfm'
    have e1 : (t - 1) ^ 2 + (t ^ 2 - 1) = 2 * (t ^ 2 - t) := by ring
    have e2 : 2 * (t ^ 2 - 1) * (t - 1) + 2 * (t ^ 2 - 2) = 2 * (t ^ 3 - t - 1) := by ring
    rw [e1] at hfl hfm'
    rw [e2] at hfl
    linarith
  -- Σ v
  have hS0 : 0 ≤ ∑ w, v w := Finset.sum_nonneg (fun i _ => hv0 i)
  have hSL := bq_S hn2 G hGo v (specRad G) hv hle
  rw [← ht2] at hSL
  -- at x
  have hx2 := bq_sq G hGo v (specRad G) hv hv0 x
  rw [hx] at hx2
  simp only [mul_one] at hx2
  -- counts and the split of Σ v
  have hcnt := bq_part G x (fun _ => (1:ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    at hcnt
  rw [← ht2] at hcnt
  have hNs : ∑ u ∈ Finset.univ.filter (G.Adj x), v u = specRad G := by
    rw [Finset.sum_filter, bq_row G v (specRad G) hv x, hx, mul_one]
  have hSs := bq_part G x v
  rw [hNs, hx] at hSs
  have hb1 : (1:ℝ) ≤ ((Finset.univ.filter (fun z => z ≠ x ∧ ¬ G.Adj x z)).card : ℝ) := by
    have hy : y ∈ Finset.univ.filter (fun z => z ≠ x ∧ ¬ G.Adj x z) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hyx, hxy⟩
    have := Finset.card_pos.2 ⟨y, hy⟩
    exact_mod_cast this
  have hβ0 : 0 ≤ ∑ z ∈ Finset.univ.filter (fun z => z ≠ x ∧ ¬ G.Adj x z), v z :=
    Finset.sum_nonneg (fun i _ => hv0 i)
  -- vertices other than x and the mass of B
  have hd : ((Finset.univ.filter (G.Adj x)).card : ℝ) ≤ n := by
    have := Finset.card_le_univ (Finset.univ.filter (G.Adj x))
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hK0 : 0 ≤ ((n : ℝ) + 2 - ((Finset.univ.filter (G.Adj x)).card : ℝ)) + 2 * ∑ w, v w := by
    linarith
  have hβK := bq_beta G hGo v (specRad G) hv x _ hK0
    (fun u hu => bq_vertex G hGo v (specRad G) hv hv0 hle x u hu)
  rw [← ht2] at hβK
  exact bq_arith t (t ^ 2 - t) (specRad G) (∑ w, v w)
    ((Finset.univ.filter (G.Adj x)).card : ℝ)
    ((Finset.univ.filter (fun z => z ≠ x ∧ ¬ G.Adj x z)).card : ℝ)
    (∑ z ∈ Finset.univ.filter (fun z => z ≠ x ∧ ¬ G.Adj x z), v z)
    ((t ^ 2 + 2 - ((Finset.univ.filter (G.Adj x)).card : ℝ)) + 2 * ∑ w, v w)
    ht0 rfl hfan hS0 hSL hx2 hcnt hSs hb1 hβ0 rfl hβK

end BQMain

open Classical WangKangXue.SpectralTuran TaitTobin.Outerplanar in
theorem solution : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    IsSpecMax IsOuterplanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∀ y : Fin n, y ≠ x → G.Adj x y :=
  ⟨4000000, fun _ hn G hG v hv hpos hle x hx y hyx => bq_main hn G hG v hv hpos hle x hx y hyx⟩

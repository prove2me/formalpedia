-- Prove2me | solution 1 for StengelZeroSum.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T10:40:52.734576+00:00
-- url     : https://prove2.me/submissions/9ea3ec77-eaec-49b7-ba2d-5e6f36ca53bd

import Mathlib
import Definitions.Def_StengelZeroSum_IsSuitableM
import Definitions.Def_StengelZeroSum_bound55

set_option autoImplicit false

namespace S37
open Matrix VanderbeiLP.StrictComp ZeroSumLP.DantzigExt StengelZeroSum

section dots
variable {k : Type*} [Fintype k]

lemma dle {u v w : k → ℝ} (h : ∀ i, u i ≤ v i) (hw : ∀ i, 0 ≤ w i) : w ⬝ᵥ u ≤ w ⬝ᵥ v :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hw i)

lemma dot_const (w : k → ℝ) (v : ℝ) : w ⬝ᵥ (fun _ => v) = v * ∑ i, w i := by
  simp only [dotProduct, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

lemma dot_sub_smul (w f g : k → ℝ) (t : ℝ) :
    w ⬝ᵥ (fun i => f i - g i * t) = w ⬝ᵥ f - t * (g ⬝ᵥ w) := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dot_neg_add_smul (w f g : k → ℝ) (t : ℝ) :
    w ⬝ᵥ (fun i => -f i + g i * t) = -(w ⬝ᵥ f) + t * (g ⬝ᵥ w) := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dot_add_smul (w f : k → ℝ) (t : ℝ) :
    w ⬝ᵥ (fun i => f i + t) = w ⬝ᵥ f + t * ∑ i, w i := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dot3 (w f g : k → ℝ) (r s : ℝ) :
    w ⬝ᵥ (fun i => -f i + g i * r + s) = -(w ⬝ᵥ f) + r * (g ⬝ᵥ w) + s * ∑ i, w i := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dot4 (w f g : k → ℝ) (r s : ℝ) :
    w ⬝ᵥ (fun i => f i - g i * r + s) = w ⬝ᵥ f - r * (g ⬝ᵥ w) + s * ∑ i, w i := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dot_div (g x : k → ℝ) (t : ℝ) : g ⬝ᵥ (fun j => x j / t) = g ⬝ᵥ x / t := by
  simp only [dotProduct, Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring

lemma dot_nonneg' {w f : k → ℝ} (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) : 0 ≤ w ⬝ᵥ f :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hf i)

end dots

lemma mulVec_div {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (t : ℝ) (i : Fin m) :
    (A *ᵥ fun j => x j / t) i = (A *ᵥ x) i / t := by
  simp only [mulVec]; exact dot_div _ _ _

lemma key {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ) (x : Fin n → ℝ) :
    y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

section generic
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma weak_game (G : Matrix ι κ ℝ) (Z : κ → ℝ) (v : ℝ) (Q : ι → ℝ) (u : ℝ)
    (hZ0 : 0 ≤ Z) (hZ1 : ∑ j, Z j = 1) (hZ : G *ᵥ Z ≤ fun _ => v)
    (hQ0 : 0 ≤ Q) (hQ1 : ∑ i, Q i = 1) (hQ : (fun _ => u) ≤ Q ᵥ* G) : u ≤ v := by
  have e : Q ⬝ᵥ (G *ᵥ Z) = (Q ᵥ* G) ⬝ᵥ Z := dotProduct_mulVec Q G Z
  have h1 : Q ⬝ᵥ (G *ᵥ Z) ≤ v := by
    calc Q ⬝ᵥ (G *ᵥ Z) = ∑ i, Q i * (G *ᵥ Z) i := rfl
      _ ≤ ∑ i, Q i * v := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hZ i) (hQ0 i)
      _ = v := by rw [← Finset.sum_mul, hQ1, one_mul]
  have h2 : u ≤ (Q ᵥ* G) ⬝ᵥ Z := by
    calc u = ∑ j, u * Z j := by rw [← Finset.mul_sum, hZ1, mul_one]
      _ ≤ ∑ j, (Q ᵥ* G) j * Z j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hQ j) (hZ0 j)
      _ = (Q ᵥ* G) ⬝ᵥ Z := rfl
  linarith

lemma value_unique (G : Matrix ι κ ℝ) {Z Z' : κ → ℝ} {v v' : ℝ}
    (h : IsMinMaxStrategy G Z v) (h' : IsMinMaxStrategy G Z' v') : v = v' :=
  le_antisymm (h.2 Z' v' h'.1) (h'.2 Z v h.1)

end generic

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (M : ℝ)

lemma gz1 (Z : (Fin m ⊕ Fin n) ⊕ Unit → ℝ) (i : Fin m) :
    (extGame A b c M *ᵥ Z) (.inl (.inl (.inl i))) =
      (A *ᵥ fun j => Z (.inl (.inr j))) i - b i * Z (.inr ()) := by
  simp [extGame, mulVec, dotProduct, Fintype.sum_sum_type]; ring

lemma gz2 (Z : (Fin m ⊕ Fin n) ⊕ Unit → ℝ) (j : Fin n) :
    (extGame A b c M *ᵥ Z) (.inl (.inl (.inr j))) =
      -(Aᵀ *ᵥ fun i => Z (.inl (.inl i))) j + c j * Z (.inr ()) := by
  simp [extGame, mulVec, dotProduct, Fintype.sum_sum_type]

lemma gz3 (Z : (Fin m ⊕ Fin n) ⊕ Unit → ℝ) :
    (extGame A b c M *ᵥ Z) (.inl (.inr ())) =
      b ⬝ᵥ (fun i => Z (.inl (.inl i))) - c ⬝ᵥ (fun j => Z (.inl (.inr j))) := by
  simp [extGame, mulVec, dotProduct, Fintype.sum_sum_type]; ring

lemma gz4 (Z : (Fin m ⊕ Fin n) ⊕ Unit → ℝ) :
    (extGame A b c M *ᵥ Z) (.inr ()) =
      ∑ i, Z (.inl (.inl i)) + ∑ j, Z (.inl (.inr j)) - M * Z (.inr ()) := by
  simp [extGame, mulVec, dotProduct, Fintype.sum_sum_type]; ring

lemma qg1 (Q : ((Fin m ⊕ Fin n) ⊕ Unit) ⊕ Unit → ℝ) (i : Fin m) :
    (Q ᵥ* extGame A b c M) (.inl (.inl i)) =
      -(A *ᵥ fun j => Q (.inl (.inl (.inr j)))) i + b i * Q (.inl (.inr ())) + Q (.inr ()) := by
  simp [extGame, vecMul, mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]

lemma qg2 (Q : ((Fin m ⊕ Fin n) ⊕ Unit) ⊕ Unit → ℝ) (j : Fin n) :
    (Q ᵥ* extGame A b c M) (.inl (.inr j)) =
      (Aᵀ *ᵥ fun i => Q (.inl (.inl (.inl i)))) j - c j * Q (.inl (.inr ())) + Q (.inr ()) := by
  simp [extGame, vecMul, mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]; ring

lemma qg3 (Q : ((Fin m ⊕ Fin n) ⊕ Unit) ⊕ Unit → ℝ) :
    (Q ᵥ* extGame A b c M) (.inr ()) =
      -(b ⬝ᵥ fun i => Q (.inl (.inl (.inl i)))) + c ⬝ᵥ (fun j => Q (.inl (.inl (.inr j))))
        - M * Q (.inr ()) := by
  simp [extGame, vecMul, mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]; ring

/-- The relaxation (58) of von Stengel (in the variables of (53) plus `bᵀy − cᵀx ≤ w`, `w ≥ 0`). -/
def Feas58 (x : Fin n → ℝ) (y : Fin m → ℝ) (w : ℝ) : Prop :=
  (∀ i, (A *ᵥ x) i ≤ b i + w) ∧ (∀ j, 0 ≤ x j) ∧ (∀ j, c j - w ≤ (Aᵀ *ᵥ y) j) ∧
    (∀ i, 0 ≤ y i) ∧ b ⬝ᵥ y - c ⬝ᵥ x ≤ w ∧ 0 ≤ w

/-- Row player cannot have all of its weight on the last row. -/
lemma s_lt_one (y' : Fin m → ℝ) (x' : Fin n → ℝ) (r s v : ℝ) (hM : 0 ≤ M) (hv : 0 < v)
    (hy' : ∀ i, 0 ≤ y' i) (hx' : ∀ j, 0 ≤ x' j) (hr : 0 ≤ r)
    (hsum : ∑ i, y' i + ∑ j, x' j + r + s = 1)
    (c3 : v ≤ -(b ⬝ᵥ y') + c ⬝ᵥ x' - M * s) (hs : 1 ≤ s) : False := by
  have h1 : 0 ≤ ∑ i, y' i := Finset.sum_nonneg fun i _ => hy' i
  have h2 : 0 ≤ ∑ j, x' j := Finset.sum_nonneg fun j _ => hx' j
  have e1 : ∑ i, y' i = 0 := by linarith
  have e2 : ∑ j, x' j = 0 := by linarith
  have z1 : ∀ i, y' i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hy' i).1 e1 i (Finset.mem_univ _)
  have z2 : ∀ j, x' j = 0 := fun j =>
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hx' j).1 e2 j (Finset.mem_univ _)
  have d1 : b ⬝ᵥ y' = 0 := by simp [dotProduct, z1]
  have d2 : c ⬝ᵥ x' = 0 := by simp [dotProduct, z2]
  rw [d1, d2] at c3
  have := mul_nonneg hM (by linarith : (0:ℝ) ≤ s)
  linarith

set_option maxHeartbeats 1000000 in
/-- The heart of Theorem 8(b), in scalar form. `(y, x, t)` is a min-max strategy of `B_M`
with value `v > 0`, `(y', x', r, s)` a max-min strategy with the same value, and `(x0, y0, w0)`
an optimal solution of (58) with `1ᵀx0 + 1ᵀy0 + 1 ≤ M`. -/
lemma core_b (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (w0 : ℝ) (hf : Feas58 A b c x0 y0 w0)
    (hopt : ∀ x y w, Feas58 A b c x y w → w0 ≤ w)
    (hM : ∑ j, x0 j + ∑ i, y0 i + 1 ≤ M)
    (y : Fin m → ℝ) (x : Fin n → ℝ) (t v : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hx : ∀ j, 0 ≤ x j) (ht : 0 ≤ t)
    (hsum : ∑ i, y i + ∑ j, x j + t = 1)
    (r1 : ∀ i, (A *ᵥ x) i - b i * t ≤ v) (r2 : ∀ j, -(Aᵀ *ᵥ y) j + c j * t ≤ v)
    (r3 : b ⬝ᵥ y - c ⬝ᵥ x ≤ v) (r4 : ∑ i, y i + ∑ j, x j - M * t ≤ v)
    (y' : Fin m → ℝ) (x' : Fin n → ℝ) (r s : ℝ)
    (hy' : ∀ i, 0 ≤ y' i) (hx' : ∀ j, 0 ≤ x' j) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hsum' : ∑ i, y' i + ∑ j, x' j + r + s = 1)
    (c1 : ∀ i, v ≤ -(A *ᵥ x') i + b i * r + s) (c2 : ∀ j, v ≤ (Aᵀ *ᵥ y') j - c j * r + s)
    (c3 : v ≤ -(b ⬝ᵥ y') + c ⬝ᵥ x' - M * s) (hv : 0 < v) :
    r = 0 ∧ s = v ∧ v < 1 ∧ (∀ i, (A *ᵥ x') i ≤ 0) ∧ (∀ j, 0 ≤ (Aᵀ *ᵥ y') j) ∧
      b ⬝ᵥ y' - c ⬝ᵥ x' < 0 ∧ w0 = (M + 1) / (1 / v - 1) := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hf
  have hx0 : 0 ≤ ∑ j, x0 j := Finset.sum_nonneg fun j _ => f2 j
  have hy0 : 0 ≤ ∑ i, y0 i := Finset.sum_nonneg fun i _ => f4 i
  have hsy' : 0 ≤ ∑ i, y' i := Finset.sum_nonneg fun i _ => hy' i
  have hsx' : 0 ≤ ∑ j, x' j := Finset.sum_nonneg fun j _ => hx' j
  have hM1 : 1 ≤ M := by linarith
  have P1 : v * ∑ i, y' i ≤ -(y' ⬝ᵥ (A *ᵥ x')) + r * (b ⬝ᵥ y') + s * ∑ i, y' i := by
    have := dle (w := y') (u := fun _ => v) (v := fun i => -(A *ᵥ x') i + b i * r + s) c1 hy'
    rwa [dot_const, dot3] at this
  have P2 : v * ∑ j, x' j ≤ x' ⬝ᵥ (Aᵀ *ᵥ y') - r * (c ⬝ᵥ x') + s * ∑ j, x' j := by
    have := dle (w := x') (u := fun _ => v) (v := fun j => (Aᵀ *ᵥ y') j - c j * r + s) c2 hx'
    rwa [dot_const, dot4] at this
  have K1 := key A y' x'
  -- Step 1: s ≥ v
  have hsv : v ≤ s := by
    by_contra hlt
    push_neg at hlt
    have hrv : 0 ≤ r * v := mul_nonneg hr hv.le
    have hrs : 0 ≤ M * (r * s) := mul_nonneg (by linarith) (mul_nonneg hr hs)
    have hc := mul_le_mul_of_nonneg_left (show b ⬝ᵥ y' - c ⬝ᵥ x' ≤ -v - M * s by linarith) hr
    have hc' : r * (b ⬝ᵥ y') - r * (c ⬝ᵥ x') ≤ -(r * v) - M * (r * s) := by
      linarith [hc, show r * (b ⬝ᵥ y' - c ⬝ᵥ x') = r * (b ⬝ᵥ y') - r * (c ⬝ᵥ x') by ring,
        show r * (-v - M * s) = -(r * v) - M * (r * s) by ring]
    have hA : v * ∑ i, y' i + v * ∑ j, x' j - (s * ∑ i, y' i + s * ∑ j, x' j)
        ≤ -(r * v) - M * (r * s) := by linarith
    have hP := mul_nonneg (show 0 ≤ v - s by linarith) (add_nonneg hsy' hsx')
    have hE : (v - s) * (∑ i, y' i + ∑ j, x' j) =
        v * ∑ i, y' i + v * ∑ j, x' j - (s * ∑ i, y' i + s * ∑ j, x' j) := by ring
    have hZ : (v - s) * (∑ i, y' i + ∑ j, x' j) = 0 := by linarith
    have hC : ∑ i, y' i + ∑ j, x' j = 0 := by
      rcases mul_eq_zero.1 hZ with h | h
      · linarith
      · exact h
    have hr0 : r = 0 := by
      rcases eq_or_lt_of_le hr with h | h
      · exact h.symm
      · have := mul_pos h hv; linarith
    exact s_lt_one b c M y' x' r s v (by linarith) hv hy' hx' hr hsum' c3 (by linarith)
  have hs0 : 0 < s := lt_of_lt_of_le hv hsv
  -- Step 2: complementary slackness on the last row
  have Q1 : y' ⬝ᵥ (fun i => (A *ᵥ x) i - b i * t) ≤ v * ∑ i, y' i := by
    have := dle (w := y') r1 hy'; rwa [dot_const] at this
  have Q2 : x' ⬝ᵥ (fun j => -(Aᵀ *ᵥ y) j + c j * t) ≤ v * ∑ j, x' j := by
    have := dle (w := x') r2 hx'; rwa [dot_const] at this
  have Q3 : r * (b ⬝ᵥ y - c ⬝ᵥ x) ≤ r * v := mul_le_mul_of_nonneg_left r3 hr
  have R1 : v * ∑ i, y i ≤ y ⬝ᵥ (fun i => -(A *ᵥ x') i + b i * r + s) := by
    have := dle (w := y) (u := fun _ => v) (v := fun i => -(A *ᵥ x') i + b i * r + s) c1 hy
    rwa [dot_const] at this
  have R2 : v * ∑ j, x j ≤ x ⬝ᵥ (fun j => (Aᵀ *ᵥ y') j - c j * r + s) := by
    have := dle (w := x) (u := fun _ => v) (v := fun j => (Aᵀ *ᵥ y') j - c j * r + s) c2 hx
    rwa [dot_const] at this
  have R3 : t * v ≤ t * (-(b ⬝ᵥ y') + c ⬝ᵥ x' - M * s) := mul_le_mul_of_nonneg_left c3 ht
  rw [dot_sub_smul] at Q1
  rw [dot_neg_add_smul] at Q2
  rw [dot3] at R1
  rw [dot4] at R2
  have K2 := key A y' x
  have K3 := key A y x'
  have ident : (y' ⬝ᵥ (A *ᵥ x) - t * (b ⬝ᵥ y')) + (-(x' ⬝ᵥ (Aᵀ *ᵥ y)) + t * (c ⬝ᵥ x'))
      + r * (b ⬝ᵥ y - c ⬝ᵥ x) + s * (∑ i, y i + ∑ j, x j - M * t)
      = (-(y ⬝ᵥ (A *ᵥ x')) + r * (b ⬝ᵥ y) + s * ∑ i, y i)
      + (x ⬝ᵥ (Aᵀ *ᵥ y') - r * (c ⬝ᵥ x) + s * ∑ j, x j)
      + t * (-(b ⬝ᵥ y') + c ⬝ᵥ x' - M * s) := by
    linear_combination K2 + K3
  have e4 : v * ∑ i, y' i + v * ∑ j, x' j + r * v + s * v = v := by linear_combination v * hsum'
  have e5 : v * ∑ i, y i + v * ∑ j, x j + t * v = v := by linear_combination v * hsum
  have hlast : s * v ≤ s * (∑ i, y i + ∑ j, x j - M * t) := by linarith
  have hrow4 : ∑ i, y i + ∑ j, x j - M * t = v := le_antisymm r4 (le_of_mul_le_mul_left hlast hs0)
  have htM : t * (M + 1) = 1 - v := by linear_combination hsum - hrow4
  -- Step 3: v < 1, t > 0
  have hv1 : v < 1 := by
    by_contra hge
    push_neg at hge
    exact s_lt_one b c M y' x' r s v (by linarith) hv hy' hx' hr hsum' c3 (by linarith)
  have htpos : 0 < t := by
    by_contra h0
    have : t = 0 := le_antisymm (not_lt.1 h0) ht
    rw [this] at htM; linarith
  -- Step 4: (x/t, y/t, v/t) is feasible for (58)
  have hF : Feas58 A b c (fun j => x j / t) (fun i => y i / t) (v / t) := by
    refine ⟨fun i => ?_, fun j => div_nonneg (hx j) ht, fun j => ?_, fun i => div_nonneg (hy i) ht,
      ?_, div_nonneg hv.le ht⟩
    · rw [mulVec_div, div_le_iff₀ htpos, add_mul, div_mul_cancel₀ _ htpos.ne']; linarith [r1 i]
    · rw [mulVec_div, le_div_iff₀ htpos, sub_mul, div_mul_cancel₀ _ htpos.ne']; linarith [r2 j]
    · rw [dot_div, dot_div, ← sub_div, div_le_div_iff_of_pos_right htpos]; exact r3
  have hw0t : w0 ≤ v / t := hopt _ _ _ hF
  have hw0t' : w0 * t ≤ v := by rwa [le_div_iff₀ htpos] at hw0t
  have S4 : w0 - w0 * v ≤ M * v + v := by
    have h := mul_le_mul_of_nonneg_right hw0t' (by linarith : (0:ℝ) ≤ M + 1)
    have h2 : w0 * t * (M + 1) = w0 * (1 - v) := by rw [mul_assoc, htM]
    linarith [show w0 * (1 - v) = w0 - w0 * v by ring, show v * (M + 1) = M * v + v by ring]
  -- Step 5: the chain (71)
  have F1 : y' ⬝ᵥ (A *ᵥ x0) ≤ b ⬝ᵥ y' + w0 * ∑ i, y' i := by
    have := dle (w := y') (u := A *ᵥ x0) (v := fun i => b i + w0) f1 hy'
    rwa [dot_add_smul, dotProduct_comm y' b] at this
  have F3 : c ⬝ᵥ x' - w0 * ∑ j, x' j ≤ x' ⬝ᵥ (Aᵀ *ᵥ y0) := by
    have := dle (w := x') (u := fun j => c j - w0) (v := Aᵀ *ᵥ y0) f3 hx'
    have e : x' ⬝ᵥ (fun j => c j - w0) = c ⬝ᵥ x' - w0 * ∑ j, x' j := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rwa [e] at this
  have F5 : r * (b ⬝ᵥ y0) - r * (c ⬝ᵥ x0) ≤ r * w0 := by
    have := mul_le_mul_of_nonneg_left f5 hr
    linarith [show r * (b ⬝ᵥ y0 - c ⬝ᵥ x0) = r * (b ⬝ᵥ y0) - r * (c ⬝ᵥ x0) by ring]
  have P1' : v * ∑ i, y0 i ≤ -(y0 ⬝ᵥ (A *ᵥ x')) + r * (b ⬝ᵥ y0) + s * ∑ i, y0 i := by
    have := dle (w := y0) (u := fun _ => v) (v := fun i => -(A *ᵥ x') i + b i * r + s) c1 f4
    rwa [dot_const, dot3] at this
  have P2' : v * ∑ j, x0 j ≤ x0 ⬝ᵥ (Aᵀ *ᵥ y') - r * (c ⬝ᵥ x0) + s * ∑ j, x0 j := by
    have := dle (w := x0) (u := fun _ => v) (v := fun j => (Aᵀ *ᵥ y') j - c j * r + s) c2 f2
    rwa [dot_const, dot4] at this
  have K4 := key A y' x0
  have K5 := key A y0 x'
  have hdelta : s * ∑ j, x0 j + s * ∑ i, y0 i - v * ∑ j, x0 j - v * ∑ i, y0 i
      ≤ M * s - s - M * v + v := by
    have := mul_le_mul_of_nonneg_left (show ∑ j, x0 j + ∑ i, y0 i ≤ M - 1 by linarith)
      (show 0 ≤ s - v by linarith)
    linarith [show (s - v) * (∑ j, x0 j + ∑ i, y0 i) =
        s * ∑ j, x0 j + s * ∑ i, y0 i - v * ∑ j, x0 j - v * ∑ i, y0 i by ring,
      show (s - v) * (M - 1) = M * s - s - M * v + v by ring]
  have e6 : w0 * ∑ i, y' i + w0 * ∑ j, x' j + w0 * r = w0 - w0 * s := by
    linear_combination w0 * hsum'
  have hb : s + M * v ≤ w0 - w0 * s := by linarith
  have hsv' : s = v := by
    have := mul_nonneg f6 (show 0 ≤ s - v by linarith)
    linarith [show w0 * (s - v) = w0 * s - w0 * v by ring]
  subst hsv'
  have hw0eq : w0 - w0 * s = M * s + s := by linarith
  -- Step 6: r = 0
  have hneg' : b ⬝ᵥ y' - c ⬝ᵥ x' < 0 := by
    have := mul_nonneg (show (0:ℝ) ≤ M by linarith) hs
    linarith
  have hr0 : r = 0 := by
    have h1 : 0 ≤ r * (b ⬝ᵥ y') - r * (c ⬝ᵥ x') := by linarith
    rcases eq_or_lt_of_le hr with h | h
    · exact h.symm
    · have := mul_neg_of_pos_of_neg h hneg'
      linarith [show r * (b ⬝ᵥ y' - c ⬝ᵥ x') = r * (b ⬝ᵥ y') - r * (c ⬝ᵥ x') by ring]
  subst hr0
  refine ⟨rfl, rfl, hv1, fun i => ?_, fun j => ?_, hneg', ?_⟩
  · have := c1 i; linarith
  · have := c2 j; linarith
  · have hs' : s ≠ 0 := hs0.ne'
    have h3 : (1:ℝ) / s - 1 = (1 - s) / s := by field_simp
    have hne : (1:ℝ) / s - 1 ≠ 0 := by rw [h3]; exact div_ne_zero (by linarith) hs'
    rw [eq_div_iff hne, h3, mul_div_assoc', div_eq_iff hs']
    linarith [show w0 * (1 - s) = w0 - w0 * s by ring, show (M + 1) * s = M * s + s by ring]


lemma exists_between_fin {ι : Type} (s r : Finset ι) (L U : ι → ℝ)
    (h : ∀ q ∈ s, ∀ p ∈ r, L q ≤ U p) :
    ∃ t : ℝ, (∀ q ∈ s, L q ≤ t) ∧ ∀ p ∈ r, t ≤ U p := by
  by_cases hs : s.Nonempty
  · refine ⟨s.sup' hs L, fun q hq => Finset.le_sup' L hq, fun p hp => ?_⟩
    exact Finset.sup'_le hs L (fun q hq => h q hq p hp)
  · by_cases hr : r.Nonempty
    · exact ⟨r.inf' hr U, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => Finset.inf'_le U hp⟩
    · exact ⟨0, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => absurd ⟨p, hp⟩ hr⟩

set_option maxHeartbeats 1000000 in
/-- Theorem of alternatives (Fourier–Motzkin), variables indexed by `Fin n`. -/
theorem fm_alt (n : ℕ) : ∀ {ι : Type} [Fintype ι] (a : ι → Fin n → ℝ) (b : ι → ℝ),
    (∃ x : Fin n → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  induction n with
  | zero =>
    intro ι _ a b
    classical
    by_cases h : ∀ i, 0 ≤ b i
    · left; exact ⟨0, fun i => by simpa using h i⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      refine ⟨fun j => if j = i then 1 else 0, fun j => ?_, fun s => s.elim0, ?_⟩
      · dsimp only; split_ifs <;> norm_num
      · simpa using hi
  | succ n ih =>
    intro ι _ a b
    classical
    let W : ι ⊕ (ι × ι) → ι → ℝ := Sum.elim (fun z i => if a z 0 = 0 ∧ i = z then 1 else 0)
      (fun pq i => if 0 < a pq.1 0 ∧ a pq.2 0 < 0 then
        (if i = pq.1 then -a pq.2 0 else 0) + (if i = pq.2 then a pq.1 0 else 0) else 0)
    have hW0 : ∀ k i, 0 ≤ W k i := by
      intro k i
      rcases k with z | ⟨p, q⟩
      · simp only [W, Sum.elim_inl]; split_ifs <;> norm_num
      · simp only [W, Sum.elim_inr]
        split_ifs with h1 h2 h3 h3 <;> subst_vars <;> first | linarith [h1.1, h1.2] | norm_num
    let C : ι ⊕ (ι × ι) → Fin (n + 1) → ℝ := fun k s => ∑ i, W k i * a i s
    let D : ι ⊕ (ι × ι) → ℝ := fun k => ∑ i, W k i * b i
    have hC0 : ∀ k, C k 0 = 0 := by
      intro k
      rcases k with z | ⟨p, q⟩
      · by_cases hz : a z 0 = 0
        · simp [C, W, hz]
        · simp [C, W, hz]
      · by_cases h : 0 < a p 0 ∧ a q 0 < 0
        · simp only [C, W, Sum.elim_inr, if_pos h, add_mul, ite_mul, zero_mul,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        · simp [C, W, h]
    rcases ih (fun k s => C k s.succ) D with ⟨y, hy⟩ | ⟨μ, hμ0, hμ1, hμ2⟩
    · left
      let r : ι → ℝ := fun i => b i - ∑ s : Fin n, a i s.succ * y s
      have key : ∀ k, 0 ≤ ∑ i, W k i * r i := by
        intro k
        have e : ∑ i, W k i * r i = D k - ∑ s, C k s.succ * y s := by
          simp only [r, D, C, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
            mul_assoc]
          congr 1
          exact Finset.sum_comm
        rw [e]; linarith [hy k]
      have kinl : ∀ z, a z 0 = 0 → 0 ≤ r z := by
        intro z hz
        have := key (Sum.inl z)
        simpa [W, hz] using this
      have kinr : ∀ p q, 0 < a p 0 → a q 0 < 0 → 0 ≤ -a q 0 * r p + a p 0 * r q := by
        intro p q hp hq
        have := key (Sum.inr (p, q))
        simp only [W, Sum.elim_inr, if_pos (And.intro hp hq), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        exact this
      obtain ⟨t, ht1, ht2⟩ := exists_between_fin (Finset.univ.filter (fun q => a q 0 < 0))
        (Finset.univ.filter (fun p => 0 < a p 0)) (fun q => r q / a q 0) (fun p => r p / a p 0)
        (by
          intro q hq p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hp
          have h := kinr p q hp hq
          have e : -a q 0 * r p + a p 0 * r q =
              -(a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0)) := by
            have h1 : r p = (r p / a p 0) * a p 0 := (div_mul_cancel₀ _ hp.ne').symm
            have h2 : r q = (r q / a q 0) * a q 0 := (div_mul_cancel₀ _ hq.ne).symm
            set U := r p / a p 0
            set V := r q / a q 0
            rw [h1, h2]; ring
          by_contra hc
          push Not at hc
          have hpq : 0 < a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0) :=
            mul_pos (mul_pos hp (neg_pos.2 hq)) (sub_pos.2 hc)
          linarith)
      refine ⟨Fin.cons t y, fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hr : r i = b i - ∑ s : Fin n, a i s.succ * y s := rfl
      suffices a i 0 * t ≤ r i by linarith
      rcases lt_trichotomy (a i 0) 0 with hneg | hz | hpos
      · have := ht1 i (by simp [hneg])
        rw [div_le_iff_of_neg hneg] at this
        linarith
      · rw [hz, zero_mul]; exact kinl i hz
      · have := ht2 i (by simp [hpos])
        rw [le_div_iff₀ hpos] at this
        linarith
    · right
      refine ⟨fun i => ∑ k, μ k * W k i, fun i => Finset.sum_nonneg
        (fun k _ => mul_nonneg (hμ0 k) (hW0 k i)), fun s => ?_, ?_⟩
      · have e : ∑ i, (∑ k, μ k * W k i) * a i s = ∑ k, μ k * C k s := by
          simp only [C, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]
        refine Fin.cases ?_ (fun s => ?_) s
        · simp [hC0]
        · exact hμ1 s
      · have e : ∑ i, (∑ k, μ k * W k i) * b i = ∑ k, μ k * D k := by
          simp only [D, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]; exact hμ2

/-- Theorem of alternatives over an arbitrary finite variable type. -/
theorem fm_alt' {σ ι : Type} [Fintype σ] [Fintype ι] (a : ι → σ → ℝ) (b : ι → ℝ) :
    (∃ x : σ → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  classical
  let e := Fintype.equivFin σ
  rcases fm_alt _ (fun i k => a i (e.symm k)) b with ⟨x, hx⟩ | ⟨l, h0, h1, h2⟩
  · left
    refine ⟨fun s => x (e s), fun i => ?_⟩
    rw [Fintype.sum_equiv e _ (fun k => a i (e.symm k) * x k) (fun s => by simp)]
    exact hx i
  · right
    exact ⟨l, h0, fun s => by simpa using h1 (e s), h2⟩


lemma weak_game' {ι κ : Type} [Fintype ι] [Fintype κ] (G : Matrix ι κ ℝ) (Z : κ → ℝ) (v : ℝ) (Q : ι → ℝ) (u : ℝ)
    (hZ0 : 0 ≤ Z) (hZ1 : ∑ j, Z j = 1) (hZ : G *ᵥ Z ≤ fun _ => v)
    (hQ0 : 0 ≤ Q) (hQ1 : ∑ i, Q i = 1) (hQ : (fun _ => u) ≤ Q ᵥ* G) : u ≤ v := by
  have e : Q ⬝ᵥ (G *ᵥ Z) = (Q ᵥ* G) ⬝ᵥ Z := dotProduct_mulVec Q G Z
  have h1 : Q ⬝ᵥ (G *ᵥ Z) ≤ v := by
    calc Q ⬝ᵥ (G *ᵥ Z) = ∑ i, Q i * (G *ᵥ Z) i := rfl
      _ ≤ ∑ i, Q i * v := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hZ i) (hQ0 i)
      _ = v := by rw [← Finset.sum_mul, hQ1, one_mul]
  have h2 : u ≤ (Q ᵥ* G) ⬝ᵥ Z := by
    calc u = ∑ j, u * Z j := by rw [← Finset.mul_sum, hZ1, mul_one]
      _ ≤ ∑ j, (Q ᵥ* G) j * Z j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hQ j) (hZ0 j)
      _ = (Q ᵥ* G) ⬝ᵥ Z := rfl
  linarith

section minimax
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Constraint matrix of the combined primal/dual system of a matrix game. -/
def mmA (G : Matrix ι κ ℝ) : ((κ ⊕ ι) ⊕ (ι ⊕ κ)) ⊕ Fin 4 → (κ ⊕ ι) ⊕ Unit → ℝ
  | .inl (.inl (.inl k)), .inl (.inl k') => if k' = k then -1 else 0
  | .inl (.inl (.inl _)), _ => 0
  | .inl (.inl (.inr r)), .inl (.inl k) => G r k
  | .inl (.inl (.inr _)), .inl (.inr _) => 0
  | .inl (.inl (.inr _)), .inr _ => -1
  | .inl (.inr (.inl r)), .inl (.inr r') => if r' = r then -1 else 0
  | .inl (.inr (.inl _)), _ => 0
  | .inl (.inr (.inr _)), .inl (.inl _) => 0
  | .inl (.inr (.inr k)), .inl (.inr r) => -G r k
  | .inl (.inr (.inr _)), .inr _ => 1
  | .inr i, .inl (.inl _) => if i = 0 then 1 else if i = 1 then -1 else 0
  | .inr i, .inl (.inr _) => if i = 2 then 1 else if i = 3 then -1 else 0
  | .inr _, .inr _ => 0

def mmB : ((κ ⊕ ι) ⊕ (ι ⊕ κ)) ⊕ Fin 4 → ℝ
  | .inl _ => 0
  | .inr i => if i = 0 then 1 else if i = 1 then -1 else if i = 2 then 1 else -1

set_option maxHeartbeats 1000000 in
theorem minimax [Nonempty ι] [Nonempty κ] (G : Matrix ι κ ℝ) :
    ∃ (Z : κ → ℝ) (v : ℝ) (Q : ι → ℝ), IsMinMaxStrategy G Z v ∧ IsMaxMinStrategy G Q v := by
  rcases fm_alt' (mmA G) (mmB (ι := ι) (κ := κ)) with ⟨x, hx⟩ | ⟨l, h0, h1, h2⟩
  · let Z : κ → ℝ := fun k => x (.inl (.inl k))
    let Q : ι → ℝ := fun r => x (.inl (.inr r))
    let v : ℝ := x (.inr ())
    have hZ0 : 0 ≤ Z := fun k => by
      have := hx (.inl (.inl (.inl k)))
      simp [mmA, mmB, Fintype.sum_sum_type] at this
      exact this
    have hQ0 : 0 ≤ Q := fun r => by
      have := hx (.inl (.inr (.inl r)))
      simp [mmA, mmB, Fintype.sum_sum_type] at this
      exact this
    have hZ1 : ∑ k, Z k = 1 := by
      have e0 := hx (.inr 0)
      have e1 := hx (.inr 1)
      simp [mmA, mmB, Fintype.sum_sum_type] at e0 e1
      simp only [Z]; linarith
    have hQ1 : ∑ r, Q r = 1 := by
      have e0 := hx (.inr 2)
      have e1 := hx (.inr 3)
      simp [mmA, mmB, Fintype.sum_sum_type] at e0 e1
      simp only [Q]; linarith
    have hGZ : G *ᵥ Z ≤ fun _ => v := fun r => by
      have := hx (.inl (.inl (.inr r)))
      simp [mmA, mmB, Fintype.sum_sum_type] at this
      simp only [mulVec, dotProduct, Z, v]; linarith
    have hQG : (fun _ => v) ≤ Q ᵥ* G := fun k => by
      have := hx (.inl (.inr (.inr k)))
      simp [mmA, mmB, Fintype.sum_sum_type] at this
      simp only [vecMul, dotProduct, Q, v]
      have e : ∑ r, x (.inl (.inr r)) * G r k = ∑ r, G r k * x (.inl (.inr r)) :=
        Finset.sum_congr rfl fun r _ => mul_comm _ _
      linarith
    refine ⟨Z, v, Q, ⟨⟨hZ0, hZ1, hGZ⟩, fun Z' v' h => ?_⟩, ⟨⟨hQ0, hQ1, hQG⟩, fun Q' u' h => ?_⟩⟩
    · obtain ⟨h1, h2, h3⟩ := h
      exact weak_game' G Z' v' Q v h1 h2 h3 hQ0 hQ1 hQG
    · obtain ⟨h1, h2, h3⟩ := h
      exact weak_game' G Z v Q' u' hZ0 hZ1 hGZ h1 h2 h3
  · exfalso
    let α : κ → ℝ := fun k => l (.inl (.inl (.inl k)))
    let lam : ι → ℝ := fun r => l (.inl (.inl (.inr r)))
    let γ : ι → ℝ := fun r => l (.inl (.inr (.inl r)))
    let μ : κ → ℝ := fun k => l (.inl (.inr (.inr k)))
    have hZk : ∀ k, -α k + ∑ r, lam r * G r k + (l (.inr 0) - l (.inr 1)) = 0 := fun k => by
      have := h1 (.inl (.inl k))
      simp [mmA, Fintype.sum_sum_type, Fin.sum_univ_four] at this
      simp only [α, lam]; linarith
    have hQr : ∀ r, -γ r - ∑ k, μ k * G r k + (l (.inr 2) - l (.inr 3)) = 0 := fun r => by
      have := h1 (.inl (.inr r))
      simp [mmA, Fintype.sum_sum_type, Fin.sum_univ_four] at this
      simp only [γ, μ]
      have e : ∑ k, l (.inl (.inr (.inr k))) * -G r k = -∑ k, l (.inl (.inr (.inr k))) * G r k := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
      linarith
    have hv : -∑ r, lam r + ∑ k, μ k = 0 := by
      have := h1 (.inr ())
      simp [mmA, Fintype.sum_sum_type, Fin.sum_univ_four] at this
      simp only [lam, μ]; linarith
    have hb : l (.inr 0) - l (.inr 1) + (l (.inr 2) - l (.inr 3)) < 0 := by
      simp [mmB, Fintype.sum_sum_type, Fin.sum_univ_four] at h2
      linarith
    set B := l (.inr 0) - l (.inr 1)
    set D := l (.inr 2) - l (.inr 3)
    have hα : ∀ k, 0 ≤ α k := fun k => h0 _
    have hlam : ∀ r, 0 ≤ lam r := fun r => h0 _
    have hγ : ∀ r, 0 ≤ γ r := fun r => h0 _
    have hμ : ∀ k, 0 ≤ μ k := fun k => h0 _
    have hL : 0 ≤ ∑ r, lam r := Finset.sum_nonneg fun r _ => hlam r
    have S1 : ∑ k, μ k * (-α k + ∑ r, lam r * G r k + B) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hZk k, mul_zero]
    have S2 : ∑ r, lam r * (-γ r - ∑ k, μ k * G r k + D) = 0 :=
      Finset.sum_eq_zero fun r _ => by rw [hQr r, mul_zero]
    have E1 : ∑ k, μ k * (-α k + ∑ r, lam r * G r k + B) =
        -∑ k, μ k * α k + ∑ k, ∑ r, μ k * (lam r * G r k) + B * ∑ k, μ k := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
      congr 1; exact Finset.sum_congr rfl fun k _ => by ring
    have E2 : ∑ r, lam r * (-γ r - ∑ k, μ k * G r k + D) =
        -∑ r, lam r * γ r - ∑ r, ∑ k, lam r * (μ k * G r k) + D * ∑ r, lam r := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
        mul_neg, Finset.sum_neg_distrib]
      congr 1; exact Finset.sum_congr rfl fun k _ => by ring
    have E3 : ∑ k, ∑ r, μ k * (lam r * G r k) = ∑ r, ∑ k, lam r * (μ k * G r k) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => by ring
    have T1 : 0 ≤ ∑ k, μ k * α k := Finset.sum_nonneg fun k _ => mul_nonneg (hμ k) (hα k)
    have T2 : 0 ≤ ∑ r, lam r * γ r := Finset.sum_nonneg fun r _ => mul_nonneg (hlam r) (hγ r)
    have hBD : 0 ≤ (B + D) * ∑ r, lam r := by
      have : ∑ k, μ k = ∑ r, lam r := by linarith
      rw [this] at E1
      nlinarith
    rcases eq_or_lt_of_le hL with hL0 | hLpos
    · have hl0 : ∀ r, lam r = 0 := fun r =>
        (Finset.sum_eq_zero_iff_of_nonneg fun r _ => hlam r).1 hL0.symm r (Finset.mem_univ _)
      have hm0' : ∑ k, μ k = 0 := by linarith
      have hm0 : ∀ k, μ k = 0 := fun k =>
        (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hμ k).1 hm0' k (Finset.mem_univ _)
      obtain ⟨k0⟩ := (inferInstance : Nonempty κ)
      obtain ⟨r0⟩ := (inferInstance : Nonempty ι)
      have a1 := hZk k0
      have a2 := hQr r0
      simp only [hl0, hm0, zero_mul, Finset.sum_const_zero] at a1 a2
      have := hα k0
      have := hγ r0
      linarith
    · have : 0 ≤ B + D := nonneg_of_mul_nonneg_left hBD hLpos
      linarith

end minimax


section assembly
variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (M : ℝ)

lemma col_decode {Z : (Fin m ⊕ Fin n) ⊕ Unit → ℝ} {v : ℝ}
    (h : 0 ≤ Z ∧ ∑ s, Z s = 1 ∧ extGame A b c M *ᵥ Z ≤ fun _ => v) :
    (∀ i, 0 ≤ Z (.inl (.inl i))) ∧ (∀ j, 0 ≤ Z (.inl (.inr j))) ∧ 0 ≤ Z (.inr ()) ∧
    ∑ i, Z (.inl (.inl i)) + ∑ j, Z (.inl (.inr j)) + Z (.inr ()) = 1 ∧
    (∀ i, (A *ᵥ fun j => Z (.inl (.inr j))) i - b i * Z (.inr ()) ≤ v) ∧
    (∀ j, -(Aᵀ *ᵥ fun i => Z (.inl (.inl i))) j + c j * Z (.inr ()) ≤ v) ∧
    b ⬝ᵥ (fun i => Z (.inl (.inl i))) - c ⬝ᵥ (fun j => Z (.inl (.inr j))) ≤ v ∧
    ∑ i, Z (.inl (.inl i)) + ∑ j, Z (.inl (.inr j)) - M * Z (.inr ()) ≤ v := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨fun i => h0 _, fun j => h0 _, h0 _, ?_, fun i => ?_, fun j => ?_, ?_, ?_⟩
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h1; simpa using h1
  · have := h2 (.inl (.inl (.inl i))); rw [gz1] at this; exact this
  · have := h2 (.inl (.inl (.inr j))); rw [gz2] at this; exact this
  · have := h2 (.inl (.inr ())); rw [gz3] at this; exact this
  · have := h2 (.inr ()); rw [gz4] at this; exact this

lemma row_decode {Q : ((Fin m ⊕ Fin n) ⊕ Unit) ⊕ Unit → ℝ} {u : ℝ}
    (h : 0 ≤ Q ∧ ∑ s, Q s = 1 ∧ (fun _ => u) ≤ Q ᵥ* extGame A b c M) :
    (∀ i, 0 ≤ Q (.inl (.inl (.inl i)))) ∧ (∀ j, 0 ≤ Q (.inl (.inl (.inr j)))) ∧
    0 ≤ Q (.inl (.inr ())) ∧ 0 ≤ Q (.inr ()) ∧
    ∑ i, Q (.inl (.inl (.inl i))) + ∑ j, Q (.inl (.inl (.inr j))) + Q (.inl (.inr ()))
      + Q (.inr ()) = 1 ∧
    (∀ i, u ≤ -(A *ᵥ fun j => Q (.inl (.inl (.inr j)))) i + b i * Q (.inl (.inr ()))
      + Q (.inr ())) ∧
    (∀ j, u ≤ (Aᵀ *ᵥ fun i => Q (.inl (.inl (.inl i)))) j - c j * Q (.inl (.inr ()))
      + Q (.inr ())) ∧
    u ≤ -(b ⬝ᵥ fun i => Q (.inl (.inl (.inl i)))) + c ⬝ᵥ (fun j => Q (.inl (.inl (.inr j))))
      - M * Q (.inr ()) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨fun i => h0 _, fun j => h0 _, h0 _, h0 _, ?_, fun i => ?_, fun j => ?_, ?_⟩
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at h1; simpa using h1
  · have := h2 (.inl (.inl i)); rw [qg1] at this; exact this
  · have := h2 (.inl (.inr j)); rw [qg2] at this; exact this
  · have := h2 (.inr ()); rw [qg3] at this; exact this

lemma pf_iff (x : Fin n → ℝ) : PrimalFeasible A b x ↔ (∀ j, 0 ≤ x j) ∧ ∀ i, (A *ᵥ x) i ≤ b i := by
  simp only [PrimalFeasible, primalSlack, Pi.sub_apply, sub_nonneg]

lemma df_iff (y : Fin m → ℝ) : DualFeasible A c y ↔ (∀ i, 0 ≤ y i) ∧ ∀ j, c j ≤ (Aᵀ *ᵥ y) j := by
  simp only [DualFeasible, dualSlack, Pi.sub_apply, sub_nonneg]

lemma lp_weak {x : Fin n → ℝ} {y : Fin m → ℝ} (hx : PrimalFeasible A b x)
    (hy : DualFeasible A c y) : c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  rw [pf_iff] at hx; rw [df_iff] at hy
  have h1 : x ⬝ᵥ c ≤ x ⬝ᵥ (Aᵀ *ᵥ y) := dle hy.2 hx.1
  have h2 : y ⬝ᵥ (A *ᵥ x) ≤ y ⬝ᵥ b := dle hx.2 hy.1
  have k := key A y x
  rw [dotProduct_comm x c] at h1; rw [dotProduct_comm y b] at h2; linarith

lemma cert_infeas (x' : Fin n → ℝ) (y' : Fin m → ℝ) (h1 : ∀ i, (A *ᵥ x') i ≤ 0)
    (hx' : ∀ j, 0 ≤ x' j) (h2 : ∀ j, 0 ≤ (Aᵀ *ᵥ y') j) (hy' : ∀ i, 0 ≤ y' i)
    (h3 : b ⬝ᵥ y' - c ⬝ᵥ x' < 0) :
    ¬((∃ x, PrimalFeasible A b x) ∧ ∃ y, DualFeasible A c y) := by
  rintro ⟨⟨x1, hx1⟩, ⟨y1, hy1⟩⟩
  rw [pf_iff] at hx1; rw [df_iff] at hy1
  have a1 : y' ⬝ᵥ (A *ᵥ x1) ≤ y' ⬝ᵥ b := dle hx1.2 hy'
  have a2 : 0 ≤ x1 ⬝ᵥ (Aᵀ *ᵥ y') := dot_nonneg' hx1.1 h2
  have a3 : x' ⬝ᵥ c ≤ x' ⬝ᵥ (Aᵀ *ᵥ y1) := dle hy1.2 hx'
  have a4 : y1 ⬝ᵥ (A *ᵥ x') ≤ y1 ⬝ᵥ (fun _ => (0:ℝ)) := dle h1 hy1.1
  rw [dot_const, zero_mul] at a4
  have k1 := key A y' x1
  have k2 := key A y1 x'
  rw [dotProduct_comm y' b] at a1; rw [dotProduct_comm x' c] at a3
  linarith

lemma val_nonneg (y : Fin m → ℝ) (x : Fin n → ℝ) (t v : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hx : ∀ j, 0 ≤ x j) (ht : 0 ≤ t)
    (hsum : ∑ i, y i + ∑ j, x j + t = 1)
    (r1 : ∀ i, (A *ᵥ x) i - b i * t ≤ v) (r2 : ∀ j, -(Aᵀ *ᵥ y) j + c j * t ≤ v)
    (r3 : b ⬝ᵥ y - c ⬝ᵥ x ≤ v) : 0 ≤ v := by
  have Q1 : y ⬝ᵥ (fun i => (A *ᵥ x) i - b i * t) ≤ v * ∑ i, y i := by
    have := dle (w := y) r1 hy; rwa [dot_const] at this
  have Q2 : x ⬝ᵥ (fun j => -(Aᵀ *ᵥ y) j + c j * t) ≤ v * ∑ j, x j := by
    have := dle (w := x) r2 hx; rwa [dot_const] at this
  rw [dot_sub_smul] at Q1
  rw [dot_neg_add_smul] at Q2
  have Q3 : t * (b ⬝ᵥ y - c ⬝ᵥ x) ≤ t * v := mul_le_mul_of_nonneg_left r3 ht
  have k := key A y x
  have e : v * ∑ i, y i + v * ∑ j, x j + t * v = v := by linear_combination v * hsum
  linarith [show t * (b ⬝ᵥ y - c ⬝ᵥ x) = t * (b ⬝ᵥ y) - t * (c ⬝ᵥ x) by ring]

lemma zero_case (hM : 1 ≤ M) (y : Fin m → ℝ) (x : Fin n → ℝ) (t : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hx : ∀ j, 0 ≤ x j) (ht : 0 ≤ t)
    (hsum : ∑ i, y i + ∑ j, x j + t = 1)
    (r1 : ∀ i, (A *ᵥ x) i - b i * t ≤ 0) (r2 : ∀ j, -(Aᵀ *ᵥ y) j + c j * t ≤ 0)
    (r3 : b ⬝ᵥ y - c ⬝ᵥ x ≤ 0) (r4 : ∑ i, y i + ∑ j, x j - M * t ≤ 0) :
    0 < t ∧ PrimalFeasible A b (fun j => x j / t) ∧ DualFeasible A c (fun i => y i / t) ∧
      b ⬝ᵥ (fun i => y i / t) ≤ c ⬝ᵥ (fun j => x j / t) := by
  have htp : 0 < t := by
    by_contra h0
    have h : t = 0 := le_antisymm (not_lt.1 h0) ht
    rw [h] at hsum r4; linarith
  refine ⟨htp, (pf_iff A b _).2 ⟨fun j => div_nonneg (hx j) ht, fun i => ?_⟩,
    (df_iff A c _).2 ⟨fun i => div_nonneg (hy i) ht, fun j => ?_⟩, ?_⟩
  · rw [mulVec_div, div_le_iff₀ htp]; linarith [r1 i]
  · rw [mulVec_div, le_div_iff₀ htp]; linarith [r2 j]
  · rw [dot_div, dot_div, div_le_div_iff_of_pos_right htp]; linarith

lemma feas58_of (x : Fin n → ℝ) (y : Fin m → ℝ) (hx : PrimalFeasible A b x)
    (hy : DualFeasible A c y) (h : b ⬝ᵥ y ≤ c ⬝ᵥ x) : Feas58 A b c x y 0 := by
  rw [pf_iff] at hx; rw [df_iff] at hy
  exact ⟨fun i => by linarith [hx.2 i], hx.1, fun j => by linarith [hy.2 j], hy.1,
    by linarith, le_refl 0⟩

set_option maxHeartbeats 1000000 in
theorem suitable (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (w0 : ℝ) (hf : Feas58 A b c x0 y0 w0)
    (hopt : ∀ x y w, Feas58 A b c x y w → w0 ≤ w) (hM : ∑ j, x0 j + ∑ i, y0 i + 1 ≤ M) :
    IsSuitableM A b c M := by
  obtain ⟨Zs, vs, Qs, hZs, hQs⟩ := minimax (extGame A b c M)
  have hx0 : 0 ≤ ∑ j, x0 j := Finset.sum_nonneg fun j _ => hf.2.1 j
  have hy0 : 0 ≤ ∑ i, y0 i := Finset.sum_nonneg fun i _ => hf.2.2.2.1 i
  have hM1 : 1 ≤ M := by linarith
  obtain ⟨zy, zx, zt, zs, zr1, zr2, zr3, zr4⟩ := col_decode A b c M hZs.1
  obtain ⟨qy, qx, qr, qs, qsum, qc1, qc2, qc3⟩ := row_decode A b c M hQs.1
  have hvs0 : 0 ≤ vs := val_nonneg A b c _ _ _ _ zy zx zt zs zr1 zr2 zr3
  have hcore := fun hv : 0 < vs => core_b A b c M x0 y0 w0 hf hopt hM _ _ _ _ zy zx zt zs zr1 zr2
    zr3 zr4 _ _ _ _ qy qx qr qs qsum qc1 qc2 qc3 hv
  have hnf : 0 < vs → ¬((∃ x, PrimalFeasible A b x) ∧ ∃ y, DualFeasible A c y) := fun hv => by
    obtain ⟨_, _, _, h1, h2, h3, _⟩ := hcore hv
    exact cert_infeas A b c _ _ h1 qx h2 qy h3
  have hzero : ∀ z : (Fin m ⊕ Fin n) ⊕ Unit → ℝ, IsMinMaxStrategy (extGame A b c M) z 0 →
      0 < z (.inr ()) ∧ PrimalFeasible A b (fun j => z (.inl (.inr j)) / z (.inr ())) ∧
      DualFeasible A c (fun i => z (.inl (.inl i)) / z (.inr ())) ∧
      b ⬝ᵥ (fun i => z (.inl (.inl i)) / z (.inr ())) ≤
        c ⬝ᵥ (fun j => z (.inl (.inr j)) / z (.inr ())) := fun z hz => by
    obtain ⟨y1, x1, t1, s1, r1, r2, r3, r4⟩ := col_decode A b c M hz.1
    exact zero_case A b c M hM1 _ _ _ y1 x1 t1 s1 r1 r2 r3 r4
  have hfeas0 : ((∃ x, PrimalFeasible A b x) ∧ ∃ y, DualFeasible A c y) → vs = 0 := fun h => by
    rcases eq_or_lt_of_le hvs0 with h0 | h0
    · exact h0.symm
    · exact absurd h (hnf h0)
  have hw00 : vs = 0 → w0 = 0 := fun h0 => by
    rw [h0] at hZs
    obtain ⟨ht, hpf, hdf, hle⟩ := hzero Zs hZs
    have := hopt _ _ _ (feas58_of A b c _ _ hpf hdf hle)
    linarith [hf.2.2.2.2.2]
  refine ⟨fun h => ?_, ⟨vs, Zs, hZs⟩, fun v ⟨Z, hZ⟩ => ?_⟩
  · have hw : w0 = 0 := hw00 (hfeas0 h)
    refine ⟨x0, y0, (pf_iff A b _).2 ⟨hf.2.1, fun i => ?_⟩, (df_iff A c _).2 ⟨hf.2.2.2.1, fun j => ?_⟩,
      hM⟩
    · have := hf.1 i; rw [hw] at this; linarith
    · have := hf.2.2.1 j; rw [hw] at this; linarith
  have hv : vs = v := value_unique _ hZs hZ
  subst hv
  refine ⟨hvs0, ⟨fun h0 => ?_, hfeas0⟩, fun h0 z hz => ?_, fun hv => ?_⟩
  · rw [h0] at hZs
    obtain ⟨_, hpf, hdf, _⟩ := hzero Zs hZs
    exact ⟨⟨_, hpf⟩, ⟨_, hdf⟩⟩
  · obtain ⟨ht, hpf, hdf, hle⟩ := hzero z hz
    obtain ⟨y1, x1, t1, s1, r1, r2, r3, r4⟩ := col_decode A b c M hz.1
    refine ⟨⟨⟨fun k => ?_, ?_, fun k => ?_⟩, fun Q' u' h => ?_⟩, ht, ⟨hpf, fun x' hx' => ?_⟩,
      ⟨hdf, fun y' hy' => ?_⟩⟩
    · rcases k with k | k
      · exact hz.1.1 k
      · exact le_refl _
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero]
      exact hz.1.2.1
    · rcases k with (i | j) | ⟨⟩
      · show (0:ℝ) ≤ ((Sum.elim z fun _ => 0) ᵥ* extGame A b c M) (.inl (.inl i))
        rw [qg1]; simp only [Sum.elim_inl, Sum.elim_inr]; linarith [r1 i]
      · show (0:ℝ) ≤ ((Sum.elim z fun _ => 0) ᵥ* extGame A b c M) (.inl (.inr j))
        rw [qg2]; simp only [Sum.elim_inl, Sum.elim_inr]; linarith [r2 j]
      · show (0:ℝ) ≤ ((Sum.elim z fun _ => 0) ᵥ* extGame A b c M) (.inr ())
        rw [qg3]; simp only [Sum.elim_inl, Sum.elim_inr]; linarith
    · exact weak_game _ z 0 Q' u' hz.1.1 hz.1.2.1 hz.1.2.2 h.1 h.2.1 h.2.2
    · exact le_trans (lp_weak A b c hx' hdf) hle
    · exact le_trans hle (lp_weak A b c hpf hy')
  · obtain ⟨_, _, hv1, hcx, hcy, hneg, hw0⟩ := hcore hv
    refine ⟨hv1, hnf hv, fun q u hq => ?_, ?_⟩
    · have hu1 : u ≤ vs :=
        weak_game _ Zs vs q u hZs.1.1 hZs.1.2.1 hZs.1.2.2 hq.1.1 hq.1.2.1 hq.1.2.2
      have hu2 : vs ≤ u := hq.2 Qs vs hQs.1
      have hu : u = vs := le_antisymm hu1 hu2
      subst hu
      obtain ⟨py, px, pr, ps, psum, pc1, pc2, pc3⟩ := row_decode A b c M hq.1
      obtain ⟨e1, e2, _, h1, h2, h3, _⟩ := core_b A b c M x0 y0 w0 hf hopt hM _ _ _ _ zy zx zt zs
        zr1 zr2 zr3 zr4 _ _ _ _ py px pr ps psum pc1 pc2 pc3 hv
      exact ⟨e1, e2, fun i => by simpa using h1 i, fun j => px j, fun j => by simpa using h2 j,
        fun i => py i, h3⟩
    · rw [← hw0]
      refine ⟨⟨x0, y0, fun i => ?_, fun j => hf.2.1 j, fun j => ?_, fun i => hf.2.2.2.1 i⟩, ?_⟩
      · simp only [Pi.add_apply]; exact hf.1 i
      · simp only [Pi.add_apply, Pi.neg_apply]; linarith [hf.2.2.1 j]
      rintro w ⟨xb, yb, h1, h2, h3, h4⟩
      have h1' : ∀ i, (A *ᵥ xb) i ≤ b i + w := fun i => by simpa using h1 i
      have h3' : ∀ j, c j - w ≤ (Aᵀ *ᵥ yb) j := fun j => by
        have := h3 j; simp only [Pi.add_apply, Pi.neg_apply] at this; linarith
      have hw : 0 ≤ w := by
        by_contra hneg'
        push_neg at hneg'
        apply hnf hv
        refine ⟨⟨xb, (pf_iff A b _).2 ⟨fun j => h2 j, fun i => ?_⟩⟩,
          ⟨yb, (df_iff A c _).2 ⟨fun i => h4 i, fun j => ?_⟩⟩⟩
        · linarith [h1' i]
        · linarith [h3' j]
      set x' : Fin n → ℝ := fun j => Qs (.inl (.inl (.inr j)))
      set y' : Fin m → ℝ := fun i => Qs (.inl (.inl (.inl i)))
      have hg : 0 < c ⬝ᵥ x' - b ⬝ᵥ y' := by linarith
      set D := b ⬝ᵥ yb - c ⬝ᵥ xb - w
      set lam := max 0 (D / (c ⬝ᵥ x' - b ⬝ᵥ y'))
      have hl0 : 0 ≤ lam := le_max_left _ _
      have hlD : D ≤ lam * (c ⬝ᵥ x' - b ⬝ᵥ y') := (div_le_iff₀ hg).1 (le_max_right _ _)
      apply hopt (xb + lam • x') (yb + lam • y') w
      refine ⟨fun i => ?_, fun j => ?_, fun j => ?_, fun i => ?_, ?_, hw⟩
      · rw [mulVec_add, mulVec_smul]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := mul_le_mul_of_nonneg_left (hcx i) hl0
        linarith [h1' i]
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (h2 j) (mul_nonneg hl0 (qx j))
      · rw [mulVec_add, mulVec_smul]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := mul_nonneg hl0 (hcy j)
        linarith [h3' j]
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (h4 i) (mul_nonneg hl0 (qy i))
      · rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
          smul_eq_mul]
        linarith [show lam * (c ⬝ᵥ x' - b ⬝ᵥ y') = lam * (c ⬝ᵥ x') - lam * (b ⬝ᵥ y') by ring]

end assembly


section eqform
variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable (E : Matrix ι κ ℝ) (r : ι → ℝ) (d : κ → ℝ)

/-- Feasibility for the equality-form LP `E u = r`, `u ≥ 0`. -/
def Feq (u : κ → ℝ) : Prop := E *ᵥ u = r ∧ ∀ k, 0 ≤ u k

/-- A basic solution: the columns of `E` on the support of `u` are linearly independent. -/
def Basic (u : κ → ℝ) : Prop := LinearIndependent ℝ (fun k : {k // u k ≠ 0} => fun i => E i k)

lemma sum_supp (u : κ → ℝ) (f : κ → ℝ) (hf : ∀ k, u k = 0 → f k = 0) :
    ∑ k, f k = ∑ s : {k // u k ≠ 0}, f s := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => u k ≠ 0) f]
  have h2 : ∑ k : {k // ¬ u k ≠ 0}, f k = 0 :=
    Finset.sum_eq_zero fun k _ => hf k (not_not.1 k.2)
  rw [h2, add_zero]

lemma kernel_dir (u : κ → ℝ) (hnb : ¬ Basic E u) :
    ∃ g : κ → ℝ, E *ᵥ g = 0 ∧ (∃ k, g k ≠ 0) ∧ ∀ k, u k = 0 → g k = 0 := by
  classical
  rw [Basic, Fintype.not_linearIndependent_iff] at hnb
  obtain ⟨g, hg, k0, hk0⟩ := hnb
  refine ⟨fun k => if h : u k ≠ 0 then g ⟨k, h⟩ else 0, ?_, ⟨k0.1, by simp [k0.2, hk0]⟩,
    fun k hk => by simp [hk]⟩
  ext i
  have := congr_fun hg i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  simp only [mulVec, dotProduct, Pi.zero_apply]
  rw [sum_supp u _ (fun k hk => by simp [hk])]
  refine Eq.trans (Finset.sum_congr rfl fun s _ => ?_) this
  rw [dif_pos s.2, mul_comm]

lemma unb (L : ℝ) (hb : ∀ u, Feq E r u → L ≤ d ⬝ᵥ u) (u : κ → ℝ) (hu : Feq E r u)
    (dd : κ → ℝ) (hdd : E *ᵥ dd = 0) (hpos : 0 < d ⬝ᵥ dd) : ∃ k, 0 < dd k := by
  by_contra hcon
  push_neg at hcon
  have hL := hb u hu
  set lam := (d ⬝ᵥ u - L + 1) / (d ⬝ᵥ dd) with hlam
  have hl0 : 0 ≤ lam := div_nonneg (by linarith) hpos.le
  have hfe : Feq E r (u - lam • dd) := by
    refine ⟨by rw [mulVec_sub, mulVec_smul, hdd, smul_zero, sub_zero]; exact hu.1, fun k => ?_⟩
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have := mul_nonpos_of_nonneg_of_nonpos hl0 (hcon k)
    linarith [hu.2 k]
  have h1 := hb _ hfe
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hlam, div_mul_cancel₀ _ hpos.ne'] at h1
  linarith

set_option maxHeartbeats 1000000 in
lemma reduce (L : ℝ) (hb : ∀ u, Feq E r u → L ≤ d ⬝ᵥ u) :
    ∀ (N : ℕ) (u : κ → ℝ), (Finset.univ.filter fun k => u k ≠ 0).card ≤ N → Feq E r u →
      ∃ u', Feq E r u' ∧ d ⬝ᵥ u' ≤ d ⬝ᵥ u ∧ Basic E u' := by
  classical
  intro N
  induction N with
  | zero =>
    intro u hc hu
    refine ⟨u, hu, le_refl _, ?_⟩
    have he : ∀ k, u k = 0 := fun k => by
      by_contra h
      have : k ∈ Finset.univ.filter fun k => u k ≠ 0 := by simp [h]
      have := Finset.card_pos.2 ⟨k, this⟩
      omega
    have : IsEmpty {k // u k ≠ 0} := ⟨fun s => s.2 (he s.1)⟩
    exact linearIndependent_empty_type
  | succ N ih =>
    intro u hc hu
    by_cases hB : Basic E u
    · exact ⟨u, hu, le_refl _, hB⟩
    obtain ⟨g, hg, ⟨k1, hk1⟩, hgs⟩ := kernel_dir E u hB
    obtain ⟨dd, hdd, hddpos, hdds, hdd0⟩ : ∃ dd : κ → ℝ, E *ᵥ dd = 0 ∧ (∃ k, 0 < dd k) ∧
        (∀ k, u k = 0 → dd k = 0) ∧ 0 ≤ d ⬝ᵥ dd := by
      have hng : E *ᵥ (-g) = 0 := by rw [mulVec_neg, hg, neg_zero]
      rcases lt_trichotomy (d ⬝ᵥ g) 0 with h | h | h
      · have hp : 0 < d ⬝ᵥ (-g) := by rw [dotProduct_neg]; linarith
        exact ⟨-g, hng, unb E r d L hb u hu _ hng hp, fun k hk => by simp [hgs k hk], hp.le⟩
      · rcases lt_or_gt_of_ne hk1 with h1 | h1
        · exact ⟨-g, hng, ⟨k1, by simp; linarith⟩, fun k hk => by simp [hgs k hk],
            by rw [dotProduct_neg, h, neg_zero]⟩
        · exact ⟨g, hg, ⟨k1, h1⟩, hgs, h.ge⟩
      · exact ⟨g, hg, unb E r d L hb u hu _ hg h, hgs, h.le⟩
    obtain ⟨kp, hkp⟩ := hddpos
    have hJ : (Finset.univ.filter fun k => 0 < dd k).Nonempty := ⟨kp, by simp [hkp]⟩
    obtain ⟨k0, hk0J, hk0min⟩ := Finset.exists_min_image _ (fun k => u k / dd k) hJ
    have hk0 : 0 < dd k0 := by simpa using hk0J
    set θ := u k0 / dd k0 with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (hu.2 k0) hk0.le
    have hfe : Feq E r (u - θ • dd) := by
      refine ⟨by rw [mulVec_sub, mulVec_smul, hdd, smul_zero, sub_zero]; exact hu.1, fun k => ?_⟩
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rcases le_or_gt (dd k) 0 with h | h
      · have := mul_nonpos_of_nonneg_of_nonpos hθ0 h
        linarith [hu.2 k]
      · have h2 : θ ≤ u k / dd k := hk0min k (by simp [h])
        rw [le_div_iff₀ h] at h2
        linarith
    have hobj : d ⬝ᵥ (u - θ • dd) ≤ d ⬝ᵥ u := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
      have := mul_nonneg hθ0 hdd0
      linarith
    have hsub : (Finset.univ.filter fun k => (u - θ • dd) k ≠ 0) ⊂
        Finset.univ.filter fun k => u k ≠ 0 := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨k0, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro h0
          have := hdds k0 h0
          linarith
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Pi.smul_apply,
            smul_eq_mul, not_not]
          rw [hθ, div_mul_cancel₀ _ hk0.ne', sub_self]
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul] at hk ⊢
        intro h0
        apply hk
        rw [h0, hdds k h0, mul_zero, sub_zero]
    have hcard := Finset.card_lt_card hsub
    obtain ⟨u', h1, h2, h3⟩ := ih (u - θ • dd) (by omega) hfe
    exact ⟨u', h1, le_trans h2 hobj, h3⟩

lemma basic_unique {u u' : κ → ℝ} (hu : Feq E r u) (hu' : Feq E r u') (hB : Basic E u)
    (hs : ∀ k, u k = 0 ↔ u' k = 0) : u = u' := by
  have key : ∀ s : {k // u k ≠ 0}, u s - u' s = 0 := by
    have := (Fintype.linearIndependent_iff.1 hB) (fun s => u s - u' s)
    apply this
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have e1 := congr_fun hu.1 i
    have e2 := congr_fun hu'.1 i
    simp only [mulVec, dotProduct] at e1 e2
    have e3 : ∑ k, E i k * (u k - u' k) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]; rw [e1, e2, sub_self]
    rw [sum_supp u _ (fun k hk => by rw [hk, (hs k).1 hk, sub_self, mul_zero])] at e3
    exact Eq.trans (Finset.sum_congr rfl fun s _ => mul_comm _ _) e3
  funext k
  by_cases h : u k = 0
  · rw [h, ((hs k).1 h)]
  · exact sub_eq_zero.1 (key ⟨k, h⟩)

lemma attain (L : ℝ) (hb : ∀ u, Feq E r u → L ≤ d ⬝ᵥ u) (hne : ∃ u, Feq E r u) :
    ∃ u, Feq E r u ∧ Basic E u ∧ ∀ u', Feq E r u' → d ⬝ᵥ u ≤ d ⬝ᵥ u' := by
  classical
  let S : Set (κ → ℝ) := {u | Feq E r u ∧ Basic E u}
  let pick : Finset κ → (κ → ℝ) := fun T =>
    if h : ∃ u ∈ S, (Finset.univ.filter fun k => u k ≠ 0) = T then h.choose else 0
  have hfin : S.Finite := by
    refine (Set.finite_range pick).subset fun u hu => ⟨Finset.univ.filter fun k => u k ≠ 0, ?_⟩
    have h : ∃ v ∈ S, (Finset.univ.filter fun k => v k ≠ 0) =
        Finset.univ.filter fun k => u k ≠ 0 := ⟨u, hu, rfl⟩
    simp only [pick, dif_pos h]
    obtain ⟨hv, hvs⟩ := h.choose_spec
    refine (basic_unique E r hv.1 hu.1 hv.2 fun k => ?_)
    have := congr_arg (fun T => k ∈ T) hvs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    exact not_iff_not.mp this
  obtain ⟨u0, hu0⟩ := hne
  obtain ⟨u1, hu1, -, hB1⟩ := reduce E r d L hb _ u0 le_rfl hu0
  obtain ⟨us, hus, hmin⟩ := Set.exists_min_image S (fun u => d ⬝ᵥ u) hfin ⟨u1, hu1, hB1⟩
  refine ⟨us, hus.1, hus.2, fun u' hu' => ?_⟩
  obtain ⟨u2, hu2, hle, hB2⟩ := reduce E r d L hb _ u' le_rfl hu'
  exact le_trans (hmin u2 ⟨hu2, hB2⟩) hle

end eqform


section inst58
variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)

/-- (58) in equality form: variables `(y, x, w)` and one slack per row. -/
def E58 : Matrix ((Fin m ⊕ Fin n) ⊕ Unit) (((Fin m ⊕ Fin n) ⊕ Unit) ⊕ ((Fin m ⊕ Fin n) ⊕ Unit)) ℝ
  | ρ, .inr k => if k = ρ then 1 else 0
  | .inl (.inl _), .inl (.inl (.inl _)) => 0
  | .inl (.inl i), .inl (.inl (.inr j)) => A i j
  | .inl (.inl _), .inl (.inr _) => -1
  | .inl (.inr j), .inl (.inl (.inl i)) => -A i j
  | .inl (.inr _), .inl (.inl (.inr _)) => 0
  | .inl (.inr _), .inl (.inr _) => -1
  | .inr _, .inl (.inl (.inl i)) => b i
  | .inr _, .inl (.inl (.inr j)) => -c j
  | .inr _, .inl (.inr _) => -1

def r58 : (Fin m ⊕ Fin n) ⊕ Unit → ℝ := Sum.elim (Sum.elim b fun j => -c j) fun _ => 0

def d58 : ((Fin m ⊕ Fin n) ⊕ Unit) ⊕ ((Fin m ⊕ Fin n) ⊕ Unit) → ℝ :=
  Sum.elim (Sum.elim 0 fun _ => 1) 0

variable (u : ((Fin m ⊕ Fin n) ⊕ Unit) ⊕ ((Fin m ⊕ Fin n) ⊕ Unit) → ℝ)

lemma e58_1 (i : Fin m) : (E58 A b c *ᵥ u) (.inl (.inl i)) =
    (A *ᵥ fun j => u (.inl (.inl (.inr j)))) i - u (.inl (.inr ())) + u (.inr (.inl (.inl i))) := by
  simp [E58, mulVec, dotProduct, Fintype.sum_sum_type]; ring

lemma e58_2 (j : Fin n) : (E58 A b c *ᵥ u) (.inl (.inr j)) =
    -(Aᵀ *ᵥ fun i => u (.inl (.inl (.inl i)))) j - u (.inl (.inr ())) + u (.inr (.inl (.inr j))) := by
  simp [E58, mulVec, dotProduct, Fintype.sum_sum_type]; ring

lemma e58_3 : (E58 A b c *ᵥ u) (.inr ()) =
    b ⬝ᵥ (fun i => u (.inl (.inl (.inl i)))) - c ⬝ᵥ (fun j => u (.inl (.inl (.inr j))))
      - u (.inl (.inr ())) + u (.inr (.inr ())) := by
  simp [E58, mulVec, dotProduct, Fintype.sum_sum_type]; ring

lemma d58_dot : d58 ⬝ᵥ u = u (.inl (.inr ())) := by
  simp [d58, dotProduct, Fintype.sum_sum_type]

lemma feq_to58 (hu : Feq (E58 A b c) (r58 b c) u) :
    Feas58 A b c (fun j => u (.inl (.inl (.inr j)))) (fun i => u (.inl (.inl (.inl i))))
      (u (.inl (.inr ()))) := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨fun i => ?_, fun j => h2 _, fun j => ?_, fun i => h2 _, ?_, h2 _⟩
  · have := congr_fun h1 (.inl (.inl i)); rw [e58_1] at this
    simp only [r58, Sum.elim_inl] at this; linarith [h2 (.inr (.inl (.inl i)))]
  · have := congr_fun h1 (.inl (.inr j)); rw [e58_2] at this
    simp only [r58, Sum.elim_inl, Sum.elim_inr] at this; linarith [h2 (.inr (.inl (.inr j)))]
  · have := congr_fun h1 (.inr ()); rw [e58_3] at this
    simp only [r58, Sum.elim_inr] at this; linarith [h2 (.inr (.inr ()))]

/-- The equality-form point of a solution of (58). -/
def lift58 (x : Fin n → ℝ) (y : Fin m → ℝ) (w : ℝ) :
    ((Fin m ⊕ Fin n) ⊕ Unit) ⊕ ((Fin m ⊕ Fin n) ⊕ Unit) → ℝ :=
  Sum.elim (Sum.elim (Sum.elim y x) fun _ => w)
    (Sum.elim (Sum.elim (fun i => b i + w - (A *ᵥ x) i) (fun j => (Aᵀ *ᵥ y) j - c j + w))
      fun _ => w - (b ⬝ᵥ y - c ⬝ᵥ x))

lemma feq_of58 (x : Fin n → ℝ) (y : Fin m → ℝ) (w : ℝ) (h : Feas58 A b c x y w) :
    Feq (E58 A b c) (r58 b c) (lift58 A b c x y w) := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := h
  refine ⟨funext fun ρ => ?_, fun k => ?_⟩
  · rcases ρ with (i | j) | ⟨⟩
    · rw [e58_1]; simp only [lift58, Sum.elim_inl, Sum.elim_inr, r58]
      have e : (fun j => x j) = x := rfl
      rw [e]; ring
    · rw [e58_2]; simp only [lift58, Sum.elim_inl, Sum.elim_inr, r58]
      have e : (fun i => y i) = y := rfl
      rw [e]; ring
    · rw [e58_3]; simp only [lift58, Sum.elim_inl, Sum.elim_inr, r58]
      have e : (fun i => y i) = y := rfl
      have e' : (fun j => x j) = x := rfl
      rw [e, e']; ring
  · rcases k with ((i | j) | ⟨⟩) | ((i | j) | ⟨⟩)
    · exact f4 i
    · exact f2 j
    · exact f6
    · simp only [lift58, Sum.elim_inl, Sum.elim_inr]; linarith [f1 i]
    · simp only [lift58, Sum.elim_inl, Sum.elim_inr]; linarith [f3 j]
    · simp only [lift58, Sum.elim_inl, Sum.elim_inr]; linarith

lemma lift58_w (x : Fin n → ℝ) (y : Fin m → ℝ) (w : ℝ) :
    d58 ⬝ᵥ lift58 A b c x y w = w := by
  rw [d58_dot]; rfl

lemma feas58_nonempty : ∃ x y w, Feas58 A b c x y w := by
  refine ⟨0, 0, ∑ i, |b i| + ∑ j, |c j|, fun i => ?_, fun j => le_refl _, fun j => ?_,
    fun i => le_refl _, ?_, ?_⟩
  · have h1 : |b i| ≤ ∑ i, |b i| := Finset.single_le_sum (fun i _ => abs_nonneg (b i)) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ j, |c j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have h3 := neg_abs_le (b i)
    simp only [mulVec_zero, Pi.zero_apply]; linarith
  · have h1 : |c j| ≤ ∑ j, |c j| := Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ j)
    have h2 : 0 ≤ ∑ i, |b i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have h3 := le_abs_self (c j)
    simp only [mulVec_zero, Pi.zero_apply]; linarith
  · simp only [dotProduct_zero, sub_zero]
    exact add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.sum_nonneg fun j _ => abs_nonneg _)
  · exact add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.sum_nonneg fun j _ => abs_nonneg _)

/-- (58) attains its minimum at a basic solution of its equality form. -/
theorem attain58 : ∃ u, Feq (E58 A b c) (r58 b c) u ∧ Basic (E58 A b c) u ∧
    ∀ x y w, Feas58 A b c x y w → u (.inl (.inr ())) ≤ w := by
  have hb : ∀ u, Feq (E58 A b c) (r58 b c) u → (0:ℝ) ≤ d58 ⬝ᵥ u := fun u hu => by
    rw [d58_dot]; exact hu.2 _
  obtain ⟨x1, y1, w1, h1⟩ := feas58_nonempty A b c
  obtain ⟨u, hu, hB, hmin⟩ := attain (E58 A b c) (r58 b c) d58 0 hb ⟨_, feq_of58 A b c _ _ _ h1⟩
  refine ⟨u, hu, hB, fun x y w h => ?_⟩
  have := hmin _ (feq_of58 A b c x y w h)
  rwa [d58_dot, lift58_w] at this

theorem part1 : ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → IsSuitableM A b c M := by
  obtain ⟨u, hu, -, hmin⟩ := attain58 A b c
  refine ⟨∑ j, u (.inl (.inl (.inr j))) + ∑ i, u (.inl (.inl (.inl i))) + 1, fun M hM => ?_⟩
  exact suitable A b c M _ _ _ (feq_to58 A b c u hu) (fun x y w h => hmin x y w h) hM

end inst58


section cramer

lemma rat_abs_le (q : ℚ) : |(q : ℝ)| ≤ (q.num.natAbs : ℝ) := by
  rw [Rat.cast_def, abs_div, Nat.cast_natAbs]
  have h1 : (1 : ℝ) ≤ |((q.den : ℤ) : ℝ)| := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast q.den_pos
  rw [Int.cast_abs]
  rw [show ((q.den : ℕ) : ℝ) = ((q.den : ℤ) : ℝ) by simp]
  exact div_le_self (abs_nonneg _) h1

lemma rat_det_lower {S : Type} [Fintype S] [DecidableEq S] (Bq : Matrix S S ℚ) (β : ℕ)
    (hβ : ∀ i j, (Bq i j).den ≤ β) (hdet : Bq.det ≠ 0) :
    1 ≤ |Bq.det| * (β : ℚ) ^ (Fintype.card S * Fintype.card S) := by
  classical
  let D : S → ℕ := fun i => ∏ j, (Bq i j).den
  have hDpos : ∀ i, 0 < D i := fun i => Finset.prod_pos fun j _ => (Bq i j).den_pos
  have hdvd : ∀ i j, (Bq i j).den ∣ D i := fun i j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  let Cz : Matrix S S ℤ := fun i j => ((D i / (Bq i j).den : ℕ) : ℤ) * (Bq i j).num
  have hC : Cz.map (Int.cast : ℤ → ℚ) = Matrix.of fun i j => (D i : ℚ) * Bq i j := by
    ext i j
    show ((Cz i j : ℤ) : ℚ) = (D i : ℚ) * Bq i j
    simp only [Cz, Int.cast_mul, Int.cast_natCast]
    have h1 : (D i : ℚ) = ((D i / (Bq i j).den : ℕ) : ℚ) * ((Bq i j).den : ℚ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (hdvd i j)]
    rw [h1, mul_assoc, Rat.den_mul_eq_num]
  have hdetC : (Matrix.of fun i j => (D i : ℚ) * Bq i j).det = (∏ i, (D i : ℚ)) * Bq.det :=
    Matrix.det_mul_column _ _
  have hz : ((Cz.det : ℤ) : ℚ) = (∏ i, (D i : ℚ)) * Bq.det := by
    rw [← hdetC, ← hC]
    have := RingHom.map_det (Int.castRingHom ℚ) Cz
    rw [RingHom.mapMatrix_apply] at this
    simpa using this
  have hprod_pos : (0 : ℚ) < ∏ i, (D i : ℚ) := Finset.prod_pos fun i _ => by exact_mod_cast hDpos i
  have hCz : Cz.det ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hz
    exact hdet ((mul_eq_zero.1 hz.symm).resolve_left hprod_pos.ne')
  have h1 : (1 : ℚ) ≤ |((Cz.det : ℤ) : ℚ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hCz
  rw [hz, abs_mul, abs_of_pos hprod_pos] at h1
  have hDle : ∀ i, D i ≤ β ^ Fintype.card S := fun i => by
    have := Finset.prod_le_pow_card (Finset.univ : Finset S) (fun j => (Bq i j).den) β
      (fun j _ => hβ i j)
    simpa [D] using this
  have hP : (∏ i, (D i : ℚ)) ≤ (β : ℚ) ^ (Fintype.card S * Fintype.card S) := by
    have := Finset.prod_le_pow_card (Finset.univ : Finset S) D (β ^ Fintype.card S)
      (fun i _ => hDle i)
    rw [Finset.card_univ, ← pow_mul] at this
    exact_mod_cast this
  nlinarith [abs_nonneg Bq.det]

lemma square_select {ι S : Type} [Fintype ι] [Fintype S] [DecidableEq S] (N : Matrix ι S ℝ)
    (hN : LinearIndependent ℝ (fun s => fun i => N i s)) :
    ∃ f : S → ι, (Matrix.of fun s' s => N (f s') s).det ≠ 0 := by
  classical
  have h1 : LinearIndependent ℝ Nᵀ.row := hN
  have hrk : N.rank = Fintype.card S := by rw [← Matrix.rank_transpose]; exact h1.rank_matrix
  obtain ⟨κ', a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ N.row
  have : Fintype κ' := Fintype.ofInjective a ha
  have hcard : Fintype.card κ' = Fintype.card S := by
    rw [linearIndependent_iff_card_eq_finrank_span.1 hli, Set.finrank, hspan,
      ← Matrix.rank_eq_finrank_span_row, hrk]
  let e : κ' ≃ S := Fintype.equivOfCardEq hcard
  refine ⟨fun s => a (e.symm s), ?_⟩
  have hli' : LinearIndependent ℝ (Matrix.of fun s' s => N (a (e.symm s')) s).row :=
    hli.comp e.symm e.symm.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hli')).ne_zero

end cramer


section bbound

lemma basic_bound {ι κ : Type} [Fintype ι] [Fintype κ]
    (E : Matrix ι κ ℝ) (r : ι → ℝ) (Eqq : Matrix ι κ ℚ) (rq : ι → ℚ)
    (hE : ∀ i k, E i k = (Eqq i k : ℝ)) (hr : ∀ i, r i = (rq i : ℝ)) (α β : ℕ)
    (hα1 : 1 ≤ α) (hβ1 : 1 ≤ β)
    (hα : ∀ i k, (Eqq i k).num.natAbs ≤ α) (hαr : ∀ i, (rq i).num.natAbs ≤ α)
    (hβ : ∀ i k, (Eqq i k).den ≤ β)
    (u : κ → ℝ) (hu : Feq E r u) (hB : Basic E u) :
    ∑ k, u k ≤ ((Fintype.card ι * (Fintype.card ι).factorial * α ^ Fintype.card ι *
      β ^ (Fintype.card ι * Fintype.card ι) : ℕ) : ℝ) := by
  classical
  let S := {k // u k ≠ 0}
  obtain ⟨f, hf⟩ := square_select (fun i (s : S) => E i s) hB
  let B : Matrix S S ℝ := Matrix.of fun s' s => E (f s') s
  let Bq : Matrix S S ℚ := Matrix.of fun s' s => Eqq (f s') s
  have hf' : B.det ≠ 0 := hf
  have hBq : B = Bq.map (Rat.cast : ℚ → ℝ) := by
    ext s' s; simp [B, Bq, hE]
  have hdetq : B.det = ((Bq.det : ℚ) : ℝ) := by
    rw [hBq]
    have := RingHom.map_det (Rat.castHom ℝ) Bq
    rw [RingHom.mapMatrix_apply] at this
    simpa using this.symm
  have hBqne : Bq.det ≠ 0 := by
    intro h; apply hf'; rw [hdetq, h, Rat.cast_zero]
  have hlow : (1:ℝ) ≤ |B.det| * (β:ℝ) ^ (Fintype.card S * Fintype.card S) := by
    have := rat_det_lower Bq β (fun i j => hβ _ _) hBqne
    rw [hdetq, ← Rat.cast_abs]
    exact_mod_cast this
  let uS : S → ℝ := fun s => u s
  have hmul : B *ᵥ uS = fun s' => r (f s') := by
    funext s'
    have h1 := congr_fun hu.1 (f s')
    simp only [mulVec, dotProduct] at h1 ⊢
    rw [sum_supp u (fun k => E (f s') k * u k) (fun k hk => by simp [hk])] at h1
    exact h1
  have h2 : cramer B (B *ᵥ uS) = B.det • uS := by
    rw [cramer_eq_adjugate_mulVec, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  have hcr : ∀ s : S, B.det * u s = (B.updateCol s (fun s' => r (f s'))).det := by
    intro s
    have := congr_fun h2 s
    rw [hmul, cramer_apply] at this
    rw [this]; rfl
  have hup : ∀ s : S, |(B.updateCol s (fun s' => r (f s'))).det| ≤
      ((Fintype.card S).factorial : ℝ) * (α : ℝ) ^ Fintype.card S := by
    intro s
    have := Matrix.det_le (abv := AbsoluteValue.abs) (x := (α : ℝ))
      (A := B.updateCol s (fun s' => r (f s'))) (fun i j => by
        rw [AbsoluteValue.abs_apply, updateCol_apply]
        split_ifs
        · rw [hr]; exact le_trans (rat_abs_le _) (by exact_mod_cast hαr _)
        · show |E (f i) j| ≤ _
          rw [hE]; exact le_trans (rat_abs_le _) (by exact_mod_cast hα _ _))
    rw [AbsoluteValue.abs_apply, nsmul_eq_mul] at this
    exact this
  have hpt : ∀ s : S, u s ≤ ((Fintype.card S).factorial : ℝ) * (α : ℝ) ^ Fintype.card S *
      (β : ℝ) ^ (Fintype.card S * Fintype.card S) := by
    intro s
    have hu0 : 0 ≤ u s := hu.2 s
    have e1 : |B.det| * u s = |B.det * u s| := by rw [abs_mul, abs_of_nonneg hu0]
    have e2 := hup s
    rw [← hcr s, ← e1] at e2
    have hβp : (0:ℝ) ≤ (β:ℝ) ^ (Fintype.card S * Fintype.card S) := by positivity
    nlinarith
  have hsum : ∑ k, u k = ∑ s : S, u s := sum_supp u u (fun k hk => hk)
  have hk : Fintype.card S ≤ Fintype.card ι := by
    have := hB.fintype_card_le_finrank
    rwa [Module.finrank_fintype_fun_eq_card] at this
  set k := Fintype.card S
  set ℓ := Fintype.card ι
  have hN : k * k.factorial * α ^ k * β ^ (k * k) ≤ ℓ * ℓ.factorial * α ^ ℓ * β ^ (ℓ * ℓ) := by
    apply Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hk (Nat.factorial_le hk))
      (pow_le_pow_right₀ hα1 hk)) (pow_le_pow_right₀ hβ1 (Nat.mul_le_mul hk hk))
  have hS : ∑ s : S, u s ≤ (k : ℝ) * (((k).factorial : ℝ) * (α : ℝ) ^ k * (β : ℝ) ^ (k * k)) := by
    have := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hpt s)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    exact this
  rw [hsum]
  refine le_trans hS (le_trans (le_of_eq (by push_cast; ring)) (Nat.cast_le.2 hN))

end bbound

section part3
variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)

/-- The rational copy of `E58`. -/
def E58q (Aq : Matrix (Fin m) (Fin n) ℚ) (bq : Fin m → ℚ) (cq : Fin n → ℚ) :
    Matrix ((Fin m ⊕ Fin n) ⊕ Unit) (((Fin m ⊕ Fin n) ⊕ Unit) ⊕ ((Fin m ⊕ Fin n) ⊕ Unit)) ℚ
  | ρ, .inr k => if k = ρ then 1 else 0
  | .inl (.inl _), .inl (.inl (.inl _)) => 0
  | .inl (.inl i), .inl (.inl (.inr j)) => Aq i j
  | .inl (.inl _), .inl (.inr _) => -1
  | .inl (.inr j), .inl (.inl (.inl i)) => -Aq i j
  | .inl (.inr _), .inl (.inl (.inr _)) => 0
  | .inl (.inr _), .inl (.inr _) => -1
  | .inr _, .inl (.inl (.inl i)) => bq i
  | .inr _, .inl (.inl (.inr j)) => -cq j
  | .inr _, .inl (.inr _) => -1

def r58q (bq : Fin m → ℚ) (cq : Fin n → ℚ) : (Fin m ⊕ Fin n) ⊕ Unit → ℚ :=
  Sum.elim (Sum.elim bq fun j => -cq j) fun _ => 0

lemma e58_cast (Aq : Matrix (Fin m) (Fin n) ℚ) (bq : Fin m → ℚ) (cq : Fin n → ℚ)
    (hA : ∀ i j, A i j = (Aq i j : ℝ)) (hb : ∀ i, b i = (bq i : ℝ)) (hc : ∀ j, c j = (cq j : ℝ)) :
    ∀ ρ k, E58 A b c ρ k = (E58q Aq bq cq ρ k : ℝ) := by
  intro ρ k
  rcases ρ with (i | j) | ⟨⟩ <;> rcases k with ((i' | j') | ⟨⟩) | k <;>
    simp only [E58, E58q, hA, hb, hc, Rat.cast_neg, Rat.cast_one, Rat.cast_zero] <;>
    split_ifs <;> simp

lemma r58_cast (bq : Fin m → ℚ) (cq : Fin n → ℚ)
    (hb : ∀ i, b i = (bq i : ℝ)) (hc : ∀ j, c j = (cq j : ℝ)) :
    ∀ ρ, r58 b c ρ = (r58q bq cq ρ : ℝ) := by
  intro ρ
  rcases ρ with (i | j) | ⟨⟩ <;> simp [r58, r58q, hb, hc]

lemma e58q_bd (Aq : Matrix (Fin m) (Fin n) ℚ) (bq : Fin m → ℚ) (cq : Fin n → ℚ) (α β : ℕ)
    (hα1 : 1 ≤ α) (hβ1 : 1 ≤ β)
    (hαA : ∀ i j, (Aq i j).num.natAbs ≤ α) (hαb : ∀ i, (bq i).num.natAbs ≤ α)
    (hαc : ∀ j, (cq j).num.natAbs ≤ α)
    (hβA : ∀ i j, (Aq i j).den ≤ β) (hβb : ∀ i, (bq i).den ≤ β) (hβc : ∀ j, (cq j).den ≤ β) :
    ∀ ρ k, (E58q Aq bq cq ρ k).num.natAbs ≤ α ∧ (E58q Aq bq cq ρ k).den ≤ β := by
  intro ρ k
  rcases ρ with (i | j) | ⟨⟩ <;> rcases k with ((i' | j') | ⟨⟩) | k <;>
    simp only [E58q] <;> (try split_ifs) <;>
    simp [hα1, hβ1, hαA, hαb, hαc, hβA, hβb, hβc]

lemma r58q_bd (bq : Fin m → ℚ) (cq : Fin n → ℚ) (α : ℕ)
    (hαb : ∀ i, (bq i).num.natAbs ≤ α) (hαc : ∀ j, (cq j).num.natAbs ≤ α) :
    ∀ ρ, (r58q bq cq ρ).num.natAbs ≤ α := by
  intro ρ
  rcases ρ with (i | j) | ⟨⟩ <;> simp [r58q, hαb, hαc]

theorem part3 (hm : 0 < m) (Aq : Matrix (Fin m) (Fin n) ℚ) (bq : Fin m → ℚ) (cq : Fin n → ℚ)
    (hA : ∀ i j, A i j = (Aq i j : ℝ)) (hb : ∀ i, b i = (bq i : ℝ)) (hc : ∀ j, c j = (cq j : ℝ))
    (M : ℝ) (hM : bound55 Aq bq cq ≤ M) : IsSuitableM A b c M := by
  set α : ℕ := max (Finset.univ.sup fun p : Fin m × Fin n => (Aq p.1 p.2).num.natAbs)
    (max (Finset.univ.sup fun i => (bq i).num.natAbs) (Finset.univ.sup fun j => (cq j).num.natAbs))
    with hαdef
  set β : ℕ := max (Finset.univ.sup fun p : Fin m × Fin n => (Aq p.1 p.2).den)
    (max (Finset.univ.sup fun i => (bq i).den) (Finset.univ.sup fun j => (cq j).den)) with hβdef
  have hbd : bound55 Aq bq cq = (((m + n + 1).factorial * (m + n + 1) * α ^ (m + n + 1) *
      β ^ ((m + n + 1) ^ 2 + (m + n + 1)) + 1 : ℕ) : ℝ) := rfl
  have hαA : ∀ i j, (Aq i j).num.natAbs ≤ α := fun i j => le_max_of_le_left
    (Finset.le_sup (f := fun p : Fin m × Fin n => (Aq p.1 p.2).num.natAbs) (Finset.mem_univ (i, j)))
  have hαb : ∀ i, (bq i).num.natAbs ≤ α := fun i => le_max_of_le_right (le_max_of_le_left
    (Finset.le_sup (f := fun i => (bq i).num.natAbs) (Finset.mem_univ i)))
  have hαc : ∀ j, (cq j).num.natAbs ≤ α := fun j => le_max_of_le_right (le_max_of_le_right
    (Finset.le_sup (f := fun j => (cq j).num.natAbs) (Finset.mem_univ j)))
  have hβA : ∀ i j, (Aq i j).den ≤ β := fun i j => le_max_of_le_left
    (Finset.le_sup (f := fun p : Fin m × Fin n => (Aq p.1 p.2).den) (Finset.mem_univ (i, j)))
  have hβb : ∀ i, (bq i).den ≤ β := fun i => le_max_of_le_right (le_max_of_le_left
    (Finset.le_sup (f := fun i => (bq i).den) (Finset.mem_univ i)))
  have hβc : ∀ j, (cq j).den ≤ β := fun j => le_max_of_le_right (le_max_of_le_right
    (Finset.le_sup (f := fun j => (cq j).den) (Finset.mem_univ j)))
  have hβ1 : 1 ≤ β := le_trans (bq ⟨0, hm⟩).den_pos (hβb _)
  rcases Nat.eq_zero_or_pos α with h0 | hα1
  · have hz : ∀ q : ℚ, q.num.natAbs ≤ α → q = 0 := fun q hq =>
      Rat.num_eq_zero.1 (Int.natAbs_eq_zero.1 (Nat.le_zero.1 (h0 ▸ hq)))
    have hA0 : ∀ i j, A i j = 0 := fun i j => by rw [hA, hz _ (hαA i j), Rat.cast_zero]
    have hb0 : ∀ i, b i = 0 := fun i => by rw [hb, hz _ (hαb i), Rat.cast_zero]
    have hc0 : ∀ j, c j = 0 := fun j => by rw [hc, hz _ (hαc j), Rat.cast_zero]
    have hM1 : 1 ≤ M := by
      rw [hbd, h0, zero_pow (by omega)] at hM; simpa using hM
    have hf : Feas58 A b c 0 0 0 := by
      refine ⟨fun i => ?_, fun j => le_refl _, fun j => ?_, fun i => le_refl _, ?_, le_refl _⟩
      · simp [hb0]
      · simp [hc0]
      · simp
    exact suitable A b c M 0 0 0 hf (fun x y w h => h.2.2.2.2.2) (by simpa using hM1)
  · obtain ⟨u, hu, hB, hmin⟩ := attain58 A b c
    have hsum := basic_bound (E58 A b c) (r58 b c) (E58q Aq bq cq) (r58q bq cq)
      (e58_cast A b c Aq bq cq hA hb hc) (r58_cast b c bq cq hb hc) α β hα1 hβ1
      (fun ρ k => (e58q_bd Aq bq cq α β hα1 hβ1 hαA hαb hαc hβA hβb hβc ρ k).1)
      (r58q_bd bq cq α hαb hαc)
      (fun ρ k => (e58q_bd Aq bq cq α β hα1 hβ1 hαA hαb hαc hβA hβb hβc ρ k).2) u hu hB
    have hcard : Fintype.card ((Fin m ⊕ Fin n) ⊕ Unit) = m + n + 1 := by simp
    rw [hcard] at hsum
    refine suitable A b c M _ _ _ (feq_to58 A b c u hu) hmin ?_
    let g : ((Fin m ⊕ Fin n) ⊕ Unit) ⊕ ((Fin m ⊕ Fin n) ⊕ Unit) → ℝ :=
      Sum.elim (Sum.elim (Sum.elim (fun i => u (.inl (.inl (.inl i))))
        (fun j => u (.inl (.inl (.inr j))))) 0) 0
    have hg : ∑ k, g k = ∑ i, u (.inl (.inl (.inl i))) + ∑ j, u (.inl (.inl (.inr j))) := by
      simp [g, Fintype.sum_sum_type]
    have hgu : ∑ k, g k ≤ ∑ k, u k := Finset.sum_le_sum fun k _ => by
      rcases k with ((i | j) | ⟨⟩) | k <;> simp [g, hu.2 _]
    have hpow : β ^ ((m + n + 1) * (m + n + 1)) ≤ β ^ ((m + n + 1) ^ 2 + (m + n + 1)) :=
      pow_le_pow_right₀ hβ1 (by rw [sq]; exact Nat.le_add_right _ _)
    have hN : (m + n + 1) * (m + n + 1).factorial * α ^ (m + n + 1) * β ^ ((m + n + 1) * (m + n + 1))
        ≤ (m + n + 1).factorial * (m + n + 1) * α ^ (m + n + 1) *
          β ^ ((m + n + 1) ^ 2 + (m + n + 1)) := by
      rw [show (m + n + 1) * (m + n + 1).factorial * α ^ (m + n + 1) =
        (m + n + 1).factorial * (m + n + 1) * α ^ (m + n + 1) by ring]
      exact Nat.mul_le_mul_left _ hpow
    have hNr := (Nat.cast_le (α := ℝ)).2 hN
    rw [hbd] at hM
    push_cast at hM hNr hsum
    linarith

end part3


end S37

open StengelZeroSum in
theorem solution {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    (∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → IsSuitableM A b c M) ∧
    ∀ (Aq : Matrix (Fin m) (Fin n) ℚ) (bq : Fin m → ℚ) (cq : Fin n → ℚ),
      (∀ i j, A i j = (Aq i j : ℝ)) → (∀ i, b i = (bq i : ℝ)) → (∀ j, c j = (cq j : ℝ)) →
      ∀ M : ℝ, bound55 Aq bq cq ≤ M → IsSuitableM A b c M := by
  exact ⟨S37.part1 A b c, fun Aq bq cq hA hb hc M hM => S37.part3 A b c hm Aq bq cq hA hb hc M hM⟩

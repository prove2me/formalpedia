-- Prove2me | solution 1 for TimeLockedSales.Reform.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T11:22:46.624704+00:00
-- url     : https://prove2.me/submissions/c09c550e-cd70-463c-b028-5ca74cfb9e67

import Mathlib
import Definitions.Def_TimeLockedSales_Reform_Model

set_option autoImplicit false

namespace TLSProof
open TimeLockedSales.Reform
open Classical

/-! ## Part B: LP (11) and program (9) -/

lemma one_le_T_of_mem_pos {P : Params} {n : ℤ} (hn : n ∈ pos P) : 1 ≤ P.T := by
  simp only [pos, Finset.mem_Icc] at hn; omega

lemma zOf_nonneg {P : Params} {y : ℕ → ℤ → SignType → ℝ} (hy : FeasibleLP P y) {t : ℕ}
    (ht : t ∈ Finset.Icc 1 P.T) (n : ℤ) : 0 ≤ zOf y t n :=
  Finset.sum_nonneg fun i _ => hy.1 t ht n i

lemma rz_eq {P : Params} {y r : ℕ → ℤ → SignType → ℝ} (hy : FeasibleLP P y)
    (hr : Recovers P y r) {t : ℕ} (ht : t ∈ Finset.Icc 1 P.T) (n : ℤ) (i : SignType) :
    r t n i * zOf y t n = y t n i := by
  by_cases hn : n ∈ pos P
  · rcases (zOf_nonneg hy ht n).lt_or_eq with hz | hz
    · rw [(hr t ht n hn).1 hz i]; field_simp
    · have h0 : ∀ j ∈ (Finset.univ : Finset SignType), y t n j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hy.1 t ht n j)).1 hz.symm
      rw [← hz, h0 i (Finset.mem_univ _)]; ring
  · have h0 : ∀ j, y t n j = 0 := fun j => hy.2.1 t ht n j hn
    have : zOf y t n = 0 := Finset.sum_eq_zero fun j _ => h0 j
    rw [this, h0]; ring

/-- Recovery (10): an LP-feasible `y` gives a (9)-feasible pair with the same objective. -/
theorem recovery (P : Params) (y : ℕ → ℤ → SignType → ℝ) (hy : FeasibleLP P y)
    (r : ℕ → ℤ → SignType → ℝ) (hr : Recovers P y r) :
    Feasible9 P r (zOf y) ∧ obj9 P r (zOf y) = objLP P y := by
  have key : ∀ {t : ℕ}, t ∈ Finset.Icc 1 P.T → ∀ n i, r t n i * zOf y t n = y t n i :=
    fun ht n i => rz_eq hy hr ht n i
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t ht n hn
    rcases (zOf_nonneg hy ht n).lt_or_eq with hz | hz
    · have hri := (hr t ht n hn).1 hz
      refine ⟨fun i => ?_, ?_⟩
      · rw [hri i]; exact div_nonneg (hy.1 t ht n i) hz.le
      · simp only [hri]; rw [← Finset.sum_div]; exact div_self hz.ne'
    · exact (hr t ht n hn).2 hz.symm
  · intro t ht n; exact zOf_nonneg hy ht n
  · intro t ht n hn
    exact Finset.sum_eq_zero fun i _ => hy.2.1 t ht n i hn
  · intro n hn; exact hy.2.2.2.2 n hn
  · intro t ht n hn
    have ht1 : t - 1 ∈ Finset.Icc 1 P.T := by
      simp only [Finset.mem_Icc] at ht ⊢; omega
    have e1 := key ht1 n 1
    have e2 := key ht1 n (-1)
    have e3 := key ht1 (n - 1) 0
    have e4 := key ht1 (n + 1) 0
    show ∑ i, y t n i = _
    rw [hy.2.2.2.1 t ht n hn]
    linear_combination -e1 - e2 - uN P (n - 1) * e3 - (1 - uN P (n + 1)) * e4
  · intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hy.2.2.1 t ht
    have k1 : ∀ i n, (vN P n - vStarStar P) * zOf y t n * r t n i =
        (vN P n - vStarStar P) * y t n i := fun i n => by
      rw [mul_assoc, mul_comm (zOf y t n), key ht]
    have k2 : ∀ i n, (vN P n - vStar P) * zOf y t n * r t n i =
        (vN P n - vStar P) * y t n i := fun i n => by
      rw [mul_assoc, mul_comm (zOf y t n), key ht]
    simp only [k1, k2]
    exact ⟨h1, h3, h4, h2⟩
  · unfold obj9 objLP
    congr 1
    refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun n _ => ?_
    have e1 := key ht n 1
    have e0 := key ht n 0
    linear_combination e1 + uN P n * e0

/-- Change of variables `y = z r`: a (9)-feasible pair gives an LP-feasible point. -/
theorem nine_to_LP (P : Params) (r : ℕ → ℤ → SignType → ℝ) (z : ℕ → ℤ → ℝ)
    (h : Feasible9 P r z) :
    FeasibleLP P (fun t n i => z t n * r t n i) ∧
      objLP P (fun t n i => z t n * r t n i) = obj9 P r z := by
  obtain ⟨hR, hz0, hzout, hz1, hflow, hIC⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t ht n i
    by_cases hn : n ∈ pos P
    · exact mul_nonneg (hz0 t ht n) ((hR t ht n hn).1 i)
    · simp [hzout t ht n hn]
  · intro t ht n i hn; simp [hzout t ht n hn]
  · intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hIC t ht
    simp only [mul_assoc] at h1 h2 h3 h4
    exact ⟨h1, h4, h2, h3⟩
  · intro t ht n hn
    have ht' : t ∈ Finset.Icc 1 P.T := by
      simp only [Finset.mem_Icc] at ht ⊢; omega
    show ∑ i, z t n * r t n i = z (t - 1) n * r (t - 1) n 1 + z (t - 1) n * r (t - 1) n (-1) +
      uN P (n - 1) * (z (t - 1) (n - 1) * r (t - 1) (n - 1) 0) +
      (1 - uN P (n + 1)) * (z (t - 1) (n + 1) * r (t - 1) (n + 1) 0)
    rw [← Finset.mul_sum, (hR t ht' n hn).2, mul_one, hflow t ht n hn]
    ring
  · intro n hn
    have h1T : 1 ∈ Finset.Icc 1 P.T := by
      have := one_le_T_of_mem_pos hn
      simp only [Finset.mem_Icc]; omega
    show ∑ i, z 1 n * r 1 n i = _
    rw [← Finset.mul_sum, (hR 1 h1T n hn).2, mul_one, hz1 n hn]
  · unfold objLP obj9
    congr 1
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun n _ => ?_
    ring

/-- Some `(R)`-vector always recovers a feasible `y`. -/
noncomputable def recOf (y : ℕ → ℤ → SignType → ℝ) : ℕ → ℤ → SignType → ℝ :=
  fun t n i => if 0 < zOf y t n then y t n i / zOf y t n else if i = 0 then 1 else 0

lemma recOf_recovers (P : Params) (y : ℕ → ℤ → SignType → ℝ) : Recovers P y (recOf y) := by
  intro t _ n _
  refine ⟨fun hz i => by simp [recOf, hz], fun hz => ?_⟩
  have hz' : ¬ 0 < zOf y t n := by rw [hz]; exact lt_irrefl 0
  refine ⟨fun i => ?_, ?_⟩
  · simp only [recOf, hz', if_false]; split_ifs <;> norm_num
  · simp only [recOf, hz', if_false]
    rw [Finset.sum_ite_eq' Finset.univ (0 : SignType) (fun _ => (1 : ℝ))]
    simp

/-! ## Algebra of beliefs -/

noncomputable def aN (P : Params) (n : ℤ) : ℝ := P.v0 * P.q ^ n.toNat * (1 - P.q) ^ (-n).toNat
noncomputable def bN (P : Params) (n : ℤ) : ℝ :=
  (1 - P.v0) * (1 - P.q) ^ n.toNat * P.q ^ (-n).toNat

lemma vN_eq (P : Params) (n : ℤ) : vN P n = aN P n / (aN P n + bN P n) := by
  unfold vN aN bN
  split_ifs with h
  · have : (-n).toNat = 0 := by omega
    simp [this]
  · have : n.toNat = 0 := by omega
    simp [this]

section
variable {P : Params} (hS : P.Standing)
include hS

lemma q_pos : 0 < P.q := by have := hS.2.2.1; linarith
lemma q_le : P.q ≤ 1 := hS.2.2.2.1
lemma one_sub_q_nonneg : 0 ≤ 1 - P.q := by linarith [q_le hS]

lemma aN_nonneg (n : ℤ) : 0 ≤ aN P n := by
  unfold aN
  exact mul_nonneg (mul_nonneg hS.2.2.2.2.1 (pow_nonneg (q_pos hS).le _))
    (pow_nonneg (one_sub_q_nonneg hS) _)

lemma bN_nonneg (n : ℤ) : 0 ≤ bN P n := by
  unfold bN
  exact mul_nonneg (mul_nonneg (by linarith [hS.2.2.2.2.2]) (pow_nonneg (one_sub_q_nonneg hS) _))
    (pow_nonneg (q_pos hS).le _)

lemma vN_mul (n : ℤ) : vN P n * (aN P n + bN P n) = aN P n := by
  rw [vN_eq]
  have ha := aN_nonneg hS n
  have hb := bN_nonneg hS n
  rcases (add_nonneg ha hb).lt_or_eq with h | h
  · field_simp
  · have : aN P n = 0 := by linarith
    rw [← h, this]; simp

lemma vN_nonneg (n : ℤ) : 0 ≤ vN P n := by
  rw [vN_eq]; exact div_nonneg (aN_nonneg hS n) (add_nonneg (aN_nonneg hS n) (bN_nonneg hS n))

lemma vN_le_one (n : ℤ) : vN P n ≤ 1 := by
  rw [vN_eq]
  exact div_le_one_of_le₀ (by linarith [bN_nonneg hS n])
    (add_nonneg (aN_nonneg hS n) (bN_nonneg hS n))

lemma uN_nonneg (n : ℤ) : 0 ≤ uN P n := by
  unfold uN
  have := vN_nonneg hS n; have := vN_le_one hS n; have := q_pos hS; have := q_le hS
  nlinarith

lemma uN_le_one (n : ℤ) : uN P n ≤ 1 := by
  unfold uN
  have := vN_nonneg hS n; have := vN_le_one hS n; have := q_pos hS; have := q_le hS
  nlinarith

/-- A pair `(x, y)` = (mass with valuable product, mass without) proportional to `(aN n, bN n)`. -/
def GForm (P : Params) (n : ℤ) (x y : ℝ) : Prop :=
  ∃ G : ℝ, 0 ≤ G ∧ x = G * aN P n ∧ y = G * bN P n

omit hS in
lemma GForm.zero (n : ℤ) : GForm P n 0 0 := ⟨0, le_refl _, by simp, by simp⟩

omit hS in
lemma GForm.add {n : ℤ} {x y x' y' : ℝ} (h : GForm P n x y) (h' : GForm P n x' y') :
    GForm P n (x + x') (y + y') := by
  obtain ⟨G, hG, rfl, rfl⟩ := h
  obtain ⟨G', hG', rfl, rfl⟩ := h'
  exact ⟨G + G', add_nonneg hG hG', by ring, by ring⟩

omit hS in
lemma GForm.smul {n : ℤ} {x y c : ℝ} (h : GForm P n x y) (hc : 0 ≤ c) :
    GForm P n (c * x) (c * y) := by
  obtain ⟨G, hG, rfl, rfl⟩ := h
  exact ⟨c * G, mul_nonneg hc hG, by ring, by ring⟩

omit hS in
lemma GForm.sum {ι : Type} (s : Finset ι) {n : ℤ} (x y : ι → ℝ)
    (h : ∀ j ∈ s, GForm P n (x j) (y j)) : GForm P n (∑ j ∈ s, x j) (∑ j ∈ s, y j) := by
  induction s using Finset.induction_on with
  | empty => simpa using GForm.zero n
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma GForm.nonneg_left {n : ℤ} {x y : ℝ} (h : GForm P n x y) : 0 ≤ x := by
  obtain ⟨G, hG, rfl, rfl⟩ := h; exact mul_nonneg hG (aN_nonneg hS n)

lemma GForm.nonneg_right {n : ℤ} {x y : ℝ} (h : GForm P n x y) : 0 ≤ y := by
  obtain ⟨G, hG, rfl, rfl⟩ := h; exact mul_nonneg hG (bN_nonneg hS n)

lemma GForm.eq_vN {n : ℤ} {x y : ℝ} (h : GForm P n x y) : x = vN P n * (x + y) := by
  obtain ⟨G, hG, rfl, rfl⟩ := h
  have := vN_mul hS n
  linear_combination (-G) * this

lemma GForm.eq_uN {n : ℤ} {x y : ℝ} (h : GForm P n x y) :
    P.q * x + (1 - P.q) * y = uN P n * (x + y) := by
  have e := h.eq_vN hS
  unfold uN
  linear_combination (2 * P.q - 1) * e

lemma GForm.step_true {n : ℤ} {x y : ℝ} (h : GForm P n x y) :
    GForm P (n + 1) (P.q * x) ((1 - P.q) * y) := by
  obtain ⟨G, hG, rfl, rfl⟩ := h
  have hq := q_pos hS
  have hq' := one_sub_q_nonneg hS
  unfold aN bN
  rcases le_or_gt 0 n with hn | hn
  · have e1 : (n + 1).toNat = n.toNat + 1 := by omega
    have e2 : (-(n + 1)).toNat = 0 := by omega
    have e3 : (-n).toNat = 0 := by omega
    refine ⟨G, hG, ?_, ?_⟩ <;> simp only [aN, bN, e1, e2, e3] <;> ring
  · have e1 : (n + 1).toNat = 0 := by omega
    have e2 : (-n).toNat = (-(n + 1)).toNat + 1 := by omega
    have e3 : n.toNat = 0 := by omega
    refine ⟨G * (P.q * (1 - P.q)), mul_nonneg hG (mul_nonneg hq.le hq'), ?_, ?_⟩ <;>
      simp only [aN, bN, e1, e2, e3] <;> ring

lemma GForm.step_false {n : ℤ} {x y : ℝ} (h : GForm P n x y) :
    GForm P (n - 1) ((1 - P.q) * x) (P.q * y) := by
  obtain ⟨G, hG, rfl, rfl⟩ := h
  have hq := q_pos hS
  have hq' := one_sub_q_nonneg hS
  unfold aN bN
  rcases le_or_gt n 0 with hn | hn
  · have e1 : (-(n - 1)).toNat = (-n).toNat + 1 := by omega
    have e2 : (n - 1).toNat = 0 := by omega
    have e3 : n.toNat = 0 := by omega
    refine ⟨G, hG, ?_, ?_⟩ <;> simp only [aN, bN, e1, e2, e3] <;> ring
  · have e1 : n.toNat = (n - 1).toNat + 1 := by omega
    have e2 : (-(n - 1)).toNat = 0 := by omega
    have e3 : (-n).toNat = 0 := by omega
    refine ⟨G * (P.q * (1 - P.q)), mul_nonneg hG (mul_nonneg hq.le hq'), ?_, ?_⟩ <;>
      simp only [aN, bN, e1, e2, e3] <;> ring

/-! ## Purchase rule algebra -/

omit hS in
lemma buysAt_iff {M : Type} [Fintype M] (σ : InfoPolicy M) (t : ℕ)
    (w : Bool → (Fin t → M × Bool) → ℝ) (s : Bool) (m : M) :
    buysAt P σ t w s m ↔
      P.p * ((∑ h, w true h * σ.σ t h m) * sigLik P true s +
        (∑ h, w false h * σ.σ t h m) * sigLik P false s) ≤
        (∑ h, w true h * σ.σ t h m) * sigLik P true s := by
  simp only [buysAt, Fintype.sum_bool, Finset.sum_mul]

lemma denSS_pos : 0 < P.p * P.q + (1 - P.p) * (1 - P.q) := by
  have := hS.1; have := hS.2.1; have := q_pos hS; have := one_sub_q_nonneg hS
  have : 0 < P.p * P.q := by positivity
  nlinarith

lemma denS_pos : 0 < P.p * (1 - P.q) + (1 - P.p) * P.q := by
  have := hS.1; have := hS.2.1; have := q_pos hS; have := one_sub_q_nonneg hS
  have : 0 < (1 - P.p) * P.q := by apply mul_pos <;> linarith
  nlinarith

/-- Buying on a pessimistic signal is the `v**` inequality. -/
lemma buys_false_iff (A B : ℝ) :
    P.p * (A * sigLik P true false + B * sigLik P false false) ≤ A * sigLik P true false ↔
      0 ≤ A - vStarStar P * (A + B) := by
  have hD := denSS_pos hS
  have e : (A - vStarStar P * (A + B)) * (P.p * P.q + (1 - P.p) * (1 - P.q)) =
      A * (1 - P.q) - P.p * (A * (1 - P.q) + B * P.q) := by
    have hD' : P.p * P.q + (1 - P.p) * (1 - P.q) ≠ 0 := hD.ne'
    unfold vStarStar; field_simp; ring
  simp only [sigLik, reduceIte, Bool.true_eq_false, Bool.false_eq_true]
  rw [← mul_nonneg_iff_of_pos_right hD, e]
  constructor <;> intro h <;> linarith

/-- Buying on an optimistic signal is the `v*` inequality. -/
lemma buys_true_iff (A B : ℝ) :
    P.p * (A * sigLik P true true + B * sigLik P false true) ≤ A * sigLik P true true ↔
      0 ≤ A - vStar P * (A + B) := by
  have hD := denS_pos hS
  have e : (A - vStar P * (A + B)) * (P.p * (1 - P.q) + (1 - P.p) * P.q) =
      A * P.q - P.p * (A * P.q + B * (1 - P.q)) := by
    have hD' : P.p * (1 - P.q) + (1 - P.p) * P.q ≠ 0 := hD.ne'
    have hv : vStar P * (P.p * (1 - P.q) + (1 - P.p) * P.q) = P.p * (1 - P.q) := by
      unfold vStar; exact div_mul_cancel₀ _ hD'
    linear_combination (-(A + B)) * hv
  simp only [sigLik, reduceIte, Bool.true_eq_false, Bool.false_eq_true]
  rw [← mul_nonneg_iff_of_pos_right hD, e]
  constructor <;> intro h <;> linarith

lemma vStar_lt_vStarStar : vStar P < vStarStar P := by
  have h1 := denS_pos hS; have h2 := denSS_pos hS
  have := hS.1; have := hS.2.1; have hq := hS.2.2.1; have := q_le hS
  unfold vStar vStarStar
  rw [div_lt_div_iff₀ h1 h2]
  have : 0 < P.p * (1 - P.p) := mul_pos hS.1 (by linarith)
  nlinarith

end

/-! ## Always-follow policy `y°` -/

lemma sum_shift (f : ℤ → ℝ) (g : ℤ → ℤ) (hg : Function.Injective g) (I s : Finset ℤ)
    (hf : ∀ m ∉ s, f m = 0) (hs : ∀ m ∈ s, ∃ n ∈ I, g n = m) :
    ∑ n ∈ I, f (g n) = ∑ m ∈ s, f m := by
  rw [← Finset.sum_image (fun x _ y _ h => hg h)]
  symm
  apply Finset.sum_subset
  · intro m hm
    obtain ⟨n, hn, rfl⟩ := hs m hm
    exact Finset.mem_image_of_mem g hn
  · intro m _ hm; exact hf m hm

noncomputable def QF (P : Params) : ℕ → ℤ → ℝ × ℝ
  | 0, n => if n = 0 then (P.v0, 1 - P.v0) else (0, 0)
  | k + 1, n => (P.q * (QF P k (n - 1)).1 + (1 - P.q) * (QF P k (n + 1)).1,
      (1 - P.q) * (QF P k (n - 1)).2 + P.q * (QF P k (n + 1)).2)

lemma QF_support (P : Params) (k : ℕ) : ∀ n : ℤ, (n < -(k : ℤ) ∨ (k : ℤ) < n) → QF P k n = (0, 0) := by
  induction k with
  | zero =>
    intro n h
    have : n ≠ 0 := by omega
    simp [QF, this]
  | succ k ih =>
    intro n h
    have h1 := ih (n - 1) (by push_cast at h; omega)
    have h2 := ih (n + 1) (by push_cast at h; omega)
    simp [QF, h1, h2]

lemma QF_GForm {P : Params} (hS : P.Standing) (k : ℕ) :
    ∀ n : ℤ, GForm P n (QF P k n).1 (QF P k n).2 := by
  induction k with
  | zero =>
    intro n
    by_cases h : n = 0
    · subst h; refine ⟨1, zero_le_one, ?_, ?_⟩ <;> simp [QF, aN, bN]
    · simpa [QF, h] using GForm.zero (P := P) n
  | succ k ih =>
    intro n
    have h1 := (ih (n - 1)).step_true hS
    have h2 := (ih (n + 1)).step_false hS
    rw [sub_add_cancel] at h1
    rw [add_sub_cancel_right] at h2
    simp only [QF]
    exact h1.add h2

lemma mem_pos_iff {P : Params} {n : ℤ} : n ∈ pos P ↔ -((P.T : ℤ) - 1) ≤ n ∧ n ≤ (P.T : ℤ) - 1 := by
  simp [pos]

lemma QF_mass {P : Params} (k : ℕ) (hk : k + 1 ≤ P.T) :
    (∑ n ∈ pos P, (QF P k n).1) = P.v0 ∧ (∑ n ∈ pos P, (QF P k n).2) = 1 - P.v0 := by
  induction k with
  | zero =>
    have h0 : (0 : ℤ) ∈ pos P := by rw [mem_pos_iff]; omega
    have e1 : ∀ n, (QF P 0 n).1 = if n = 0 then P.v0 else 0 := by
      intro n; by_cases h : n = 0 <;> simp [QF, h]
    have e2 : ∀ n, (QF P 0 n).2 = if n = 0 then 1 - P.v0 else 0 := by
      intro n; by_cases h : n = 0 <;> simp [QF, h]
    simp only [e1, e2]
    simp [h0]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have supp : ∀ (j : Bool) (m : ℤ), m ∉ Finset.Icc (-(k : ℤ)) k →
        (if j then (QF P k m).1 else (QF P k m).2) = 0 := by
      intro j m hm
      rw [Finset.mem_Icc] at hm
      have := QF_support P k m (by omega)
      cases j <;> simp [this]
    have shift : ∀ (j : Bool) (g : ℤ → ℤ), Function.Injective g → (∀ m, m ∈ Finset.Icc (-(k : ℤ)) k →
        ∃ n ∈ pos P, g n = m) →
        ∑ n ∈ pos P, (if j then (QF P k (g n)).1 else (QF P k (g n)).2) =
          ∑ n ∈ pos P, (if j then (QF P k n).1 else (QF P k n).2) := by
      intro j g hg hs
      rw [sum_shift (fun m => if j then (QF P k m).1 else (QF P k m).2) g hg (pos P) _ (supp j) hs]
      symm
      exact sum_shift (fun m => if j then (QF P k m).1 else (QF P k m).2) id Function.injective_id
          (pos P) _ (supp j) (fun m hm => by
            rw [Finset.mem_Icc] at hm
            exact ⟨m, by rw [mem_pos_iff]; omega, rfl⟩)
    have hsub : ∀ m, m ∈ Finset.Icc (-(k : ℤ)) k → ∃ n ∈ pos P, n - 1 = m := by
      intro m hm; rw [Finset.mem_Icc] at hm
      exact ⟨m + 1, by rw [mem_pos_iff]; omega, by ring⟩
    have hadd : ∀ m, m ∈ Finset.Icc (-(k : ℤ)) k → ∃ n ∈ pos P, n + 1 = m := by
      intro m hm; rw [Finset.mem_Icc] at hm
      exact ⟨m - 1, by rw [mem_pos_iff]; omega, by ring⟩
    have s1 := shift true (fun n => n - 1) (sub_left_injective) hsub
    have s2 := shift true (fun n => n + 1) (add_left_injective 1) hadd
    have s3 := shift false (fun n => n - 1) (sub_left_injective) hsub
    have s4 := shift false (fun n => n + 1) (add_left_injective 1) hadd
    simp only [if_true, Bool.false_eq_true, if_false] at s1 s2 s3 s4
    simp only [QF, Finset.sum_add_distrib, ← Finset.mul_sum, s1, s2, s3, s4, ih1, ih2]
    constructor <;> ring

noncomputable def zF (P : Params) (t : ℕ) (n : ℤ) : ℝ := (QF P (t - 1) n).1 + (QF P (t - 1) n).2

noncomputable def yF (P : Params) (t : ℕ) (n : ℤ) (i : SignType) : ℝ := if i = 0 then zF P t n else 0

lemma yF_sum (P : Params) (t : ℕ) (n : ℤ) : ∑ i, yF P t n i = zF P t n := by
  simp [yF]

lemma zF_nonneg {P : Params} (hS : P.Standing) (t : ℕ) (n : ℤ) : 0 ≤ zF P t n :=
  add_nonneg ((QF_GForm hS _ n).nonneg_left hS) ((QF_GForm hS _ n).nonneg_right hS)

lemma zF_mass {P : Params} (hS : P.Standing) {t : ℕ} (ht : t ∈ Finset.Icc 1 P.T) :
    (∑ n ∈ pos P, vN P n * zF P t n) = P.v0 ∧ (∑ n ∈ pos P, zF P t n) = 1 := by
  rw [Finset.mem_Icc] at ht
  obtain ⟨h1, h2⟩ := QF_mass (P := P) (t - 1) (by omega)
  constructor
  · rw [← h1]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact ((QF_GForm hS (t - 1) n).eq_vN hS).symm
  · unfold zF; rw [Finset.sum_add_distrib, h1, h2]; ring

lemma yF_feasible {P : Params} (hS : P.Standing) (hR : P.Region) :
    FeasibleLP P (yF P) ∧
      ∀ t ∈ Finset.Icc 1 P.T, (∑ n ∈ pos P, (vN P n - vStarStar P) * yF P t n 0) < 0 := by
  have strict : ∀ t ∈ Finset.Icc 1 P.T,
      (∑ n ∈ pos P, (vN P n - vStarStar P) * yF P t n 0) = P.v0 - vStarStar P := by
    intro t ht
    obtain ⟨m1, m2⟩ := zF_mass hS ht
    simp only [yF, if_true, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, m1, m2, mul_one]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, fun t ht => by rw [strict t ht]; linarith [hR.2]⟩
  · intro t _ n i
    unfold yF; split_ifs
    · exact zF_nonneg hS t n
    · exact le_refl 0
  · intro t ht n i hn
    rw [Finset.mem_Icc] at ht
    rw [mem_pos_iff] at hn
    have := QF_support P (t - 1) n (by omega)
    simp [yF, zF, this]
  · intro t ht
    have hs := strict t ht
    obtain ⟨m1, m2⟩ := zF_mass hS ht
    have e2 : (∑ n ∈ pos P, (vN P n - vStar P) * yF P t n 0) = P.v0 - vStar P := by
      simp only [yF, if_true, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, m1, m2, mul_one]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [yF]
    · simp [yF]
    · rw [hs]; linarith [hR.2]
    · rw [e2]; linarith [hR.1]
  · intro t ht n _
    rw [Finset.mem_Icc] at ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
    have ek : k + 2 - 1 = k + 1 := by omega
    have ek' : k + 2 - 1 - 1 = k := by omega
    have u1 := (QF_GForm hS k (n - 1)).eq_uN hS
    have u2 := (QF_GForm hS k (n + 1)).eq_uN hS
    rw [yF_sum]
    simp only [yF, zF, ek, ek', QF, if_true]
    norm_num
    linear_combination u1 - u2
  · intro n hn
    rw [yF_sum]
    by_cases h : n = 0 <;> simp [zF, QF, h]

/-! ## Part A: LP (11) attains its maximum -/

lemma feasible_congr (P : Params) {y y' : ℕ → ℤ → SignType → ℝ}
    (h : ∀ t ∈ Finset.Icc 1 P.T, ∀ n i, y t n i = y' t n i) (hy : FeasibleLP P y) :
    FeasibleLP P y' ∧ objLP P y' = objLP P y := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t ht n i; rw [← h t ht]; exact hy.1 t ht n i
  · intro t ht n i hn; rw [← h t ht]; exact hy.2.1 t ht n i hn
  · intro t ht; simp only [← h t ht]; exact hy.2.2.1 t ht
  · intro t ht n hn
    have ht' : t ∈ Finset.Icc 1 P.T := by simp only [Finset.mem_Icc] at ht ⊢; omega
    have ht1 : t - 1 ∈ Finset.Icc 1 P.T := by simp only [Finset.mem_Icc] at ht ⊢; omega
    simp only [← h t ht', ← h (t - 1) ht1]; exact hy.2.2.2.1 t ht n hn
  · intro n hn
    have h1 : 1 ∈ Finset.Icc 1 P.T := by
      have := one_le_T_of_mem_pos hn; simp only [Finset.mem_Icc]; omega
    simp only [← h 1 h1]; exact hy.2.2.2.2 n hn
  · unfold objLP; congr 1
    refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun n _ => ?_
    rw [h t ht, h t ht]

noncomputable def Sidx (P : Params) : Finset ((ℕ × ℤ) × SignType) := (Finset.Icc 1 P.T ×ˢ pos P) ×ˢ Finset.univ

noncomputable def extF (P : Params) (f : (Sidx P) → ℝ) : ℕ → ℤ → SignType → ℝ :=
  fun t n i => if h : ((t, n), i) ∈ Sidx P then f ⟨_, h⟩ else 0

def restr (P : Params) (y : ℕ → ℤ → SignType → ℝ) : (Sidx P) → ℝ :=
  fun x => y x.1.1.1 x.1.1.2 x.1.2

lemma extF_restr (P : Params) {y : ℕ → ℤ → SignType → ℝ} (hy : FeasibleLP P y) :
    FeasibleLP P (extF P (restr P y)) ∧ objLP P (extF P (restr P y)) = objLP P y := by
  apply feasible_congr P _ hy
  intro t ht n i
  unfold extF restr
  split_ifs with h
  · rfl
  · have hn : n ∉ pos P := fun hn => h (by simp [Sidx, ht, hn])
    exact hy.2.1 t ht n i hn

lemma extF_cont (P : Params) (t : ℕ) (n : ℤ) (i : SignType) :
    Continuous fun f : (Sidx P) → ℝ => extF P f t n i := by
  by_cases h : ((t, n), i) ∈ Sidx P
  · have : (fun f : (Sidx P) → ℝ => extF P f t n i) = fun f => f ⟨_, h⟩ := by
      funext f; simp [extF, h]
    rw [this]; exact continuous_apply _
  · have : (fun f : (Sidx P) → ℝ => extF P f t n i) = fun _ => 0 := by
      funext f; simp [extF, h]
    rw [this]; exact continuous_const

lemma K_closed (P : Params) : IsClosed {f : (Sidx P) → ℝ | FeasibleLP P (extF P f)} := by
  have hc := extF_cont P
  have hs : ∀ (c : ℤ → ℝ) (t : ℕ) (i : SignType),
      Continuous fun f : (Sidx P) → ℝ => ∑ n ∈ pos P, c n * extF P f t n i :=
    fun c t i => continuous_finset_sum _ fun n _ => continuous_const.mul (hc t n i)
  have hsum : ∀ (t : ℕ) (n : ℤ), Continuous fun f : (Sidx P) → ℝ => ∑ i, extF P f t n i :=
    fun t n => continuous_finset_sum _ fun i _ => hc t n i
  simp only [FeasibleLP, Set.setOf_and, Set.setOf_forall]
  repeat' first
    | exact isClosed_le continuous_const (hc _ _ _)
    | exact isClosed_eq (hc _ _ _) continuous_const
    | exact isClosed_le continuous_const (hs _ _ _)
    | exact isClosed_le (hs _ _ _) continuous_const
    | exact isClosed_eq (hsum _ _) ((((hc _ _ _).add (hc _ _ _)).add
        (continuous_const.mul (hc _ _ _))).add (continuous_const.mul (hc _ _ _)))
    | exact isClosed_eq (hsum _ _) continuous_const
    | apply IsClosed.inter
    | (apply isClosed_iInter; intro)

lemma feasible_bound {P : Params} (hS : P.Standing) {y : ℕ → ℤ → SignType → ℝ}
    (hy : FeasibleLP P y) (t : ℕ) : t ∈ Finset.Icc 1 P.T → ∀ n i, y t n i ≤ 4 ^ (t - 1) := by
  induction t with
  | zero => intro ht; simp at ht
  | succ k ih =>
    intro ht n i
    by_cases hn : n ∈ pos P
    · have hle : y (k + 1) n i ≤ ∑ j, y (k + 1) n j :=
        Finset.single_le_sum (fun j _ => hy.1 _ ht n j) (Finset.mem_univ i)
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [hy.2.2.2.2 n hn] at hle
        simp only [Nat.zero_add, Nat.sub_self, pow_zero]
        split_ifs at hle <;> linarith
      · have ht2 : k + 1 ∈ Finset.Icc 2 P.T := by
          simp only [Finset.mem_Icc] at ht ⊢; omega
        have hk1 : k ∈ Finset.Icc 1 P.T := by
          simp only [Finset.mem_Icc] at ht ⊢; omega
        rw [hy.2.2.2.1 _ ht2 n hn] at hle
        simp only [Nat.add_sub_cancel] at hle ⊢
        have b1 := ih hk1 n 1
        have b2 := ih hk1 n (-1)
        have b3 := ih hk1 (n - 1) 0
        have b4 := ih hk1 (n + 1) 0
        have c3 : uN P (n - 1) * y k (n - 1) 0 ≤ y k (n - 1) 0 :=
          mul_le_of_le_one_left (hy.1 k hk1 _ _) (uN_le_one hS _)
        have c4 : (1 - uN P (n + 1)) * y k (n + 1) 0 ≤ y k (n + 1) 0 :=
          mul_le_of_le_one_left (hy.1 k hk1 _ _) (by linarith [uN_nonneg hS (n + 1)])
        have e4 : (4 : ℝ) ^ k = 4 * 4 ^ (k - 1) := by
          rw [← pow_succ']; congr 1; omega
        linarith
    · rw [hy.2.1 _ ht n i hn]; positivity

theorem LP_attains {P : Params} (hS : P.Standing) (hR : P.Region) :
    ∃ y, FeasibleLP P y ∧ ∀ y', FeasibleLP P y' → objLP P y' ≤ objLP P y := by
  have hK : IsCompact {f : (Sidx P) → ℝ | FeasibleLP P (extF P f)} := by
    apply Metric.isCompact_of_isClosed_isBounded (K_closed P)
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨4 ^ P.T, fun f hf => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    intro x
    obtain ⟨⟨⟨t, n⟩, i⟩, hx⟩ := x
    have hx' := hx
    simp only [Sidx, Finset.mem_product] at hx'
    have e : extF P f t n i = f ⟨_, hx⟩ := by simp [extF, hx]
    have h0 := hf.1 t hx'.1.1 n i
    have h1 := feasible_bound hS hf t hx'.1.1 n i
    rw [e] at h0 h1
    rw [Real.norm_eq_abs, abs_le]
    have ht := hx'.1.1
    rw [Finset.mem_Icc] at ht
    have : (4 : ℝ) ^ (t - 1) ≤ 4 ^ P.T := pow_le_pow_right₀ (by norm_num) (by omega)
    constructor <;> linarith
  have hne : restr P (yF P) ∈ {f : (Sidx P) → ℝ | FeasibleLP P (extF P f)} :=
    (extF_restr P (yF_feasible hS hR).1).1
  have hcont : Continuous fun f : (Sidx P) → ℝ => objLP P (extF P f) := by
    unfold objLP
    exact continuous_const.mul (continuous_finset_sum _ fun t _ => continuous_finset_sum _
      fun n _ => (extF_cont P t n 1).add (continuous_const.mul (extF_cont P t n 0)))
  obtain ⟨f, hf, hmax⟩ := hK.exists_isMaxOn ⟨_, hne⟩ hcont.continuousOn
  refine ⟨extF P f, hf, fun y' hy' => ?_⟩
  obtain ⟨h1, h2⟩ := extF_restr P hy'
  rw [← h2]
  exact isMaxOn_iff.1 hmax _ h1

/-- Conjuncts 1, 2 and 4 of Proposition 5, for the LP optimum value. -/
theorem LP_nine_part {P : Params} (hS : P.Standing) (hR : P.Region) :
    ∃ y₀, FeasibleLP P y₀ ∧ (∀ y', FeasibleLP P y' → objLP P y' ≤ objLP P y₀) ∧
      IsGreatest {J | ∃ y, FeasibleLP P y ∧ J = objLP P y} (objLP P y₀) ∧
      IsGreatest {J | ∃ r z, Feasible9 P r z ∧ J = obj9 P r z} (objLP P y₀) ∧
      ∀ y, FeasibleLP P y → objLP P y = objLP P y₀ →
        ∀ r, Recovers P y r → Feasible9 P r (zOf y) ∧ obj9 P r (zOf y) = objLP P y₀ := by
  obtain ⟨y₀, hy₀, hmax⟩ := LP_attains hS hR
  refine ⟨y₀, hy₀, hmax, ⟨⟨y₀, hy₀, rfl⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rintro J ⟨y, hy, rfl⟩; exact hmax y hy
  · obtain ⟨h1, h2⟩ := recovery P y₀ hy₀ (recOf y₀) (recOf_recovers P y₀)
    exact ⟨recOf y₀, zOf y₀, h1, h2.symm⟩
  · rintro J ⟨r, z, h, rfl⟩
    obtain ⟨h1, h2⟩ := nine_to_LP P r z h
    rw [← h2]; exact hmax _ h1
  · intro y hy hopt r hr
    obtain ⟨h1, h2⟩ := recovery P y hy r hr
    exact ⟨h1, h2.trans hopt⟩


/-! ## Part C: every information policy is dominated by the LP -/

lemma s10 : (1 : SignType) ≠ 0 := by decide
lemma s01 : (0 : SignType) ≠ 1 := by decide
lemma sn0 : (-1 : SignType) ≠ 0 := by decide
lemma s0n : (0 : SignType) ≠ -1 := by decide
lemma s1n : (1 : SignType) ≠ -1 := by decide
lemma sn1 : (-1 : SignType) ≠ 1 := by decide

lemma GForm.of_eq {P : Params} {n n' : ℤ} {x y x' y' : ℝ} (h : GForm P n x y) (hn : n = n')
    (hx : x = x') (hy : y = y') : GForm P n' x' y' := by subst hn hx hy; exact h

lemma sigLik_sum (P : Params) (v : Bool) : sigLik P v true + sigLik P v false = 1 := by
  cases v <;> simp [sigLik]

lemma sum_snoc {X : Type} [Fintype X] {t : ℕ} (F : (Fin t → X) → X → ℝ) :
    ∑ h : Fin (t + 1) → X, F (Fin.init h) (h (Fin.last t)) = ∑ h, ∑ x, F h x := by
  rw [← Fintype.sum_prod_type']
  let e : (Fin (t + 1) → X) ≃ (Fin t → X) × X :=
    { toFun := fun h => (Fin.init h, h (Fin.last t))
      invFun := fun p => Fin.snoc (α := fun _ => X) p.1 p.2
      left_inv := fun h => Fin.snoc_init_self h
      right_inv := fun p => by simp }
  exact Fintype.sum_equiv e _ _ (fun h => rfl)

section PartC
variable {P : Params} {M : Type} [Fintype M]

lemma law_nonneg (hS : P.Standing) (σ : InfoPolicy M) : ∀ t v h, 0 ≤ law P σ t v h := by
  intro t
  induction t with
  | zero =>
    intro v h
    cases v <;> simp [law, prior] <;> linarith [hS.2.2.2.2.1, hS.2.2.2.2.2]
  | succ t ih =>
    intro v h
    rw [law]
    refine mul_nonneg (mul_nonneg (ih _ _) (σ.nonneg _ _ _)) (Finset.sum_nonneg fun s _ => ?_)
    split_ifs
    · unfold sigLik; split_ifs <;> linarith [q_pos hS, q_le hS]
    · exact le_refl _

/-- Mass of `(value v, message m)` at time `t`. -/
noncomputable def Aw (P : Params) (σ : InfoPolicy M) (t : ℕ) (v : Bool) (m : M) : ℝ :=
  ∑ h, law P σ t v h * σ.σ t h m

lemma Aw_nonneg (hS : P.Standing) (σ : InfoPolicy M) (t : ℕ) (v : Bool) (m : M) :
    0 ≤ Aw P σ t v m :=
  Finset.sum_nonneg fun h _ => mul_nonneg (law_nonneg hS σ t v h) (σ.nonneg t h m)

lemma buys_false_A (hS : P.Standing) (σ : InfoPolicy M) (t : ℕ) (m : M) :
    buysAt P σ t (law P σ t) false m ↔
      0 ≤ Aw P σ t true m - vStarStar P * (Aw P σ t true m + Aw P σ t false m) := by
  rw [buysAt_iff]; exact buys_false_iff hS _ _

lemma buys_true_A (hS : P.Standing) (σ : InfoPolicy M) (t : ℕ) (m : M) :
    buysAt P σ t (law P σ t) true m ↔
      0 ≤ Aw P σ t true m - vStar P * (Aw P σ t true m + Aw P σ t false m) := by
  rw [buysAt_iff]; exact buys_true_iff hS _ _

lemma buys_mono (hS : P.Standing) (σ : InfoPolicy M) (t : ℕ) (m : M)
    (h : buysAt P σ t (law P σ t) false m) : buysAt P σ t (law P σ t) true m := by
  rw [buys_false_A hS] at h; rw [buys_true_A hS]
  have hA := add_nonneg (Aw_nonneg hS σ t true m) (Aw_nonneg hS σ t false m)
  have := mul_nonneg (sub_nonneg.2 (vStar_lt_vStarStar hS).le) hA
  linarith

/-- Behaviour type of message `m` at time `t`: 1 always buys, 0 follows the signal, -1 never. -/
noncomputable def tau (P : Params) (σ : InfoPolicy M) (t : ℕ) (m : M) : SignType :=
  if buysAt P σ t (law P σ t) false m then 1
  else if buysAt P σ t (law P σ t) true m then 0 else -1

lemma tau_one {σ : InfoPolicy M} {t : ℕ} {m : M} (h : tau P σ t m = 1) :
    buysAt P σ t (law P σ t) false m := by
  unfold tau at h; split_ifs at h with h1 h2 <;> first | exact h1 | exact absurd h (by decide)

lemma tau_zero {σ : InfoPolicy M} {t : ℕ} {m : M} (h : tau P σ t m = 0) :
    ¬ buysAt P σ t (law P σ t) false m ∧ buysAt P σ t (law P σ t) true m := by
  unfold tau at h; split_ifs at h with h1 h2 <;> first | exact ⟨h1, h2⟩ | exact absurd h (by decide)

lemma tau_neg {σ : InfoPolicy M} {t : ℕ} {m : M} (h : tau P σ t m = -1) :
    ¬ buysAt P σ t (law P σ t) true m := by
  unfold tau at h; split_ifs at h with h1 h2 <;> first | exact h2 | exact absurd h (by decide)

/-- The decision factor of the law recursion. -/
noncomputable def fac (P : Params) (σ : InfoPolicy M) (t : ℕ) (v : Bool) (m : M) (d : Bool) : ℝ :=
  ∑ s : Bool, if (buysAt P σ t (law P σ t) s m ↔ d = true) then sigLik P v s else 0

lemma law_succ (σ : InfoPolicy M) (t : ℕ) (v : Bool) (h : Fin (t + 1) → M × Bool) :
    law P σ (t + 1) v h = law P σ t v (Fin.init h) * σ.σ t (Fin.init h) (h (Fin.last t)).1 *
      fac P σ t v (h (Fin.last t)).1 (h (Fin.last t)).2 := by
  rw [law]; rfl

lemma fac_both {σ : InfoPolicy M} {t : ℕ} {m : M} (hS : P.Standing)
    (hf : buysAt P σ t (law P σ t) false m) (v d : Bool) :
    fac P σ t v m d = if d then 1 else 0 := by
  have ht := buys_mono hS σ t m hf
  unfold fac; rw [Fintype.sum_bool]
  cases d <;> simp [hf, ht, sigLik_sum]

lemma fac_follow {σ : InfoPolicy M} {t : ℕ} {m : M}
    (hf : ¬ buysAt P σ t (law P σ t) false m) (ht : buysAt P σ t (law P σ t) true m) (v d : Bool) :
    fac P σ t v m d = if d then sigLik P v true else sigLik P v false := by
  unfold fac; rw [Fintype.sum_bool]
  cases d <;> simp [hf, ht]

lemma fac_never {σ : InfoPolicy M} {t : ℕ} {m : M}
    (hf : ¬ buysAt P σ t (law P σ t) false m) (ht : ¬ buysAt P σ t (law P σ t) true m) (v d : Bool) :
    fac P σ t v m d = if d then 0 else 1 := by
  unfold fac; rw [Fintype.sum_bool]
  cases d <;> simp [hf, ht, sigLik_sum]

/-- Purchase factor of `purchaseProb`. -/
noncomputable def gbuy (P : Params) (σ : InfoPolicy M) (t : ℕ) (v : Bool) (m : M) : ℝ :=
  ∑ s : Bool, if buysAt P σ t (law P σ t) s m then sigLik P v s else 0

lemma tau_both {σ : InfoPolicy M} {t : ℕ} {m : M} (hf : buysAt P σ t (law P σ t) false m) :
    tau P σ t m = 1 := by simp [tau, hf]

lemma tau_follow {σ : InfoPolicy M} {t : ℕ} {m : M}
    (hf : ¬ buysAt P σ t (law P σ t) false m) (ht : buysAt P σ t (law P σ t) true m) :
    tau P σ t m = 0 := by simp [tau, hf, ht]

lemma tau_never {σ : InfoPolicy M} {t : ℕ} {m : M}
    (hf : ¬ buysAt P σ t (law P σ t) false m) (ht : ¬ buysAt P σ t (law P σ t) true m) :
    tau P σ t m = -1 := by simp [tau, hf, ht]

/-- Net count of signal-following decisions. -/
noncomputable def stepN (P : Params) (σ : InfoPolicy M) (t : ℕ) (x : M × Bool) : ℤ :=
  if tau P σ t x.1 = 0 then (if x.2 then 1 else -1) else 0

noncomputable def Nh (P : Params) (σ : InfoPolicy M) (t : ℕ) (h : Fin t → M × Bool) : ℤ :=
  ∑ i : Fin t, stepN P σ (i : ℕ) (h i)

lemma Nh_succ (σ : InfoPolicy M) (t : ℕ) (h : Fin (t + 1) → M × Bool) :
    Nh P σ (t + 1) h = Nh P σ t (Fin.init h) + stepN P σ t (h (Fin.last t)) := by
  unfold Nh; rw [Fin.sum_univ_castSucc]; rfl

lemma Nh_abs (σ : InfoPolicy M) (t : ℕ) (h : Fin t → M × Bool) : |Nh P σ t h| ≤ t := by
  unfold Nh
  calc |∑ i : Fin t, stepN P σ (i : ℕ) (h i)| ≤ ∑ i : Fin t, |stepN P σ (i : ℕ) (h i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin t, (1 : ℤ) := Finset.sum_le_sum fun i _ => by
        unfold stepN; split_ifs <;> simp
    _ = t := by simp

lemma Nh_mem_pos (σ : InfoPolicy M) {t : ℕ} (ht : t + 1 ≤ P.T) (h : Fin t → M × Bool) :
    Nh P σ t h ∈ pos P := by
  have := abs_le.1 (Nh_abs (P := P) σ t h)
  rw [mem_pos_iff]; constructor <;> omega

lemma law_GForm (hS : P.Standing) (σ : InfoPolicy M) :
    ∀ t h, GForm P (Nh P σ t h) (law P σ t true h) (law P σ t false h) := by
  intro t
  induction t with
  | zero =>
    intro h
    refine ⟨1, zero_le_one, ?_, ?_⟩ <;> simp [Nh, law, prior, aN, bN]
  | succ t ih =>
    intro h
    rw [law_succ, law_succ, Nh_succ]
    generalize Fin.init h = h0
    generalize h (Fin.last t) = x
    obtain ⟨m, d⟩ := x
    have hG := ih h0
    have hs := σ.nonneg t h0 m
    by_cases hf : buysAt P σ t (law P σ t) false m
    · simp only [fac_both hS hf, stepN, tau_both hf, if_neg s10, add_zero]
      cases d
      · simp only [Bool.false_eq_true, if_false, mul_zero]; exact GForm.zero _
      · exact (hG.smul hs).of_eq rfl (by simp; ring) (by simp; ring)
    by_cases ht : buysAt P σ t (law P σ t) true m
    · simp only [fac_follow hf ht, stepN, tau_follow hf ht, if_true]
      cases d
      · exact ((hG.step_false hS).smul hs).of_eq (by simp; ring) (by simp [sigLik]; ring)
          (by simp [sigLik]; ring)
      · exact ((hG.step_true hS).smul hs).of_eq (by simp) (by simp [sigLik]; ring)
          (by simp [sigLik]; ring)
    · simp only [fac_never hf ht, stepN, tau_never hf ht, if_neg sn0, add_zero]
      cases d
      · exact (hG.smul hs).of_eq rfl (by simp; ring) (by simp; ring)
      · simp only [if_true, mul_zero]; exact GForm.zero _

noncomputable def totL (P : Params) (σ : InfoPolicy M) (t : ℕ) (h : Fin t → M × Bool) : ℝ :=
  law P σ t true h + law P σ t false h

/-- The LP variables induced by a policy. -/
noncomputable def yC (P : Params) (σ : InfoPolicy M) : ℕ → ℤ → SignType → ℝ
  | 0, _, _ => 0
  | t + 1, n, i => ∑ h : Fin t → M × Bool, ∑ m,
      if Nh P σ t h = n ∧ tau P σ t m = i then totL P σ t h * σ.σ t h m else 0

lemma sum_pos_y (σ : InfoPolicy M) {t : ℕ} (ht : t + 1 ≤ P.T) (f : ℤ → ℝ) (i : SignType) :
    ∑ n ∈ pos P, f n * yC P σ (t + 1) n i =
      ∑ h, ∑ m, if tau P σ t m = i then f (Nh P σ t h) * (totL P σ t h * σ.σ t h m) else 0 := by
  simp only [yC, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [ite_and, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq (pos P) (Nh P σ t h), if_pos (Nh_mem_pos σ ht h)]

lemma IC_sum (hS : P.Standing) (σ : InfoPolicy M) {t : ℕ} (ht : t + 1 ≤ P.T) (c : ℝ)
    (i : SignType) :
    ∑ n ∈ pos P, (vN P n - c) * yC P σ (t + 1) n i = ∑ m, if tau P σ t m = i then
      (Aw P σ t true m - c * (Aw P σ t true m + Aw P σ t false m)) else 0 := by
  rw [sum_pos_y σ ht, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : tau P σ t m = i
  · simp only [hm, if_true]
    unfold Aw
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    have e := (law_GForm hS σ t h).eq_vN hS
    unfold totL
    linear_combination (-(σ.σ t h m)) * e
  · simp [hm]

lemma sum_i_yC (σ : InfoPolicy M) (t : ℕ) (n : ℤ) :
    ∑ i, yC P σ (t + 1) n i = ∑ h, if Nh P σ t h = n then totL P σ t h else 0 := by
  simp only [yC]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_comm]
  by_cases hn : Nh P σ t h = n
  · simp only [hn, true_and, if_true]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_sum, σ.sum_one, mul_one]
  · simp [hn]

lemma yC_flow (hS : P.Standing) (σ : InfoPolicy M) (k : ℕ) (n : ℤ) :
    ∑ i, yC P σ (k + 1 + 1) n i = yC P σ (k + 1) n 1 + yC P σ (k + 1) n (-1) +
      uN P (n - 1) * yC P σ (k + 1) (n - 1) 0 + (1 - uN P (n + 1)) * yC P σ (k + 1) (n + 1) 0 := by
  rw [sum_i_yC]
  have e1 : ∀ h : Fin (k + 1) → M × Bool, (if Nh P σ (k + 1) h = n then totL P σ (k + 1) h else 0) =
      (fun (h0 : Fin k → M × Bool) (x : M × Bool) =>
        if Nh P σ k h0 + stepN P σ k x = n then
          law P σ k true h0 * σ.σ k h0 x.1 * fac P σ k true x.1 x.2 +
          law P σ k false h0 * σ.σ k h0 x.1 * fac P σ k false x.1 x.2 else 0)
        (Fin.init h) (h (Fin.last k)) := by
    intro h; simp only [Nh_succ, totL, law_succ]
  have key := sum_snoc (X := M × Bool) (t := k) (fun (h0 : Fin k → M × Bool) (x : M × Bool) =>
        if Nh P σ k h0 + stepN P σ k x = n then
          law P σ k true h0 * σ.σ k h0 x.1 * fac P σ k true x.1 x.2 +
          law P σ k false h0 * σ.σ k h0 x.1 * fac P σ k false x.1 x.2 else 0)
  beta_reduce at key
  simp only [e1]
  rw [key]
  simp only [yC, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Fintype.sum_bool]
  have eu := (law_GForm hS σ k h).eq_uN hS
  have ev := (law_GForm hS σ k h).eq_vN hS
  unfold totL
  by_cases hf : buysAt P σ k (law P σ k) false m
  · simp only [fac_both hS hf, stepN, tau_both hf, s10, s1n, if_false, add_zero, true_and,
      and_false, and_true, if_true, Bool.false_eq_true, mul_zero, mul_one]
    split_ifs <;> first | (exfalso; omega) | ring1
  by_cases ht : buysAt P σ k (law P σ k) true m
  · simp only [fac_follow hf ht, stepN, tau_follow hf ht, s01, s0n, if_false, true_and,
      and_false, if_true, Bool.false_eq_true, and_true, mul_zero, add_zero, zero_add]
    simp only [sigLik, if_true, Bool.false_eq_true, if_false, Bool.true_eq_false]
    split_ifs with h1 h2 h3 h4 <;> first
      | (exfalso; omega)
      | ring1
      | (have h1' : n - 1 = Nh P σ k h := by omega
         rw [h1']; linear_combination (σ.σ k h m) * eu)
      | (have h1' : n + 1 = Nh P σ k h := by omega
         rw [h1']; linear_combination (-(σ.σ k h m)) * eu)
  · simp only [fac_never hf ht, stepN, tau_never hf ht, sn0, sn1, if_false, add_zero, true_and,
      and_false, and_true, if_true, Bool.false_eq_true, mul_zero, mul_one]
    split_ifs <;> first | (exfalso; omega) | ring1

theorem yC_feasible (hS : P.Standing) (σ : InfoPolicy M) : FeasibleLP P (yC P σ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht n i
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by rw [Finset.mem_Icc] at ht; omega⟩
    simp only [yC]
    refine Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun m _ => ?_
    split_ifs
    · exact mul_nonneg (add_nonneg (law_nonneg hS σ _ _ _) (law_nonneg hS σ _ _ _))
        (σ.nonneg _ _ _)
    · exact le_refl _
  · intro t ht n i hn
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by rw [Finset.mem_Icc] at ht; omega⟩
    have hk : k + 1 ≤ P.T := (Finset.mem_Icc.1 ht).2
    simp only [yC]
    refine Finset.sum_eq_zero fun h _ => Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg]
    rintro ⟨he, -⟩
    exact hn (he ▸ Nh_mem_pos σ hk h)
  · intro t ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by rw [Finset.mem_Icc] at ht; omega⟩
    have hk : k + 1 ≤ P.T := (Finset.mem_Icc.1 ht).2
    rw [IC_sum hS σ hk, IC_sum hS σ hk, IC_sum hS σ hk, IC_sum hS σ hk]
    refine ⟨Finset.sum_nonneg fun m _ => ?_, Finset.sum_nonpos fun m _ => ?_,
      Finset.sum_nonpos fun m _ => ?_, Finset.sum_nonneg fun m _ => ?_⟩ <;> split_ifs with hm
    · exact (buys_false_A hS σ k m).1 (tau_one hm)
    · exact le_refl _
    · exact (not_le.1 ((buys_true_A hS σ k m).not.1 (tau_neg hm))).le
    · exact le_refl _
    · exact (not_le.1 ((buys_false_A hS σ k m).not.1 (tau_zero hm).1)).le
    · exact le_refl _
    · exact (buys_true_A hS σ k m).1 (tau_zero hm).2
    · exact le_refl _
  · intro t ht n _
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 + 1 := ⟨t - 2, by rw [Finset.mem_Icc] at ht; omega⟩
    rw [show k + 1 + 1 - 1 = k + 1 from rfl, yC_flow hS σ k n]
  · intro n _
    have e := sum_i_yC (P := P) σ 0 n
    simp only [zero_add] at e
    rw [e]
    by_cases hn : n = 0
    · subst hn; simp [Nh, totL, law, prior]
    · have hn' : (0 : ℤ) ≠ n := Ne.symm hn
      simp [Nh, hn, hn']

lemma gbuy_both (hS : P.Standing) {σ : InfoPolicy M} {t : ℕ} {m : M}
    (hf : buysAt P σ t (law P σ t) false m) (v : Bool) : gbuy P σ t v m = 1 := by
  unfold gbuy; rw [Fintype.sum_bool]; simp [hf, buys_mono hS σ t m hf, sigLik_sum]

lemma gbuy_follow {σ : InfoPolicy M} {t : ℕ} {m : M}
    (hf : ¬ buysAt P σ t (law P σ t) false m) (ht : buysAt P σ t (law P σ t) true m) (v : Bool) :
    gbuy P σ t v m = sigLik P v true := by
  unfold gbuy; rw [Fintype.sum_bool]; simp [hf, ht]

lemma gbuy_never {σ : InfoPolicy M} {t : ℕ} {m : M}
    (hf : ¬ buysAt P σ t (law P σ t) false m) (ht : ¬ buysAt P σ t (law P σ t) true m) (v : Bool) :
    gbuy P σ t v m = 0 := by
  unfold gbuy; rw [Fintype.sum_bool]; simp [hf, ht]

lemma purchase_eq (hS : P.Standing) (σ : InfoPolicy M) {t : ℕ} (ht : t + 1 ≤ P.T) :
    purchaseProb P σ t = ∑ n ∈ pos P, (yC P σ (t + 1) n 1 + uN P n * yC P σ (t + 1) n 0) := by
  rw [Finset.sum_add_distrib]
  have h1 := sum_pos_y σ ht (fun _ => 1) 1
  have h2 := sum_pos_y σ ht (uN P) 0
  simp only [one_mul] at h1
  rw [h1, h2, ← Finset.sum_add_distrib]
  unfold purchaseProb
  rw [Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  change law P σ t true h * (σ.σ t h m * gbuy P σ t true m) +
    law P σ t false h * (σ.σ t h m * gbuy P σ t false m) = _
  have eu := (law_GForm hS σ t h).eq_uN hS
  unfold totL
  by_cases hf : buysAt P σ t (law P σ t) false m
  · rw [gbuy_both hS hf, gbuy_both hS hf, tau_both hf]; simp only [if_true, if_neg s10]; ring
  by_cases ht : buysAt P σ t (law P σ t) true m
  · rw [gbuy_follow hf ht, gbuy_follow hf ht, tau_follow hf ht]
    simp only [if_true, if_neg s01, sigLik, Bool.true_eq_false, if_false]
    linear_combination (σ.σ t h m) * eu
  · rw [gbuy_never hf ht, gbuy_never hf ht, tau_never hf ht]
    simp only [if_neg sn1, if_neg sn0]; ring

theorem revenue_eq (hS : P.Standing) (σ : InfoPolicy M) : revenue P σ = objLP P (yC P σ) := by
  unfold revenue objLP
  congr 1
  refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_Icc, Set.mem_Icc,
      Finset.mem_range, Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_Icc, Set.mem_Icc,
      Finset.mem_range, Finset.mem_Icc] at ha ⊢; omega
  · intro a _; simp
  · intro a ha; simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_Icc, Set.mem_Icc,
      Finset.mem_range, Finset.mem_Icc] at ha ⊢; omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    exact purchase_eq hS σ (by omega)

theorem revenue_le_LP (hS : P.Standing) (σ : InfoPolicy M) :
    ∃ y, FeasibleLP P y ∧ revenue P σ ≤ objLP P y :=
  ⟨yC P σ, yC_feasible hS σ, (revenue_eq hS σ).le⟩

end PartC

/-! ## Part D: an LP point with strict type-0 IC is realized by a recommendation policy -/

lemma sum_signType (f : SignType → ℝ) : ∑ m, f m = f 0 + f (-1) + f 1 := by
  rw [show (Finset.univ : Finset SignType) = {0, -1, 1} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

lemma fac_sum {M : Type} [Fintype M] {P : Params} (σ : InfoPolicy M) (t : ℕ) (v : Bool) (m : M) :
    fac P σ t v m true + fac P σ t v m false = 1 := by
  unfold fac
  simp only [Fintype.sum_bool]
  by_cases b1 : buysAt P σ t (law P σ t) true m <;> by_cases b2 : buysAt P σ t (law P σ t) false m <;>
    cases v <;> simp [b1, b2, sigLik]

lemma gbuy_nonneg {M : Type} [Fintype M] {P : Params} (hS : P.Standing) (σ : InfoPolicy M)
    (t : ℕ) (v : Bool) (m : M) : 0 ≤ gbuy P σ t v m := by
  unfold gbuy
  refine Finset.sum_nonneg fun s _ => ?_
  split_ifs
  · unfold sigLik; split_ifs <;> linarith [q_pos hS, q_le hS]
  · exact le_refl _

lemma purchase_Aw {M : Type} [Fintype M] {P : Params} (σ : InfoPolicy M) (t : ℕ) :
    purchaseProb P σ t = ∑ m, (gbuy P σ t true m * Aw P σ t true m +
      gbuy P σ t false m * Aw P σ t false m) := by
  show (∑ v : Bool, ∑ h, law P σ t v h * ∑ m, σ.σ t h m * gbuy P σ t v m) = _
  unfold Aw
  rw [Fintype.sum_bool, Finset.sum_add_distrib]
  congr 1 <;>
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma netPos_succ {t : ℕ} (h : Fin (t + 1) → SignType × Bool) :
    netPos h = netPos (Fin.init h) +
      (if (h (Fin.last t)).1 = 0 then (if (h (Fin.last t)).2 then 1 else -1) else 0) := by
  unfold netPos; rw [Fin.sum_univ_castSucc]; rfl

lemma netPos_abs {t : ℕ} (h : Fin t → SignType × Bool) : |netPos h| ≤ t := by
  unfold netPos
  calc |∑ i, (if (h i).1 = 0 then (if (h i).2 then (1 : ℤ) else -1) else 0)|
      ≤ ∑ i, |(if (h i).1 = 0 then (if (h i).2 then (1 : ℤ) else -1) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin t, (1 : ℤ) := Finset.sum_le_sum fun i _ => by split_ifs <;> simp
    _ = t := by simp

lemma netPos_mem_pos {P : Params} {t : ℕ} (ht : t + 1 ≤ P.T) (h : Fin t → SignType × Bool) :
    netPos h ∈ pos P := by
  have := abs_le.1 (netPos_abs h)
  rw [mem_pos_iff]; constructor <;> omega

section PartD
variable {P : Params} {y : ℕ → ℤ → SignType → ℝ}

/-- Recommendation probabilities, guarded so that they are a distribution at every time. -/
noncomputable def rG (P : Params) (y : ℕ → ℤ → SignType → ℝ) (t : ℕ) (n : ℤ) (m : SignType) : ℝ :=
  if t + 1 ≤ P.T ∧ 0 < zOf y (t + 1) n then y (t + 1) n m / zOf y (t + 1) n
  else if m = 0 then 1 else 0

lemma rG_nonneg (hy : FeasibleLP P y) (t : ℕ) (n : ℤ) (m : SignType) : 0 ≤ rG P y t n m := by
  unfold rG
  split_ifs with h1 h2
  · exact div_nonneg (hy.1 (t + 1) (by rw [Finset.mem_Icc]; omega) n m) h1.2.le
  · norm_num
  · norm_num

lemma rG_sum (t : ℕ) (n : ℤ) : ∑ m, rG P y t n m = 1 := by
  unfold rG
  by_cases h1 : t + 1 ≤ P.T ∧ 0 < zOf y (t + 1) n
  · simp only [h1, and_self, if_true]
    rw [← Finset.sum_div]; exact div_self h1.2.ne'
  · simp only [h1, if_false]
    simp

lemma rG_mul (hy : FeasibleLP P y) {t : ℕ} (ht : t + 1 ≤ P.T) (n : ℤ) (m : SignType) :
    rG P y t n m * zOf y (t + 1) n = y (t + 1) n m := by
  have hmem : t + 1 ∈ Finset.Icc 1 P.T := by rw [Finset.mem_Icc]; omega
  unfold rG
  by_cases hz : 0 < zOf y (t + 1) n
  · rw [if_pos ⟨ht, hz⟩]; field_simp
  · rw [if_neg (fun h => hz h.2)]
    have h0 : zOf y (t + 1) n = 0 := le_antisymm (not_lt.1 hz) (zOf_nonneg hy hmem n)
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hy.1 (t + 1) hmem n j)).1 h0 m
      (Finset.mem_univ _)
    rw [h0, mul_zero, h1]

noncomputable def σR (hy : FeasibleLP P y) : InfoPolicy SignType :=
  ⟨fun t h m => rG P y t (netPos h) m, fun t h m => rG_nonneg hy t _ m, fun t h => rG_sum t _⟩

noncomputable def Qv (P : Params) (σ : InfoPolicy SignType) (t : ℕ) (v : Bool) (n : ℤ) : ℝ :=
  ∑ h : Fin t → SignType × Bool, if netPos h = n then law P σ t v h else 0

lemma Qv_out (σ : InfoPolicy SignType) {t : ℕ} (ht : t + 1 ≤ P.T) (v : Bool) {n : ℤ}
    (hn : n ∉ pos P) : Qv P σ t v n = 0 :=
  Finset.sum_eq_zero fun h _ => by
    rw [if_neg]; intro he; exact hn (he ▸ netPos_mem_pos ht h)

lemma Aw_group (hy : FeasibleLP P y) {t : ℕ} (ht : t + 1 ≤ P.T) (v : Bool) (m : SignType) :
    Aw P (σR hy) t v m = ∑ n ∈ pos P, rG P y t n m * Qv P (σR hy) t v n := by
  unfold Aw Qv
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq (pos P) (netPos h), if_pos (netPos_mem_pos ht h)]
  exact mul_comm _ _

/-- The aggregated invariant at time `t`. -/
def InvD (P : Params) (y : ℕ → ℤ → SignType → ℝ) (σ : InfoPolicy SignType) (t : ℕ) : Prop :=
  ∀ n, GForm P n (Qv P σ t true n) (Qv P σ t false n) ∧
    Qv P σ t true n + Qv P σ t false n = zOf y (t + 1) n

lemma Aw_comb (hS : P.Standing) (hy : FeasibleLP P y) {t : ℕ} (ht : t + 1 ≤ P.T)
    (hI : InvD P y (σR hy) t) (α β : ℝ) (m : SignType) :
    α * Aw P (σR hy) t true m + β * Aw P (σR hy) t false m =
      ∑ n ∈ pos P, (α * vN P n + β * (1 - vN P n)) * y (t + 1) n m := by
  rw [Aw_group hy ht, Aw_group hy ht, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  obtain ⟨hG, hz⟩ := hI n
  have e := hG.eq_vN hS
  rw [← rG_mul hy ht n m, ← hz]
  linear_combination (α - β) * rG P y t n m * e

lemma Aw_IC (hS : P.Standing) (hy : FeasibleLP P y) {t : ℕ} (ht : t + 1 ≤ P.T)
    (hI : InvD P y (σR hy) t) (c : ℝ) (m : SignType) :
    Aw P (σR hy) t true m - c * (Aw P (σR hy) t true m + Aw P (σR hy) t false m) =
      ∑ n ∈ pos P, (vN P n - c) * y (t + 1) n m := by
  have := Aw_comb hS hy ht hI (1 - c) (-c) m
  rw [show Aw P (σR hy) t true m - c * (Aw P (σR hy) t true m + Aw P (σR hy) t false m) =
    (1 - c) * Aw P (σR hy) t true m + (-c) * Aw P (σR hy) t false m by ring, this]
  exact Finset.sum_congr rfl fun n _ => by ring

lemma tau0 (hS : P.Standing) (hy : FeasibleLP P y)
    (hstrict : ∀ t ∈ Finset.Icc 1 P.T, (∑ n ∈ pos P, (vN P n - vStarStar P) * y t n 0) < 0)
    {t : ℕ} (ht : t + 1 ≤ P.T) (hI : InvD P y (σR hy) t) :
    ¬ buysAt P (σR hy) t (law P (σR hy) t) false 0 ∧ buysAt P (σR hy) t (law P (σR hy) t) true 0 := by
  have hmem : t + 1 ∈ Finset.Icc 1 P.T := by rw [Finset.mem_Icc]; omega
  refine ⟨fun hb => ?_, ?_⟩
  · rw [buys_false_A hS, Aw_IC hS hy ht hI] at hb
    linarith [hstrict (t + 1) hmem]
  · rw [buys_true_A hS, Aw_IC hS hy ht hI]
    exact (hy.2.2.1 (t + 1) hmem).2.2.2

lemma buys1 (hS : P.Standing) (hy : FeasibleLP P y) {t : ℕ} (ht : t + 1 ≤ P.T)
    (hI : InvD P y (σR hy) t) : buysAt P (σR hy) t (law P (σR hy) t) false 1 := by
  have hmem : t + 1 ∈ Finset.Icc 1 P.T := by rw [Finset.mem_Icc]; omega
  rw [buys_false_A hS, Aw_IC hS hy ht hI]
  exact (hy.2.2.1 (t + 1) hmem).1

lemma Qv_succ (hS : P.Standing) (hy : FeasibleLP P y) (t : ℕ) (v : Bool) (n : ℤ) :
    Qv P (σR hy) (t + 1) v n =
      (rG P y t n 1 + rG P y t n (-1)) * Qv P (σR hy) t v n +
      fac P (σR hy) t v 0 true * rG P y t (n - 1) 0 * Qv P (σR hy) t v (n - 1) +
      fac P (σR hy) t v 0 false * rG P y t (n + 1) 0 * Qv P (σR hy) t v (n + 1) := by
  set σ := σR hy with hσ
  have e1 : ∀ h : Fin (t + 1) → SignType × Bool,
      (if netPos h = n then law P σ (t + 1) v h else 0) =
      (fun (h0 : Fin t → SignType × Bool) (x : SignType × Bool) =>
        if netPos h0 + (if x.1 = 0 then (if x.2 then 1 else -1) else 0) = n then
          law P σ t v h0 * σ.σ t h0 x.1 * fac P σ t v x.1 x.2 else 0)
        (Fin.init h) (h (Fin.last t)) := by
    intro h; simp only [netPos_succ, law_succ]
  have key := sum_snoc (X := SignType × Bool) (t := t)
    (fun (h0 : Fin t → SignType × Bool) (x : SignType × Bool) =>
        if netPos h0 + (if x.1 = 0 then (if x.2 then 1 else -1) else 0) = n then
          law P σ t v h0 * σ.σ t h0 x.1 * fac P σ t v x.1 x.2 else 0)
  beta_reduce at key
  unfold Qv
  simp only [e1]
  rw [key]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Fintype.sum_prod_type, sum_signType]
  simp only [Fintype.sum_bool]
  have fs1 := fac_sum (P := P) σ t v 1
  have fsn := fac_sum (P := P) σ t v (-1)
  have hs : ∀ m, σ.σ t h m = rG P y t (netPos h) m := fun m => rfl
  simp only [hs, if_true, s10, sn0, if_false, add_zero, Bool.false_eq_true]
  split_ifs <;> first
    | (exfalso; omega)
    | ring1
    | (subst n
       try simp only [add_sub_cancel_right, neg_add_cancel_right]
       first
        | ring1
        | linear_combination (law P σ t v h * rG P y t (netPos h) 1) * fs1 +
            (law P σ t v h * rG P y t (netPos h) (-1)) * fsn)

lemma InvD_zero (hy : FeasibleLP P y) (hT : 0 + 1 ≤ P.T) : InvD P y (σR hy) 0 := by
  intro n
  have hQ : ∀ v, Qv P (σR hy) 0 v n = if n = 0 then prior P v else 0 := by
    intro v; unfold Qv
    by_cases hn : n = 0
    · subst hn; simp [netPos, law]
    · have hn' : (0 : ℤ) ≠ n := Ne.symm hn
      simp [netPos, hn, hn']
  rw [hQ, hQ, show (0 : ℕ) + 1 = 1 from rfl]
  have h0 : (0 : ℤ) ∈ pos P := by rw [mem_pos_iff]; omega
  by_cases hn : n = 0
  · subst hn
    simp only [if_true]
    refine ⟨⟨1, zero_le_one, by simp [prior, aN], by simp [prior, bN]⟩, ?_⟩
    have := hy.2.2.2.2 0 h0
    unfold zOf; rw [this]; simp [prior]
  · simp only [hn, if_false]
    refine ⟨GForm.zero n, ?_⟩
    by_cases hp : n ∈ pos P
    · have := hy.2.2.2.2 n hp
      unfold zOf; rw [this, if_neg hn]; ring
    · unfold zOf
      rw [Finset.sum_eq_zero fun i _ => hy.2.1 1 (by rw [Finset.mem_Icc]; omega) n i hp]; ring

lemma InvD_succ (hS : P.Standing) (hy : FeasibleLP P y)
    (hstrict : ∀ t ∈ Finset.Icc 1 P.T, (∑ n ∈ pos P, (vN P n - vStarStar P) * y t n 0) < 0)
    {t : ℕ} (ht : t + 1 + 1 ≤ P.T) (hI : InvD P y (σR hy) t) : InvD P y (σR hy) (t + 1) := by
  have ht1 : t + 1 ≤ P.T := by omega
  obtain ⟨hf0, ht0⟩ := tau0 hS hy hstrict ht1 hI
  have fT : ∀ v, fac P (σR hy) t v 0 true = sigLik P v true := fun v => by
    simp [fac_follow hf0 ht0]
  have fF : ∀ v, fac P (σR hy) t v 0 false = sigLik P v false := fun v => by
    simp [fac_follow hf0 ht0]
  intro n
  have hr1 := add_nonneg (rG_nonneg hy t n 1) (rG_nonneg hy t n (-1))
  obtain ⟨hGn, hzn⟩ := hI n
  obtain ⟨hGm, hzm⟩ := hI (n - 1)
  obtain ⟨hGp, hzp⟩ := hI (n + 1)
  refine ⟨?_, ?_⟩
  · rw [Qv_succ hS hy, Qv_succ hS hy, fT, fT, fF, fF]
    simp only [sigLik, if_true, Bool.false_eq_true, Bool.true_eq_false, if_false]
    have g1 := hGn.smul hr1
    have g2 := ((hGm.step_true hS).smul (rG_nonneg hy t (n - 1) 0)).of_eq (n' := n) (by ring) rfl rfl
    have g3 := ((hGp.step_false hS).smul (rG_nonneg hy t (n + 1) 0)).of_eq (n' := n) (by ring) rfl rfl
    exact ((g1.add g2).add g3).of_eq rfl (by ring) (by ring)
  · by_cases hp : n ∈ pos P
    · rw [Qv_succ hS hy, Qv_succ hS hy, fT, fT, fF, fF]
      simp only [sigLik, if_true, Bool.false_eq_true, Bool.true_eq_false, if_false]
      have hmem : t + 1 + 1 ∈ Finset.Icc 2 P.T := by rw [Finset.mem_Icc]; omega
      have flow := hy.2.2.2.1 (t + 1 + 1) hmem n hp
      rw [show t + 1 + 1 - 1 = t + 1 from rfl] at flow
      have eum := hGm.eq_uN hS
      have eup := hGp.eq_uN hS
      have a1 := rG_mul hy ht1 n 1
      have a2 := rG_mul hy ht1 n (-1)
      have a3 := rG_mul hy ht1 (n - 1) 0
      have a4 := rG_mul hy ht1 (n + 1) 0
      rw [← hzn] at a1 a2; rw [← hzm] at a3; rw [← hzp] at a4
      unfold zOf
      linear_combination a1 + a2 + rG P y t (n - 1) 0 * eum + uN P (n - 1) * a3 -
        rG P y t (n + 1) 0 * eup + (1 - uN P (n + 1)) * a4 - flow
    · rw [Qv_out (σR hy) ht true hp, Qv_out (σR hy) ht false hp]
      unfold zOf
      rw [Finset.sum_eq_zero fun i _ => hy.2.1 (t + 1 + 1) (by rw [Finset.mem_Icc]; omega) n i hp]
      ring

lemma InvD_all (hS : P.Standing) (hy : FeasibleLP P y)
    (hstrict : ∀ t ∈ Finset.Icc 1 P.T, (∑ n ∈ pos P, (vN P n - vStarStar P) * y t n 0) < 0) :
    ∀ t, t + 1 ≤ P.T → InvD P y (σR hy) t := by
  intro t
  induction t with
  | zero => intro ht; exact InvD_zero hy ht
  | succ t ih => intro ht; exact InvD_succ hS hy hstrict ht (ih (by omega))

lemma purchase_ge (hS : P.Standing) (hy : FeasibleLP P y)
    (hstrict : ∀ t ∈ Finset.Icc 1 P.T, (∑ n ∈ pos P, (vN P n - vStarStar P) * y t n 0) < 0)
    {t : ℕ} (ht : t + 1 ≤ P.T) :
    ∑ n ∈ pos P, (y (t + 1) n 1 + uN P n * y (t + 1) n 0) ≤ purchaseProb P (σR hy) t := by
  have hI := InvD_all hS hy hstrict t ht
  obtain ⟨hf0, ht0⟩ := tau0 hS hy hstrict ht hI
  have hb1 := buys1 hS hy ht hI
  rw [purchase_Aw, sum_signType, gbuy_follow hf0 ht0, gbuy_follow hf0 ht0, gbuy_both hS hb1,
    gbuy_both hS hb1]
  rw [Aw_comb hS hy ht hI _ _ 0, Aw_comb hS hy ht hI 1 1 1]
  have hneg : 0 ≤ gbuy P (σR hy) t true (-1) * Aw P (σR hy) t true (-1) +
      gbuy P (σR hy) t false (-1) * Aw P (σR hy) t false (-1) :=
    add_nonneg (mul_nonneg (gbuy_nonneg hS _ t true _) (Aw_nonneg hS _ t true _))
      (mul_nonneg (gbuy_nonneg hS _ t false _) (Aw_nonneg hS _ t false _))
  have s0 : ∑ n ∈ pos P, (sigLik P true true * vN P n + sigLik P false true * (1 - vN P n)) *
      y (t + 1) n 0 = ∑ n ∈ pos P, uN P n * y (t + 1) n 0 :=
    Finset.sum_congr rfl fun n _ => by simp only [sigLik, uN, if_true, Bool.true_eq_false, if_false]
  have s1 : ∑ n ∈ pos P, (1 * vN P n + 1 * (1 - vN P n)) * y (t + 1) n 1 =
      ∑ n ∈ pos P, y (t + 1) n 1 := Finset.sum_congr rfl fun n _ => by ring
  rw [s0, s1, Finset.sum_add_distrib]
  linarith

theorem LP_realize (hS : P.Standing) (y : ℕ → ℤ → SignType → ℝ) (hy : FeasibleLP P y)
    (hstrict : ∀ t ∈ Finset.Icc 1 P.T, (∑ n ∈ pos P, (vN P n - vStarStar P) * y t n 0) < 0) :
    ∃ σ : InfoPolicy SignType, objLP P y ≤ revenue P σ := by
  refine ⟨σR hy, ?_⟩
  unfold objLP revenue
  refine mul_le_mul_of_nonneg_left ?_ hS.1.le
  have e : ∑ t ∈ Finset.Icc 1 P.T, ∑ n ∈ pos P, (y t n 1 + uN P n * y t n 0) =
      ∑ t ∈ Finset.range P.T, ∑ n ∈ pos P, (y (t + 1) n 1 + uN P n * y (t + 1) n 0) := by
    refine Finset.sum_nbij' (· - 1) (· + 1) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_Icc, Set.mem_Icc,
        Finset.mem_range, Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_Icc, Set.mem_Icc,
        Finset.mem_range, Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_Icc, Set.mem_Icc,
        Finset.mem_range, Finset.mem_Icc] at ha ⊢; omega
    · intro a _; simp
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      rw [Nat.sub_add_cancel ha.1]
  rw [e]
  exact Finset.sum_le_sum fun t ht => purchase_ge hS hy hstrict (by simp at ht; omega)

/-! ## Mixing -/

def mixY (y0 y1 : ℕ → ℤ → SignType → ℝ) (l : ℝ) : ℕ → ℤ → SignType → ℝ :=
  fun t n i => (1 - l) * y0 t n i + l * y1 t n i

lemma sum_mix {α : Type} (s : Finset α) (c a b : α → ℝ) (l : ℝ) :
    ∑ x ∈ s, c x * ((1 - l) * a x + l * b x) = (1 - l) * ∑ x ∈ s, c x * a x + l * ∑ x ∈ s, c x * b x := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

lemma sum_mix' {α : Type} (s : Finset α) (a b : α → ℝ) (l : ℝ) :
    ∑ x ∈ s, ((1 - l) * a x + l * b x) = (1 - l) * ∑ x ∈ s, a x + l * ∑ x ∈ s, b x := by
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

lemma comb_nonneg {a b l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (1 - l) * a + l * b := by nlinarith

lemma comb_nonpos {a b l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (ha : a ≤ 0) (hb : b ≤ 0) :
    (1 - l) * a + l * b ≤ 0 := by nlinarith

lemma mix_feasible {y0 y1 : ℕ → ℤ → SignType → ℝ} (h0 : FeasibleLP P y0) (h1 : FeasibleLP P y1)
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) : FeasibleLP P (mixY y0 y1 l) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht n i
    exact comb_nonneg hl0 hl1 (h0.1 t ht n i) (h1.1 t ht n i)
  · intro t ht n i hn
    simp only [mixY, h0.2.1 t ht n i hn, h1.2.1 t ht n i hn]; ring
  · intro t ht
    obtain ⟨a1, a2, a3, a4⟩ := h0.2.2.1 t ht
    obtain ⟨b1, b2, b3, b4⟩ := h1.2.2.1 t ht
    simp only [mixY]
    rw [sum_mix, sum_mix, sum_mix, sum_mix]
    exact ⟨comb_nonneg hl0 hl1 a1 b1, comb_nonpos hl0 hl1 a2 b2, comb_nonpos hl0 hl1 a3 b3,
      comb_nonneg hl0 hl1 a4 b4⟩
  · intro t ht n hn
    simp only [mixY]
    rw [sum_mix', h0.2.2.2.1 t ht n hn, h1.2.2.2.1 t ht n hn]; ring
  · intro n hn
    simp only [mixY]
    rw [sum_mix', h0.2.2.2.2 n hn, h1.2.2.2.2 n hn]; split_ifs <;> ring

lemma mix_obj (y0 y1 : ℕ → ℤ → SignType → ℝ) (l : ℝ) :
    objLP P (mixY y0 y1 l) = (1 - l) * objLP P y0 + l * objLP P y1 := by
  unfold objLP mixY
  have e : ∀ t n, ((1 - l) * y0 t n 1 + l * y1 t n 1) + uN P n * ((1 - l) * y0 t n 0 + l * y1 t n 0) =
      (1 - l) * (y0 t n 1 + uN P n * y0 t n 0) + l * (y1 t n 1 + uN P n * y1 t n 0) := by
    intros; ring
  simp only [e, sum_mix']
  ring

lemma mix_strict {y0 y1 : ℕ → ℤ → SignType → ℝ} (h0 : FeasibleLP P y0)
    (hs1 : ∀ t ∈ Finset.Icc 1 P.T, (∑ n ∈ pos P, (vN P n - vStarStar P) * y1 t n 0) < 0)
    {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    ∀ t ∈ Finset.Icc 1 P.T, (∑ n ∈ pos P, (vN P n - vStarStar P) * mixY y0 y1 l t n 0) < 0 := by
  intro t ht
  simp only [mixY]
  rw [sum_mix]
  have a := (h0.2.2.1 t ht).2.2.1
  have b := hs1 t ht
  nlinarith

end PartD

end TLSProof

open TimeLockedSales.Reform in
theorem solution (P : Params) (hS : P.Standing) (hR : P.Region) :
    ∃ π : ℝ,
      IsGreatest {J | ∃ y, FeasibleLP P y ∧ J = objLP P y} π ∧
      IsGreatest {J | ∃ r z, Feasible9 P r z ∧ J = obj9 P r z} π ∧
      IsLUB (AchievableRevenue P) π ∧
      ∀ y, FeasibleLP P y → objLP P y = π →
        ∀ r, Recovers P y r →
          Feasible9 P r (zOf y) ∧ obj9 P r (zOf y) = π := by
  obtain ⟨y₀, hy₀, hmax, h1, h2, h4⟩ := TLSProof.LP_nine_part hS hR
  refine ⟨objLP P y₀, h1, h2, ⟨?_, ?_⟩, h4⟩
  · rintro J ⟨M, hM, σ, rfl⟩
    obtain ⟨y, hy, hle⟩ := TLSProof.revenue_le_LP hS σ
    exact hle.trans (hmax y hy)
  · intro b hb
    obtain ⟨hF, hFs⟩ := TLSProof.yF_feasible hS hR
    have key : ∀ l : ℝ, 0 < l → l ≤ 1 →
        (1 - l) * objLP P y₀ + l * objLP P (TLSProof.yF P) ≤ b := by
      intro l hl0 hl1
      obtain ⟨σ, hσ⟩ := TLSProof.LP_realize hS _ (TLSProof.mix_feasible hy₀ hF hl0.le hl1)
        (TLSProof.mix_strict hy₀ hFs hl0 hl1)
      rw [TLSProof.mix_obj] at hσ
      exact hσ.trans (hb ⟨SignType, inferInstance, σ, rfl⟩)
    by_contra hlt
    rw [not_le] at hlt
    have hd : 0 < |objLP P (TLSProof.yF P) - objLP P y₀| + 1 := by positivity
    have hpos : 0 < (objLP P y₀ - b) / (2 * (|objLP P (TLSProof.yF P) - objLP P y₀| + 1)) :=
      div_pos (by linarith) (by positivity)
    have hl0 : 0 < min 1 ((objLP P y₀ - b) / (2 * (|objLP P (TLSProof.yF P) - objLP P y₀| + 1))) :=
      lt_min one_pos hpos
    have hl1 := min_le_left (1 : ℝ)
      ((objLP P y₀ - b) / (2 * (|objLP P (TLSProof.yF P) - objLP P y₀| + 1)))
    have hl2 := min_le_right (1 : ℝ)
      ((objLP P y₀ - b) / (2 * (|objLP P (TLSProof.yF P) - objLP P y₀| + 1)))
    set l := min 1 ((objLP P y₀ - b) / (2 * (|objLP P (TLSProof.yF P) - objLP P y₀| + 1)))
    have h3 : l * (2 * (|objLP P (TLSProof.yF P) - objLP P y₀| + 1)) ≤ objLP P y₀ - b :=
      (le_div_iff₀ (by positivity)).1 hl2
    have h5 : l * -|objLP P (TLSProof.yF P) - objLP P y₀| ≤
        l * (objLP P (TLSProof.yF P) - objLP P y₀) :=
      mul_le_mul_of_nonneg_left (neg_abs_le _) hl0.le
    have := key l hl0 hl1
    nlinarith

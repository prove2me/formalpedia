-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P01.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:22:14.61687+00:00
-- url     : https://prove2.me/submissions/6d90715d-13f6-4ecb-bdff-4b8748fb8656

import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P01_lemma_3_5
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P01_lemma_3_6
noncomputable section

open scoped BigOperators Classical

namespace X8L25
variable {R : Type*} [CommRing R]
lemma span_map {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {s : Set M} {Q : Submodule R N} (L : M →ₗ[R] N) (h : ∀ z ∈ s, L z ∈ Q) {z : M}
    (hz : z ∈ Submodule.span R s) : L z ∈ Q :=
  (Submodule.span_le.mpr (fun z hz => h z hz) : Submodule.span R s ≤ Q.comap L) hz
end X8L25


namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L25C

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma rel {a b : FreeAlgebra R (CyclotomicLetter n)} (h : NonsplitBMWRel P n a b) :
    presentationMap P n a = presentationMap P n b :=
  RingQuot.mkAlgHom_rel R h

lemma x_xi (i : ℕ) (hi : 1 ≤ i ∧ i < n) : X P n i false * X P n i true = 1 := by
  have := rel P n (NonsplitBMWRel.invL i hi); simpa [X, map_mul] using this

lemma xi_x (i : ℕ) (hi : 1 ≤ i ∧ i < n) : X P n i true * X P n i false = 1 := by
  have := rel P n (NonsplitBMWRel.invR i hi); simpa [X, map_mul] using this

lemma nearL (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 = j ∨ j + 1 = i) :
    X P n i false * X P n j false * E P n i = E P n j * E P n i := by
  have := rel P n (NonsplitBMWRel.nearL i j hi hj hd); simpa [X, E, map_mul] using this

lemma nearR (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 = j ∨ j + 1 = i) :
    E P n j * X P n i false * X P n j false = E P n j * E P n i := by
  have := rel P n (NonsplitBMWRel.nearR i j hi hj hd); simpa [X, E, map_mul] using this

lemma tripleE (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 = j ∨ j + 1 = i) :
    E P n i * E P n j * E P n i = E P n i := by
  have := rel P n (NonsplitBMWRel.tripleE i j hi hj hd); simpa [E, map_mul] using this

lemma xeFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 < j ∨ j + 1 < i) :
    X P n i false * E P n j = E P n j * X P n i false := by
  have := rel P n (NonsplitBMWRel.xeFar i j hi hj hd); simpa [X, E, map_mul] using this

lemma xFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 < j ∨ j + 1 < i) :
    X P n i false * X P n j false = X P n j false * X P n i false := by
  have := rel P n (NonsplitBMWRel.xFar i j hi hj hd); simpa [X, map_mul] using this

lemma braid (i : ℕ) (hi : 1 ≤ i ∧ i + 1 < n) :
    X P n i false * X P n (i+1) false * X P n i false =
      X P n (i+1) false * X P n i false * X P n (i+1) false := by
  have := rel P n (NonsplitBMWRel.braid i hi); simpa [X, map_mul] using this

lemma ye (i : ℕ) (hi : 1 < i ∧ i < n) : Y P n false * E P n i = E P n i * Y P n false := by
  have := rel P n (NonsplitBMWRel.ye i hi); simpa [Y, E, map_mul] using this

lemma yx (i : ℕ) (hi : 1 < i ∧ i < n) : Y P n false * X P n i false = X P n i false * Y P n false := by
  have := rel P n (NonsplitBMWRel.yx i hi); simpa [Y, X, map_mul] using this

lemma skein (i : ℕ) (hi : 1 ≤ i ∧ i < n) :
    X P n i false - X P n i true = skeinDelta P • (1 - E P n i) := by
  have h := rel P n (NonsplitBMWRel.skein i hi)
  simp only [map_sub, map_mul, map_one, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma xe (i : ℕ) (hi : 1 ≤ i ∧ i < n) : X P n i false * E P n i = (P.lam : R) • E P n i := by
  have h := rel P n (NonsplitBMWRel.xe i hi)
  simp only [map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma ex (i : ℕ) (hi : 1 ≤ i ∧ i < n) : E P n i * X P n i false = (P.lam : R) • E P n i := by
  have h := rel P n (NonsplitBMWRel.ex i hi)
  simp only [map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma sqE (i : ℕ) (hi : 1 ≤ i ∧ i < n) : E P n i * E P n i = loopZero P • E P n i := by
  have h := rel P n (NonsplitBMWRel.squareE i hi)
  simp only [map_pow, map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def, ← pow_two]; exact h

lemma affine (hn : 2 ≤ n) :
    X P n 1 false * Y P n false * X P n 1 false * Y P n false =
      Y P n false * X P n 1 false * Y P n false * X P n 1 false := by
  have := rel P n (NonsplitBMWRel.affine hn); simpa [X, Y, map_mul] using this

lemma unwrapL (hn : 2 ≤ n) :
    Y P n false * X P n 1 false * Y P n false * E P n 1 = (↑P.lam⁻¹ : R) • E P n 1 := by
  have h := rel P n (NonsplitBMWRel.unwrapL hn)
  simp only [map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma unwrapR (hn : 2 ≤ n) :
    E P n 1 * Y P n false * X P n 1 false * Y P n false = (↑P.lam⁻¹ : R) • E P n 1 := by
  have h := rel P n (NonsplitBMWRel.unwrapR hn)
  simp only [map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma yinv1 (hn : 0 < n) : Y P n false * Y P n true = 1 := by
  have := rel P n (NonsplitBMWRel.yInvL hn); simpa [Y, map_mul] using this

lemma yinv2 (hn : 0 < n) : Y P n true * Y P n false = 1 := by
  have := rel P n (NonsplitBMWRel.yInvR hn); simpa [Y, map_mul] using this

lemma cyc (hn : 0 < n) :
    Y P n false ^ k = ∑ j : Fin k, P.coeff j • Y P n false ^ j.val := by
  have h := rel P n (NonsplitBMWRel.cyclotomic hn)
  simp only [map_pow, map_sum, map_mul, AlgHom.commutes] at h
  simp only [Algebra.smul_def]; exact h

lemma loopr (m : Fin k) (hn : 2 ≤ n) :
    E P n 1 * Y P n false ^ m.val * E P n 1 = P.loop m • E P n 1 := by
  have h := rel P n (NonsplitBMWRel.loop m hn)
  simp only [map_pow, map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma JM_succ (inv : Bool) (i : ℕ) (hi : 1 ≤ i) :
    JM P n inv (i+1) = X P n i inv * JM P n inv i * X P n i inv := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rfl

lemma jm_inv (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    JM P n false i * JM P n true i = 1 ∧ JM P n true i * JM P n false i = 1 := by
  induction i, hi using Nat.le_induction with
  | base => exact ⟨yinv1 P n (by omega), yinv2 P n (by omega)⟩
  | succ i hi ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [JM_succ P n false i hi, JM_succ P n true i hi]
    have a1 := x_xi P n i ⟨hi, by omega⟩
    have a2 := xi_x P n i ⟨hi, by omega⟩
    constructor
    · calc X P n i false * JM P n false i * X P n i false * (X P n i true * JM P n true i * X P n i true)
          = X P n i false * JM P n false i * (X P n i false * X P n i true) * JM P n true i * X P n i true := by
            simp only [mul_assoc]
        _ = 1 := by rw [a1, mul_one, mul_assoc (X P n i false), h1, mul_one, a1]
    · calc X P n i true * JM P n true i * X P n i true * (X P n i false * JM P n false i * X P n i false)
          = X P n i true * JM P n true i * (X P n i true * X P n i false) * JM P n false i * X P n i false := by
            simp only [mul_assoc]
        _ = 1 := by rw [a2, mul_one, mul_assoc (X P n i true), h2, mul_one, a2]

lemma jx_comm (j : ℕ) (hj : 1 ≤ j) : ∀ m, j + 1 ≤ m → m < n →
    JM P n false j * X P n m false = X P n m false * JM P n false j := by
  induction j, hj using Nat.le_induction with
  | base => intro m hm hmn; exact yx P n m ⟨by omega, hmn⟩
  | succ j hj ih =>
    intro m hm hmn
    have h1 := ih m (by omega) hmn
    have h2 := xFar P n j m ⟨hj, by omega⟩ ⟨by omega, hmn⟩ (Or.inl (by omega))
    rw [JM_succ P n false j hj]
    exact ((Commute.mul_left (Commute.mul_left h2 h1) h2) : Commute _ _).eq

lemma je_comm (j : ℕ) (hj : 1 ≤ j) : ∀ m, j + 1 ≤ m → m < n →
    JM P n false j * E P n m = E P n m * JM P n false j := by
  induction j, hj using Nat.le_induction with
  | base => intro m hm hmn; exact ye P n m ⟨by omega, hmn⟩
  | succ j hj ih =>
    intro m hm hmn
    have h1 := ih m (by omega) hmn
    have h2 := xeFar P n j m ⟨hj, by omega⟩ ⟨by omega, hmn⟩ (Or.inl (by omega))
    rw [JM_succ P n false j hj]
    exact ((Commute.mul_left (Commute.mul_left h2 h1) h2) : Commute _ _).eq

lemma jj_succ (j : ℕ) (hj : 1 ≤ j) (hjn : j + 1 ≤ n) :
    JM P n false j * JM P n false (j+1) = JM P n false (j+1) * JM P n false j := by
  induction j, hj using Nat.le_induction with
  | base =>
    rw [JM_succ P n false 1 le_rfl]
    show Y P n false * (X P n 1 false * Y P n false * X P n 1 false) =
      X P n 1 false * Y P n false * X P n 1 false * Y P n false
    have := (affine P n (by omega)).symm
    simpa only [mul_assoc] using this
  | succ j hj ih =>
    have ih := ih (by omega)
    rw [JM_succ P n false (j+1) (by omega), JM_succ P n false j hj] at *
    set a := X P n j false
    set b := X P n (j+1) false
    set c := JM P n false j
    have br0 : a * (b * a) = b * (a * b) := by
      have := braid P n j ⟨hj, by omega⟩; simpa only [mul_assoc] using this
    have br : ∀ z, a * (b * (a * z)) = b * (a * (b * z)) := by
      intro z; rw [← mul_assoc b, ← mul_assoc a, br0, mul_assoc, mul_assoc]
    have cb : ∀ z, c * (b * z) = b * (c * z) := by
      intro z; rw [← mul_assoc, jx_comm P n j hj (j+1) le_rfl (by omega), mul_assoc]
    have ih' : ∀ z, c * (a * (c * (a * z))) = a * (c * (a * (c * z))) := by
      intro z; have := congrArg (· * z) ih; simpa only [mul_assoc] using this
    simp only [mul_assoc]
    conv_lhs => rw [br (c * (a * b)), cb (a * (b * (c * (a * b)))), ← cb (a * b), ← br0,
      ih' (b * a), br (c * (a * (c * (b * a))))]
    conv_rhs => rw [br (c * a), cb (a * (b * (c * a))), ← cb a]

lemma jj_comm (j : ℕ) (hj : 1 ≤ j) : ∀ m, j < m → m ≤ n →
    JM P n false j * JM P n false m = JM P n false m * JM P n false j := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => intro h; exact jj_succ P n j hj h
  | succ m hm ih =>
    intro hmn
    have h1 : Commute (JM P n false j) (JM P n false m) := ih (by omega)
    have h2 : Commute (JM P n false j) (X P n m false) := jx_comm P n j hj m hm (by omega)
    rw [JM_succ P n false m (by omega)]
    exact ((h2.mul_right h1).mul_right h2).eq

def uU (i : ℕ) : (NonsplitBMW P n)ˣ :=
  if h : 1 ≤ i ∧ i ≤ n then
    ⟨JM P n false i, JM P n true i, (jm_inv P n i h.1 h.2).1, (jm_inv P n i h.1 h.2).2⟩
  else 1

lemma uU_val (i : ℕ) (h : 1 ≤ i ∧ i ≤ n) : (uU P n i : NonsplitBMW P n) = JM P n false i := by
  simp [uU, h]

lemma uU_inv_val (i : ℕ) (h : 1 ≤ i ∧ i ≤ n) :
    (↑(uU P n i)⁻¹ : NonsplitBMW P n) = JM P n true i := by
  simp [uU, h]

lemma uU_val_any (i : ℕ) (h : ¬ (1 ≤ i ∧ i ≤ n)) : (uU P n i : NonsplitBMW P n) = 1 := by
  simp [uU, h]

/-- Every integer power of Y lies in the span of Y^m, m < k. -/
lemma ypow (hn : 0 < n) (p : ℤ) :
    (↑(uU P n 1 ^ p) : NonsplitBMW P n) ∈
      Submodule.span R (Set.range fun m : Fin k => Y P n false ^ m.val) := by
  set W := Submodule.span R (Set.range fun m : Fin k => Y P n false ^ m.val)
  have hgen : ∀ m, m < k → Y P n false ^ m ∈ W := fun m hm =>
    Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩
  have hv : (uU P n 1 : NonsplitBMW P n) = Y P n false := uU_val P n 1 ⟨le_rfl, hn⟩
  have hvi : (↑(uU P n 1)⁻¹ : NonsplitBMW P n) = Y P n true := uU_inv_val P n 1 ⟨le_rfl, hn⟩
  have hYk : Y P n false ^ k ∈ W := by
    rw [cyc P n hn]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hgen j.val j.isLt))
  have hY : ∀ w ∈ W, Y P n false * w ∈ W := by
    intro w hw
    refine X8L25.span_map (LinearMap.mulLeft R (Y P n false)) (Q := W) ?_ hw
    rintro _ ⟨⟨m, hm⟩, rfl⟩
    simp only [LinearMap.mulLeft_apply, ← pow_succ']
    rcases Nat.lt_or_ge (m+1) k with h | h
    · exact hgen _ h
    · obtain rfl : m + 1 = k := by omega
      exact hYk
  have hYinv : Y P n true ∈ W := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := P.positive; omega⟩
    have hc := cyc P n hn
    rw [Fin.sum_univ_succ] at hc
    have hc0 : P.coeff 0 = (P.constant : R) := by
      rw [← P.constant_eq]; rfl
    set w0 := Y P n false ^ k' - ∑ j : Fin k', P.coeff j.succ • Y P n false ^ j.val with hw0
    have h1 : Y P n false * w0 = (P.constant : R) • (1 : NonsplitBMW P n) := by
      rw [hw0, mul_sub, ← pow_succ', hc, Finset.mul_sum, hc0]
      simp only [Fin.val_zero, pow_zero, Fin.val_succ, mul_smul_comm, ← pow_succ']
      abel
    have h2 : w0 = (P.constant : R) • Y P n true := by
      have := congrArg (Y P n true * ·) h1
      simp only [← mul_assoc, yinv2 P n hn, one_mul, mul_smul_comm, mul_one] at this
      exact this
    have h3 : Y P n true = (↑P.constant⁻¹ : R) • w0 := by
      rw [h2, smul_smul, Units.inv_mul, one_smul]
    rw [h3]
    refine Submodule.smul_mem _ _ (sub_mem (hgen _ (by omega)) ?_)
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hgen _ (by omega)))
  have hYi : ∀ w ∈ W, Y P n true * w ∈ W := by
    intro w hw
    refine X8L25.span_map (LinearMap.mulLeft R (Y P n true)) (Q := W) ?_ hw
    rintro _ ⟨⟨m, hm⟩, rfl⟩
    simp only [LinearMap.mulLeft_apply]
    rcases m with _ | m
    · simpa using hYinv
    · rw [pow_succ', ← mul_assoc, yinv2 P n hn, one_mul]
      exact hgen _ (by omega)
  induction p using Int.induction_on with
  | zero => simpa using hgen 0 P.positive
  | succ t ih =>
    rw [show (t:ℤ) + 1 = 1 + t by ring, zpow_add, zpow_one, Units.val_mul, hv]
    exact hY _ ih
  | pred t ih =>
    rw [show (-(t:ℤ) - 1) = -1 + -(t:ℤ) by ring, zpow_add, zpow_neg_one, Units.val_mul, hvi]
    exact hYi _ ih

end X8L25C

namespace X8L33

set_option linter.unusedSectionVars false

open X8L25C

section ip
variable {M : Type*} [Monoid M] (a : ℕ → M)

lemma ip_self (s : ℕ) : intervalProduct a s s = 1 := by simp [intervalProduct]

lemma ip_snoc {s t : ℕ} (h : s ≤ t) :
    intervalProduct a s (t+1) = intervalProduct a s t * a t := by
  unfold intervalProduct
  rw [show t + 1 - s = (t - s) + 1 by omega, List.range_succ, List.map_append, List.prod_append]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  congr 2; omega

lemma ip_cons {s t : ℕ} (h : s < t) :
    intervalProduct a s t = a s * intervalProduct a (s+1) t := by
  unfold intervalProduct
  rw [show t - s = (t - (s+1)) + 1 by omega, List.range_succ_eq_map]
  simp only [List.map_cons, List.prod_cons, List.map_map, add_zero]
  congr 2
  apply List.map_congr_left
  intro j _; simp only [Function.comp_apply]; congr 1; omega

lemma ip_one {s : ℕ} : intervalProduct a s (s+1) = a s := by
  rw [ip_snoc a le_rfl, ip_self, one_mul]

lemma ip_split {s u t : ℕ} (h1 : s ≤ u) (h2 : u ≤ t) :
    intervalProduct a s t = intervalProduct a s u * intervalProduct a u t := by
  induction t, h2 using Nat.le_induction with
  | base => rw [ip_self, mul_one]
  | succ t ht ih => rw [ip_snoc a (by omega), ip_snoc a ht, ih, mul_assoc]

lemma ip_comm (y : M) {s t : ℕ} (h : ∀ k, s ≤ k → k < t → Commute (a k) y) :
    Commute (intervalProduct a s t) y := by
  unfold intervalProduct
  apply Commute.list_prod_left
  intro z hz
  simp only [List.mem_map, List.mem_range] at hz
  obtain ⟨j, hj, rfl⟩ := hz
  exact h _ (by omega) (by omega)

end ip

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma ip_mem (S : Subalgebra R (NonsplitBMW P n)) (a : ℕ → NonsplitBMW P n) {s t : ℕ}
    (h : ∀ k, s ≤ k → k < t → a k ∈ S) : intervalProduct a s t ∈ S := by
  unfold intervalProduct
  apply Subalgebra.list_prod_mem
  intro z hz
  simp only [List.mem_map, List.mem_range] at hz
  obtain ⟨j, hj, rfl⟩ := hz
  exact h _ (by omega) (by omega)

/-! level membership -/

lemma lv_X (inv : Bool) {i l : ℕ} (h1 : 1 ≤ i) (h2 : i < l) : X P n i inv ∈ level P n l :=
  Algebra.subset_adjoin (Or.inr ⟨i, h1, h2, by cases inv <;> simp⟩)

lemma lv_E {i l : ℕ} (h1 : 1 ≤ i) (h2 : i < l) : E P n i ∈ level P n l :=
  Algebra.subset_adjoin (Or.inr ⟨i, h1, h2, by simp⟩)

lemma lv_Y (inv : Bool) {l : ℕ} (h : 1 ≤ l) : Y P n inv ∈ level P n l :=
  Algebra.subset_adjoin (Or.inl ⟨h, by cases inv <;> simp⟩)

lemma lv_mono {l l' : ℕ} (h : l ≤ l') : level P n l ≤ level P n l' := by
  apply Algebra.adjoin_mono
  rintro z (⟨h1, hz⟩ | ⟨i, h1, h2, hz⟩)
  · exact Or.inl ⟨by omega, hz⟩
  · exact Or.inr ⟨i, h1, by omega, hz⟩

lemma lv_JM (inv : Bool) {i l : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ l) : JM P n inv i ∈ level P n l := by
  induction i, h1 using Nat.le_induction with
  | base => exact lv_Y P n inv (by omega)
  | succ i hi ih =>
    rw [JM_succ P n inv i hi]
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (lv_X P n inv hi (by omega)) (ih (by omega)))
      (lv_X P n inv hi (by omega))

lemma lv_JP {i l : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ l) (p : ℤ) : JPower P n i p ∈ level P n l := by
  unfold JPower
  split_ifs
  · exact Subalgebra.pow_mem _ (lv_JM P n false h1 h2) _
  · exact Subalgebra.pow_mem _ (lv_JM P n true h1 h2) _

lemma lv_ipX {s t l : ℕ} (hs : 1 ≤ s) (ht : t ≤ l) :
    intervalProduct (fun t => X P n t false) s t ∈ level P n l :=
  ip_mem P n _ _ (fun k h1 h2 => lv_X P n false (by omega) (by omega))

lemma lv_ipE {s t l : ℕ} (hs : 1 ≤ s) (ht : t ≤ l) :
    intervalProduct (E P n) s t ∈ level P n l :=
  ip_mem P n _ _ (fun k h1 h2 => lv_E P n (by omega) (by omega))

lemma lv_M {i l : ℕ} (h : i ≤ l + 1) (s : Fin (i-1) → ℤ) :
    (List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod ∈ level P n l := by
  apply Subalgebra.list_prod_mem
  intro z hz
  rw [List.mem_ofFn] at hz
  obtain ⟨j, rfl⟩ := hz
  exact lv_JP P n (by omega) (by have := j.isLt; omega) _

/-! alphaSpan helpers -/

lemma ac_def (i j l : ℕ) (p : ℤ) : alphaChain P n i j l p =
    JPower P n i p * intervalProduct (fun t => X P n t false) i j * intervalProduct (E P n) j (l+1) :=
  rfl

lemma as_mem {l : ℕ} {F : ℕ → ℤ → Prop} (i' j' : ℕ) (p' : ℤ) (h1 : 1 ≤ i') (h2 : i' ≤ j')
    (h3 : j' ≤ l) (hF : F i' p') {b : NonsplitBMW P n} (hb : b ∈ level P n (l-1)) :
    alphaChain P n i' j' l p' * b ∈ alphaSpan P n l F :=
  Submodule.subset_span ⟨i', j', p', h1, h2, h3, hF, b, hb, rfl⟩

lemma as_mem1 {l : ℕ} {F : ℕ → ℤ → Prop} (i' j' : ℕ) (p' : ℤ) (h1 : 1 ≤ i') (h2 : i' ≤ j')
    (h3 : j' ≤ l) (hF : F i' p') : alphaChain P n i' j' l p' ∈ alphaSpan P n l F := by
  simpa using as_mem P n i' j' p' h1 h2 h3 hF (Subalgebra.one_mem _)

lemma as_mul {l : ℕ} {F : ℕ → ℤ → Prop} {z : NonsplitBMW P n} (hz : z ∈ alphaSpan P n l F)
    {b : NonsplitBMW P n} (hb : b ∈ level P n (l-1)) : z * b ∈ alphaSpan P n l F := by
  have := X8L25.span_map (LinearMap.mulRight R b) (Q := alphaSpan P n l F) ?_ hz
  · simpa using this
  rintro _ ⟨i, j, p, h1, h2, h3, hF, b', hb', rfl⟩
  simp only [LinearMap.mulRight_apply, mul_assoc]
  exact as_mem P n i j p h1 h2 h3 hF (Subalgebra.mul_mem _ hb' hb)

lemma as_mono {l : ℕ} {F G : ℕ → ℤ → Prop} (h : ∀ i p, F i p → G i p) :
    alphaSpan P n l F ≤ alphaSpan P n l G := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, j, p, h1, h2, h3, hF, b, hb, rfl⟩
  exact as_mem P n i j p h1 h2 h3 (h i p hF) hb

end X8L33
end QAlgorithms.Papers.Independent.Gap48.P01
noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L36

set_option linter.unusedSectionVars false

open X8L33

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

def V (l m : ℕ) : Submodule R (NonsplitBMW P n) :=
  productSpan (R := R) (chainWords P n l m false) (level P n (l-2*m) : Set (NonsplitBMW P n))

lemma cw_zero (l : ℕ) {z : NonsplitBMW P n} (hz : z ∈ chainWords P n l 0 false) : z = 1 := by
  obtain ⟨-, i, j, p, -, -, rfl⟩ := hz
  simp

lemma cw_zero' (l : ℕ) : (1 : NonsplitBMW P n) ∈ chainWords P n l 0 false :=
  ⟨by omega, Fin.elim0, Fin.elim0, Fin.elim0, fun f => f.elim0, (fun h => by cases h), by simp⟩

lemma cw_succ (l m : ℕ) {z : NonsplitBMW P n} (hz : z ∈ chainWords P n l (m+1) false) :
    2*(m+1) ≤ l ∧ ∃ i j : ℕ, ∃ p : ℤ, ∃ w, 1 ≤ i ∧ i ≤ j ∧ j ≤ l-1 ∧ exponentRange k p ∧
      w ∈ chainWords P n (l-2) m false ∧ z = alphaChain P n i j (l-1) p * w := by
  obtain ⟨h2, i, j, p, hc, -, rfl⟩ := hz
  refine ⟨h2, i 0, j 0, p 0, _, (hc 0).1, (hc 0).2.1, by simpa using (hc 0).2.2.1, (hc 0).2.2.2,
    ⟨by omega, fun f => i f.succ, fun f => j f.succ, fun f => p f.succ, ?_, by simp, rfl⟩, ?_⟩
  · intro f
    obtain ⟨a1, a2, a3, a4⟩ := hc f.succ
    simp only [Fin.val_succ] at a3
    exact ⟨a1, a2, by dsimp only; omega, a4⟩
  · rw [List.ofFn_succ, List.prod_cons]
    have e : ∀ f : ℕ, l - 2*(f+1) - 1 = l - 2 - 2*f - 1 := fun f => by omega
    simp [Fin.val_succ, e]

lemma cw_cons (l m : ℕ) (h2 : 2*(m+1) ≤ l) (i j : ℕ) (p : ℤ) (w : NonsplitBMW P n)
    (h1 : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ l-1) (hp : exponentRange k p)
    (hw : w ∈ chainWords P n (l-2) m false) :
    alphaChain P n i j (l-1) p * w ∈ chainWords P n l (m+1) false := by
  obtain ⟨-, i', j', p', hc, -, rfl⟩ := hw
  refine ⟨h2, Fin.cons i i', Fin.cons j j', Fin.cons p p', ?_, by simp, ?_⟩
  · intro f
    refine Fin.cases ?_ (fun f => ?_) f
    · simpa using ⟨h1, hij, hj, hp⟩
    · obtain ⟨a1, a2, a3, a4⟩ := hc f
      simp only [Fin.cons_succ, Fin.val_succ]
      exact ⟨a1, a2, by omega, a4⟩
  · rw [List.ofFn_succ, List.prod_cons]
    have e : ∀ f : ℕ, l - 2*(f+1) - 1 = l - 2 - 2*f - 1 := fun f => by omega
    simp [Fin.val_succ, e]

lemma V_gen (l m : ℕ) {a b : NonsplitBMW P n} (ha : a ∈ chainWords P n l m false)
    (hb : b ∈ level P n (l-2*m)) : a * b ∈ V P n l m :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

lemma V_left (l m : ℕ) (a : NonsplitBMW P n) {Q : Submodule R (NonsplitBMW P n)}
    (h : ∀ w b, w ∈ chainWords P n l m false → b ∈ level P n (l-2*m) → a * (w * b) ∈ Q)
    {z : NonsplitBMW P n} (hz : z ∈ V P n l m) : a * z ∈ Q := by
  have := X8L25.span_map (LinearMap.mulLeft R a) (Q := Q) ?_ hz
  · simpa using this
  rintro _ ⟨w, hw, b, hb, rfl⟩
  exact h w b hw hb

end X8L36

end QAlgorithms.Papers.Independent.Gap48.P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L37

set_option linter.unusedSectionVars false

open X8L33 X8L36

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

/-- ordered chain words whose indices are all below B -/
def CWb (l m B : ℕ) : Set (NonsplitBMW P n) :=
  {z | 2*m ≤ l ∧ ∃ i j : Fin m → ℕ, ∃ p : Fin m → ℤ,
    (∀ f, 1 ≤ i f ∧ i f ≤ j f ∧ j f ≤ l-2*f.val-1 ∧ exponentRange k (p f)) ∧
    (∀ f g, f < g → i g < i f) ∧ (∀ f, i f < B) ∧
    z = (List.ofFn fun f : Fin m => alphaChain P n (i f) (j f) (l-2*f.val-1) (p f)).prod}

def Vo (l m : ℕ) : Submodule R (NonsplitBMW P n) :=
  productSpan (R := R) (chainWords P n l m true) (level P n (l-2*m) : Set (NonsplitBMW P n))

lemma cwb_sub (l m B : ℕ) {z : NonsplitBMW P n} (hz : z ∈ CWb P n l m B) :
    z ∈ chainWords P n l m true := by
  obtain ⟨h2, i, j, p, hc, ho, -, rfl⟩ := hz
  exact ⟨h2, i, j, p, hc, fun _ => ho, rfl⟩

lemma cwt_f (l m : ℕ) {z : NonsplitBMW P n} (hz : z ∈ chainWords P n l m true) :
    z ∈ chainWords P n l m false := by
  obtain ⟨h2, i, j, p, hc, -, rfl⟩ := hz
  exact ⟨h2, i, j, p, hc, (fun h => by cases h), rfl⟩

lemma cwf_t (l m : ℕ) (hm : m ≤ 1) {z : NonsplitBMW P n} (hz : z ∈ chainWords P n l m false) :
    z ∈ chainWords P n l m true := by
  obtain ⟨h2, i, j, p, hc, -, rfl⟩ := hz
  exact ⟨h2, i, j, p, hc, fun _ f g hfg => by
    have := f.isLt; have := g.isLt; have : f.val < g.val := hfg; omega, rfl⟩

lemma cwo_succ (l m : ℕ) {z : NonsplitBMW P n} (hz : z ∈ chainWords P n l (m+1) true) :
    2*(m+1) ≤ l ∧ ∃ i j : ℕ, ∃ p : ℤ, ∃ w, 1 ≤ i ∧ i ≤ j ∧ j ≤ l-1 ∧ exponentRange k p ∧
      w ∈ CWb P n (l-2) m i ∧ z = alphaChain P n i j (l-1) p * w := by
  obtain ⟨h2, i, j, p, hc, ho, rfl⟩ := hz
  have ho' := ho rfl
  refine ⟨h2, i 0, j 0, p 0, _, (hc 0).1, (hc 0).2.1, by simpa using (hc 0).2.2.1, (hc 0).2.2.2,
    ⟨by omega, fun f => i f.succ, fun f => j f.succ, fun f => p f.succ, ?_,
      fun f g hfg => ho' _ _ (Fin.succ_lt_succ_iff.mpr hfg), fun f => ho' _ _ (Fin.succ_pos f), rfl⟩, ?_⟩
  · intro f
    obtain ⟨a1, a2, a3, a4⟩ := hc f.succ
    simp only [Fin.val_succ] at a3
    exact ⟨a1, a2, by dsimp only; omega, a4⟩
  · rw [List.ofFn_succ, List.prod_cons]
    have e : ∀ f : ℕ, l - 2*(f+1) - 1 = l - 2 - 2*f - 1 := fun f => by omega
    simp [Fin.val_succ, e]

lemma cwb_cons (l m B : ℕ) (h2 : 2*(m+1) ≤ l) (i j : ℕ) (p : ℤ) (w : NonsplitBMW P n)
    (h1 : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ l-1) (hp : exponentRange k p) (hB : i < B)
    (hw : w ∈ CWb P n (l-2) m i) :
    alphaChain P n i j (l-1) p * w ∈ CWb P n l (m+1) B := by
  obtain ⟨-, i', j', p', hc, ho, hb, rfl⟩ := hw
  refine ⟨h2, Fin.cons i i', Fin.cons j j', Fin.cons p p', ?_, ?_, ?_, ?_⟩
  · intro f
    refine Fin.cases ?_ (fun f => ?_) f
    · simpa using ⟨h1, hij, hj, hp⟩
    · obtain ⟨a1, a2, a3, a4⟩ := hc f
      simp only [Fin.cons_succ, Fin.val_succ]
      exact ⟨a1, a2, by omega, a4⟩
  · intro f g hfg
    refine Fin.cases (fun hfg => absurd hfg (Fin.not_lt_zero _)) (fun g hfg => ?_) g hfg
    refine Fin.cases (fun _ => ?_) (fun f hfg => ?_) f hfg
    · simpa using hb g
    · simpa using ho f g (Fin.succ_lt_succ_iff.mp hfg)
  · intro f
    refine Fin.cases ?_ (fun f => ?_) f
    · simpa using hB
    · simpa using (hb f).trans hB
  · rw [List.ofFn_succ, List.prod_cons]
    have e : ∀ f : ℕ, l - 2*(f+1) - 1 = l - 2 - 2*f - 1 := fun f => by omega
    simp [Fin.val_succ, e]

lemma Vo_gen (l m : ℕ) {a b : NonsplitBMW P n} (ha : a ∈ chainWords P n l m true)
    (hb : b ∈ level P n (l-2*m)) : a * b ∈ Vo P n l m :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

lemma Vo_left (l m : ℕ) (a : NonsplitBMW P n) {Q : Submodule R (NonsplitBMW P n)}
    (h : ∀ w b, w ∈ chainWords P n l m true → b ∈ level P n (l-2*m) → a * (w * b) ∈ Q)
    {z : NonsplitBMW P n} (hz : z ∈ Vo P n l m) : a * z ∈ Q := by
  have := X8L25.span_map (LinearMap.mulLeft R a) (Q := Q) ?_ hz
  · simpa using this
  rintro _ ⟨w, hw, b, hb, rfl⟩
  exact h w b hw hb

/-- alpha times V(l-2,m) lands in V(l,m+1) -/
lemma hA (l m : ℕ) (h2 : 2*(m+1) ≤ l) (i j : ℕ) (p : ℤ) (h1 : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ l-1) (hp : exponentRange k p) {u : NonsplitBMW P n} (hu : u ∈ V P n (l-2) m) :
    alphaChain P n i j (l-1) p * u ∈ V P n l (m+1) := by
  refine V_left P n (l-2) m _ (fun w b hw hb => ?_) hu
  rw [← mul_assoc]
  exact V_gen P n l (m+1) (cw_cons P n l m h2 i j p w h1 hij hj hp hw)
    (by rw [show l - 2*(m+1) = l - 2 - 2*m by omega]; exact hb)

theorem main37 (m : ℕ) : ∀ l, l ≤ n → V P n l m ≤ Vo P n l m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro l hl
  rcases (by omega : m ≤ 1 ∨ 2 ≤ m) with hm | hm
  · intro z hz
    simpa using V_left P n l m 1 (Q := Vo P n l m)
      (fun w b hw hb => by rw [one_mul]; exact Vo_gen P n l m (cwf_t P n l m hm hw) hb) hz
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have ih1 := ih (m+1) (by omega)
  -- the descending induction on the first index
  have Q : ∀ d, ∀ i, l - i = d → ∀ j p, 1 ≤ i → i ≤ j → j ≤ l-1 → exponentRange k p →
      2*(m+2) ≤ l → ∀ u ∈ Vo P n (l-2) (m+1), alphaChain P n i j (l-1) p * u ∈ Vo P n l (m+2) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ihd =>
    intro i hd j p h1 hij hj hp h2 u hu
    refine Vo_left P n (l-2) (m+1) _ (fun w' b hw' hb => ?_) hu
    obtain ⟨-, i2, j2, s, w'', a1, a2, a3, a4, hw'', rfl⟩ := cwo_succ P n (l-2) m hw'
    have hb' : b ∈ level P n (l - 2*(m+2)) := by
      rw [show l - 2*(m+2) = l - 2 - 2*(m+1) by omega]; exact hb
    rcases lt_or_ge i2 i with hlt | hge
    · rw [← mul_assoc]
      refine Vo_gen P n l (m+2) (cwb_sub P n l (m+2) (i+1) ?_) hb'
      refine cwb_cons P n l (m+1) (i+1) h2 i j p _ h1 hij hj hp (by omega) ?_
      exact cwb_cons P n (l-2) m i (by omega) i2 j2 s w'' a1 a2 a3 a4 hlt hw''
    · have h35 := lemma_3_5 P n (l-1) i j i2 j2 (by omega) h1 hij hj a1 a2 (by omega) hge p s hp a4
      rw [show l - 1 - 2 = l - 2 - 1 by omega] at h35
      have hwb : w'' * b ∈ V P n (l-2-2) m :=
        V_gen P n (l-2-2) m (cwt_f P n _ m (cwb_sub P n _ m i2 hw''))
          (by rw [show l - 2 - 2 - 2*m = l - 2 - 2*(m+1) by omega]; exact hb)
      have h36 : IsLeftIdealIn (level P n (l-2-2)) (V P n (l-2-2) m) :=
        lemma_3_6 P n (l-2-2) m (by omega)
      have e1 : alphaChain P n i j (l-1) p * (alphaChain P n i2 j2 (l-2-1) s * w'' * b) =
          (alphaChain P n i j (l-1) p * alphaChain P n i2 j2 (l-2-1) s) * (w'' * b) := by
        simp only [mul_assoc]
      rw [e1]
      have := X8L25.span_map (LinearMap.mulRight R (w'' * b)) (Q := Vo P n l (m+2)) ?_ h35
      · simpa only [LinearMap.mulRight_apply] using this
      rintro _ ⟨ip, jp, gp, hh, pp, rr, b1, b2, b3, b4, b5, b6, b7, b8, b9, b'', hb'', rfl⟩
      simp only [LinearMap.mulRight_apply, mul_assoc]
      have hin : b'' * (w'' * b) ∈ V P n (l-2-2) m :=
        h36.2 b'' (by rw [show l - 2 - 2 = l - 1 - 3 by omega]; exact hb'') _ hwb
      have hin2 : alphaChain P n gp hh (l-2-1) rr * (b'' * (w'' * b)) ∈ V P n (l-2) (m+1) :=
        hA P n (l-2) m (by omega) gp hh rr b5 b6 (by omega) b9 hin
      exact ihd (l - ip) (by omega) ip rfl jp pp b1 b2 (by omega) b8 h2 _ (ih1 (l-2) (by omega) hin2)
  intro z hz
  suffices H : ∀ w b, w ∈ chainWords P n l (m+2) false → b ∈ level P n (l-2*(m+2)) →
      1 * (w * b) ∈ Vo P n l (m+2) by
    simpa using V_left P n l (m+2) 1 H hz
  intro w b hw hb
  obtain ⟨h2, i, j, p, w0, h1, hij, hj, hp, hw0, rfl⟩ := cw_succ P n l (m+1) hw
  rw [one_mul, mul_assoc]
  refine Q (l - i) i rfl j p h1 hij hj hp h2 _ (ih1 (l-2) (by omega) ?_)
  exact V_gen P n (l-2) (m+1) hw0 (by rw [show l - 2 - 2*(m+1) = l - 2*(m+2) by omega]; exact hb)

theorem main37' (l m : ℕ) (hl : l ≤ n) : V P n l m = Vo P n l m := by
  refine le_antisymm (main37 P n m l hl) ?_
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨w, hw, b, hb, rfl⟩
  exact V_gen P n l m (cwt_f P n l m hw) hb

end X8L37

end QAlgorithms.Papers.Independent.Gap48.P01

open QAlgorithms.Papers.Independent.Gap48.P01 in
theorem solution {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)
    (l m : ℕ) (hl : l ≤ n) :
    productSpan (R := R) (chainWords P n l m false) (level P n (l-2*m) : Set (NonsplitBMW P n)) =
    productSpan (R := R) (chainWords P n l m true) (level P n (l-2*m) : Set (NonsplitBMW P n)) :=
  X8L37.main37' P n l m hl

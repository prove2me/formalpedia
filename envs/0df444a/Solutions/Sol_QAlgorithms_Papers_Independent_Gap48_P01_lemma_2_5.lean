-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P01.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:23:04.993107+00:00
-- url     : https://prove2.me/submissions/acd47b72-398b-4ab0-ad2d-1ace1c5e8f8e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01

namespace X8L25

set_option linter.unusedSectionVars false

structure Sys (R A : Type*) [CommRing R] [Ring A] [Algebra R A] (n : ℕ) where
  δ : R
  lam : R
  lami : R
  hlam : lami * lam = 1
  x : ℕ → A
  xi : ℕ → A
  e : ℕ → A
  u : ℕ → Aˣ
  x_xi : ∀ i, 1 ≤ i → i < n → x i * xi i = 1
  xi_x : ∀ i, 1 ≤ i → i < n → xi i * x i = 1
  skein : ∀ i, 1 ≤ i → i < n → x i - xi i = δ • (1 - e i)
  xe : ∀ i, 1 ≤ i → i < n → x i * e i = lam • e i
  ex : ∀ i, 1 ≤ i → i < n → e i * x i = lam • e i
  sq : ∀ i, 1 ≤ i → i < n → ∃ c : R, e i * e i = c • e i
  nearL : ∀ a, 1 ≤ a → a + 1 < n → x (a+1) * x a * e (a+1) = e a * e (a+1)
  nearR : ∀ a, 1 ≤ a → a + 1 < n → e (a+1) * x a * x (a+1) = e (a+1) * e a
  triple : ∀ a, 1 ≤ a → a + 1 < n → e (a+1) * e a * e (a+1) = e (a+1)
  urec : ∀ a, 1 ≤ a → a < n → (u (a+1) : A) = x a * u a * x a
  m9L : ∀ a, 1 ≤ a → a < n → (u a : A) * u (a+1) * e a = e a
  m9R : ∀ a, 1 ≤ a → a < n → e a * u a * u (a+1) = e a
  ucomm : ∀ j m, 1 ≤ j → j < m → m ≤ n → (u j : A) * u m = u m * u j
  ux : ∀ j m, 1 ≤ j → j < m → m < n → (u j : A) * x m = x m * u j
  ue : ∀ j m, 1 ≤ j → j < m → m < n → (u j : A) * e m = e m * u j
  base : 1 < n → ∀ p : ℤ, ∃ c : R, e 1 * ↑(u 1 ^ p) * e 1 = c • e 1

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {n : ℕ}

inductive IsMon (u : ℕ → Aˣ) : ℕ → A → Prop
  | base : IsMon u 1 1
  | step (i : ℕ) (m : A) (t : ℤ) : IsMon u i m → IsMon u (i+1) (m * ↑(u i ^ t))

namespace IsMon
variable {u : ℕ → Aˣ}

lemma pos {i : ℕ} {m : A} (h : IsMon u i m) : 1 ≤ i := by
  cases h <;> omega

lemma inv_step {i : ℕ} {m : A} (h : IsMon u (i+1) m) (hi : 1 ≤ i) :
    ∃ m0, ∃ t : ℤ, IsMon u i m0 ∧ m = m0 * ↑(u i ^ t) := by
  generalize hk : i + 1 = k at h
  cases h with
  | base => omega
  | step j m0 t h0 =>
    obtain rfl : j = i := by omega
    exact ⟨m0, t, h0, rfl⟩

lemma mul_pow {i : ℕ} {m : A} (h : IsMon u (i+1) m) (hi : 1 ≤ i) (w : ℤ) :
    IsMon u (i+1) (m * ↑(u i ^ w)) := by
  obtain ⟨m0, t, h0, rfl⟩ := h.inv_step hi
  have := IsMon.step i m0 (t + w) h0
  rwa [zpow_add, Units.val_mul, ← mul_assoc] at this

lemma one : ∀ i, 1 ≤ i → IsMon u i (1 : A) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact IsMon.base
  | succ i hi ih => simpa using IsMon.step i 1 0 ih

lemma comm {i : ℕ} {m : A} (h : IsMon u i m) (y : A)
    (hy : ∀ j, 1 ≤ j → j < i → Commute (u j : A) y) : Commute m y := by
  induction h with
  | base => exact Commute.one_left y
  | step i m t h ih =>
    exact (ih (fun j hj hji => hy j hj (by omega))).mul_left
      ((hy i h.pos (by omega)).units_zpow_left t)

lemma of_inv {i : ℕ} {m : A} (h : IsMon (fun j => (u j)⁻¹) i m) : IsMon u i m := by
  induction h with
  | base => exact IsMon.base
  | step i m t h ih =>
    have := IsMon.step i m (-t) ih
    simpa [inv_zpow'] using this

end IsMon

lemma span_map {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {s : Set M} {Q : Submodule R N} (L : M →ₗ[R] N) (h : ∀ z ∈ s, L z ∈ Q) {z : M}
    (hz : z ∈ Submodule.span R s) : L z ∈ Q :=
  (Submodule.span_le.mpr (fun z hz => h z hz) : Submodule.span R s ≤ Q.comap L) hz

lemma fix_left (w : Aˣ) (e : A) (h : (w : A) * e = e) (t : ℤ) : (↑(w ^ t) : A) * e = e := by
  have h' : (↑w⁻¹ : A) * e = e := by
    calc (↑w⁻¹ : A) * e = ↑w⁻¹ * (↑w * e) := by rw [h]
    _ = e := by rw [← mul_assoc, Units.inv_mul, one_mul]
  induction t using Int.induction_on with
  | zero => simp
  | succ t ih => rw [zpow_add_one, Units.val_mul, mul_assoc, h, ih]
  | pred t ih => rw [zpow_sub_one, Units.val_mul, mul_assoc, h', ih]

lemma fix_right (w : Aˣ) (e : A) (h : e * (w : A) = e) (t : ℤ) : e * (↑(w ^ t) : A) = e := by
  have h' : e * (↑w⁻¹ : A) = e := by
    calc e * (↑w⁻¹ : A) = (e * ↑w) * ↑w⁻¹ := by rw [h]
    _ = e := by rw [mul_assoc, Units.mul_inv, mul_one]
  induction t using Int.induction_on with
  | zero => simp
  | succ t ih =>
    rw [show (t:ℤ) + 1 = 1 + t by ring, zpow_add, zpow_one, Units.val_mul, ← mul_assoc, h, ih]
  | pred t ih =>
    rw [show (-(t:ℤ) - 1) = -1 + -(t:ℤ) by ring, zpow_add, zpow_neg_one, Units.val_mul,
      ← mul_assoc, h', ih]

namespace Sys
variable (S : Sys R A n)

def J (i : ℕ) (t : ℤ) : A := ↑(S.u i ^ t)

lemma J_add (i : ℕ) (s t : ℤ) : S.J i (s + t) = S.J i s * S.J i t := by
  simp [J, zpow_add]
lemma J_zero (i : ℕ) : S.J i 0 = 1 := by simp [J]
lemma J_one (i : ℕ) : S.J i 1 = S.u i := by simp [J]
lemma J_comm_self (i : ℕ) (s t : ℤ) : S.J i s * S.J i t = S.J i t * S.J i s := by
  rw [← S.J_add, ← S.J_add, add_comm]

lemma cx {j m : ℕ} (hj : 1 ≤ j) (hjm : j < m) (hm : m < n) (t : ℤ) :
    Commute (S.J j t) (S.x m) :=
  (show Commute (S.u j : A) (S.x m) from S.ux j m hj hjm hm).units_zpow_left t

lemma ce {j m : ℕ} (hj : 1 ≤ j) (hjm : j < m) (hm : m < n) (t : ℤ) :
    Commute (S.J j t) (S.e m) :=
  (show Commute (S.u j : A) (S.e m) from S.ue j m hj hjm hm).units_zpow_left t

lemma cxi1 {j m : ℕ} (hj : 1 ≤ j) (hjm : j < m) (hm : m < n) :
    Commute (S.u j : A) (S.xi m) := by
  have h := S.ux j m hj hjm hm
  show _ = _
  calc (S.u j : A) * S.xi m = (S.xi m * S.x m) * S.u j * S.xi m := by
        rw [S.xi_x m (by omega) hm, one_mul]
  _ = S.xi m * (S.u j * S.x m) * S.xi m := by rw [h]; simp only [mul_assoc]
  _ = S.xi m * S.u j := by rw [mul_assoc, mul_assoc, S.x_xi m (by omega) hm, mul_one]

lemma cxi {j m : ℕ} (hj : 1 ≤ j) (hjm : j < m) (hm : m < n) (t : ℤ) :
    Commute (S.J j t) (S.xi m) := (S.cxi1 hj hjm hm).units_zpow_left t

lemma uc {j m : ℕ} (hj : 1 ≤ j) (hjm : j < m) (hm : m ≤ n) :
    Commute (S.u j) (S.u m) := Units.ext (by simpa using S.ucomm j m hj hjm hm)

lemma cJJ {j m : ℕ} (hj : 1 ≤ j) (hjm : j < m) (hm : m ≤ n) (s t : ℤ) :
    Commute (S.J j s) (S.J m t) :=
  ((show Commute (S.u j : A) (S.u m) from S.ucomm j m hj hjm hm).units_zpow_left s).units_zpow_right t

lemma m9Lz {a : ℕ} (ha : 1 ≤ a) (han : a < n) (t : ℤ) :
    S.J (a+1) t * S.e a = S.J a (-t) * S.e a := by
  have h : (↑(S.u a * S.u (a+1)) : A) * S.e a = S.e a := by
    rw [Units.val_mul]; exact S.m9L a ha han
  have key : S.J a t * S.J (a+1) t * S.e a = S.e a := by
    have := fix_left _ _ h t
    rw [(S.uc ha (by omega) (by omega)).mul_zpow, Units.val_mul] at this
    exact this
  calc S.J (a+1) t * S.e a = S.J a (-t) * (S.J a t * S.J (a+1) t * S.e a) := by
        rw [← mul_assoc, ← mul_assoc, ← S.J_add, neg_add_cancel, S.J_zero, one_mul]
  _ = S.J a (-t) * S.e a := by rw [key]

lemma m9Rz {a : ℕ} (ha : 1 ≤ a) (han : a < n) (t : ℤ) :
    S.e a * S.J (a+1) t = S.e a * S.J a (-t) := by
  have h : S.e a * (↑(S.u a * S.u (a+1)) : A) = S.e a := by
    rw [Units.val_mul, ← mul_assoc]; exact S.m9R a ha han
  have key : S.e a * (S.J a t * S.J (a+1) t) = S.e a := by
    have := fix_right _ _ h t
    rw [(S.uc ha (by omega) (by omega)).mul_zpow, Units.val_mul] at this
    exact this
  calc S.e a * S.J (a+1) t = (S.e a * (S.J a t * S.J (a+1) t)) * S.J a (-t) := by
        rw [(S.cJJ ha (by omega) (by omega) t t).eq, mul_assoc, mul_assoc, ← S.J_add,
          add_neg_cancel, S.J_zero, mul_one]
  _ = S.e a * S.J a (-t) := by rw [key]

lemma xi_eq (i : ℕ) (hi : 1 ≤ i) (hin : i < n) : S.xi i = S.x i - S.δ • (1 - S.e i) := by
  rw [← S.skein i hi hin]; abel

lemma exe {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) :
    S.e (a+1) * S.x a * S.e (a+1) = S.lami • S.e (a+1) := by
  have h1 : S.e (a+1) * S.x a * S.x (a+1) * S.e (a+1) = S.e (a+1) := by
    rw [S.nearR a ha han, S.triple a ha han]
  have h2 : S.e (a+1) * S.x a * S.x (a+1) * S.e (a+1) =
      S.lam • (S.e (a+1) * S.x a * S.e (a+1)) := by
    rw [mul_assoc _ (S.x (a+1)), S.xe (a+1) (by omega) han, mul_smul_comm]
  rw [h2] at h1
  conv_rhs => rw [← h1]
  rw [smul_smul, S.hlam, one_smul]

end Sys
end X8L25


namespace X8L25

set_option linter.unusedSectionVars false

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {n : ℕ}

namespace Sys
variable (S : Sys R A n)

def T (i : ℕ) : Submodule R A := Submodule.span R {z | ∃ m, IsMon S.u i m ∧ z = m * S.e i}
def U (i : ℕ) (r : ℤ) : Submodule R A :=
  Submodule.span R {z | ∃ m, ∃ t : ℤ, IsMon S.u i m ∧ |t| ≤ r ∧ z = m * S.J i t * S.e i}

lemma T_gen {i : ℕ} {m : A} (h : IsMon S.u i m) : m * S.e i ∈ S.T i :=
  Submodule.subset_span ⟨m, h, rfl⟩

lemma U_gen {i : ℕ} {m : A} {t r : ℤ} (h : IsMon S.u i m) (ht : |t| ≤ r) :
    m * S.J i t * S.e i ∈ S.U i r :=
  Submodule.subset_span ⟨m, t, h, ht, rfl⟩

lemma U_gen1 {i : ℕ} (hi : 1 ≤ i) {t r : ℤ} (ht : |t| ≤ r) : S.J i t * S.e i ∈ S.U i r := by
  simpa using S.U_gen (IsMon.one i hi) ht

lemma T_le_U (i : ℕ) {r : ℤ} (hr : 0 ≤ r) : S.T i ≤ S.U i r := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, hm, rfl⟩
  have := S.U_gen hm (t := 0) (r := r) (by simpa using hr)
  simpa [S.J_zero] using this

lemma U_mono (i : ℕ) {r r' : ℤ} (h : r ≤ r') : S.U i r ≤ S.U i r' := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, t, hm, ht, rfl⟩
  exact S.U_gen hm (ht.trans h)

lemma monc {i : ℕ} {m : A} (h : IsMon S.u i m) (y : A)
    (hy : ∀ j, 1 ≤ j → j < i → Commute (S.u j : A) y) : Commute m y := h.comm y hy

/-- f z f for z in U_a. -/
lemma L1 {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) {r : ℤ} {z : A} (hz : z ∈ S.U a r) :
    S.e (a+1) * z * S.e (a+1) ∈ S.T (a+1) := by
  have := span_map (LinearMap.mulLeft R (S.e (a+1)) ∘ₗ LinearMap.mulRight R (S.e (a+1)))
    (Q := S.T (a+1)) ?_ hz
  · simpa [mul_assoc] using this
  rintro _ ⟨m, t, hm, ht, rfl⟩
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  have h1 : Commute m (S.e (a+1)) := S.monc hm _ (fun j hj hja => S.ue j (a+1) hj (by omega) han)
  have h2 : Commute (S.J a t) (S.e (a+1)) := S.ce ha (by omega) han t
  have : S.e (a+1) * (m * S.J a t * S.e a * S.e (a+1)) =
      m * S.J a t * (S.e (a+1) * S.e a * S.e (a+1)) := by
    rw [show S.e (a+1) * (m * S.J a t * S.e a * S.e (a+1)) =
      (S.e (a+1) * m) * S.J a t * S.e a * S.e (a+1) by simp only [mul_assoc], ← h1.eq,
      mul_assoc m (S.e (a+1)), ← h2.eq]
    simp only [mul_assoc]
  rw [this, S.triple a ha han]
  exact S.T_gen (IsMon.step a m t hm)

/-- right multiplication of T_(a+1) by powers of J_a. -/
lemma L2 {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) {z : A} (hz : z ∈ S.T (a+1)) (w : ℤ) :
    z * S.J a w ∈ S.T (a+1) := by
  have := span_map (LinearMap.mulRight R (S.J a w)) (Q := S.T (a+1)) ?_ hz
  · simpa using this
  rintro _ ⟨m, hm, rfl⟩
  simp only [LinearMap.mulRight_apply]
  rw [mul_assoc, ← (S.ce ha (by omega) han w).eq, ← mul_assoc]
  exact S.T_gen (hm.mul_pow ha w)

/-- f e z for z in U_(a+1). -/
lemma L3 {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) {r : ℤ} {z : A} (hz : z ∈ S.U (a+1) r) :
    S.e (a+1) * S.e a * z ∈ S.T (a+1) := by
  have := span_map (LinearMap.mulLeft R (S.e (a+1) * S.e a)) (Q := S.T (a+1)) ?_ hz
  · simpa [mul_assoc] using this
  rintro _ ⟨m, t, hm, ht, rfl⟩
  simp only [LinearMap.mulLeft_apply]
  obtain ⟨m0, t', hm0, rfl⟩ := hm.inv_step ha
  have h1 : Commute m0 (S.e (a+1)) :=
    S.monc hm0 _ (fun j hj hja => S.ue j (a+1) hj (by omega) han)
  have h1' : Commute m0 (S.e a) :=
    S.monc hm0 _ (fun j hj hja => S.ue j a hj hja (by omega))
  have hJ : (↑(S.u a ^ t') : A) = S.J a t' := rfl
  have h3 : S.e a * S.J (a+1) t = S.e a * S.J a (-t) := S.m9Rz ha (by omega) t
  have h4 : Commute (S.J a (-t) * S.J a t') (S.e (a+1)) :=
    (S.ce ha (by omega) han _).mul_left (S.ce ha (by omega) han _)
  have h5 : Commute (S.J a (-t + t')) (S.e (a+1)) := S.ce ha (by omega) han _
  have : S.e (a+1) * S.e a * (m0 * ↑(S.u a ^ t') * S.J (a+1) t * S.e (a+1)) =
      m0 * S.J a (-t + t') * S.e (a+1) := by
    rw [hJ, mul_assoc m0, (S.cJJ (m := a+1) ha (by omega) (by omega) t' t).eq]
    calc S.e (a+1) * S.e a * (m0 * (S.J (a+1) t * S.J a t') * S.e (a+1))
        = m0 * ((S.e (a+1) * (S.e a * S.J (a+1) t)) * S.J a t' * S.e (a+1)) := by
          simp only [mul_assoc]; rw [h1'.symm.left_comm, h1.symm.left_comm]
      _ = m0 * (S.e (a+1) * S.e a * ((S.J a (-t) * S.J a t') * S.e (a+1))) := by
          rw [h3]; simp only [mul_assoc]
      _ = m0 * ((S.e (a+1) * S.e a * S.e (a+1)) * (S.J a (-t) * S.J a t')) := by
          rw [h4.eq]; simp only [mul_assoc]
      _ = m0 * S.J a (-t + t') * S.e (a+1) := by
          rw [S.triple a ha han, ← S.J_add, ← h5.eq]; simp only [mul_assoc]
  rw [this]
  exact S.T_gen (IsMon.step a m0 _ hm0)

/-- J_(i+1)^w T_i ⊆ U_i. -/
lemma L4 {i : ℕ} (hi : 1 ≤ i) (hin : i < n) {z : A} (hz : z ∈ S.T i) (w r : ℤ) (hw : |w| ≤ r) :
    S.J (i+1) w * z ∈ S.U i r := by
  have := span_map (LinearMap.mulLeft R (S.J (i+1) w)) (Q := S.U i r) ?_ hz
  · simpa using this
  rintro _ ⟨m, hm, rfl⟩
  simp only [LinearMap.mulLeft_apply]
  have h1 : Commute m (S.J (i+1) w) := S.monc hm _ (fun j hj hji =>
    ((show Commute (S.u j : A) (S.u (i+1)) from S.ucomm j (i+1) hj (by omega) (by omega))
      ).units_zpow_right w)
  rw [← mul_assoc, ← h1.eq, mul_assoc, S.m9Lz hi hin, ← mul_assoc]
  exact S.U_gen hm (by rwa [abs_neg])

lemma b1 (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    S.x i * S.J i 1 = S.J (i+1) 1 * S.x i - S.δ • S.J (i+1) 1 + S.δ • (S.J (i+1) 1 * S.e i) := by
  have h : S.J (i+1) 1 * S.xi i = S.x i * S.J i 1 := by
    rw [S.J_one, S.J_one, S.urec i hi hin, mul_assoc, S.x_xi i hi hin, mul_one]
  rw [← h, S.xi_eq i hi hin]
  simp only [mul_sub, smul_sub, mul_smul_comm, mul_one]; abel

lemma b3 (a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    S.x a * S.J (a+1) 1 = S.J a 1 * S.x a + S.δ • S.J (a+1) 1 - S.δ • (S.e a * S.J (a+1) 1) := by
  have hxx : S.x a * S.x a = 1 + S.δ • S.x a - S.δ • (S.e a * S.x a) := by
    have h := S.xi_eq a ha han
    have : S.x a = S.xi a + S.δ • (1 - S.e a) := by rw [h]; abel
    conv_lhs => rw [show S.x a * S.x a = S.x a * (S.xi a + S.δ • (1 - S.e a)) by rw [← this]]
    rw [mul_add, S.x_xi a ha han, mul_smul_comm, mul_sub, mul_one, S.xe a ha han, ← S.ex a ha han,
      smul_sub]; abel
  have hv : S.J (a+1) 1 = S.x a * S.J a 1 * S.x a := by
    rw [S.J_one, S.J_one, S.urec a ha han]
  rw [hv, show S.x a * (S.x a * S.J a 1 * S.x a) = (S.x a * S.x a) * (S.J a 1 * S.x a) by
    simp only [mul_assoc], hxx]
  simp only [add_mul, sub_mul, one_mul, smul_mul_assoc, mul_assoc]

end Sys
end X8L25


namespace X8L25

set_option linter.unusedSectionVars false

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {n : ℕ}

namespace Sys
variable (S : Sys R A n)

lemma IIstep (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℕ)
    (hI : ∀ r : ℕ, r < p → S.e i * S.J i r * S.e i ∈ S.T i) :
    ∀ w : ℕ, S.J (i+1) w * S.x i * S.J i p * S.e i ∈ S.U i (w + p) := by
  induction p with
  | zero =>
    intro w
    rw [Nat.cast_zero, S.J_zero, mul_one, mul_assoc, S.xe i hi hin, mul_smul_comm, S.m9Lz hi hin]
    exact Submodule.smul_mem _ _ (S.U_gen1 hi (by simp))
  | succ p ih =>
    intro w
    have hI' : ∀ r : ℕ, r < p → S.e i * S.J i r * S.e i ∈ S.T i := fun r hr => hI r (by omega)
    have e1 : S.J i ((p+1 : ℕ) : ℤ) = S.J i 1 * S.J i p := by
      rw [← S.J_add]; push_cast; ring_nf
    have e2 : S.J (i+1) ((w+1 : ℕ) : ℤ) = S.J (i+1) w * S.J (i+1) 1 := by
      rw [← S.J_add]; push_cast; ring_nf
    have : S.J (i+1) w * S.x i * S.J i ((p+1 : ℕ) : ℤ) * S.e i =
        S.J (i+1) ((w+1 : ℕ) : ℤ) * S.x i * S.J i p * S.e i -
        S.δ • (S.J (i+1) ((w+1 : ℕ) : ℤ) * S.J i p * S.e i) +
        S.δ • (S.J (i+1) ((w+1 : ℕ) : ℤ) * (S.e i * S.J i p * S.e i)) := by
      rw [e1, e2, show S.J (i+1) w * S.x i * (S.J i 1 * S.J i p) * S.e i =
        S.J (i+1) w * (S.x i * S.J i 1) * S.J i p * S.e i by simp only [mul_assoc], S.b1 i hi hin]
      simp only [mul_sub, mul_add, sub_mul, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    rw [this]
    refine add_mem (sub_mem ?_ (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_)
    · refine S.U_mono i ?_ (ih hI' (w+1)); push_cast; omega
    · rw [← (S.cJJ (m := i+1) hi (by omega) (by omega) (p:ℤ) ((w+1:ℕ):ℤ)).eq, mul_assoc,
        S.m9Lz hi hin, ← mul_assoc, ← S.J_add]
      exact S.U_gen1 hi (by rw [abs_le]; constructor <;> push_cast <;> omega)
    · exact S.L4 hi hin (hI p (by omega)) _ _ (by rw [abs_le]; push_cast; constructor <;> omega)

lemma mainII_of (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℕ)
    (hI : ∀ r : ℕ, r < p → S.e i * S.J i r * S.e i ∈ S.T i) :
    S.x i * S.J i p * S.e i ∈ S.U i p := by
  simpa [S.J_zero] using S.IIstep i hi hin p hI 0

lemma Fx {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) (r : ℕ)
    (hIr : S.e (a+1) * S.J (a+1) r * S.e (a+1) ∈ S.T (a+1))
    (hIIr : S.x (a+1) * S.J (a+1) r * S.e (a+1) ∈ S.U (a+1) r) :
    S.e (a+1) * S.x a * S.J (a+1) r * S.e (a+1) ∈ S.T (a+1) := by
  have hfx : S.e (a+1) * S.x a = S.e (a+1) * S.e a * S.xi (a+1) := by
    rw [← S.nearR a ha han, mul_assoc _ (S.x (a+1)), S.x_xi (a+1) (by omega) han, mul_one]
  have : S.e (a+1) * S.x a * S.J (a+1) r * S.e (a+1) =
      S.e (a+1) * S.e a * (S.x (a+1) * S.J (a+1) r * S.e (a+1)) -
      S.δ • (S.e (a+1) * S.e a * (S.J (a+1) r * S.e (a+1))) +
      S.δ • ((S.e (a+1) * S.e a * S.e (a+1)) * S.J (a+1) r * S.e (a+1)) := by
    rw [hfx, S.xi_eq (a+1) (by omega) han]
    simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_one, mul_assoc,
      smul_sub]
    abel
  rw [this, S.triple a ha han]
  refine add_mem (sub_mem (S.L3 ha han hIIr) (Submodule.smul_mem _ _
    (S.L3 ha han (S.U_gen1 (i := a+1) (by omega) (t := r) (r := r) (by simp))))) ?_
  · exact Submodule.smul_mem _ _ hIr

lemma G {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n)
    (hIa : ∀ p : ℕ, S.e a * S.J a p * S.e a ∈ S.T a)
    (hIIa : ∀ p : ℕ, S.x a * S.J a p * S.e a ∈ S.U a p) (q : ℕ)
    (hq : ∀ r : ℕ, r ≤ q → S.e (a+1) * S.J (a+1) r * S.e (a+1) ∈ S.T (a+1)) :
    ∀ q' : ℕ, q' ≤ q → ∀ c : ℕ,
      S.e (a+1) * S.x a * S.J a c * S.x a * S.J (a+1) q' * S.e (a+1) ∈ S.T (a+1) := by
  have hIIq : ∀ r : ℕ, r ≤ q → S.x (a+1) * S.J (a+1) r * S.e (a+1) ∈ S.U (a+1) r :=
    fun r hr => S.mainII_of (a+1) (by omega) han r (fun r' hr' => hq r' (by omega))
  intro q'
  induction q' with
  | zero =>
    intro _ c
    have hxf : S.x a * S.e (a+1) = S.xi (a+1) * (S.e a * S.e (a+1)) := by
      rw [← S.nearL a ha han, ← mul_assoc, ← mul_assoc, S.xi_x (a+1) (by omega) han, one_mul]
    have hfxXi : S.e (a+1) * S.x a * S.xi (a+1) =
        S.e (a+1) * S.e a - S.δ • (S.e (a+1) * S.x a) + (S.δ * S.lami) • S.e (a+1) := by
      rw [S.xi_eq (a+1) (by omega) han, mul_sub, S.nearR a ha han, mul_smul_comm, mul_sub,
        mul_one, S.exe ha han, smul_sub, smul_smul]; abel
    have hc : Commute (S.J a c) (S.xi (a+1)) := S.cxi ha (by omega) han _
    have : S.e (a+1) * S.x a * S.J a c * S.x a * S.J (a+1) ((0:ℕ):ℤ) * S.e (a+1) =
        S.e (a+1) * (S.e a * S.J a c * S.e a) * S.e (a+1) -
        S.δ • (S.e (a+1) * (S.x a * S.J a c * S.e a) * S.e (a+1)) +
        (S.δ * S.lami) • (S.e (a+1) * (S.J a c * S.e a) * S.e (a+1)) := by
      rw [Nat.cast_zero, S.J_zero, mul_one, mul_assoc _ (S.x a), hxf, ← mul_assoc, mul_assoc _ (S.J a c),
        hc.eq, ← mul_assoc, ← mul_assoc, hfxXi]
      simp only [add_mul, sub_mul, smul_mul_assoc, mul_assoc]
    rw [this]
    refine add_mem (sub_mem (S.L1 ha han (S.T_le_U a (le_refl 0) (hIa c)))
      (Submodule.smul_mem _ _ (S.L1 ha han (hIIa c)))) (Submodule.smul_mem _ _ ?_)
    exact S.L1 ha han (S.U_gen1 ha (t := c) (r := c) (by simp))
  | succ q' ih =>
    intro hq' c
    have e1 : S.J (a+1) ((q'+1 : ℕ) : ℤ) = S.J (a+1) 1 * S.J (a+1) q' := by
      rw [← S.J_add]; push_cast; ring_nf
    have e2 : S.J a ((c+1 : ℕ) : ℤ) = S.J a c * S.J a 1 := by
      rw [← S.J_add]; push_cast; ring_nf
    have : S.e (a+1) * S.x a * S.J a c * S.x a * S.J (a+1) ((q'+1 : ℕ) : ℤ) * S.e (a+1) =
        S.e (a+1) * S.x a * S.J a ((c+1 : ℕ) : ℤ) * S.x a * S.J (a+1) q' * S.e (a+1) +
        S.δ • (S.e (a+1) * S.x a * S.J a c * S.J (a+1) ((q'+1 : ℕ) : ℤ) * S.e (a+1)) -
        S.δ • (S.e (a+1) * S.x a * S.J a c * (S.e a * S.J (a+1) ((q'+1 : ℕ) : ℤ)) * S.e (a+1)) := by
      rw [e1, e2, show S.e (a+1) * S.x a * S.J a c * S.x a * (S.J (a+1) 1 * S.J (a+1) q') * S.e (a+1)
        = S.e (a+1) * S.x a * S.J a c * (S.x a * S.J (a+1) 1) * S.J (a+1) q' * S.e (a+1) by
          simp only [mul_assoc], S.b3 a ha (by omega)]
      simp only [mul_sub, mul_add, sub_mul, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    rw [this]
    refine sub_mem (add_mem (ih (by omega) (c+1)) (Submodule.smul_mem _ _ ?_))
      (Submodule.smul_mem _ _ ?_)
    · have hc1 : Commute (S.J a c) (S.J (a+1) ((q'+1 : ℕ) : ℤ)) := S.cJJ ha (by omega) (by omega) _ _
      have hc2 : Commute (S.J a c) (S.e (a+1)) := S.ce ha (by omega) han _
      have : S.e (a+1) * S.x a * S.J a c * S.J (a+1) ((q'+1 : ℕ) : ℤ) * S.e (a+1) =
          S.e (a+1) * S.x a * S.J (a+1) ((q'+1 : ℕ) : ℤ) * S.e (a+1) * S.J a c := by
        rw [mul_assoc _ (S.J a c), hc1.eq, ← mul_assoc, mul_assoc _ (S.J a c), hc2.eq, ← mul_assoc]
      rw [this]
      exact S.L2 ha han (S.Fx ha han _ (hq _ hq') (hIIq _ hq')) _
    · have hc2 : Commute (S.J a (-((q'+1 : ℕ) : ℤ))) (S.e (a+1)) := S.ce ha (by omega) han _
      rw [S.m9Rz ha (by omega)]
      have : S.e (a+1) * S.x a * S.J a c * (S.e a * S.J a (-((q'+1 : ℕ) : ℤ))) * S.e (a+1) =
          S.e (a+1) * (S.x a * S.J a c * S.e a) * S.e (a+1) * S.J a (-((q'+1 : ℕ) : ℤ)) := by
        rw [← mul_assoc, mul_assoc _ (S.J a _), hc2.eq]; simp only [mul_assoc]
      rw [this]
      exact S.L2 ha han (S.L1 ha han (hIIa c)) _

theorem mainI : ∀ i, 1 ≤ i → i < n → ∀ p : ℕ, S.e i * S.J i p * S.e i ∈ S.T i := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro h1 p
    obtain ⟨c, hc⟩ := S.base h1 p
    rw [show S.J 1 p = ↑(S.u 1 ^ (p:ℤ)) from rfl, hc]
    exact Submodule.smul_mem _ _ (by simpa using S.T_gen (IsMon.base (u := S.u)))
  | succ a ha ih =>
    intro han p
    have hIa := ih (by omega)
    have hIIa : ∀ p : ℕ, S.x a * S.J a p * S.e a ∈ S.U a p :=
      fun p => S.mainII_of a ha (by omega) p (fun r _ => hIa r)
    induction p using Nat.strong_induction_on with
    | _ p hp =>
      cases p with
      | zero =>
        obtain ⟨c, hc⟩ := S.sq (a+1) (by omega) han
        rw [Nat.cast_zero, S.J_zero, mul_one, hc]
        exact Submodule.smul_mem _ _ (by simpa using S.T_gen (IsMon.one (u := S.u) (a+1) (by omega)))
      | succ q =>
        have := S.G ha han hIa hIIa q (fun r hr => hp r (by omega)) q le_rfl 1
        rw [Nat.cast_one] at this
        convert this using 1
        rw [show ((q+1:ℕ):ℤ) = 1 + q by push_cast; ring, S.J_add, S.J_one (a+1),
          S.urec a ha (by omega), ← S.J_one a]
        simp only [mul_assoc]

theorem mainII (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℕ) :
    S.x i * S.J i p * S.e i ∈ S.U i p :=
  S.mainII_of i hi hin p (fun r _ => S.mainI i hi hin r)

end Sys
end X8L25


namespace X8L25

set_option linter.unusedSectionVars false

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {n : ℕ}

open MulOpposite

def opU (w : Aˣ) : (Aᵐᵒᵖ)ˣ :=
  ⟨op (w : A), op (↑w⁻¹ : A), by rw [← op_mul, Units.inv_mul, op_one],
    by rw [← op_mul, Units.mul_inv, op_one]⟩

@[simp] lemma opU_val (w : Aˣ) : (↑(opU w) : Aᵐᵒᵖ) = op (w : A) := rfl

lemma opU_zpow (w : Aˣ) (t : ℤ) : (↑(opU w ^ t) : Aᵐᵒᵖ) = op (↑(w ^ t) : A) := by
  induction t using Int.induction_on with
  | zero => simp
  | succ t ih =>
    rw [zpow_add_one, Units.val_mul, ih, opU_val, ← op_mul, ← Units.val_mul, ← zpow_one_add,
      add_comm]
  | pred t ih =>
    rw [zpow_sub_one, Units.val_mul, ih, show (↑(opU w)⁻¹ : Aᵐᵒᵖ) = op (↑w⁻¹ : A) from rfl,
      ← op_mul, ← Units.val_mul, show (-(t:ℤ) - 1) = -1 + -(t:ℤ) by ring, zpow_add, zpow_neg_one]

namespace Sys
variable (S : Sys R A n)

lemma xie (i : ℕ) (hi : 1 ≤ i) (hin : i < n) : S.xi i * S.e i = S.lami • S.e i := by
  have h := congrArg (S.xi i * ·) (S.xe i hi hin)
  simp only [← mul_assoc, S.xi_x i hi hin, one_mul, mul_smul_comm] at h
  conv_rhs => rw [h]
  rw [smul_smul, S.hlam, one_smul]

lemma exi (i : ℕ) (hi : 1 ≤ i) (hin : i < n) : S.e i * S.xi i = S.lami • S.e i := by
  have h := congrArg (· * S.xi i) (S.ex i hi hin)
  simp only [mul_assoc, S.x_xi i hi hin, mul_one, smul_mul_assoc] at h
  conv_rhs => rw [h]
  rw [smul_smul, S.hlam, one_smul]

lemma nearLi {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) :
    S.xi (a+1) * S.xi a * S.e (a+1) = S.e a * S.e (a+1) := by
  have h1 : S.xi (a+1) * (S.e a * S.e (a+1)) = S.x a * S.e (a+1) := by
    rw [← S.nearL a ha han, ← mul_assoc, ← mul_assoc, S.xi_x (a+1) (by omega) han, one_mul]
  have h2 : S.xi (a+1) * S.e (a+1) = S.lami • S.e (a+1) := S.xie (a+1) (by omega) han
  have h3 : S.xi (a+1) * (S.x a * S.e (a+1)) =
      S.e a * S.e (a+1) - S.δ • (S.x a * S.e (a+1)) + (S.δ * S.lami) • S.e (a+1) := by
    rw [S.xi_eq (a+1) (by omega) han, sub_mul, ← mul_assoc, S.nearL a ha han, smul_mul_assoc,
      sub_mul, one_mul, ← mul_assoc, S.exe ha han, smul_sub, smul_smul]; abel
  calc S.xi (a+1) * S.xi a * S.e (a+1)
      = S.xi (a+1) * ((S.x a - S.δ • (1 - S.e a)) * S.e (a+1)) := by
        rw [S.xi_eq a ha (by omega), mul_assoc]
    _ = S.xi (a+1) * (S.x a * S.e (a+1)) - S.δ • (S.xi (a+1) * S.e (a+1)) +
        S.δ • (S.xi (a+1) * (S.e a * S.e (a+1))) := by
        simp only [sub_mul, mul_sub, one_mul, smul_mul_assoc, mul_smul_comm, smul_sub]; abel
    _ = S.e a * S.e (a+1) := by
        rw [h1, h2, h3, smul_smul]; abel

lemma nearRi {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) :
    S.e (a+1) * S.xi a * S.xi (a+1) = S.e (a+1) * S.e a := by
  have h1 : S.e (a+1) * S.e a * S.xi (a+1) = S.e (a+1) * S.x a := by
    rw [← S.nearR a ha han, mul_assoc _ (S.x (a+1)), S.x_xi (a+1) (by omega) han, mul_one]
  have h2 : S.e (a+1) * S.xi (a+1) = S.lami • S.e (a+1) := S.exi (a+1) (by omega) han
  have h3 : S.e (a+1) * S.x a * S.xi (a+1) =
      S.e (a+1) * S.e a - S.δ • (S.e (a+1) * S.x a) + (S.δ * S.lami) • S.e (a+1) := by
    rw [S.xi_eq (a+1) (by omega) han, mul_sub, S.nearR a ha han, mul_smul_comm, mul_sub,
      mul_one, S.exe ha han, smul_sub, smul_smul]; abel
  calc S.e (a+1) * S.xi a * S.xi (a+1)
      = S.e (a+1) * (S.x a - S.δ • (1 - S.e a)) * S.xi (a+1) := by
        rw [S.xi_eq a ha (by omega)]
    _ = S.e (a+1) * S.x a * S.xi (a+1) - S.δ • (S.e (a+1) * S.xi (a+1)) +
        S.δ • (S.e (a+1) * S.e a * S.xi (a+1)) := by
        simp only [sub_mul, mul_sub, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub, mul_assoc]
        abel
    _ = S.e (a+1) * S.e a := by
        rw [h1, h2, h3, smul_smul]; abel

lemma ureci {a : ℕ} (ha : 1 ≤ a) (han : a < n) :
    (↑(S.u (a+1))⁻¹ : A) = S.xi a * ↑(S.u a)⁻¹ * S.xi a := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [S.urec a ha han]
  calc S.x a * ↑(S.u a) * S.x a * (S.xi a * ↑(S.u a)⁻¹ * S.xi a)
      = S.x a * ↑(S.u a) * (S.x a * S.xi a) * ↑(S.u a)⁻¹ * S.xi a := by simp only [mul_assoc]
    _ = 1 := by
      rw [S.x_xi a ha han, mul_one, mul_assoc (S.x a), Units.mul_inv, mul_one, S.x_xi a ha han]

lemma Jinv (i : ℕ) : (↑(S.u i)⁻¹ : A) = S.J i (-1) := by simp [J]

def mirror : Sys R A n where
  δ := -S.δ
  lam := S.lami
  lami := S.lam
  hlam := by rw [mul_comm]; exact S.hlam
  x := S.xi
  xi := S.x
  e := S.e
  u := fun i => (S.u i)⁻¹
  x_xi := S.xi_x
  xi_x := S.x_xi
  skein := fun i hi hin => by rw [← neg_sub, S.skein i hi hin, neg_smul]
  xe := fun i hi hin => S.xie i hi hin
  ex := fun i hi hin => S.exi i hi hin
  sq := S.sq
  nearL := fun a ha han => S.nearLi ha han
  nearR := fun a ha han => S.nearRi ha han
  triple := S.triple
  urec := fun a ha han => S.ureci ha han
  m9L := fun a ha han => by
    rw [S.Jinv, S.Jinv, mul_assoc, S.m9Lz ha han, ← mul_assoc, ← S.J_add]; simp [S.J_zero]
  m9R := fun a ha han => by
    rw [S.Jinv, S.Jinv, mul_assoc, (S.cJJ (m := a+1) ha (by omega) (by omega) (-1) (-1)).eq,
      ← mul_assoc, S.m9Rz ha han, mul_assoc, ← S.J_add]; simp [S.J_zero]
  ucomm := fun j m hj hjm hm => by
    have := congrArg Units.val (S.uc hj hjm hm).inv_inv.eq
    simpa using this
  ux := fun j m hj hjm hm => ((S.cxi1 hj hjm hm).units_inv_left).eq
  ue := fun j m hj hjm hm =>
    ((show Commute (S.u j : A) (S.e m) from S.ue j m hj hjm hm).units_inv_left).eq
  base := fun h p => by simpa [inv_zpow'] using S.base h (-p)

lemma mirror_J (i : ℕ) (t : ℤ) : S.mirror.J i t = S.J i (-t) := by
  show (↑((S.u i)⁻¹ ^ t) : A) = ↑(S.u i ^ (-t)); rw [inv_zpow']

lemma T_mirror_le (i : ℕ) : S.mirror.T i ≤ S.T i := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, hm, rfl⟩
  exact S.T_gen (IsMon.of_inv hm)

lemma U_mirror_le (i : ℕ) (r : ℤ) : S.mirror.U i r ≤ S.U i r := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, t, hm, ht, rfl⟩
  rw [S.mirror_J]
  exact S.U_gen (IsMon.of_inv hm) (by rwa [abs_neg])

theorem allI (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℤ) :
    S.e i * S.J i p * S.e i ∈ S.T i := by
  rcases le_or_gt 0 p with hp | hp
  · have := S.mainI i hi hin p.toNat
    rwa [Int.toNat_of_nonneg hp] at this
  · have := S.mirror.mainI i hi hin (-p).toNat
    rw [S.mirror_J, Int.toNat_of_nonneg (by omega), neg_neg] at this
    exact S.T_mirror_le i this

theorem allII (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℤ) :
    S.x i * S.J i p * S.e i ∈ S.U i |p| := by
  rcases le_or_gt 0 p with hp | hp
  · have := S.mainII i hi hin p.toNat
    rw [Int.toNat_of_nonneg hp] at this
    rwa [abs_of_nonneg hp]
  · have h := S.mirror.mainII i hi hin (-p).toNat
    rw [S.mirror_J, Int.toNat_of_nonneg (by omega), neg_neg, ← abs_of_neg hp] at h
    have h' : S.xi i * S.J i p * S.e i ∈ S.U i |p| := S.U_mirror_le i _ h
    have : S.x i * S.J i p * S.e i = S.xi i * S.J i p * S.e i + S.δ • (S.J i p * S.e i) -
        S.δ • (S.e i * S.J i p * S.e i) := by
      rw [show S.x i = S.xi i + S.δ • (1 - S.e i) by rw [S.xi_eq i hi hin]; abel]
      simp only [add_mul, sub_mul, one_mul, smul_mul_assoc, smul_sub, mul_assoc]
      abel
    rw [this]
    exact sub_mem (add_mem h' (Submodule.smul_mem _ _ (S.U_gen1 hi le_rfl)))
      (Submodule.smul_mem _ _ (S.T_le_U i (abs_nonneg p) (S.allI i hi hin p)))

end Sys
end X8L25


namespace X8L25

set_option linter.unusedSectionVars false

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {n : ℕ}

open MulOpposite

namespace Sys
variable (S : Sys R A n)

def opS : Sys R Aᵐᵒᵖ n where
  δ := S.δ
  lam := S.lam
  lami := S.lami
  hlam := S.hlam
  x := fun i => op (S.x i)
  xi := fun i => op (S.xi i)
  e := fun i => op (S.e i)
  u := fun i => opU (S.u i)
  x_xi := fun i hi hin => by
    apply unop_injective; simp [S.xi_x i hi hin]
  xi_x := fun i hi hin => by
    apply unop_injective; simp [S.x_xi i hi hin]
  skein := fun i hi hin => by
    apply unop_injective; simp [S.skein i hi hin]
  xe := fun i hi hin => by
    apply unop_injective; simp [S.ex i hi hin]
  ex := fun i hi hin => by
    apply unop_injective; simp [S.xe i hi hin]
  sq := fun i hi hin => by
    obtain ⟨c, hc⟩ := S.sq i hi hin
    exact ⟨c, by apply unop_injective; simp [hc]⟩
  nearL := fun a ha han => by
    apply unop_injective; simp only [unop_mul, unop_op]; simpa only [mul_assoc] using S.nearR a ha han
  nearR := fun a ha han => by
    apply unop_injective; simp only [unop_mul, unop_op]
    simpa only [mul_assoc] using S.nearL a ha han
  triple := fun a ha han => by
    apply unop_injective; simp only [unop_mul, unop_op]
    simpa only [mul_assoc] using S.triple a ha han
  urec := fun a ha han => by
    apply unop_injective; simp only [opU_val, unop_mul, unop_op]
    rw [S.urec a ha han, mul_assoc]
  m9L := fun a ha han => by
    apply unop_injective; simp only [opU_val, unop_mul, unop_op]
    rw [← S.ucomm a (a+1) ha (by omega) (by omega), ← mul_assoc, S.m9R a ha han]
  m9R := fun a ha han => by
    apply unop_injective; simp only [opU_val, unop_mul, unop_op]
    rw [← mul_assoc, ← S.ucomm a (a+1) ha (by omega) (by omega), S.m9L a ha han]
  ucomm := fun j m hj hjm hm => by
    apply unop_injective; simp only [opU_val, unop_mul, unop_op]
    exact (S.ucomm j m hj hjm hm).symm
  ux := fun j m hj hjm hm => by
    apply unop_injective; simp only [opU_val, unop_mul, unop_op]
    exact (S.ux j m hj hjm hm).symm
  ue := fun j m hj hjm hm => by
    apply unop_injective; simp only [opU_val, unop_mul, unop_op]
    exact (S.ue j m hj hjm hm).symm
  base := fun h p => by
    obtain ⟨c, hc⟩ := S.base h p
    refine ⟨c, ?_⟩
    apply unop_injective; simp only [opU_zpow, unop_mul, unop_op, unop_smul]
    rw [← mul_assoc, hc]

lemma opS_J (i : ℕ) (t : ℤ) : S.opS.J i t = op (S.J i t) := opU_zpow _ _

lemma isMon_op {i : ℕ} {m' : Aᵐᵒᵖ} (h : IsMon S.opS.u i m') (hin : i ≤ n) :
    ∃ m, IsMon S.u i m ∧ m' = op m := by
  induction h with
  | base => exact ⟨1, IsMon.base, rfl⟩
  | step i m' t h ih =>
    obtain ⟨m, hm, rfl⟩ := ih (by omega)
    refine ⟨m * ↑(S.u i ^ t), IsMon.step i m t hm, ?_⟩
    have hc : Commute m (S.J i t) := S.monc hm _ (fun j hj hji =>
      ((show Commute (S.u j : A) (S.u i) from S.ucomm j i hj hji (by omega))).units_zpow_right t)
    show op m * S.opS.J i t = _
    rw [S.opS_J, ← op_mul, ← hc.eq]; rfl

def V (i : ℕ) (r : ℤ) : Submodule R A :=
  Submodule.span R {z | ∃ m, ∃ t : ℤ, IsMon S.u i m ∧ |t| ≤ r ∧ z = S.e i * (m * S.J i t)}

lemma V_gen {i : ℕ} {m : A} {t r : ℤ} (h : IsMon S.u i m) (ht : |t| ≤ r) :
    S.e i * (m * S.J i t) ∈ S.V i r :=
  Submodule.subset_span ⟨m, t, h, ht, rfl⟩

lemma U_op_le (i : ℕ) (hin : i ≤ n) (r : ℤ) {y : Aᵐᵒᵖ} (hy : y ∈ S.opS.U i r) :
    unop y ∈ S.V i r := by
  have := span_map (MulOpposite.opLinearEquiv R (M := A)).symm.toLinearMap (Q := S.V i r) ?_ hy
  · simpa using this
  rintro _ ⟨m', t, hm', ht, rfl⟩
  obtain ⟨m, hm, rfl⟩ := S.isMon_op hm' hin
  have hc : Commute m (S.J i t) := S.monc hm _ (fun j hj hji =>
    ((show Commute (S.u j : A) (S.u i) from S.ucomm j i hj hji (by omega))).units_zpow_right t)
  simp only [LinearEquiv.coe_toLinearMap, MulOpposite.coe_opLinearEquiv_symm]
  show unop (op m * S.opS.J i t * op (S.e i)) ∈ _
  rw [S.opS_J]
  simp only [unop_mul, unop_op]
  rw [← hc.eq]
  exact Submodule.subset_span ⟨m, t, hm, ht, rfl⟩

lemma T_le_V (i : ℕ) (hi : 1 ≤ i) (hin : i < n) {r : ℤ} (hr : 0 ≤ r) : S.T i ≤ S.V i r := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, hm, rfl⟩
  have hc : Commute m (S.e i) := S.monc hm _ (fun j hj hji => S.ue j i hj hji hin)
  rw [hc.eq]
  have := S.V_gen hm (t := 0) (r := r) (by simpa using hr)
  simpa [S.J_zero] using this

theorem allIII (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℤ) :
    S.e i * S.J i p * S.x i ∈ S.V i |p| := by
  have h0 := S.opS.allII i hi hin p
  rcases le_or_gt 0 p with hp | hp
  · have := S.U_op_le i hin.le _ h0
    rw [S.opS_J] at this
    simpa [mul_assoc, opS] using this
  · -- use the mirror of the op system to get xi, then convert
    have h1 := S.opS.mirror.mainII i hi hin (-p).toNat
    rw [S.opS.mirror_J, Int.toNat_of_nonneg (by omega), neg_neg, ← abs_of_neg hp] at h1
    have h2 := S.U_op_le i hin.le _ (S.opS.U_mirror_le i _ h1)
    rw [S.opS_J] at h2
    have h2' : S.e i * S.J i p * S.xi i ∈ S.V i |p| := by
      simpa [mul_assoc, opS, mirror] using h2
    have : S.e i * S.J i p * S.x i = S.e i * S.J i p * S.xi i + S.δ • (S.e i * S.J i p) -
        S.δ • (S.e i * S.J i p * S.e i) := by
      rw [show S.x i = S.xi i + S.δ • (1 - S.e i) by rw [S.xi_eq i hi hin]; abel]
      simp only [mul_add, mul_sub, mul_one, mul_smul_comm, smul_sub, mul_assoc]
      abel
    rw [this]
    have h3 : S.e i * S.J i p ∈ S.V i |p| := by
      simpa using S.V_gen (IsMon.one i hi) (t := p) (r := |p|) le_rfl
    exact sub_mem (add_mem h2' (Submodule.smul_mem _ _ h3))
      (Submodule.smul_mem _ _ (S.T_le_V i hi hin (abs_nonneg p) (S.allI i hi hin p)))

end Sys
end X8L25

noncomputable section

open scoped BigOperators Classical

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

end X8L25C
end QAlgorithms.Papers.Independent.Gap48.P01



namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L25C

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

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

lemma p1dL (a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    JM P n false a * X P n a false * JM P n false a * E P n a = (↑P.lam⁻¹ : R) • E P n a := by
  induction a, ha using Nat.le_induction with
  | base => exact unwrapL P n (by omega)
  | succ a ha ih =>
    have ih := ih (by omega)
    rw [JM_succ P n false a ha]
    set x := X P n a false
    set b := X P n (a+1) false
    set c := JM P n false a
    set e := E P n a
    set f := E P n (a+1)
    have br0 : x * (b * x) = b * (x * b) := by
      have := braid P n a ⟨ha, han⟩; simpa only [mul_assoc] using this
    have br : ∀ z, x * (b * (x * z)) = b * (x * (b * z)) := by
      intro z; rw [← mul_assoc b, ← mul_assoc x, br0, mul_assoc, mul_assoc]
    have cb : ∀ z, c * (b * z) = b * (c * z) := by
      intro z; rw [← mul_assoc, jx_comm P n a ha (a+1) le_rfl han, mul_assoc]
    have nl1 : b * (x * f) = e * f := by
      have := nearL P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
      simpa only [mul_assoc] using this
    have nl2 : x * (b * (e * f)) = f * (e * f) := by
      have := nearL P n a (a+1) ⟨ha, by omega⟩ ⟨by omega, han⟩ (Or.inl rfl)
      have := congrArg (· * f) this; simpa only [mul_assoc] using this
    have tr : f * (e * f) = f := by
      have := tripleE P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
      simpa only [mul_assoc] using this
    have ih' : c * (x * (c * (e * f))) = (↑P.lam⁻¹ : R) • (e * f) := by
      have := congrArg (· * f) ih; simpa only [mul_assoc, smul_mul_assoc] using this
    simp only [mul_assoc]
    rw [br (c * (x * f)), cb (x * (b * (c * (x * f)))), ← cb (x * f), nl1, ih',
      mul_smul_comm, mul_smul_comm, nl2, tr]

lemma p1dR (a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    E P n a * JM P n false a * X P n a false * JM P n false a = (↑P.lam⁻¹ : R) • E P n a := by
  induction a, ha using Nat.le_induction with
  | base => exact unwrapR P n (by omega)
  | succ a ha ih =>
    have ih := ih (by omega)
    rw [JM_succ P n false a ha]
    set x := X P n a false
    set b := X P n (a+1) false
    set c := JM P n false a
    set e := E P n a
    set f := E P n (a+1)
    have br0 : x * (b * x) = b * (x * b) := by
      have := braid P n a ⟨ha, han⟩; simpa only [mul_assoc] using this
    have br : ∀ z, x * (b * (x * z)) = b * (x * (b * z)) := by
      intro z; rw [← mul_assoc b, ← mul_assoc x, br0, mul_assoc, mul_assoc]
    have cb : ∀ z, c * (b * z) = b * (c * z) := by
      intro z; rw [← mul_assoc, jx_comm P n a ha (a+1) le_rfl han, mul_assoc]
    have nr1 : ∀ z, f * (x * (b * z)) = f * (e * z) := by
      intro z
      have := nearR P n a (a+1) ⟨ha, by omega⟩ ⟨by omega, han⟩ (Or.inl rfl)
      have := congrArg (· * z) this; simpa only [mul_assoc] using this
    have nr2 : e * (b * x) = e * f := by
      have := nearR P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
      simpa only [mul_assoc] using this
    have tr : f * (e * f) = f := by
      have := tripleE P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
      simpa only [mul_assoc] using this
    have ih' : ∀ z, e * (c * (x * (c * z))) = (↑P.lam⁻¹ : R) • (e * z) := by
      intro z; have := congrArg (· * z) ih; simpa only [mul_assoc, smul_mul_assoc] using this
    simp only [mul_assoc]
    rw [br (c * x), cb (x * (b * (c * x))), ← cb x, nr1, ih', mul_smul_comm, nr2, tr]

end X8L25C
end QAlgorithms.Papers.Independent.Gap48.P01



namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L25C

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

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

lemma ybase (hn : 1 < n) (p : ℤ) :
    ∃ c : R, E P n 1 * ↑(uU P n 1 ^ p) * E P n 1 = c • E P n 1 := by
  have hw := ypow P n (by omega) p
  have : E P n 1 * (↑(uU P n 1 ^ p) * E P n 1) ∈ Submodule.span R {E P n 1} := by
    refine X8L25.span_map (LinearMap.mulLeft R (E P n 1) ∘ₗ LinearMap.mulRight R (E P n 1))
      (Q := Submodule.span R {E P n 1}) ?_ hw
    rintro _ ⟨m, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      ← mul_assoc, loopr P n m (by omega)]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
  exact ⟨c, by rw [mul_assoc, ← hc]⟩

def sysOf : X8L25.Sys R (NonsplitBMW P n) n where
  δ := skeinDelta P
  lam := (P.lam : R)
  lami := (↑P.lam⁻¹ : R)
  hlam := by simp
  x := fun i => X P n i false
  xi := fun i => X P n i true
  e := E P n
  u := uU P n
  x_xi := fun i hi hin => x_xi P n i ⟨hi, hin⟩
  xi_x := fun i hi hin => xi_x P n i ⟨hi, hin⟩
  skein := fun i hi hin => skein P n i ⟨hi, hin⟩
  xe := fun i hi hin => xe P n i ⟨hi, hin⟩
  ex := fun i hi hin => ex P n i ⟨hi, hin⟩
  sq := fun i hi hin => ⟨loopZero P, sqE P n i ⟨hi, hin⟩⟩
  nearL := fun a ha han => nearL P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
  nearR := fun a ha han => nearR P n a (a+1) ⟨ha, by omega⟩ ⟨by omega, han⟩ (Or.inl rfl)
  triple := fun a ha han => tripleE P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
  urec := fun a ha han => by
    rw [uU_val P n (a+1) ⟨by omega, han⟩, uU_val P n a ⟨ha, by omega⟩, JM_succ P n false a ha]
  m9L := fun a ha han => by
    rw [uU_val P n (a+1) ⟨by omega, han⟩, uU_val P n a ⟨ha, by omega⟩, JM_succ P n false a ha]
    have p := p1dL P n a ha han
    simp only [mul_assoc] at p ⊢
    rw [xe P n a ⟨ha, han⟩, mul_smul_comm, mul_smul_comm, mul_smul_comm, p, smul_smul,
      Units.mul_inv, one_smul]
  m9R := fun a ha han => by
    rw [uU_val P n (a+1) ⟨by omega, han⟩, uU_val P n a ⟨ha, by omega⟩, JM_succ P n false a ha]
    have p := congrArg (· * X P n a false) (p1dR P n a ha han)
    simp only [mul_assoc, smul_mul_assoc] at p ⊢
    rw [p, ex P n a ⟨ha, han⟩, smul_smul, Units.inv_mul, one_smul]
  ucomm := fun j m hj hjm hm => by
    rw [uU_val P n j ⟨hj, by omega⟩, uU_val P n m ⟨by omega, hm⟩]
    exact jj_comm P n j hj m hjm hm
  ux := fun j m hj hjm hm => by
    rw [uU_val P n j ⟨hj, by omega⟩]; exact jx_comm P n j hj m hjm hm
  ue := fun j m hj hjm hm => by
    rw [uU_val P n j ⟨hj, by omega⟩]; exact je_comm P n j hj m hjm hm
  base := fun h p => ybase P n h p

lemma JPower_eq (i : ℕ) (h : 1 ≤ i ∧ i ≤ n) (p : ℤ) :
    JPower P n i p = (sysOf P n).J i p := by
  show _ = (↑(uU P n i ^ p) : NonsplitBMW P n)
  unfold JPower
  split_ifs with hp
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    simp [zpow_natCast, Units.val_pow_eq_pow_val, uU_val P n i h]
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, p = -(q:ℤ) := ⟨(-p).toNat, by omega⟩
    subst hq
    simp [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, uU_inv_val P n i h]

lemma mon_list {i : ℕ} {m : NonsplitBMW P n} (h : X8L25.IsMon (uU P n) i m) (hin : i ≤ n) :
    ∃ s : Fin (i-1) → ℤ,
      m = (List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod := by
  induction h with
  | base => exact ⟨Fin.elim0, by simp⟩
  | step i m t h ih =>
    obtain ⟨s, rfl⟩ := ih (by omega)
    obtain ⟨c, rfl⟩ : ∃ c, i = c + 1 := ⟨i - 1, by have := h.pos; omega⟩
    change Fin c → ℤ at s
    change ∃ s' : Fin (c+1) → ℤ, (List.ofFn fun j : Fin c => JPower P n (j.val+1) (s j)).prod *
      ↑(uU P n (c+1) ^ t) = (List.ofFn fun j : Fin (c+1) => JPower P n (j.val+1) (s' j)).prod
    refine ⟨Fin.snoc (α := fun _ => ℤ) s t, ?_⟩
    rw [List.ofFn_succ', List.prod_concat]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    rw [JPower_eq P n (c+1) ⟨by omega, by omega⟩]
    rfl

end X8L25C
end QAlgorithms.Papers.Independent.Gap48.P01



namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L25C

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

theorem x8_main (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℤ) :
    (E P n i * JPower P n i p * E P n i ∈ Submodule.span R
      {z | ∃ s : Fin (i-1) → ℤ,
        z = (List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod * E P n i}) ∧
    (X P n i false * JPower P n i p * E P n i ∈ Submodule.span R
      {z | ∃ s : Fin (i-1) → ℤ, ∃ t : ℤ, |t| ≤ |p| ∧
        z = (List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod * JPower P n i t * E P n i}) ∧
    (E P n i * JPower P n i p * X P n i false ∈ Submodule.span R
      {z | ∃ s : Fin (i-1) → ℤ, ∃ t : ℤ, |t| ≤ |p| ∧
        z = E P n i * ((List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod * JPower P n i t)}) := by
  have hJ := JPower_eq P n i ⟨hi, hin.le⟩
  rw [hJ p]
  refine ⟨?_, ?_, ?_⟩
  · refine (Submodule.span_le.mpr ?_) ((sysOf P n).allI i hi hin p)
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨s, rfl⟩ := mon_list P n hm hin.le
    exact Submodule.subset_span ⟨s, rfl⟩
  · refine (Submodule.span_le.mpr ?_) ((sysOf P n).allII i hi hin p)
    rintro _ ⟨m, t, hm, ht, rfl⟩
    obtain ⟨s, rfl⟩ := mon_list P n hm hin.le
    exact Submodule.subset_span ⟨s, t, ht, by rw [hJ t]; rfl⟩
  · refine (Submodule.span_le.mpr ?_) ((sysOf P n).allIII i hi hin p)
    rintro _ ⟨m, t, hm, ht, rfl⟩
    obtain ⟨s, rfl⟩ := mon_list P n hm hin.le
    exact Submodule.subset_span ⟨s, t, ht, by rw [hJ t]; rfl⟩

end X8L25C

end QAlgorithms.Papers.Independent.Gap48.P01

open QAlgorithms.Papers.Independent.Gap48.P01 in
theorem solution {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)
    (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℤ) :
    (E P n i * JPower P n i p * E P n i ∈ Submodule.span R
      {z | ∃ s : Fin (i-1) → ℤ,
        z = (List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod * E P n i}) ∧
    (X P n i false * JPower P n i p * E P n i ∈ Submodule.span R
      {z | ∃ s : Fin (i-1) → ℤ, ∃ t : ℤ, |t| ≤ |p| ∧
        z = (List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod * JPower P n i t * E P n i}) ∧
    (E P n i * JPower P n i p * X P n i false ∈ Submodule.span R
      {z | ∃ s : Fin (i-1) → ℤ, ∃ t : ℤ, |t| ≤ |p| ∧
        z = E P n i * ((List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod * JPower P n i t)}) :=
  X8L25C.x8_main P n i hi hin p


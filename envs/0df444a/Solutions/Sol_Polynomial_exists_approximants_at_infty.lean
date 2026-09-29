-- Prove2me | solution 1 for Polynomial.exists_approximants_at_infty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c168e5ce-e682-5571-8b47-e19d056f89f9

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_approximants_at_infty

set_option autoImplicit false

open Polynomial Finset

namespace M4cP1D1

variable {K : Type*} [Field K]

def WtLe (w D : ℕ) (H : K[X][X]) : Prop := ∀ k j : ℕ, D < j + w * k → (H.coeff k).coeff j = 0

namespace WtLe

variable {w D D₁ D₂ : ℕ} {H H₁ H₂ : K[X][X]}

theorem zero : WtLe w D (0 : K[X][X]) := fun k j _ => by simp

theorem add (h₁ : WtLe w D H₁) (h₂ : WtLe w D H₂) : WtLe w D (H₁ + H₂) := fun k j hj => by
  rw [coeff_add, coeff_add, h₁ k j hj, h₂ k j hj, add_zero]

theorem neg (h : WtLe w D H) : WtLe w D (-H) := fun k j hj => by
  rw [coeff_neg, coeff_neg, h k j hj, neg_zero]

theorem sub (h₁ : WtLe w D H₁) (h₂ : WtLe w D H₂) : WtLe w D (H₁ - H₂) := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg

theorem mono (h : WtLe w D₁ H) (hD : D₁ ≤ D₂) : WtLe w D₂ H := fun k j hj =>
  h k j (lt_of_le_of_lt hD hj)

theorem const_mul (h : WtLe w D H) (a : K) : WtLe w D (C (C a) * H) := fun k j hj => by
  rw [coeff_C_mul, coeff_C_mul, h k j hj, mul_zero]

theorem mul (h₁ : WtLe w D₁ H₁) (h₂ : WtLe w D₂ H₂) : WtLe w (D₁ + D₂) (H₁ * H₂) := by
  intro k j hj
  rw [coeff_mul, finsetSum_coeff]
  refine sum_eq_zero fun ab hab => ?_
  rw [coeff_mul]
  refine sum_eq_zero fun cd hcd => ?_
  have hab' := mem_antidiagonal.mp hab
  have hcd' := mem_antidiagonal.mp hcd
  by_cases hc : D₁ < cd.1 + w * ab.1
  · rw [h₁ ab.1 cd.1 hc, zero_mul]
  · have hd : D₂ < cd.2 + w * ab.2 := by
      push Not at hc
      have : j + w * k = (cd.1 + w * ab.1) + (cd.2 + w * ab.2) := by
        rw [← hab', ← hcd']; ring
      lia
    rw [h₂ ab.2 cd.2 hd, mul_zero]

theorem prod {ι : Type*} (s : Finset ι) (f : ι → K[X][X]) (h : ∀ i ∈ s, WtLe w D (f i)) :
    WtLe w (s.card * D) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro k j hj
    rw [prod_empty, card_empty, zero_mul] at *
    rw [coeff_one]
    split_ifs with hk
    · subst hk; rw [coeff_one]; split_ifs with hj0
      · subst hj0; simp at hj
      · rfl
    · simp
  | insert a s ha ih =>
    rw [prod_insert ha, card_insert_of_notMem ha, Nat.succ_mul, add_comm]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

end WtLe

theorem wtLe_X (w : ℕ) : WtLe w w (X : K[X][X]) := by
  intro k j hj
  rw [coeff_X]
  split_ifs with hk
  · subst hk
    rw [coeff_one]
    split_ifs with hj0
    · subst hj0; simp at hj
    · rfl
  · simp

theorem wtLe_C {w D : ℕ} (P : K[X]) (hP : P.natDegree ≤ D) : WtLe w D (C P : K[X][X]) := by
  intro k j hj
  rw [coeff_C]
  split_ifs with hk
  · subst hk
    exact coeff_eq_zero_of_natDegree_lt (by lia)
  · simp

theorem wtLe_X_sub_C {w : ℕ} (P : K[X]) (hP : P.natDegree ≤ w) : WtLe w w (X - C P : K[X][X]) :=
  (wtLe_X w).sub (wtLe_C P hP)

theorem WtLe.coeff_eval_eq_zero {w D : ℕ} {H : K[X][X]} (h : WtLe w D H) {P : K[X]}
    (hP : P.natDegree ≤ w) {e : ℕ} (he : D < e) : (H.eval P).coeff e = 0 := by
  rw [eval_eq_sum_range, finsetSum_coeff]
  refine sum_eq_zero fun k _ => ?_
  rw [coeff_mul]
  refine sum_eq_zero fun cd hcd => ?_
  have hcd' := mem_antidiagonal.mp hcd
  by_cases hc : D < cd.1 + w * k
  · rw [h k cd.1 hc, zero_mul]
  · push Not at hc
    have hd : (P ^ k).natDegree < cd.2 :=
      lt_of_le_of_lt (natDegree_pow_le.trans (Nat.mul_le_mul_left k hP)) (by lia)
    rw [coeff_eq_zero_of_natDegree_lt hd, mul_zero]

theorem WtLe.natDegree_eval_le {w D : ℕ} {H : K[X][X]} (h : WtLe w D H) {P : K[X]}
    (hP : P.natDegree ≤ w) : (H.eval P).natDegree ≤ D :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ he => h.coeff_eval_eq_zero hP (by exact_mod_cast he)

noncomputable def topPart (w D : ℕ) (H : K[X][X]) : K[X] :=
  ∑ k ∈ range (H.natDegree + 1), C ((H.coeff k).coeff (D - w * k)) * X ^ k

theorem coeff_topPart (w D : ℕ) (H : K[X][X]) (k : ℕ) :
    (topPart w D H).coeff k = (H.coeff k).coeff (D - w * k) := by
  rw [topPart, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (p := H)]
    · simp
    · simpa [Nat.lt_succ_iff] using hk

theorem eval_topPart (w D : ℕ) (H : K[X][X]) (y : K) :
    (topPart w D H).eval y = ∑ k ∈ range (H.natDegree + 1), (H.coeff k).coeff (D - w * k) * y ^ k := by
  simp only [topPart, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

theorem WtLe.coeff_eval_top {w D : ℕ} {H : K[X][X]} (h : WtLe w D H) {P : K[X]}
    (hP : P.natDegree ≤ w) : (H.eval P).coeff D = (topPart w D H).eval (P.coeff w) := by
  rw [eval_eq_sum_range, finsetSum_coeff, eval_topPart]
  refine sum_congr rfl fun k _ => ?_
  rw [coeff_mul]
  by_cases hwk : w * k ≤ D
  · rw [sum_eq_single (D - w * k, w * k)]
    · rw [mul_comm w k, coeff_pow_of_natDegree_le hP]
    · intro cd hcd hne
      have hcd' := mem_antidiagonal.mp hcd
      rcases lt_trichotomy cd.1 (D - w * k) with hlt | heq | hgt
      · have hd : (P ^ k).natDegree < cd.2 :=
          lt_of_le_of_lt (natDegree_pow_le.trans (Nat.mul_le_mul_left k hP)) (by lia)
        rw [coeff_eq_zero_of_natDegree_lt hd, mul_zero]
      · exfalso; apply hne; ext <;> simp <;> lia
      · rw [h k cd.1 (by lia), zero_mul]
    · intro hmem
      exfalso; exact hmem (mem_antidiagonal.mpr (by simp; lia))
  · push Not at hwk
    have h0 : (H.coeff k).coeff (D - w * k) = 0 := by
      rw [Nat.sub_eq_zero_of_le hwk.le]; exact h k 0 (by lia)
    rw [h0, zero_mul]
    refine sum_eq_zero fun cd hcd => ?_
    rw [h k cd.1 (by lia), zero_mul]

theorem WtLe.hasseDeriv {w D : ℕ} {H : K[X][X]} (h : WtLe w D H) (m : ℕ) :
    WtLe w (D - m * w) (hasseDeriv m H) := by
  intro k j hj
  rw [hasseDeriv_coeff, ← C_eq_natCast, coeff_C_mul, h (k + m) j (by
    rcases le_or_gt (m * w) D with hm | hm
    · have : D - m * w + m * w = D := Nat.sub_add_cancel hm
      nlinarith
    · nlinarith), mul_zero]

theorem topPart_derivative {w D : ℕ} (H : K[X][X]) :
    topPart w (D - w) (derivative H) = derivative (topPart w D H) := by
  ext k
  rw [coeff_derivative, coeff_topPart, coeff_topPart, coeff_derivative, ← Nat.cast_succ,
    coeff_mul_natCast, Nat.cast_succ]
  congr 2
  rw [Nat.mul_succ]
  lia

theorem eval_add_eq_sum_hasseDeriv (F : K[X][X]) (P Q : K[X]) :
    F.eval (P + Q) = ∑ m ∈ range (F.natDegree + 1), (hasseDeriv m F).eval P * Q ^ m := by
  rw [add_comm, ← taylor_eval, eval_eq_sum_range, natDegree_taylor]
  simp only [taylor_coeff]

theorem coeff_mul_C_mul_X_pow' (A : K[X]) (a : K) (i e : ℕ) :
    (A * (C a * X ^ i)).coeff e = if i ≤ e then a * A.coeff (e - i) else 0 := by
  split_ifs with hi
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [← mul_assoc, mul_comm A, mul_assoc, coeff_C_mul, add_comm i d, coeff_mul_X_pow,
      Nat.add_sub_cancel]
  · push Not at hi
    rw [← mul_assoc, mul_comm A, mul_assoc, coeff_C_mul, coeff_mul_X_pow', if_neg hi.not_ge,
      mul_zero]

theorem sum_range_eq_of_vanish {M : Type*} [AddCommMonoid M] {f : ℕ → M} {A B : ℕ}
    (hA : ∀ k, A ≤ k → f k = 0) (hB : ∀ k, B ≤ k → f k = 0) :
    ∑ k ∈ range A, f k = ∑ k ∈ range B, f k := by
  have key : ∀ {X Y : ℕ}, (∀ k, X ≤ k → f k = 0) → X ≤ Y → ∑ k ∈ range X, f k = ∑ k ∈ range Y, f k :=
    fun hX hXY => sum_subset (range_subset_range.mpr hXY) fun k _ hk =>
      hX k (not_lt.mp fun h => hk (mem_range.mpr h))
  rcases le_total A B with h | h
  · exact key hA h
  · exact (key hB h).symm

theorem coeff_eval_add_monomial {n w : ℕ} {F : K[X][X]} (hF : F.natDegree ≤ n)
    (hwt : WtLe w (n * w) F) {P : K[X]} (hP : P.natDegree ≤ w) {j : ℕ} (hj : j < w) (δ : K)
    (hn : 0 < n) (e : ℕ) (he : n * w - w + j ≤ e) :
    (F.eval (P + C δ * X ^ j)).coeff e = (F.eval P).coeff e +
      if e = n * w - w + j then δ * (derivative (topPart w (n * w) F)).eval (P.coeff w) else 0 := by
  have hwle : w ≤ n * w := Nat.le_mul_of_pos_left w hn
  rw [eval_add_eq_sum_hasseDeriv, finsetSum_coeff]

  have key2 : ∀ m, 2 ≤ m → ((hasseDeriv m F).eval P * (C δ * X ^ j) ^ m).coeff e = 0 := by
    intro m h2
    rcases le_or_gt m n with hmn | hmn
    · rw [mul_pow, ← C_pow, ← pow_mul, coeff_mul_C_mul_X_pow']
      split_ifs with hi
      · rw [(hwt.hasseDeriv m).coeff_eval_eq_zero hP, mul_zero]
        have h1 : m * w ≤ n * w := Nat.mul_le_mul_right w hmn
        zify [h1, hi, hwle] at he ⊢
        nlinarith
      · rfl
    · rw [hasseDeriv_eq_zero_of_lt_natDegree F m (lt_of_le_of_lt hF hmn), eval_zero, zero_mul,
        coeff_zero]
  have keyN : ∀ m, F.natDegree + 1 ≤ m → ((hasseDeriv m F).eval P * (C δ * X ^ j) ^ m).coeff e = 0 :=
    fun m hm => by
      rw [hasseDeriv_eq_zero_of_lt_natDegree F m (by lia), eval_zero, zero_mul, coeff_zero]
  rw [sum_range_eq_of_vanish keyN key2, sum_range_succ, sum_range_one, pow_zero, mul_one,
    hasseDeriv_zero', pow_one, hasseDeriv_one', coeff_mul_C_mul_X_pow', if_pos (by lia)]
  congr 1
  split_ifs with heq
  · subst heq
    rw [show n * w - w + j - j = n * w - w by lia]
    have h1 : WtLe w (n * w - w) (derivative F) := by
      have := hwt.hasseDeriv 1
      rwa [one_mul, hasseDeriv_one'] at this
    rw [h1.coeff_eval_top hP, topPart_derivative F]
  · have h1 : WtLe w (n * w - w) (derivative F) := by
      have := hwt.hasseDeriv 1
      rwa [one_mul, hasseDeriv_one'] at this
    rw [h1.coeff_eval_eq_zero hP (by lia), mul_zero]

theorem stage_zero {n w : ℕ} {F : K[X][X]} (hwt : WtLe w (n * w) F) (r : K)
    (h0 : (topPart w (n * w) F).eval r = 0) :
    ∀ e, n * w ≤ e → (F.eval (C r * X ^ w)).coeff e = 0 := by
  have hP : (C r * X ^ w : K[X]).natDegree ≤ w := (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le w)
  intro e he
  rcases he.lt_or_eq with hlt | heq
  · exact hwt.coeff_eval_eq_zero hP hlt
  · subst heq
    rw [hwt.coeff_eval_top hP, coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one, h0]

theorem exists_approximant {n w : ℕ} {F : K[X][X]} (hF : F.natDegree ≤ n) (hn : 0 < n)
    (hwt : WtLe w (n * w) F) (r : K) (h0 : (topPart w (n * w) F).eval r = 0)
    (h1 : (derivative (topPart w (n * w) F)).eval r ≠ 0) :
    ∃ P : K[X], P.natDegree ≤ w ∧ P.coeff w = r ∧ ∀ e, n * w - w ≤ e → (F.eval P).coeff e = 0 := by

  suffices ∀ s, s ≤ w → ∃ P : K[X], P.natDegree ≤ w ∧ P.coeff w = r ∧
      ∀ e, n * w - s ≤ e → (F.eval P).coeff e = 0 by
    exact this w le_rfl
  intro s
  induction s with
  | zero =>
    intro _
    refine ⟨C r * X ^ w, (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le w), ?_, ?_⟩
    · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    · simpa using stage_zero hwt r h0
  | succ s ih =>
    intro hs
    obtain ⟨P, hPdeg, hPw, hPe⟩ := ih (Nat.le_of_succ_le hs)
    have hwle : w ≤ n * w := Nat.le_mul_of_pos_left w hn

    set j := w - (s + 1) with hj
    have hjw : j < w := by lia
    have hej : n * w - w + j = n * w - (s + 1) := by lia
    set δ : K := -(F.eval P).coeff (n * w - (s + 1)) / (derivative (topPart w (n * w) F)).eval r
    refine ⟨P + C δ * X ^ j, ?_, ?_, ?_⟩
    · exact (natDegree_add_le _ _).trans (max_le hPdeg ((natDegree_C_mul_le _ _).trans
        ((natDegree_X_pow_le j).trans hjw.le)))
    · rw [coeff_add, coeff_C_mul, coeff_X_pow, if_neg (by lia), mul_zero, add_zero, hPw]
    · intro e he
      rw [coeff_eval_add_monomial hF hwt hPdeg hjw δ hn e (by lia), hPw]
      split_ifs with heq
      · rw [heq, hej, div_mul_cancel₀ _ h1, add_neg_cancel]
      · rw [add_zero]
        exact hPe e (by lia)

theorem wt_lt_of_eval_approximants {n w D₀ : ℕ} {R : K[X][X]}
    (hRdeg : ∀ k, n ≤ k → R.coeff k = 0) (P : Fin n → K[X]) (hP : ∀ i, (P i).natDegree ≤ w)
    (hinj : Function.Injective fun i => (P i).coeff w)
    (heval : ∀ i e, D₀ ≤ e → ((R.eval (P i)).coeff e) = 0) :
    ∀ k j, D₀ ≤ j + w * k → (R.coeff k).coeff j = 0 := by
  classical
  by_contra hcon
  push Not at hcon

  set S : Finset ℕ := R.support.biUnion fun k => ((R.coeff k).support).image fun j => j + w * k
    with hS
  have hmemS : ∀ {k j}, (R.coeff k).coeff j ≠ 0 → j + w * k ∈ S := by
    intro k j h
    refine mem_biUnion.mpr ⟨k, mem_support_iff.mpr ?_, mem_image.mpr ⟨j, mem_support_iff.mpr h, rfl⟩⟩
    intro hk; rw [hk, coeff_zero] at h; exact h rfl
  obtain ⟨k₀, j₀, hkj₀, hne₀⟩ := hcon
  have hSne : S.Nonempty := ⟨_, hmemS hne₀⟩
  set d := S.max' hSne with hd
  have hdmem : d ∈ S := max'_mem S hSne
  have hdle : ∀ {k j}, (R.coeff k).coeff j ≠ 0 → j + w * k ≤ d := fun h => le_max' S _ (hmemS h)

  have hRd : WtLe w d R := fun k j hj => by
    by_contra h; exact absurd (hdle h) (not_le.mpr hj)
  have hD₀d : D₀ ≤ d := hkj₀.trans (hdle hne₀)

  set ρ := topPart w d R with hρ
  have hρdeg : ρ.natDegree < n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · exfalso
      subst hn0
      obtain ⟨k, hk, hk'⟩ := mem_biUnion.mp hdmem
      exact (mem_support_iff.mp hk) (hRdeg k (Nat.zero_le k))
    · rw [Nat.lt_iff_le_pred hnpos]
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk
      rw [hρ, coeff_topPart, hRdeg k (by exact_mod_cast Nat.le_of_pred_lt hk), coeff_zero]
  have hρne : ρ ≠ 0 := by
    obtain ⟨k, hk, hk'⟩ := mem_biUnion.mp hdmem
    obtain ⟨j, hj, hjk⟩ := mem_image.mp hk'
    intro h0
    have := congr_arg (fun q => q.coeff k) h0
    simp only [hρ, coeff_topPart, coeff_zero] at this
    rw [← hjk, Nat.add_sub_cancel] at this
    exact (mem_support_iff.mp hj) this
  have hroots : ∀ i, ρ.eval ((P i).coeff w) = 0 := fun i => by
    rw [hρ, ← hRd.coeff_eval_top (hP i), heval i d hD₀d]
  have := eq_zero_of_natDegree_lt_card_of_eval_eq_zero ρ hinj hroots (by simpa using hρdeg)
  exact hρne this

theorem topPart_eq_sum {n w : ℕ} (F : K[X][X]) (hF : F.natDegree ≤ n) :
    topPart w (n * w) F = ∑ k ∈ range (n + 1), C ((F.coeff k).coeff (w * (n - k))) * X ^ k := by
  ext k
  rw [coeff_topPart, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  split_ifs with hk
  · congr 1
    rw [Nat.mul_sub, mul_comm]
  · rw [coeff_eq_zero_of_natDegree_lt (p := F) (by simp at hk; lia), coeff_zero]

theorem exists_approximants_at_infty (n w : ℕ) (F : K[X][X]) (hF : F.natDegree ≤ n)
    (hwt : ∀ k j : ℕ, w * (n - k) < j → (F.coeff k).coeff j = 0) (c : K) (hlead : F.coeff n = C c)
    (r : Fin n → K) (hr : Function.Injective r)
    (h0 : ∀ i, (∑ k ∈ Finset.range (n + 1), C ((F.coeff k).coeff (w * (n - k))) * X ^ k).eval (r i) = 0)
    (h1 : ∀ i, (derivative (∑ k ∈ Finset.range (n + 1),
      C ((F.coeff k).coeff (w * (n - k))) * X ^ k)).eval (r i) ≠ 0) :
    ∃ P : Fin n → K[X], (∀ i, (P i).natDegree ≤ w) ∧ (∀ i, (P i).coeff w = r i) ∧
      ∀ k j : ℕ, w * (n - k) ≤ j + w →
        ((F - C (C c) * ∏ i, (X - C (P i))).coeff k).coeff j = 0 := by
  classical

  have hwtF : WtLe w (n * w) F := by
    intro k j hj
    rcases le_or_gt k n with hk | hk
    · have hwk : w * k ≤ w * n := Nat.mul_le_mul_left w hk
      rw [mul_comm n w] at hj
      exact hwt k j (by rw [Nat.mul_sub]; lia)
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hF hk), coeff_zero]
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  ·
    subst hn0
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun k j hkj => ?_⟩
    have hFC : F = C (C c) := by
      rw [eq_C_of_natDegree_le_zero hF, ← hlead]
    rw [hFC, Finset.univ_eq_empty, prod_empty, mul_one, sub_self, coeff_zero, coeff_zero]
  rw [← topPart_eq_sum F hF] at h0 h1

  choose P hPdeg hPw hPe using fun i => exists_approximant hF hn hwtF (r i) (h0 i) (h1 i)
  refine ⟨P, hPdeg, hPw, ?_⟩

  set R := F - C (C c) * ∏ i, (X - C (P i)) with hRdef
  have hRdeg : ∀ k, n ≤ k → R.coeff k = 0 := by
    intro k hk
    have hmonic : (∏ i, (X - C (P i)) : K[X][X]).Monic := monic_prod_of_monic _ _ fun i _ =>
      monic_X_sub_C (P i)
    have hdegp : (∏ i, (X - C (P i)) : K[X][X]).natDegree = n := by
      rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (P i)]
      simp
    rcases hk.lt_or_eq with hlt | heq
    · rw [hRdef, coeff_sub, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hF hlt),
        coeff_eq_zero_of_natDegree_lt (by rw [hdegp]; exact hlt), mul_zero, sub_zero]
    · subst heq
      rw [hRdef, coeff_sub, coeff_C_mul, hlead]
      have : (∏ i, (X - C (P i)) : K[X][X]).coeff n = 1 := by
        have h1 := hmonic.coeff_natDegree; rwa [hdegp] at h1
      rw [this, mul_one, sub_self]
  have heval : ∀ i e, n * w - w ≤ e → (R.eval (P i)).coeff e = 0 := by
    intro i e he
    rw [hRdef, eval_sub, eval_mul, eval_C, eval_prod, coeff_sub]
    rw [prod_eq_zero (mem_univ i) (by rw [eval_sub, eval_X, eval_C, sub_self]), mul_zero,
      coeff_zero, sub_zero]
    exact hPe i e he
  have hinj : Function.Injective fun i => (P i).coeff w := by
    intro i j hij; apply hr; simp only [hPw] at hij; exact hij
  intro k j hkj
  refine wt_lt_of_eval_approximants hRdeg P hPdeg hinj heval k j ?_
  rcases le_or_gt k n with hk | hk
  · have hwk : w * k ≤ w * n := Nat.mul_le_mul_left w hk
    rw [Nat.mul_sub] at hkj
    rw [mul_comm n w]
    lia
  · have : n * w ≤ w * k := by nlinarith
    lia

end M4cP1D1

open Polynomial in
theorem solution {K : Type*} [Field K] (n w : ℕ) (F : Polynomial (Polynomial K)) (hF : F.natDegree ≤ n)
    (hwt : ∀ k j : ℕ, w * (n - k) < j → (F.coeff k).coeff j = 0) (c : K) (hlead : F.coeff n = C c)
    (r : Fin n → K) (hr : Function.Injective r)
    (h0 : ∀ i, (∑ k ∈ Finset.range (n + 1), C ((F.coeff k).coeff (w * (n - k))) * X ^ k).eval (r i) = 0)
    (h1 : ∀ i, (derivative (∑ k ∈ Finset.range (n + 1),
      C ((F.coeff k).coeff (w * (n - k))) * X ^ k)).eval (r i) ≠ 0) :
    ∃ P : Fin n → Polynomial K, (∀ i, (P i).natDegree ≤ w) ∧ (∀ i, (P i).coeff w = r i) ∧
      ∀ k j : ℕ, w * (n - k) ≤ j + w → ((F - C (C c) * ∏ i, (X - C (P i))).coeff k).coeff j = 0 :=
  M4cP1D1.exists_approximants_at_infty n w F hF hwt c hlead r hr h0 h1

end S_Polynomial_exists_approximants_at_infty
end P2MW
export P2MW.S_Polynomial_exists_approximants_at_infty (solution)

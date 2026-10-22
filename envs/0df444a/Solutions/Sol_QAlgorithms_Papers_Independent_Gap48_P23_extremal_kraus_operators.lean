-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.extremal_kraus_operators
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:09:03.351653+00:00
-- url     : https://prove2.me/submissions/5d4e5426-66d1-4aa4-a569-f0c32ffeaebd

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)


lemma g74f_D (ell : ℕ) (r : Fin ell ⊕ Fin (ell + 2)) (a : Fin 2) (w : Fin (ell+1)) :
    dualCG ell r (a, w) = if a = 0 then -ordinaryCG ell r (1, w) else ordinaryCG ell r (0, w) := by
  simp only [dualCG, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases a <;> simp [Matrix.one_apply]

lemma g74f_Dl0 (ell : ℕ) (x : Fin ell) (w : Fin (ell+1)) :
    dualCG ell (Sum.inl x) (0, w) = if x.val = w.val then
      (Real.sqrt ((ell:ℝ) - x.val) : ℂ) / (Real.sqrt ((ell:ℝ)+1) : ℂ) else 0 := by
  rw [g74f_D]; simp only [if_true, ordinaryCG]
  simp
  split_ifs with h <;> simp [h, neg_div]

lemma g74f_Dl1 (ell : ℕ) (x : Fin ell) (w : Fin (ell+1)) :
    dualCG ell (Sum.inl x) (1, w) = if w.val = x.val + 1 then
      (Real.sqrt ((x.val:ℝ) + 1) : ℂ) / (Real.sqrt ((ell:ℝ)+1) : ℂ) else 0 := by
  rw [g74f_D]; simp only [ordinaryCG]
  simp
  split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | simp | skip
  have : ((w:ℕ):ℝ) = (x:ℕ) + 1 := by exact_mod_cast h2
  rw [this]

lemma g74f_Dr0 (ell : ℕ) (y : Fin (ell+2)) (w : Fin (ell+1)) :
    dualCG ell (Sum.inr y) (0, w) = if w.val + 1 = y.val then
      -((Real.sqrt (y.val:ℝ) : ℂ) / (Real.sqrt ((ell:ℝ)+1) : ℂ)) else 0 := by
  rw [g74f_D]; simp only [if_true, ordinaryCG]
  simp
  split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | simp | skip
  have : ((y:ℕ):ℝ) = (w:ℕ) + 1 := by exact_mod_cast h1
  rw [this]

lemma g74f_Dr1 (ell : ℕ) (y : Fin (ell+2)) (w : Fin (ell+1)) :
    dualCG ell (Sum.inr y) (1, w) = if w.val = y.val then
      (Real.sqrt ((ell:ℝ) + 1 - y.val) : ℂ) / (Real.sqrt ((ell:ℝ)+1) : ℂ) else 0 := by
  rw [g74f_D]; simp only [ordinaryCG]
  simp
  split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | simp | skip
  have : ((w:ℕ):ℝ) = (y:ℕ) := by exact_mod_cast h2
  rw [this]

lemma g74f_choiF (ell : ℕ) (p q : Fin 2 × Fin (ell+1)) :
    extremalChoi ell false p q = ∑ x : Fin ell, conj (dualCG ell (Sum.inl x) p) * (((ell:ℂ)+1)/ell) *
      dualCG ell (Sum.inl x) q := by
  simp [extremalChoi, Matrix.mul_apply, Fintype.sum_sum_type, blockDiagonal, Matrix.one_apply]

lemma g74f_choiT (ell : ℕ) (p q : Fin 2 × Fin (ell+1)) :
    extremalChoi ell true p q = ∑ y : Fin (ell+2), conj (dualCG ell (Sum.inr y) p) * (((ell:ℂ)+1)/(ell+2)) *
      dualCG ell (Sum.inr y) q := by
  simp [extremalChoi, Matrix.mul_apply, Fintype.sum_sum_type, blockDiagonal, Matrix.one_apply]


lemma g74f_sqR (A B L M : ℝ) (hL : 0 < L + 1) (hM : 0 < M) :
    (Real.sqrt A / Real.sqrt (L+1)) * ((L+1)/M) * (Real.sqrt B / Real.sqrt (L+1)) =
      Real.sqrt (A/M) * Real.sqrt (B/M) := by
  rw [Real.sqrt_div' _ hM.le, Real.sqrt_div' _ hM.le]
  have s1 := Real.mul_self_sqrt hL.le
  have s2 := Real.mul_self_sqrt hM.le
  have p1 : 0 < Real.sqrt (L+1) := Real.sqrt_pos.mpr hL
  have p2 : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  field_simp
  rw [Real.sq_sqrt hL.le, Real.sq_sqrt hM.le]; ring

lemma g74f_sqC (A B L M : ℝ) (hL : 0 < L + 1) (hM : 0 < M) :
    ((Real.sqrt A : ℂ) / (Real.sqrt (L+1) : ℂ)) * (((L:ℂ)+1)/(M:ℂ)) * ((Real.sqrt B : ℂ) / (Real.sqrt (L+1) : ℂ)) =
      (Real.sqrt (A/M) : ℂ) * (Real.sqrt (B/M) : ℂ) := by
  have := g74f_sqR A B L M hL hM
  have h2 : (((Real.sqrt A / Real.sqrt (L+1)) * ((L+1)/M) * (Real.sqrt B / Real.sqrt (L+1)) : ℝ) : ℂ) =
      ((Real.sqrt (A/M) * Real.sqrt (B/M) : ℝ) : ℂ) := by rw [this]
  push_cast at h2
  exact h2

lemma g74f_ptF (ell : ℕ) (hell : 1 ≤ ell) (x : Fin ell) (a b : Fin 2) (w v : Fin (ell+1)) :
    conj (dualCG ell (Sum.inl x) (a, w)) * (((ell:ℂ)+1)/ell) * dualCG ell (Sum.inl x) (b, v) =
      traceKraus ell x a w * conj (traceKraus ell x b v) := by
  have hl : (0:ℝ) < ell := by exact_mod_cast hell
  have hL : (0:ℝ) < (ell:ℝ) + 1 := by linarith
  fin_cases a <;> fin_cases b <;>
    simp [g74f_Dl0, g74f_Dl1, traceKraus] <;> split_ifs <;> (try (exfalso; omega)) <;> (try simp) <;>
    first
    | (have := g74f_sqC ((ell:ℝ) - x.val) ((ell:ℝ) - x.val) ell ell hL hl; simpa [mul_assoc] using this)
    | (have := g74f_sqC ((ell:ℝ) - x.val) ((x.val:ℝ) + 1) ell ell hL hl; simpa [mul_assoc] using this)
    | (have := g74f_sqC ((x.val:ℝ) + 1) ((ell:ℝ) - x.val) ell ell hL hl; simpa [mul_assoc] using this)
    | (have := g74f_sqC ((x.val:ℝ) + 1) ((x.val:ℝ) + 1) ell ell hL hl; simpa [mul_assoc] using this)

lemma g74f_ptT (ell : ℕ) (y : Fin (ell+2)) (a b : Fin 2) (w v : Fin (ell+1)) :
    conj (dualCG ell (Sum.inr y) (a, w)) * (((ell:ℂ)+1)/(ell+2)) * dualCG ell (Sum.inr y) (b, v) =
      notKraus ell y a w * conj (notKraus ell y b v) := by
  have hl : (0:ℝ) < (ell:ℝ) + 2 := by positivity
  have hL : (0:ℝ) < (ell:ℝ) + 1 := by positivity
  have e2 : ((ell:ℂ) + 2) = (((ell:ℝ)+2 : ℝ) : ℂ) := by push_cast; ring
  fin_cases a <;> fin_cases b <;>
    simp [g74f_Dr0, g74f_Dr1, notKraus] <;> split_ifs <;> (try (exfalso; omega)) <;> (try simp) <;>
    rw [e2] <;>
    first
    | (have := g74f_sqC (y.val:ℝ) (y.val:ℝ) ell ((ell:ℝ)+2) hL hl; simpa [mul_assoc] using this)
    | (have := g74f_sqC (y.val:ℝ) ((ell:ℝ) + 1 - y.val) ell ((ell:ℝ)+2) hL hl; simpa [mul_assoc] using this)
    | (have := g74f_sqC ((ell:ℝ) + 1 - y.val) (y.val:ℝ) ell ((ell:ℝ)+2) hL hl; simpa [mul_assoc] using this)
    | (have := g74f_sqC ((ell:ℝ) + 1 - y.val) ((ell:ℝ) + 1 - y.val) ell ((ell:ℝ)+2) hL hl; simpa [mul_assoc] using this)
    | trace_state

lemma g74f_ofChoi_kraus {K I O : Type*} [Fintype K] [Fintype I] (J : Op (O × I)) (E : K → Matrix O I ℂ)
    (hJ : ∀ a i b j, J (a, i) (b, j) = ∑ k, E k a i * conj (E k b j)) :
    ofChoi J = krausApply E := by
  funext rho
  funext a b
  simp only [ofChoi, krausApply]
  rw [Matrix.sum_apply]
  simp only [hJ, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, RCLike.star_def]
  calc _ = ∑ i, ∑ k, ∑ j, E k a i * conj (E k b j) * rho i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
     _ = ∑ k, ∑ i, ∑ j, E k a i * conj (E k b j) * rho i j := Finset.sum_comm
     _ = ∑ k, ∑ j, ∑ i, E k a i * conj (E k b j) * rho i j :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
     _ = _ := Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i _ => by ring

lemma g74f_chF (ell : ℕ) (hell : 1 ≤ ell) : extremalChannel ell false = krausApply (traceKraus ell) := by
  apply g74f_ofChoi_kraus
  intro a i b j
  rw [g74f_choiF]
  exact Finset.sum_congr rfl fun x _ => g74f_ptF ell hell x a b i j

lemma g74f_chT (ell : ℕ) : extremalChannel ell true = krausApply (notKraus ell) := by
  apply g74f_ofChoi_kraus
  intro a i b j
  rw [g74f_choiT]
  exact Finset.sum_congr rfl fun x _ => g74f_ptT ell x a b i j

lemma g74f_sumfin (l n : ℕ) (c : ℂ) :
    ∑ x : Fin l, (if (x:ℕ) = n then c else 0) = if n < l then c else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if x = n then c else 0), Finset.sum_ite_eq']
  simp

lemma g74f_csq (t : ℝ) (ht : 0 ≤ t) : conj ((Real.sqrt t : ℂ)) * (Real.sqrt t : ℂ) = (t : ℂ) := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt ht]

lemma g74f_csq2 (A M : ℝ) (hA : 0 ≤ A) (hM : 0 < M) :
    ((Real.sqrt A : ℝ) : ℂ) / ((Real.sqrt M : ℝ) : ℂ) * (((Real.sqrt A : ℝ) : ℂ) / ((Real.sqrt M : ℝ) : ℂ)) =
      ((A:ℝ):ℂ) / ((M:ℝ):ℂ) := by
  rw [div_mul_div_comm, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt hA, Real.mul_self_sqrt hM.le]

lemma g74f_krausF (ell : ℕ) (hell : 1 ≤ ell) : IsKrausFamily (traceKraus ell) := by
  have hl : (0:ℝ) < ell := by exact_mod_cast hell
  unfold IsKrausFamily
  ext w v
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, RCLike.star_def]
  by_cases hwv : w = v
  · subst hwv
    have hterm : ∀ x : Fin ell, conj (traceKraus ell x 0 w) * traceKraus ell x 0 w +
        conj (traceKraus ell x 1 w) * traceKraus ell x 1 w =
        (if (x:ℕ) = w.val then ((((ell:ℝ) - w.val)/ell : ℝ) : ℂ) else 0) +
        (if (x:ℕ) = w.val - 1 ∧ 1 ≤ w.val then (((w.val : ℝ)/ell : ℝ) : ℂ) else 0) := by
      intro x
      simp only [traceKraus]
      simp only [Fin.isValue, true_and, zero_ne_one, false_and, if_false, one_ne_zero, and_true]
      split_ifs with h1 h2 h3 <;> (try (exfalso; omega)) <;> simp
      all_goals first
        | (have e : ((x:ℕ):ℝ) = (w:ℕ) := by exact_mod_cast (show x.val = w.val by omega)
           rw [e]
           have := g74f_csq2 ((ell:ℝ) - w.val) ell (by
             have : (w:ℕ) < ell := by omega
             have : ((w:ℕ):ℝ) < ell := by exact_mod_cast this
             linarith) hl
           push_cast at this; exact this)
        | (have e : ((x:ℕ):ℝ) + 1 = (w:ℕ) := by exact_mod_cast (show x.val + 1 = w.val by omega)
           rw [e]
           have := g74f_csq2 (w.val : ℝ) ell (by positivity) hl
           push_cast at this; exact this)
    rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_add_distrib, g74f_sumfin]
    have h2 : ∑ x : Fin ell, (if (x:ℕ) = w.val - 1 ∧ 1 ≤ w.val then (((w.val : ℝ)/ell : ℝ) : ℂ) else 0) =
        if 1 ≤ w.val then (((w.val : ℝ)/ell : ℝ) : ℂ) else 0 := by
      by_cases hw : 1 ≤ w.val
      · simp only [hw, and_true, if_true]
        rw [g74f_sumfin, if_pos (by omega)]
      · simp [hw]
    rw [h2, Matrix.one_apply_eq]
    have hw := w.isLt
    split_ifs with h3 h4 h4 <;> push_cast
    · field_simp; ring
    · have : (w:ℕ) = 0 := by omega
      rw [this]; field_simp; try simp
    · have : (w:ℕ) = ell := by omega
      rw [this]; field_simp; try simp
    · omega
  · rw [Matrix.one_apply_ne hwv]
    apply Finset.sum_eq_zero
    intro x _
    have : (w:ℕ) ≠ v := fun h => hwv (Fin.ext h)
    simp only [traceKraus]
    split_ifs <;> first | (exfalso; omega) | simp

lemma g74f_krausT (ell : ℕ) : IsKrausFamily (notKraus ell) := by
  have hl : (0:ℝ) < (ell:ℝ) + 2 := by positivity
  unfold IsKrausFamily
  ext w v
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, RCLike.star_def]
  by_cases hwv : w = v
  · subst hwv
    have hterm : ∀ y : Fin (ell+2), conj (notKraus ell y 0 w) * notKraus ell y 0 w +
        conj (notKraus ell y 1 w) * notKraus ell y 1 w =
        (if (y:ℕ) = w.val + 1 then ((((w.val:ℝ) + 1)/((ell:ℝ)+2) : ℝ) : ℂ) else 0) +
        (if (y:ℕ) = w.val then ((((ell:ℝ) + 1 - w.val)/((ell:ℝ)+2) : ℝ) : ℂ) else 0) := by
      intro y
      simp only [notKraus]
      simp only [Fin.isValue, true_and, zero_ne_one, false_and, if_false, one_ne_zero, and_true]
      split_ifs with h1 h2 h3 <;> (try (exfalso; omega)) <;> simp
      all_goals first
        | (have e : ((y:ℕ):ℝ) = (w:ℕ) + 1 := by exact_mod_cast (show y.val = w.val + 1 by omega)
           rw [e]
           have := g74f_csq2 ((w.val : ℝ) + 1) ((ell:ℝ) + 2) (by positivity) hl
           push_cast at this; exact this)
        | (have e : ((y:ℕ):ℝ) = (w:ℕ) := by exact_mod_cast (show y.val = w.val by omega)
           rw [e]
           have hA : (0:ℝ) ≤ (ell:ℝ) + 1 - w.val := by
             have : (w:ℕ) < ell + 1 := w.isLt
             have : ((w:ℕ):ℝ) < ell + 1 := by exact_mod_cast this
             linarith
           rw [← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg hA hl.le)]
           push_cast; ring)
    rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_add_distrib, g74f_sumfin, g74f_sumfin,
      Matrix.one_apply_eq]
    have hw := w.isLt
    rw [if_pos (by omega), if_pos (by omega)]
    push_cast
    field_simp
    ring
  · rw [Matrix.one_apply_ne hwv]
    apply Finset.sum_eq_zero
    intro x _
    have : (w:ℕ) ≠ v := fun h => hwv (Fin.ext h)
    simp only [notKraus]
    split_ifs <;> first | (exfalso; omega) | simp

theorem solution (ell : ℕ) (hell : 1 ≤ ell) :
    IsKrausFamily (traceKraus ell) ∧ IsKrausFamily (notKraus ell) ∧
    extremalChannel ell false = krausApply (traceKraus ell) ∧
    extremalChannel ell true = krausApply (notKraus ell) ∧
    notKraus ell 0 = (Real.sqrt (((ell : ℝ)+1)/(ell+2)) : ℂ) • Matrix.single 1 0 1 ∧
    notKraus ell ⟨ell+1, by omega⟩ =
      -(Real.sqrt (((ell : ℝ)+1)/(ell+2)) : ℂ) • Matrix.single 0 ⟨ell, by omega⟩ 1 := by
  refine ⟨g74f_krausF ell hell, g74f_krausT ell, g74f_chF ell hell, g74f_chT ell, ?_, ?_⟩
  · ext i j
    fin_cases i <;> simp [notKraus, Matrix.single_apply] <;>
      (split_ifs with h1 h2 <;> first | rfl | (exfalso; apply h2; exact h1.symm) |
        (exfalso; apply h1; exact h2.symm) | (exfalso; apply h2; ext; simp [h1]) | (exfalso; apply h1; rw [← h2]) |
        (rename_i h; exfalso; exact h1 h.symm) | (rename_i h; exfalso; apply h1; rw [← h]))
  · ext i j
    fin_cases i <;> simp [notKraus, Matrix.single_apply] <;>
      (split_ifs with h1 h2 <;> first | rfl | (exfalso; apply h2; exact h1.symm) |
        (exfalso; apply h1; exact h2.symm) | (exfalso; apply h2; ext; simp [h1]) | (exfalso; apply h1; rw [← h2]) |
        (rename_i h; exfalso; exact h1 h.symm) | (rename_i h; exfalso; apply h1; rw [← h]))

end

-- Prove2me | solution 1 for WeilConjectures.deligne_cohomology_realization
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T18:35:45.368506+00:00
-- url     : https://prove2.me/submissions/7113d2d5-3c7a-406f-8135-e7bc0f411f8a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_deligne_weil_charpolys

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

section CompanionAndPoincare

private lemma matrix_mul_eq_one_comm {R : Type*} [CommRing R] {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) R} (hAB : A * B = 1) : B * A = 1 := by
  have hmul : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hdet : IsUnit A.det := ⟨⟨A.det, B.det, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  have hB : B = A⁻¹ := by
    calc
      B = 1 * B := (Matrix.one_mul B).symm
      _ = (A⁻¹ * A) * B := by rw [Matrix.nonsing_inv_mul A hdet]
      _ = A⁻¹ * (A * B) := Matrix.mul_assoc _ _ _
      _ = A⁻¹ := by rw [hAB, Matrix.mul_one]
  rw [hB, Matrix.nonsing_inv_mul A hdet]

private lemma coeff_comp_C_mul_X (P : ℚ[X]) (a : ℚ) (j : ℕ) :
    (P.comp (C a * X)).coeff j = P.coeff j * a ^ j := by
  induction P using Polynomial.induction_on' generalizing j with
  | add p q hp hq =>
    simp [Polynomial.add_comp, hp, hq, add_mul]
  | monomial n r =>
    rw [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
      ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp

private lemma natDegree_reverse_le_self (P : ℚ[X]) :
    P.reverse.natDegree ≤ P.natDegree := by
  rw [Polynomial.reverse]
  simpa using (Polynomial.natDegree_reflect_le (p := P) (N := P.natDegree))

private def companionMat (d : ℕ) (c : ℕ → ℚ) : Matrix (Fin d) (Fin d) ℚ :=
  Matrix.of fun r s =>
    if s.val + 1 = d then -(c r.val)
    else if r.val = s.val + 1 then 1
    else 0

private def companionMatrix (P : ℚ[X]) : Matrix (Fin P.natDegree) (Fin P.natDegree) ℚ :=
  companionMat P.natDegree P.coeff

private lemma charpoly_companionMat (d : ℕ) (c : ℕ → ℚ) :
    (companionMat d c).charpoly =
      X ^ d + ∑ k ∈ Finset.range d, C (c k) * X ^ k := by
  induction d generalizing c with
  | zero =>
    simp [Matrix.charpoly, Matrix.charmatrix]
  | succ m ih =>
    cases m with
    | zero =>
      rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]
      simp [companionMat]
    | succ m =>
      rw [Matrix.charpoly, Matrix.det_succ_row_zero]
      have hrow0 : ∀ j : Fin (m + 2),
          (companionMat (m + 2) c).charmatrix 0 j =
            if j = 0 then X
            else if j = Fin.last (m + 1) then C (c 0)
            else 0 := by
        intro j
        by_cases hj0 : j = 0
        · subst hj0
          simp [Matrix.charmatrix_apply_eq, companionMat]
        · rw [if_neg hj0, Matrix.charmatrix_apply_ne _ _ _ (Ne.symm hj0)]
          by_cases hjl : j = Fin.last (m + 1)
          · subst hjl
            simp [companionMat]
          · rw [if_neg hjl]
            have h1 : j.val ≠ m + 1 := by
              intro h
              apply hjl
              ext
              simpa [Fin.val_last] using h
            simp [companionMat, h1]
      have hne : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
        intro h
        have := congrArg Fin.val h
        simp at this
      have hsum :
          ∑ j : Fin (m + 2), (-1 : ℚ[X]) ^ (j : ℕ) *
              (companionMat (m + 2) c).charmatrix 0 j *
              ((companionMat (m + 2) c).charmatrix.submatrix Fin.succ j.succAbove).det =
            X * ((companionMat (m + 2) c).charmatrix.submatrix Fin.succ (0 : Fin (m + 2)).succAbove).det +
            (-1 : ℚ[X]) ^ (m + 1) * C (c 0) *
              ((companionMat (m + 2) c).charmatrix.submatrix Fin.succ (Fin.last (m + 1)).succAbove).det := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin (m + 2)))]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩)]
        have hrest :
            ∑ j ∈ (Finset.univ.erase (0 : Fin (m + 2))).erase (Fin.last (m + 1)),
              (-1 : ℚ[X]) ^ (j : ℕ) *
                (companionMat (m + 2) c).charmatrix 0 j *
                ((companionMat (m + 2) c).charmatrix.submatrix Fin.succ j.succAbove).det = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          have hjl : j ≠ Fin.last (m + 1) := (Finset.mem_erase.mp hj).1
          have hj0 : j ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
          rw [hrow0 j, if_neg hj0, if_neg hjl, mul_zero, zero_mul]
        rw [hrest, add_zero, hrow0 0, if_pos rfl, hrow0 (Fin.last (m + 1)), if_neg hne.symm, if_pos rfl]
        simp
      rw [hsum]
      have hsub0 :
          (companionMat (m + 2) c).charmatrix.submatrix Fin.succ (0 : Fin (m + 2)).succAbove =
            (companionMat (m + 1) (fun k => c (k + 1))).charmatrix := by
        ext i j
        simp only [Matrix.submatrix_apply, Fin.succAbove_zero]
        by_cases hij : i = j
        · subst hij
          simp only [Matrix.charmatrix_apply_eq, companionMat, Matrix.of_apply, Fin.val_succ]
          by_cases hlast : i.val + 1 = m + 1 <;> simp
        · have hij' : i.succ ≠ j.succ := fun h => hij (Fin.succ_injective _ h)
          rw [Matrix.charmatrix_apply_ne _ _ _ hij', Matrix.charmatrix_apply_ne _ _ _ hij]
          simp only [companionMat, Matrix.of_apply, Fin.val_succ]
          by_cases hlast : j.val + 1 = m + 1
          · simp [hlast]
          · have hlast2 : j.val + 1 + 1 ≠ m + 2 := by omega
            simp only [hlast, hlast2, ↓reduceIte]
            by_cases hsub : i.val = j.val + 1
            · simp [hsub]
            · simp [hsub]
      have hsubLast_tri :
          ((companionMat (m + 2) c).charmatrix.submatrix Fin.succ
            (Fin.last (m + 1)).succAbove).IsUpperTriangular := by
        intro i j hij
        have hij_lt : j.val < i.val := hij
        simp only [Matrix.submatrix_apply, Fin.succAbove_last]
        have hne_ij : i.succ ≠ j.castSucc := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_succ, Fin.val_castSucc] at this
          omega
        rw [Matrix.charmatrix_apply_ne _ _ _ hne_ij]
        simp only [companionMat, Matrix.of_apply, Fin.val_succ, Fin.val_castSucc]
        have h1 : j.val ≠ m + 1 := by omega
        have h2 : i.val ≠ j.val := by omega
        simp [h1, h2]
      have hsubLast_det :
          ((companionMat (m + 2) c).charmatrix.submatrix Fin.succ
            (Fin.last (m + 1)).succAbove).det = (-1 : ℚ[X]) ^ (m + 1) := by
        rw [Matrix.det_of_isUpperTriangular hsubLast_tri]
        have hdiag : ∀ i : Fin (m + 1),
            ((companionMat (m + 2) c).charmatrix.submatrix Fin.succ
              (Fin.last (m + 1)).succAbove) i i = -1 := by
          intro i
          simp only [Matrix.submatrix_apply, Fin.succAbove_last]
          have hne_ii : i.succ ≠ i.castSucc := by
            intro h
            have := congrArg Fin.val h
            simp at this
          rw [Matrix.charmatrix_apply_ne _ _ _ hne_ii]
          simp only [companionMat, Matrix.of_apply, Fin.val_succ, Fin.val_castSucc]
          have h1 : i.val ≠ m + 1 := by omega
          simp [h1]
        simp_rw [hdiag]
        simp
      rw [hsub0, hsubLast_det]
      change X * (companionMat (m + 1) (fun k => c (k + 1))).charpoly + _ = _
      rw [ih (fun k => c (k + 1))]
      have hsign : (-1 : ℚ[X]) ^ (m + 1) * C (c 0) * (-1 : ℚ[X]) ^ (m + 1) = C (c 0) := by
        calc
          (-1 : ℚ[X]) ^ (m + 1) * C (c 0) * (-1 : ℚ[X]) ^ (m + 1)
              = ((-1 : ℚ[X]) * (-1 : ℚ[X])) ^ (m + 1) * C (c 0) := by rw [mul_pow]; ring
          _ = C (c 0) := by simp
      rw [hsign, mul_add, Finset.mul_sum]
      have hpow : (X : ℚ[X]) * X ^ (m + 1) = X ^ (m + 2) := by ring
      rw [hpow]
      have hterm : ∀ k ∈ Finset.range (m + 1),
          X * (C (c (k + 1)) * X ^ k) = C (c (k + 1)) * X ^ (k + 1) := by
        intro k _
        ring
      rw [Finset.sum_congr rfl hterm]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [pow_zero, mul_one]
      ring

private lemma charpoly_companionMatrix (P : ℚ[X]) (hP : P.Monic) :
    (companionMatrix P).charpoly = P := by
  rw [companionMatrix, charpoly_companionMat]
  conv_rhs => rw [P.as_sum_range_C_mul_X_pow]
  rw [Finset.sum_range_succ, hP.coeff_natDegree, map_one, one_mul, add_comm]

private lemma coeff_reverse_comp_C_mul_X (P : ℚ[X]) (a : ℚ) (ha : a ≠ 0) (m : ℕ) :
    ((P.comp (C a * X)).reverse).coeff m =
      if m ≤ P.natDegree then P.coeff (P.natDegree - m) * a ^ (P.natDegree - m) else 0 := by
  have hdeg_ca : (C a * X : ℚ[X]).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul_X _ ha]
  have hdeg_comp : (P.comp (C a * X)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_comp, hdeg_ca, mul_one]
  by_cases hm : m ≤ P.natDegree
  · rw [if_pos hm, Polynomial.coeff_reverse, ← hdeg_comp,
      Polynomial.revAt_le (hdeg_comp.symm ▸ hm), hdeg_comp, coeff_comp_C_mul_X]
  · rw [if_neg hm]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc
      (P.comp (C a * X)).reverse.natDegree ≤ (P.comp (C a * X)).natDegree :=
        natDegree_reverse_le_self _
      _ = P.natDegree := hdeg_comp
      _ < m := Nat.lt_of_not_ge hm

private lemma poincare_duality_companion (P Q : ℚ[X]) (hP : P.Monic) (hQ : Q.Monic)
    (hc0 : P.coeff 0 ≠ 0) (a : ℚ) (ha : a ≠ 0)
    (hdeg : Q.natDegree = P.natDegree)
    (hrec : P.coeff 0 • Q = (P.comp (C a * X)).reverse) :
    ∃ (G : Matrix (Fin P.natDegree) (Fin Q.natDegree) ℚ)
      (H : Matrix (Fin Q.natDegree) (Fin P.natDegree) ℚ),
      G * H = 1 ∧ H * G = 1 ∧
      (companionMatrix P).transpose * G * companionMatrix Q = a • G := by
  let d := P.natDegree
  let e : Fin Q.natDegree ≃ Fin d := finCongr hdeg
  have hQ_eq : companionMatrix Q = (companionMat d Q.coeff).submatrix e e := by
    ext i j
    simp [companionMatrix, companionMat, Matrix.submatrix_apply, d, e, hdeg]
  suffices h : ∃ (G H : Matrix (Fin d) (Fin d) ℚ),
      G * H = 1 ∧ H * G = 1 ∧
      (companionMat d P.coeff).transpose * G * companionMat d Q.coeff = a • G by
    rcases h with ⟨G, H, hGH, hHG, hcomm⟩
    refine ⟨G.submatrix id e, H.submatrix e id, ?_, ?_, ?_⟩
    · ext i j
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, Matrix.one_apply]
      rw [Equiv.sum_comp e (fun k => G i k * H k j)]
      simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hGH i) j
    · ext i j
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, Matrix.one_apply]
      have hij := congrFun (congrFun hHG (e i)) (e j)
      simpa [Matrix.mul_apply, Matrix.one_apply, Equiv.apply_eq_iff_eq] using hij
    · rw [hQ_eq]
      ext i j
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, Matrix.smul_apply, smul_eq_mul]
      rw [Equiv.sum_comp e (fun k =>
        (∑ y : Fin d, (companionMatrix P).transpose i y * G y k) * companionMat d Q.coeff k (e j))]
      have hij := congrFun (congrFun hcomm i) (e j)
      simpa [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, companionMatrix, d] using hij
  by_cases hd : d = 0
  · refine ⟨1, 1, by simp, by simp, ?_⟩
    ext i j
    exact Fin.elim0 (hd ▸ i)
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    let MP := companionMat d P.coeff
    let MQ := companionMat d Q.coeff
    let Binv : Matrix (Fin d) (Fin d) ℚ := Matrix.of fun r s =>
      (if r.val = s.val + 1 then (1 : ℚ) else 0) -
      (if r.val = 0 then (if s.val + 1 < d then P.coeff (s.val + 1) else 1) / P.coeff 0 else 0)
    have hMP_Binv : MP.transpose * Binv = 1 := by
      ext i j
      rw [Matrix.mul_apply, Matrix.one_apply]
      have hterm : ∀ k : Fin d,
          MP.transpose i k * Binv k j =
            (if i.val + 1 = d then -(P.coeff k.val)
             else if k.val = i.val + 1 then 1 else 0) *
            ((if k.val = j.val + 1 then (1 : ℚ) else 0) -
             (if k.val = 0 then (if j.val + 1 < d then P.coeff (j.val + 1) else 1) / P.coeff 0 else 0)) := by
        intro k
        simp [MP, companionMat, Binv]
      simp_rw [hterm]
      by_cases hi : i.val + 1 = d
      · simp only [hi, ↓reduceIte]
        have hsplit :
            ∑ k : Fin d, -(P.coeff k.val) *
              ((if k.val = j.val + 1 then (1 : ℚ) else 0) -
               (if k.val = 0 then (if j.val + 1 < d then P.coeff (j.val + 1) else 1) / P.coeff 0 else 0)) =
            (∑ k : Fin d, if k.val = j.val + 1 then -(P.coeff k.val) else 0) +
            (∑ k : Fin d, if k.val = 0 then P.coeff k.val *
              ((if j.val + 1 < d then P.coeff (j.val + 1) else 1) / P.coeff 0) else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> ring
        rw [hsplit]
        have hsum0 :
            (∑ k : Fin d, if k.val = 0 then P.coeff k.val *
              ((if j.val + 1 < d then P.coeff (j.val + 1) else 1) / P.coeff 0) else 0) =
            (if j.val + 1 < d then P.coeff (j.val + 1) else 1) := by
          rw [Finset.sum_eq_single ⟨0, hdpos⟩]
          · simp only [↓reduceIte]
            field_simp [hc0]
          · intro k _ hk
            have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
            simp [hk0]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum0]
        by_cases hj : j.val + 1 < d
        · have hne : i ≠ j := by
            intro h; subst h; omega
          rw [if_pos hj, if_neg hne]
          rw [Finset.sum_eq_single ⟨j.val + 1, hj⟩]
          · simp
          · intro k _ hk
            have hkv : k.val ≠ j.val + 1 := fun h => hk (Fin.ext h)
            simp [hkv]
          · intro h; exact absurd (Finset.mem_univ _) h
        · have heq : i = j := by
            ext; omega
          rw [if_neg hj, if_pos heq]
          have hsum1 : (∑ k : Fin d, if k.val = j.val + 1 then -(P.coeff k.val) else 0) = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            have hkv : k.val ≠ j.val + 1 := by omega
            simp [hkv]
          rw [hsum1, zero_add]
      · simp only [hi, ↓reduceIte]
        have hilt : i.val + 1 < d := by omega
        rw [Finset.sum_eq_single ⟨i.val + 1, hilt⟩]
        · simp only [↓reduceIte, one_mul, Nat.add_eq_zero_iff, one_ne_zero, and_false, sub_zero]
          by_cases hij : i = j
          · subst hij; simp
          · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
            simp [hij, hne]
        · intro k _ hk
          have hkv : k.val ≠ i.val + 1 := fun h => hk (Fin.ext h)
          simp [hkv]
        · intro h; exact absurd (Finset.mem_univ _) h
    have hBinv_MP : Binv * MP.transpose = 1 := matrix_mul_eq_one_comm hMP_Binv
    let A : Matrix (Fin d) (Fin d) ℚ := a • Binv
    have hMPA : MP.transpose * A = a • 1 := by
      rw [Matrix.mul_smul, hMP_Binv]
    have hAMP : A * MP.transpose = a • 1 := by
      rw [Matrix.smul_mul, hBinv_MP]
    have hcomm_MPA : Commute MP.transpose A := by
      unfold Commute SemiconjBy
      rw [hMPA, hAMP]
    have hQA : Polynomial.aeval A Q = 0 := by
      have hMP_ch : Polynomial.aeval MP P = 0 := by
        have hch := Matrix.aeval_self_charpoly MP
        have hPeq : MP.charpoly = P := charpoly_companionMatrix P hP
        rwa [hPeq] at hch
      have hMPT_ch : Polynomial.aeval MP.transpose P = 0 := by
        have htr : ∀ R : ℚ[X], Polynomial.aeval MP.transpose R = (Polynomial.aeval MP R).transpose := by
          intro R
          induction R using Polynomial.induction_on' with
          | add p q hp hq =>
            rw [map_add, map_add, Matrix.transpose_add, hp, hq]
          | monomial n r =>
            rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
              Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul,
              Matrix.smul_mul, Matrix.one_mul, Matrix.transpose_smul, Matrix.transpose_pow]
        rw [htr P, hMP_ch, Matrix.transpose_zero]
      have hmul : (MP.transpose ^ d) * (P.coeff 0 • Polynomial.aeval A Q) = 0 := by
        have hQsum : P.coeff 0 • Polynomial.aeval A Q =
            ∑ m ∈ Finset.range (d + 1),
              (P.coeff (d - m) * a ^ (d - m)) • (A ^ m) := by
          have h1 : P.coeff 0 • Polynomial.aeval A Q =
              Polynomial.aeval A (P.coeff 0 • Q) := by
            simp
          rw [h1, hrec, Polynomial.aeval_eq_sum_range' (n := d + 1)]
          · refine Finset.sum_congr rfl fun m hm => ?_
            have hmle : m ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            rw [coeff_reverse_comp_C_mul_X P a ha m, if_pos hmle]
          · calc
              (P.comp (C a * X)).reverse.natDegree ≤ (P.comp (C a * X)).natDegree :=
                natDegree_reverse_le_self _
              _ = d := by rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X _ ha, mul_one]
              _ < d + 1 := Nat.lt_succ_self d
        rw [hQsum, Finset.mul_sum]
        have hterm_eq : ∀ m ∈ Finset.range (d + 1),
            MP.transpose ^ d * ((P.coeff (d - m) * a ^ (d - m)) • A ^ m) =
              a ^ d • (P.coeff (d - m) • MP.transpose ^ (d - m)) := by
          intro m hm
          have hmle : m ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
          have hpow_split : MP.transpose ^ d * A ^ m = a ^ m • MP.transpose ^ (d - m) := by
            have hd_eq : (d - m) + m = d := Nat.sub_add_cancel hmle
            have hpow : MP.transpose ^ d = MP.transpose ^ (d - m) * MP.transpose ^ m := by
              rw [← pow_add, hd_eq]
            rw [hpow, mul_assoc, ← hcomm_MPA.mul_pow, hMPA, _root_.smul_pow,
              one_pow, Matrix.mul_smul, Matrix.mul_one]
          rw [Matrix.mul_smul, hpow_split, smul_smul, smul_smul]
          congr 1
          have hadd : (d - m) + m = d := Nat.sub_add_cancel hmle
          calc
            P.coeff (d - m) * a ^ (d - m) * a ^ m
                = P.coeff (d - m) * (a ^ (d - m) * a ^ m) := by ring
            _ = P.coeff (d - m) * a ^ ((d - m) + m) := by rw [← pow_add]
            _ = a ^ d * P.coeff (d - m) := by rw [hadd, mul_comm]
        rw [Finset.sum_congr rfl hterm_eq, ← Finset.smul_sum]
        have hrev :
            ∑ m ∈ Finset.range (d + 1), P.coeff (d - m) • MP.transpose ^ (d - m) =
              ∑ j ∈ Finset.range (d + 1), P.coeff j • MP.transpose ^ j := by
          exact Finset.sum_range_reflect (fun j => P.coeff j • MP.transpose ^ j) (d + 1)
        rw [hrev]
        have hP_eval :
            ∑ j ∈ Finset.range (d + 1), P.coeff j • MP.transpose ^ j =
              Polynomial.aeval MP.transpose P := by
          rw [Polynomial.aeval_eq_sum_range' (n := d + 1) (Nat.lt_succ_self d)]
        rw [hP_eval, hMPT_ch, smul_zero]
      have hleft_cancel : P.coeff 0 • Polynomial.aeval A Q = 0 := by
        have h := congrArg (fun M => Binv ^ d * M) hmul
        simp only [Matrix.mul_zero, ← Matrix.mul_assoc] at h
        have hcomm_B : Commute Binv MP.transpose := by
          unfold Commute SemiconjBy; rw [hBinv_MP, hMP_Binv]
        rw [← hcomm_B.mul_pow, hBinv_MP, one_pow, Matrix.one_mul] at h
        exact h
      exact (smul_eq_zero.mp hleft_cancel).resolve_left hc0
    let e0 : Fin d := ⟨0, hdpos⟩
    let G : Matrix (Fin d) (Fin d) ℚ := Matrix.of fun r s => (A ^ s.val) r e0
    have hG_tri_diag : ∀ j : Fin d,
        (∀ r : Fin d, j.val < r.val → (A ^ j.val) r e0 = 0) ∧
        (A ^ j.val) j e0 = a ^ j.val := by
      intro j
      rcases j with ⟨jv, hjv⟩
      induction jv with
      | zero =>
        refine ⟨?_, ?_⟩
        · intro r hr
          have hne : r ≠ e0 := by
            intro h; subst h; simp [e0] at hr
          simp [hne]
        · simp [e0]
      | succ jv ih =>
        have ih' := ih (Nat.lt_of_succ_lt hjv)
        have hstep : ∀ r : Fin d,
            (A ^ (jv + 1)) r e0 = ∑ k : Fin d, A r k * (A ^ jv) k e0 := by
          intro r
          rw [pow_succ', Matrix.mul_apply]
        refine ⟨?_, ?_⟩
        · intro r hr
          have hr_gt : jv + 1 < r.val := hr
          rw [hstep r]
          refine Finset.sum_eq_zero fun k _ => ?_
          by_cases hk : jv < k.val
          · rw [ih'.1 k hk, mul_zero]
          · have hkle : k.val ≤ jv := Nat.le_of_not_lt hk
            have hr0 : r.val ≠ 0 := by omega
            have hrk : r.val ≠ k.val + 1 := by omega
            have hA0 : A r k = 0 := by
              simp [A, Binv, hr0, hrk]
            rw [hA0, zero_mul]
        · rw [hstep ⟨jv + 1, hjv⟩]
          rw [Finset.sum_eq_single ⟨jv, Nat.lt_of_succ_lt hjv⟩]
          · rw [ih'.2]
            have hA_sub : A ⟨jv + 1, hjv⟩ ⟨jv, Nat.lt_of_succ_lt hjv⟩ = a := by
              simp [A, Binv]
            rw [hA_sub, pow_succ']
          · intro k _ hk
            by_cases hkgt : jv < k.val
            · rw [ih'.1 k hkgt, mul_zero]
            · have hklt : k.val < jv := by
                have hne : k.val ≠ jv := fun h => hk (Fin.ext h)
                omega
              have hA0 : A ⟨jv + 1, hjv⟩ k = 0 := by
                have h1 : jv ≠ k.val := by omega
                simp [A, Binv, h1]
              rw [hA0, zero_mul]
          · intro h; exact absurd (Finset.mem_univ _) h
    have hG_tri : G.IsUpperTriangular := by
      intro i j hij
      exact (hG_tri_diag j).1 i hij
    have hG_det : G.det ≠ 0 := by
      rw [Matrix.det_of_isUpperTriangular hG_tri]
      have hdiag : ∀ j : Fin d, G j j = a ^ j.val := fun j => (hG_tri_diag j).2
      simp_rw [hdiag]
      exact Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ ha
    have hG_unit : IsUnit G.det := isUnit_iff_ne_zero.mpr hG_det
    have hAG_GMQ : A * G = G * MQ := by
      ext r s
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have hlhs : ∑ k : Fin d, A r k * G k s = (A ^ (s.val + 1)) r e0 := by
        rw [pow_succ', Matrix.mul_apply]
        rfl
      rw [hlhs]
      by_cases hs : s.val + 1 = d
      · have hrhs : ∑ k : Fin d, G r k * MQ k s =
            ∑ k : Fin d, -(Q.coeff k.val) * (A ^ k.val) r e0 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [G, MQ, companionMat, Matrix.of_apply, hs, ↓reduceIte]
          ring
        rw [hrhs]
        have hQ_eval : Polynomial.aeval A Q =
            A ^ d + ∑ k ∈ Finset.range d, Q.coeff k • A ^ k := by
          conv_lhs => rw [Q.as_sum_range_C_mul_X_pow]
          rw [hdeg, Finset.sum_range_succ, ← hdeg, hQ.coeff_natDegree, map_one, one_mul,
            map_add, map_pow, Polynomial.aeval_X, map_sum, add_comm]
          congr 1
          · rw [hdeg]
          · refine Finset.sum_congr (by rw [hdeg]) fun k _ => ?_
            rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
              Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
        have h0 := congrFun (congrFun (hQ_eval.symm.trans hQA) r) e0
        simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
          Matrix.zero_apply] at h0
        have hsum_fin :
            ∑ k : Fin d, -(Q.coeff k.val) * (A ^ k.val) r e0 =
            -(∑ k ∈ Finset.range d, Q.coeff k * (A ^ k) r e0) := by
          rw [← Finset.sum_neg_distrib,
            ← Fin.sum_univ_eq_sum_range (fun k => -(Q.coeff k * (A ^ k) r e0)) d]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [hs, hsum_fin]
        linarith
      · have hslt : s.val + 1 < d := by omega
        rw [Finset.sum_eq_single ⟨s.val + 1, hslt⟩]
        · simp [G, MQ, companionMat, hs]
        · intro k _ hk
          have hkv : k.val ≠ s.val + 1 := fun h => hk (Fin.ext h)
          simp [MQ, companionMat, hs, hkv]
        · intro h; exact absurd (Finset.mem_univ _) h
    refine ⟨G, G⁻¹, Matrix.mul_nonsing_inv G hG_unit, Matrix.nonsing_inv_mul G hG_unit, ?_⟩
    rw [Matrix.mul_assoc, ← hAG_GMQ, ← Matrix.mul_assoc, hMPA, Matrix.smul_mul, Matrix.one_mul]

end CompanionAndPoincare

section JacobiTraceFormula

open PowerSeries

private lemma derivative_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → PowerSeries ℚ) :
    PowerSeries.derivative ℚ (∏ i ∈ s, f i) =
      ∑ i ∈ s, (PowerSeries.derivative ℚ (f i)) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha,
      Finset.erase_insert ha, smul_eq_mul, smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hia : a ≠ i := fun h => ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne hia,
        Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring

private lemma derivative_det {d : ℕ} (A : Matrix (Fin d) (Fin d) (PowerSeries ℚ)) :
    PowerSeries.derivative ℚ A.det =
      (A.adjugate * A.map (PowerSeries.derivative ℚ)).trace := by
  rw [Matrix.det_apply, map_sum]
  have h1 :
      ∑ σ : Equiv.Perm (Fin d),
        PowerSeries.derivative ℚ (Equiv.Perm.sign σ • ∏ i : Fin d, A (σ i) i) =
      ∑ σ : Equiv.Perm (Fin d), ∑ i : Fin d,
        Equiv.Perm.sign σ •
          ((PowerSeries.derivative ℚ (A (σ i) i)) * ∏ j ∈ Finset.univ.erase i, A (σ j) j) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, map_zsmul, derivative_finset_prod, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Units.smul_def]
  rw [h1, Finset.sum_comm]
  rw [Matrix.trace]
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcol :
      ∑ σ : Equiv.Perm (Fin d),
        Equiv.Perm.sign σ •
          ((PowerSeries.derivative ℚ (A (σ i) i)) * ∏ j ∈ Finset.univ.erase i, A (σ j) j) =
      (A.updateCol i (fun r => PowerSeries.derivative ℚ (A r i))).det := by
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp [Matrix.updateCol_self]
    · refine Finset.prod_congr rfl fun j hj => ?_
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [Matrix.updateCol_ne hji]
  rw [hcol]
  have hvec : (fun r => PowerSeries.derivative ℚ (A r i)) =
      ∑ r : Fin d, (PowerSeries.derivative ℚ (A r i)) • Pi.single r (1 : PowerSeries ℚ) := by
    ext r
    simp [Finset.sum_apply, Pi.single_apply]
  have hlin : ∀ (s : Finset (Fin d)) (g : Fin d → PowerSeries ℚ),
      (A.updateCol i (∑ r ∈ s, g r • Pi.single r (1 : PowerSeries ℚ))).det =
        ∑ r ∈ s, g r * (A.updateCol i (Pi.single r (1 : PowerSeries ℚ))).det := by
    intro s g
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact Matrix.det_eq_zero_of_column_eq_zero i (fun r => by simp)
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Matrix.det_updateCol_add, Matrix.det_updateCol_smul, ih,
        Finset.sum_insert ha]
  rw [hvec, hlin]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mul_comm]
  congr 1
  rw [← Matrix.transpose_apply A.adjugate r i, Matrix.adjugate_transpose,
    Matrix.adjugate_apply, ← Matrix.det_transpose (A.updateCol i (Pi.single r 1))]
  congr 1
  ext a b
  by_cases ha : a = i <;> simp [ha]

private lemma charpolyRev_log_deriv {d : ℕ} (M : Matrix (Fin d) (Fin d) ℚ) :
    -(PowerSeries.derivative ℚ (M.charpolyRev : PowerSeries ℚ)) =
      (M.charpolyRev : PowerSeries ℚ) *
        PowerSeries.mk (fun m => ((M ^ (m + 1)).trace)) := by
  let A : Matrix (Fin d) (Fin d) (PowerSeries ℚ) :=
    1 - (PowerSeries.X : PowerSeries ℚ) • M.map PowerSeries.C
  let G : Matrix (Fin d) (Fin d) (PowerSeries ℚ) :=
    Matrix.of fun i j => PowerSeries.mk fun m => (M ^ m) i j
  have hAdet : A.det = (M.charpolyRev : PowerSeries ℚ) := by
    have hmap : A = (1 - (Polynomial.X : ℚ[X]) • M.map Polynomial.C).map
        (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) := by
      ext i j n
      by_cases hij : i = j
      · simp only [A, Matrix.sub_apply, Matrix.one_apply, hij, ↓reduceIte, Matrix.smul_apply,
          Matrix.map_apply, smul_eq_mul, map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
          Polynomial.coe_X, Polynomial.coe_C, PowerSeries.coeff_mul_C]
      · simp only [A, Matrix.sub_apply, Matrix.one_apply, hij, ↓reduceIte, Matrix.smul_apply,
          Matrix.map_apply, smul_eq_mul, map_sub, map_zero, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
          Polynomial.coe_X, Polynomial.coe_C, PowerSeries.coeff_mul_C]
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hAG : A * G = 1 := by
    ext i j m
    rw [Matrix.mul_apply, map_sum]
    cases m with
    | zero =>
      simp only [Matrix.one_apply, PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
      have h0 : ∀ k : Fin d,
          PowerSeries.constantCoeff (A i k) * PowerSeries.constantCoeff (G k j) =
            if i = k then (if k = j then 1 else 0) else 0 := by
        intro k
        have hA0 : PowerSeries.constantCoeff (A i k) = if i = k then 1 else 0 := by
          simp only [A, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
            smul_eq_mul, map_sub, map_mul, PowerSeries.constantCoeff_X, zero_mul, sub_zero]
          by_cases hik : i = k <;> simp [hik]
        have hG0 : PowerSeries.constantCoeff (G k j) = if k = j then 1 else 0 := by
          rw [← PowerSeries.coeff_zero_eq_constantCoeff]
          simp only [G, Matrix.of_apply, PowerSeries.coeff_mk, pow_zero, Matrix.one_apply]
        rw [hA0, hG0]
        by_cases hik : i = k <;> simp [hik]
      simp [h0]
    | succ m =>
      have h1 : PowerSeries.coeff (m + 1) ((1 : Matrix (Fin d) (Fin d) (PowerSeries ℚ)) i j) = 0 := by
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [h1]
      have hterm : ∀ k : Fin d,
          PowerSeries.coeff (m + 1) (A i k * G k j) =
            (if i = k then (M ^ (m + 1)) k j else 0) - M i k * (M ^ m) k j := by
        intro k
        have hAk : A i k = (if i = k then 1 else 0) - PowerSeries.X * PowerSeries.C (M i k) := by
          simp [A, Matrix.one_apply, smul_eq_mul]
        rw [hAk, sub_mul, map_sub]
        congr 1
        · by_cases hik : i = k <;> simp [G, hik]
        · rw [mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul]
          simp [G]
      simp_rw [hterm, Finset.sum_sub_distrib]
      have hleft : (∑ k : Fin d, if i = k then (M ^ (m + 1)) k j else 0) = (M ^ (m + 1)) i j := by
        simp
      have hright : (∑ k : Fin d, M i k * (M ^ m) k j) = (M ^ (m + 1)) i j := by
        rw [pow_succ', Matrix.mul_apply]
      rw [hleft, hright, sub_self]
  have hGA : G * A = 1 := matrix_mul_eq_one_comm hAG
  have hadj : A.adjugate = A.det • G := by
    have h1 := congrArg (fun X => G * X) (Matrix.mul_adjugate A)
    rw [← Matrix.mul_assoc, hGA, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at h1
    exact h1
  have hAderiv : A.map (PowerSeries.derivative ℚ) = -(M.map PowerSeries.C) := by
    ext i j
    have hAk : A i j = (if i = j then 1 else 0) - PowerSeries.X * PowerSeries.C (M i j) := by
      simp [A, Matrix.one_apply, smul_eq_mul]
    rw [Matrix.map_apply, hAk, map_sub, Derivation.leibniz, PowerSeries.derivative_X,
      PowerSeries.derivative_C, smul_eq_mul, smul_eq_mul, mul_zero, zero_add, mul_one]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  rw [← hAdet, derivative_det A, hadj, hAderiv, Matrix.smul_mul, Matrix.mul_neg,
    Matrix.trace_smul, Matrix.trace_neg, smul_neg, neg_neg, smul_eq_mul]
  congr 1
  apply PowerSeries.ext
  intro m
  rw [Matrix.trace, map_sum, PowerSeries.coeff_mk]
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, map_sum]
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, pow_succ, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [G, PowerSeries.coeff_mul_C]

private lemma derivative_finset_prod_charpolyRev {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (d : ι → ℕ) (Φ : (i : ι) → Matrix (Fin (d i)) (Fin (d i)) ℚ) :
    PowerSeries.derivative ℚ (∏ i ∈ s, ((Φ i).charpolyRev : PowerSeries ℚ)) =
      (∏ i ∈ s, ((Φ i).charpolyRev : PowerSeries ℚ)) *
        (-(∑ i ∈ s, PowerSeries.mk (fun m => (((Φ i) ^ (m + 1)).trace)))) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, smul_eq_mul, smul_eq_mul]
    have hda : PowerSeries.derivative ℚ (((Φ a).charpolyRev : PowerSeries ℚ)) =
        ((Φ a).charpolyRev : PowerSeries ℚ) *
          -(PowerSeries.mk (fun m => (((Φ a) ^ (m + 1)).trace))) := by
      have h := charpolyRev_log_deriv (Φ a)
      calc
        PowerSeries.derivative ℚ (((Φ a).charpolyRev : PowerSeries ℚ))
            = -(-(PowerSeries.derivative ℚ (((Φ a).charpolyRev : PowerSeries ℚ)))) := (neg_neg _).symm
        _ = -(((Φ a).charpolyRev : PowerSeries ℚ) *
              PowerSeries.mk (fun m => (((Φ a) ^ (m + 1)).trace))) := by rw [h]
        _ = ((Φ a).charpolyRev : PowerSeries ℚ) *
              -(PowerSeries.mk (fun m => (((Φ a) ^ (m + 1)).trace))) := (mul_neg _ _).symm
    rw [hda]
    ring

private lemma trace_formula_of_zeta_factorization (N : ℕ → ℕ) (n : ℕ) (d : ℕ → ℕ)
    (Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) ℚ)
    (hzeta : zetaOfCounts N *
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, (((Φ i).charpolyRev : ℚ[X]) : PowerSeries ℚ) =
      ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, (((Φ i).charpolyRev : ℚ[X]) : PowerSeries ℚ)) :
    ∀ m : ℕ, 0 < m → (N m : ℚ) =
      ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℚ) ^ i * ((Φ i) ^ m).trace := by
  let L : PowerSeries ℚ :=
    PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else (N m : ℚ) / (m : ℚ)
  let Z : PowerSeries ℚ := zetaOfCounts N
  let F : PowerSeries ℚ :=
    ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, (((Φ i).charpolyRev : ℚ[X]) : PowerSeries ℚ)
  let G : PowerSeries ℚ :=
    ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, (((Φ i).charpolyRev : ℚ[X]) : PowerSeries ℚ)
  have hL0 : PowerSeries.constantCoeff L = 0 := by
    simp [L]
  have hLsubst : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  have hZdef : Z = (PowerSeries.exp ℚ).subst L := rfl
  have hZderiv : PowerSeries.derivative ℚ Z = Z * PowerSeries.derivative ℚ L := by
    rw [hZdef, PowerSeries.derivative_subst hLsubst, PowerSeries.derivative_exp]
  have hFderiv : PowerSeries.derivative ℚ F =
      F * -(∑ i ∈ (Finset.range (2 * n + 1)).filter Even,
        PowerSeries.mk (fun m => (((Φ i) ^ (m + 1)).trace))) :=
    derivative_finset_prod_charpolyRev _ d Φ
  have hGderiv : PowerSeries.derivative ℚ G =
      G * -(∑ i ∈ (Finset.range (2 * n + 1)).filter Odd,
        PowerSeries.mk (fun m => (((Φ i) ^ (m + 1)).trace))) :=
    derivative_finset_prod_charpolyRev _ d Φ
  have hdiff := congrArg (PowerSeries.derivative ℚ) hzeta
  change PowerSeries.derivative ℚ (Z * F) = PowerSeries.derivative ℚ G at hdiff
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hZderiv, hFderiv, hGderiv] at hdiff
  change Z * F = G at hzeta
  rw [← hzeta] at hdiff
  have hfactor : (Z * F) *
      (PowerSeries.derivative ℚ L -
        ∑ i ∈ (Finset.range (2 * n + 1)).filter Even,
          PowerSeries.mk (fun m => (((Φ i) ^ (m + 1)).trace))) =
      (Z * F) *
        -(∑ i ∈ (Finset.range (2 * n + 1)).filter Odd,
          PowerSeries.mk (fun m => (((Φ i) ^ (m + 1)).trace))) := by
    linear_combination hdiff
  have hZF_unit : IsUnit (Z * F) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_mul]
    have hZ0 : PowerSeries.constantCoeff Z = 1 := by
      change MvPowerSeries.constantCoeff (PowerSeries.subst L (PowerSeries.exp ℚ)) = 1
      rw [PowerSeries.constantCoeff_subst hLsubst (PowerSeries.exp ℚ)]
      rw [finsum_eq_single _ 0]
      · simp [PowerSeries.coeff_exp]
      · intro k hk
        rw [map_pow, show MvPowerSeries.constantCoeff L = 0 from hL0, zero_pow hk, smul_zero]
    have hF0 : PowerSeries.constantCoeff F = 1 := by
      rw [map_prod]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe,
        Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    rw [hZ0, hF0, mul_one]
    exact isUnit_one
  have hcancel :
      PowerSeries.derivative ℚ L -
        ∑ i ∈ (Finset.range (2 * n + 1)).filter Even,
          PowerSeries.mk (fun m => (((Φ i) ^ (m + 1)).trace)) =
      -(∑ i ∈ (Finset.range (2 * n + 1)).filter Odd,
          PowerSeries.mk (fun m => (((Φ i) ^ (m + 1)).trace))) :=
    hZF_unit.mul_left_cancel hfactor
  intro m hm
  cases m with
  | zero => exact absurd hm (Nat.lt_irrefl 0)
  | succ m =>
    have hc := congrArg (PowerSeries.coeff m) hcancel
    simp only [map_sub, map_neg, map_sum, PowerSeries.coeff_derivative, PowerSeries.coeff_mk] at hc
    have hLcoeff : PowerSeries.coeff (m + 1) L * (m + 1 : ℚ) = (N (m + 1) : ℚ) := by
      simp only [L, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      have hm0 : ((m : ℚ) + 1) ≠ 0 := by positivity
      field_simp [hm0]
    rw [hLcoeff] at hc
    have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.range (2 * n + 1)) Even
      (fun i => (-1 : ℚ) ^ i * ((Φ i) ^ (m + 1)).trace)).symm
    rw [hsplit]
    have heven :
        ∑ i ∈ (Finset.range (2 * n + 1)).filter Even, (-1 : ℚ) ^ i * ((Φ i) ^ (m + 1)).trace =
          ∑ i ∈ (Finset.range (2 * n + 1)).filter Even, ((Φ i) ^ (m + 1)).trace := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiE : Even i := (Finset.mem_filter.mp hi).2
      rw [hiE.neg_one_pow, one_mul]
    have hodd_filter :
        (Finset.range (2 * n + 1)).filter (fun i => ¬Even i) =
          (Finset.range (2 * n + 1)).filter Odd := by
      ext i
      simp [Nat.not_even_iff_odd]
    have hodd :
        ∑ i ∈ (Finset.range (2 * n + 1)).filter (fun i => ¬Even i),
            (-1 : ℚ) ^ i * ((Φ i) ^ (m + 1)).trace =
          -(∑ i ∈ (Finset.range (2 * n + 1)).filter Odd, ((Φ i) ^ (m + 1)).trace) := by
      rw [hodd_filter, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiO : Odd i := (Finset.mem_filter.mp hi).2
      rw [hiO.neg_one_pow, neg_one_mul]
    rw [heven, hodd]
    linarith

end JacobiTraceFormula

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K) (d : ℕ → ℕ)
      (Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) K),
      (∀ m : ℕ, 0 < m → (pointCount p f m : K) =
        ∑ i ∈ Finset.range (2 * n + 1), (-1 : K) ^ i * ((Φ i) ^ m).trace) ∧
      (∀ i ≤ 2 * n, ∃ (G : Matrix (Fin (d i)) (Fin (d (2 * n - i))) K)
          (H : Matrix (Fin (d (2 * n - i))) (Fin (d i)) K),
          G * H = 1 ∧ H * G = 1 ∧
          (Φ i).transpose * G * Φ (2 * n - i) = (Nat.card k : K) ^ n • G) ∧
      (d 0 = 1 ∧ Φ 0 = 1) ∧
      (∀ i ≤ 2 * n, ∃ W : ℚ[X], W ≠ 0 ∧ (Φ i).charpoly ∣ W.map (algebraMap ℚ K) ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  obtain ⟨C, hmonic, hC0, hzeta, hPD, hweight⟩ :=
    WeilConjectures.exists_deligne_weil_charpolys p k n X f hproj
  let d : ℕ → ℕ := fun i => (C i).natDegree
  let Φ : (i : ℕ) → Matrix (Fin (d i)) (Fin (d i)) ℚ := fun i => companionMatrix (C i)
  have hchar : ∀ i ≤ 2 * n, (Φ i).charpoly = C i := fun i hi =>
    charpoly_companionMatrix (C i) (hmonic i hi).1
  have hrev : ∀ i ≤ 2 * n, (Φ i).charpolyRev = (C i).reverse := fun i hi => by
    rw [← Matrix.reverse_charpoly, hchar i hi]
  have hcard_pos : 0 < Nat.card k := Nat.card_pos
  have ha_ne : ((Nat.card k : ℚ) ^ n) ≠ 0 := by
    positivity
  refine ⟨ℚ, inferInstance, inferInstance, d, Φ, ?_, ?_, ?_, ?_⟩
  · have hzeta' : zetaOfCounts (pointCount p f) *
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, (((Φ i).charpolyRev : ℚ[X]) : PowerSeries ℚ) =
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, (((Φ i).charpolyRev : ℚ[X]) : PowerSeries ℚ) := by
      have hev :
          ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, (((Φ i).charpolyRev : ℚ[X]) : PowerSeries ℚ) =
          ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, (((C i).reverse : ℚ[X]) : PowerSeries ℚ) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hile : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
        rw [hrev i hile]
      have hodd :
          ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, (((Φ i).charpolyRev : ℚ[X]) : PowerSeries ℚ) =
          ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, (((C i).reverse : ℚ[X]) : PowerSeries ℚ) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hile : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
        rw [hrev i hile]
      rw [hev, hodd]
      exact hzeta
    exact trace_formula_of_zeta_factorization (pointCount p f) n d Φ hzeta'
  · intro i hi
    have hdual_le : 2 * n - i ≤ 2 * n := Nat.sub_le (2 * n) i
    exact poincare_duality_companion (C i) (C (2 * n - i))
      (hmonic i hi).1 (hmonic (2 * n - i) hdual_le).1
      (hmonic i hi).2 ((Nat.card k : ℚ) ^ n) ha_ne
      (hPD i hi).1 (hPD i hi).2
  · have hX1 : (Polynomial.X - 1 : ℚ[X]).natDegree = 1 := by
      simpa using (Polynomial.natDegree_X_sub_C (1 : ℚ))
    have h0deg : d 0 = 1 := by
      simp only [d, hC0, hX1]
    refine ⟨h0deg, ?_⟩
    ext i j
    have hi0 : i.val = 0 := by omega
    have hj0 : j.val = 0 := by omega
    have hij : i = j := Fin.ext (by omega)
    subst hij
    simp only [Φ, companionMatrix, companionMat, Matrix.of_apply, Matrix.one_apply, ↓reduceIte,
      hi0, zero_add, hC0, hX1, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
      Polynomial.coeff_one_zero, zero_sub, neg_neg]
  · intro i hi
    refine ⟨C i, (hmonic i hi).1.ne_zero, ?_, hweight i hi⟩
    rw [hchar i hi]
    change C i ∣ (C i).map (RingHom.id ℚ)
    rw [Polynomial.map_id]

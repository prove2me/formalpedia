-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P08.generated_and_central_projectors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:36:59.419957+00:00
-- url     : https://prove2.me/submissions/273ba673-c2f1-482f-b3d4-29c1d3886254

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Support21.P08
open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)
open Polynomial

section G67EL
variable {R : Type*} [CommRing R] {d : ℕ}

lemma g67e_diag_mul (A B : Matrix (Fin d) (Fin d) R) (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (a : Fin d) : (A * B) a a = A a a * B a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

lemma g67e_list_prod (l : List (Matrix (Fin d) (Fin d) R))
    (h : ∀ M ∈ l, M.BlockTriangular id) :
    l.prod.BlockTriangular id ∧ ∀ a, l.prod a a = (l.map (fun M => M a a)).prod := by
  induction l with
  | nil => exact ⟨Matrix.blockTriangular_one, fun a => by simp⟩
  | cons M l ih =>
    have hM := h M (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := ih (fun N hN => h N (List.mem_cons_of_mem _ hN))
    refine ⟨by rw [List.prod_cons]; exact hM.mul h1, fun a => ?_⟩
    rw [List.prod_cons, g67e_diag_mul _ _ hM h1, h2, List.map_cons, List.prod_cons]

lemma g67e_diag_pow (A : Matrix (Fin d) (Fin d) R) (hA : A.BlockTriangular id) (a : Fin d) :
    ∀ m : ℕ, (A ^ m) a a = (A a a) ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, g67e_diag_mul _ _ (hA.pow m) hA, ih, pow_succ]

/-- interval version: zero diagonal on [a,b] kills (Z^m)_{ab} for m > b - a -/
lemma g67e_pow_zero_interval (Z : Matrix (Fin d) (Fin d) R) (hZ : Z.BlockTriangular id) (b : Fin d) :
    ∀ m : ℕ, ∀ a : Fin d, (∀ k : Fin d, a ≤ k → k ≤ b → Z k k = 0) →
      b.val < a.val + m → (Z ^ m) a b = 0 := by
  intro m
  induction m with
  | zero =>
    intro a _ hab
    simp only [pow_zero]
    exact Matrix.one_apply_ne (by intro h; subst h; omega)
  | succ m ih =>
    intro a h0 hab
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_trichotomy k a with h | h | h
    · rw [hZ h, zero_mul]
    · subst h
      by_cases hk : k ≤ b
      · rw [h0 k le_rfl hk, zero_mul]
      · push Not at hk
        rw [ih k h0 (Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _)), mul_zero]
    · rw [ih k (fun k' h1 h2 => h0 k' (le_trans h.le h1) h2)
        (by have : a.val < k.val := h; omega), mul_zero]

lemma g67e_aeval_upper (Z : Matrix (Fin d) (Fin d) R) (hZ : Z.BlockTriangular id) (p : R[X]) :
    (aeval Z p).BlockTriangular id ∧ ∀ a, (aeval Z p) a a = p.eval (Z a a) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨by rw [map_add]; exact hp.1.add hq.1, fun a => ?_⟩
    rw [map_add, Matrix.add_apply, hp.2, hq.2, eval_add]
  | monomial n c =>
    rw [aeval_monomial]
    have h1 : (algebraMap R (Matrix (Fin d) (Fin d) R) c).BlockTriangular id :=
      Matrix.blockTriangular_algebraMap c
    refine ⟨h1.mul (hZ.pow n), fun a => ?_⟩
    rw [g67e_diag_mul _ _ h1 (hZ.pow n), g67e_diag_pow Z hZ a n, eval_monomial,
      Matrix.algebraMap_eq_diagonal]
    simp

lemma g67e_aeval_commute (P Y : Matrix (Fin d) (Fin d) R) (h : P * Y = Y * P) (p : R[X]) :
    P * aeval Y p = aeval Y p * P := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, mul_add, add_mul, hp, hq]
  | monomial n c =>
    rw [aeval_monomial]
    have hc : Commute P Y := h
    rw [← mul_assoc, ← Algebra.commutes, mul_assoc, (hc.pow_right n).eq, mul_assoc]

lemma g67e_shape_of_idem (e : Matrix (Fin d) (Fin d) R) (he : e * e = e) (hu : e.BlockTriangular id)
    (J : Finset (Fin d)) (hJ : J.Nonempty) (hdiag : ∀ a, e a a = if a ∈ J then 1 else 0) :
    HasShape e J := by
  refine ⟨hJ, fun a b hab => ?_, hdiag⟩
  by_contra hc
  push Not at hc
  have hpow : ∀ m, e ^ (m + 1) = e := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, he]
  have hd : 0 < d := by have := a.isLt; omega
  have := g67e_pow_zero_interval e hu b d a (fun k h1 h2 => by
    rw [hdiag k, if_neg]; intro hk; exact absurd h2 (not_le.mpr (hc k hk h1)))
    (by have := b.isLt; omega)
  have h2 : e ^ d = e := by
    have := hpow (d - 1); rwa [Nat.sub_add_cancel hd] at this
  rw [h2] at this
  exact hab this

end G67EL

section G67EL2
variable {R : Type*} [CommRing R] [IsLocalRing R] {d n : ℕ}

lemma g67e_linked_symm (S : TriangularSystem R d n) {i j : Fin d} (h : linked S i j) :
    linked S j i := fun k => (h k).symm

lemma g67e_linked_trans (S : TriangularSystem R d n) {i j l : Fin d} (h : linked S i j)
    (h' : linked S j l) : linked S i l := fun k => (h k).trans (h' k)

lemma g67e_mem_part (S : TriangularSystem R d n) {J : Finset (Fin d)}
    (hJ : J ∈ linkagePartition S) : ∃ i0, J = linkageClass S i0 := by
  unfold linkagePartition at hJ
  obtain ⟨i0, _, h⟩ := Finset.mem_image.mp hJ
  exact ⟨i0, h.symm⟩

lemma g67e_mem_class (S : TriangularSystem R d n) (i0 a : Fin d) :
    a ∈ linkageClass S i0 ↔ linked S i0 a := by
  simp [linkageClass]

lemma g67e_class_eq (S : TriangularSystem R d n) {J U : Finset (Fin d)}
    (hJ : J ∈ linkagePartition S) (hU : U ∈ linkagePartition S) (a : Fin d)
    (haJ : a ∈ J) (haU : a ∈ U) : J = U := by
  obtain ⟨i, rfl⟩ := g67e_mem_part S hJ
  obtain ⟨j, rfl⟩ := g67e_mem_part S hU
  rw [g67e_mem_class] at haJ haU
  ext x
  rw [g67e_mem_class, g67e_mem_class]
  constructor
  · intro h; exact g67e_linked_trans S haU (g67e_linked_trans S (g67e_linked_symm S haJ) h)
  · intro h; exact g67e_linked_trans S haJ (g67e_linked_trans S (g67e_linked_symm S haU) h)

lemma g67e_classY (S : TriangularSystem R d n) {J : Finset (Fin d)}
    (hJ : J ∈ linkagePartition S) :
    ∃ Y : Matrix (Fin d) (Fin d) R, Y.BlockTriangular id ∧ Y ∈ representedAlgebra S ∧
      (∀ a, a ∉ J → Y a a = 0) ∧ (∀ a ∈ J, IsUnit (Y a a)) := by
  obtain ⟨i0, rfl⟩ := g67e_mem_part S hJ
  have hk : ∀ j : {j : Fin d // j ∉ linkageClass S i0}, ∃ k : Fin n,
      IsLocalRing.residue R (triangularDiagonalEntry S k i0) ≠
        IsLocalRing.residue R (triangularDiagonalEntry S k j.1) := by
    intro ⟨j, hj⟩
    rw [g67e_mem_class] at hj
    unfold linked at hj; push Not at hj
    exact hj
  choose kf hkf using hk
  let fac : {j : Fin d // j ∉ linkageClass S i0} → Matrix (Fin d) (Fin d) R := fun j =>
    S.L (kf j) - algebraMap R (Matrix (Fin d) (Fin d) R) (triangularDiagonalEntry S (kf j) j.1)
  let lst := (Finset.univ : Finset {j : Fin d // j ∉ linkageClass S i0}).toList.map fac
  have hup : ∀ M ∈ lst, M.BlockTriangular id := by
    intro M hM
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hM
    intro a b hab
    have hab' : b < a := hab
    simp [fac, S.upper _ _ _ hab', Matrix.algebraMap_eq_diagonal,
      Matrix.diagonal_apply_ne _ (ne_of_lt hab').symm]
  obtain ⟨h1, h2⟩ := g67e_list_prod lst hup
  have hdf : ∀ j a, fac j a a = triangularDiagonalEntry S (kf j) a - triangularDiagonalEntry S (kf j) j.1 := by
    intro j a
    simp [fac, Matrix.algebraMap_eq_diagonal, triangularDiagonalEntry]
  refine ⟨lst.prod, h1, ?_, ?_, ?_⟩
  · apply Subalgebra.list_prod_mem
    intro M hM
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hM
    exact Subalgebra.sub_mem _ (Algebra.subset_adjoin ⟨kf j, rfl⟩) (Subalgebra.algebraMap_mem _ _)
  · intro a ha
    rw [h2, List.map_map]
    apply List.prod_eq_zero
    refine List.mem_map.mpr ⟨⟨a, ha⟩, by simp, ?_⟩
    simp only [Function.comp, hdf, sub_self]
  · intro a ha
    rw [h2, List.map_map]
    apply List.prod_isUnit
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    simp only [Function.comp, hdf]
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, sub_ne_zero]
    rw [g67e_mem_class] at ha
    rw [← (ha (kf j))]
    exact hkf j

end G67EL2

section G67EL3
variable {R : Type*} [CommRing R] {d n : ℕ}

lemma g67e_coprime (f : R[X]) (hu : IsUnit (f.coeff 0)) (m : ℕ) :
    ∃ p q : R[X], p * f + q * X ^ m = 1 := by
  obtain ⟨g, hg⟩ := X_dvd_sub_C (p := f)
  have hc : IsCoprime f X := by
    refine ⟨C (↑hu.unit⁻¹ : R), -(C (↑hu.unit⁻¹ : R) * g), ?_⟩
    have h1 : C (↑hu.unit⁻¹ : R) * C (f.coeff 0) = 1 := by
      rw [← C_mul, IsUnit.val_inv_mul, C_1]
    linear_combination (C (↑hu.unit⁻¹ : R)) * hg + h1
  exact hc.pow_right

lemma g67e_aeval_mem (S : TriangularSystem R d n) (Y : Matrix (Fin d) (Fin d) R)
    (hY : Y ∈ representedAlgebra S) (g : R[X]) : aeval Y g ∈ representedAlgebra S := by
  have := (aeval (⟨Y, hY⟩ : representedAlgebra S) g).2
  rwa [aeval_subalgebra_coe] at this

end G67EL3

section G67EL4
variable {R : Type*} [CommRing R] [IsLocalRing R] {d n : ℕ}

lemma g67e_step (S : TriangularSystem R d n) (P : Matrix (Fin d) (Fin d) R)
    (hPP : P * P = P) (hPu : P.BlockTriangular id) (hPa : P ∈ representedAlgebra S)
    (W : Finset (Fin d)) (hPd : ∀ a, P a a = if a ∈ W then 1 else 0)
    (J : Finset (Fin d)) (hJ : J ∈ linkagePartition S) (hJW : J ⊆ W) :
    ∃ e : Matrix (Fin d) (Fin d) R, e * e = e ∧ e.BlockTriangular id ∧
      e ∈ representedAlgebra S ∧ (∀ a, e a a = if a ∈ J then 1 else 0) ∧
      P * e = e ∧ e * P = e := by
  obtain ⟨Y0, hYu, hYa, hY0, hY1⟩ := g67e_classY S hJ
  set Y := P * Y0 * P with hYdef
  have hYu' : Y.BlockTriangular id := (hPu.mul hYu).mul hPu
  have hYmem : Y ∈ representedAlgebra S :=
    Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hPa hYa) hPa
  have hYd : ∀ a, Y a a = if a ∈ J then Y0 a a else 0 := by
    intro a
    rw [hYdef, g67e_diag_mul _ _ (hPu.mul hYu) hPu, g67e_diag_mul _ _ hPu hYu, hPd]
    by_cases ha : a ∈ J
    · simp [ha, hJW ha]
    · by_cases hw : a ∈ W <;> simp [ha, hw, hY0 a ha]
  have hPY : P * Y = Y := by simp only [hYdef, ← mul_assoc, hPP]
  have hYP : Y * P = Y := by simp only [hYdef, mul_assoc, hPP]
  set m := Jᶜ.card with hm
  set f : R[X] := ∏ a ∈ J, (X - C (Y a a)) with hfdef
  have hchar : Y.charpoly = f * X ^ m := by
    rw [Matrix.charpoly_of_isUpperTriangular Y hYu', ← Finset.prod_mul_prod_compl J]
    congr 1
    rw [Finset.prod_congr rfl (fun a ha => by
      rw [hYd, if_neg (Finset.mem_compl.mp ha), C_0, sub_zero]), Finset.prod_const]
  have hf0 : IsUnit (f.coeff 0) := by
    rw [coeff_zero_eq_eval_zero, hfdef, eval_prod]
    apply Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
    intro a ha
    simp only [eval_sub, eval_X, eval_C, zero_sub, IsUnit.neg_iff]
    rw [hYd, if_pos ha]; exact hY1 a ha
  obtain ⟨p, q, hpq⟩ := g67e_coprime f hf0 m
  set e0 := aeval Y (q * X ^ m) with he0def
  have he0' : 1 - e0 = aeval Y (p * f) := by
    have := congrArg (aeval Y) hpq
    rw [map_add, map_one] at this
    rw [← this, he0def, add_sub_cancel_right]
  have he0 : e0 * e0 = e0 := by
    have hz : e0 * (1 - e0) = 0 := by
      rw [he0', he0def, ← map_mul]
      have : q * X ^ m * (p * f) = (p * q) * Y.charpoly := by rw [hchar]; ring
      rw [this, map_mul, Matrix.aeval_self_charpoly, mul_zero]
    rw [mul_sub, mul_one, sub_eq_zero] at hz; exact hz.symm
  have hcomm : P * e0 = e0 * P := g67e_aeval_commute P Y (by rw [hPY, hYP]) _
  obtain ⟨he0u, he0d⟩ := g67e_aeval_upper Y hYu' (q * X ^ m)
  have hev : ∀ a ∈ J, (q * X ^ m).eval (Y a a) = 1 := by
    intro a ha
    have := congrArg (eval (Y a a)) hpq
    rw [eval_add, eval_mul, eval_one] at this
    have hfa : f.eval (Y a a) = 0 := by
      rw [hfdef, eval_prod]
      exact Finset.prod_eq_zero ha (by simp)
    rw [hfa, mul_zero, zero_add] at this
    exact this
  refine ⟨e0 * P, ?_, he0u.mul hPu, Subalgebra.mul_mem _ (g67e_aeval_mem S Y hYmem _) hPa,
    ?_, ?_, ?_⟩
  · calc e0 * P * (e0 * P) = e0 * (P * e0) * P := by simp only [mul_assoc]
      _ = e0 * e0 * (P * P) := by rw [hcomm]; simp only [mul_assoc]
      _ = e0 * P := by rw [he0, hPP]
  · intro a
    rw [g67e_diag_mul _ _ he0u hPu, he0d]
    by_cases ha : a ∈ J
    · rw [hev a ha, hPd, if_pos (hJW ha), if_pos ha, mul_one]
    · rw [if_neg ha]
      have hmpos : 0 < m := Finset.card_pos.mpr ⟨a, Finset.mem_compl.mpr ha⟩
      rw [hYd, if_neg ha, eval_mul, eval_pow, eval_X, zero_pow hmpos.ne', mul_zero, zero_mul]
  · rw [← mul_assoc, hcomm, mul_assoc, hPP]
  · rw [mul_assoc, hPP]

lemma g67e_inv (S : TriangularSystem R d n) (L : List (Finset (Fin d))) (hL : L.Nodup)
    (hcl : ∀ J ∈ L, J ∈ linkagePartition S) :
    ∃ (P : Matrix (Fin d) (Fin d) R) (e : Finset (Fin d) → Matrix (Fin d) (Fin d) R),
      P * P = P ∧ P.BlockTriangular id ∧ P ∈ representedAlgebra S ∧
      (∀ a, P a a = if (∀ U ∈ L, a ∉ U) then 1 else 0) ∧
      (∀ J ∈ L, e J * e J = e J ∧ (e J).BlockTriangular id ∧ e J ∈ representedAlgebra S ∧
        (∀ a, e J a a = if a ∈ J then 1 else 0) ∧ e J * P = 0 ∧ P * e J = 0) ∧
      (∀ J ∈ L, ∀ U ∈ L, J ≠ U → e J * e U = 0) ∧
      P + (L.map e).sum = 1 := by
  induction L with
  | nil =>
    refine ⟨1, fun _ => 0, by simp, Matrix.blockTriangular_one, Subalgebra.one_mem _,
      fun a => by simp, by simp, by simp, by simp⟩
  | cons J L ih =>
    rw [List.nodup_cons] at hL
    obtain ⟨hJL, hL⟩ := hL
    have hJp := hcl J (List.mem_cons_self ..)
    obtain ⟨P, e, hPP, hPu, hPa, hPd, hE, hOrth, hSum⟩ :=
      ih hL (fun U hU => hcl U (List.mem_cons_of_mem _ hU))
    let W := Finset.univ.filter (fun a => ∀ U ∈ L, a ∉ U)
    have hPd' : ∀ a, P a a = if a ∈ W then 1 else 0 := by
      intro a; rw [hPd]; simp [W]
    have hJW : J ⊆ W := by
      intro a ha
      simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
      intro U hU haU
      have := g67e_class_eq S hJp (hcl U (List.mem_cons_of_mem _ hU)) a ha haU
      subst this; exact hJL hU
    obtain ⟨eJ, hee, heu, hea, hed, hPe, heP⟩ := g67e_step S P hPP hPu hPa W hPd' J hJp hJW
    have hUJ : ∀ U ∈ L, U ≠ J := fun U hU h => hJL (h ▸ hU)
    -- products of eJ with old idempotents
    have hold1 : ∀ U ∈ L, e U * eJ = 0 := by
      intro U hU; rw [← hPe, ← mul_assoc, (hE U hU).2.2.2.2.1, zero_mul]
    have hold2 : ∀ U ∈ L, eJ * e U = 0 := by
      intro U hU; rw [← heP, mul_assoc, (hE U hU).2.2.2.2.2, mul_zero]
    refine ⟨P - eJ, fun U => if U = J then eJ else e U, ?_, hPu.sub heu,
      Subalgebra.sub_mem _ hPa hea, ?_, ?_, ?_, ?_⟩
    · rw [sub_mul, mul_sub, mul_sub, hPP, hPe, heP, hee]; abel
    · intro a
      rw [Matrix.sub_apply, hPd', hed]
      by_cases ha : a ∈ J
      · have hw := hJW ha
        rw [if_pos hw, if_pos ha, sub_self, if_neg]
        intro h; exact h J (List.mem_cons_self ..) ha
      · rw [if_neg ha, sub_zero]
        by_cases hw : a ∈ W
        · rw [if_pos hw, if_pos]
          intro U hU
          rcases List.mem_cons.mp hU with h | h
          · rw [h]; exact ha
          · simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hw
            exact hw U h
        · rw [if_neg hw, if_neg]
          intro h; apply hw
          simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun U hU => h U (List.mem_cons_of_mem _ hU)
    · intro U hU
      by_cases h : U = J
      · subst h
        simp only [if_true]
        refine ⟨hee, heu, hea, hed, ?_, ?_⟩
        · rw [mul_sub, heP, hee, sub_self]
        · rw [sub_mul, hPe, hee, sub_self]
      · simp only [if_neg h]
        have hU' : U ∈ L := (List.mem_cons.mp hU).resolve_left h
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hE U hU'
        refine ⟨h1, h2, h3, h4, ?_, ?_⟩
        · rw [mul_sub, h5, hold1 U hU', sub_self]
        · rw [sub_mul, h6, hold2 U hU', sub_self]
    · intro U hU V hV hUV
      by_cases h1 : U = J
      · have h2 : V ≠ J := fun h => hUV (h1.trans h.symm)
        have hV' : V ∈ L := (List.mem_cons.mp hV).resolve_left h2
        simp only [if_pos h1, if_neg h2]; exact hold2 V hV'
      · have hU' : U ∈ L := (List.mem_cons.mp hU).resolve_left h1
        by_cases h2 : V = J
        · simp only [if_neg h1, if_pos h2]; exact hold1 U hU'
        · have hV' : V ∈ L := (List.mem_cons.mp hV).resolve_left h2
          simp only [if_neg h1, if_neg h2]; exact hOrth U hU' V hV' hUV
    · rw [List.map_cons, List.sum_cons, if_pos rfl]
      have : L.map (fun U => if U = J then eJ else e U) = L.map e :=
        List.map_congr_left (fun U hU => if_neg (hUJ U hU))
      rw [this, ← hSum]; abel

end G67EL4

section AppendixDefinitions

variable {R : Type*} [CommRing R]

theorem g68n_link [IsDomain R] [IsLocalRing R] {d n : ℕ}
    (S : TriangularSystem R d n) :
    ∃ e : Finset (Fin d) → Matrix (Fin d) (Fin d) R, ClassProjectors S e := by
  obtain ⟨P, e, hPP, hPu, hPa, hPd, hE, hOrth, hSum⟩ :=
    g67e_inv S (linkagePartition S).toList (Finset.nodup_toList _)
      (fun J hJ => Finset.mem_toList.mp hJ)
  have hP0 : P = 0 := by
    have hdiag : ∀ a, P a a = 0 := by
      intro a
      rw [hPd, if_neg]
      intro h
      apply h (linkageClass S a)
      · rw [Finset.mem_toList]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
      · rw [g67e_mem_class]; intro k; rfl
    have hpow : ∀ m, P ^ (m + 1) = P := by
      intro m; induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, ih, hPP]
    ext a b
    have hd : 0 < d := by have := a.isLt; omega
    have h2 : P ^ d = P := by
      have := hpow (d - 1); rwa [Nat.sub_add_cancel hd] at this
    rw [← h2, Matrix.zero_apply]
    exact g67e_pow_zero_interval P hPu b d a (fun k _ _ => hdiag k) (by have := b.isLt; omega)
  rw [hP0, zero_add] at hSum
  refine ⟨e, ?_, ?_, ?_⟩
  · intro J hJ
    have hJ' : J ∈ (linkagePartition S).toList := Finset.mem_toList.mpr hJ
    obtain ⟨h1, h2, h3, h4, _, _⟩ := hE J hJ'
    refine ⟨g67e_shape_of_idem (e J) h1 h2 J ?_ h4, h3, h1⟩
    obtain ⟨i0, rfl⟩ := g67e_mem_part S hJ
    exact ⟨i0, by rw [g67e_mem_class]; intro k; rfl⟩
  · intro J hJ U hU hJU
    exact hOrth J (Finset.mem_toList.mpr hJ) U (Finset.mem_toList.mpr hU) hJU
  · rw [← Finset.sum_map_toList]; exact hSum

theorem solution [IsDomain R] [IsLocalRing R] :
    (∀ (d n : ℕ) (S : TriangularSystem R d n),
      ∃ e : Finset (Fin d) → Matrix (Fin d) (Fin d) R, ClassProjectors S e) ∧
    (∀ (A : Type*) [Ring A] [Algebra R A] (d n : ℕ)
      (b : Module.Basis (Fin d) R A) (L : Fin n → A)
      (hupper : ∀ k i j, j < i → regularMatrix b (L k) i j = 0),
      (∀ k, Central (L k)) →
      ∃ e : Finset (Fin d) → A,
        (∀ J ∈ linkagePartition (regularSystem b L hupper),
          e J ∈ Algebra.adjoin R (Set.range L) ∧ Central (e J) ∧ e J * e J = e J ∧
          HasShape (regularMatrix b (e J)) J) ∧
        (∀ J ∈ linkagePartition (regularSystem b L hupper),
          ∀ U ∈ linkagePartition (regularSystem b L hupper), J ≠ U → e J * e U = 0) ∧
        (∑ J ∈ linkagePartition (regularSystem b L hupper), e J = 1) ∧
        (IsField R → ∀ p : A, PrimitiveCentralIdempotent p →
          ∃! J : {J // J ∈ linkagePartition (regularSystem b L hupper)}, e J.val * p = p)) := by
  refine ⟨fun d n S => g68n_link S, ?_⟩
  intro A _ _ d n b L hupper hcent
  set S := regularSystem b L hupper with hS
  set φ := Algebra.leftMulMatrix b with hφ
  have hreg : ∀ x, regularMatrix b x = φ x := by
    intro x; ext i j; rw [hφ, Algebra.leftMulMatrix_eq_repr_mul]; rfl
  have hinj : Function.Injective φ := Algebra.leftMulMatrix_injective b
  obtain ⟨em, ⟨hshape, hOrth, hSum⟩⟩ := g68n_link S
  have hrep : representedAlgebra S = (Algebra.adjoin R (Set.range L)).map φ := by
    rw [AlgHom.map_adjoin, representedAlgebra, ← Set.range_comp]
    congr 1
    ext M
    simp only [Set.mem_range, Function.comp_apply, hS, regularSystem, hreg]
  have hpre : ∀ J ∈ linkagePartition S, ∃ y ∈ Algebra.adjoin R (Set.range L), φ y = em J := by
    intro J hJ
    have := (hshape J hJ).2.1
    rw [hrep] at this
    obtain ⟨y, hy, hy'⟩ := Subalgebra.mem_map.mp this
    exact ⟨y, hy, hy'⟩
  let e : Finset (Fin d) → A := fun J =>
    if h : ∃ y ∈ Algebra.adjoin R (Set.range L), φ y = em J then Classical.choose h else 0
  have he : ∀ J ∈ linkagePartition S, e J ∈ Algebra.adjoin R (Set.range L) ∧ φ (e J) = em J := by
    intro J hJ
    have h := hpre J hJ
    simp only [e, dif_pos h]
    exact Classical.choose_spec h
  have hcentral : ∀ y ∈ Algebra.adjoin R (Set.range L), Central y := by
    intro y hy
    have hle : Algebra.adjoin R (Set.range L) ≤ Subalgebra.center R A := by
      apply Algebra.adjoin_le
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_center_iff]
      intro g; exact (hcent k g).symm
    have := hle hy
    rw [Subalgebra.mem_center_iff] at this
    intro a; exact (this a).symm
  have hidem : ∀ J ∈ linkagePartition S, e J * e J = e J := by
    intro J hJ
    apply hinj
    rw [map_mul, (he J hJ).2]
    exact (hshape J hJ).2.2
  have horth : ∀ J ∈ linkagePartition S, ∀ U ∈ linkagePartition S, J ≠ U → e J * e U = 0 := by
    intro J hJ U hU hJU
    apply hinj
    rw [map_mul, (he J hJ).2, (he U hU).2, map_zero]
    exact hOrth J hJ U hU hJU
  have hsum1 : ∑ J ∈ linkagePartition S, e J = 1 := by
    apply hinj
    rw [map_sum, map_one, ← hSum]
    exact Finset.sum_congr rfl (fun J hJ => (he J hJ).2)
  refine ⟨e, fun J hJ => ⟨(he J hJ).1, hcentral _ (he J hJ).1, hidem J hJ, ?_⟩, horth, hsum1, ?_⟩
  · rw [hreg, (he J hJ).2]; exact (hshape J hJ).1
  · intro hfield p hp
    obtain ⟨hp0, hpp, hpc, hprim⟩ := hp
    -- each e J * p is a central idempotent
    have hcJ : ∀ J ∈ linkagePartition S, Central (e J * p) := by
      intro J hJ a
      rw [mul_assoc, hpc a, ← mul_assoc, hcentral _ (he J hJ).1 a, mul_assoc]
    have hiJ : ∀ J ∈ linkagePartition S, e J * p * (e J * p) = e J * p := by
      intro J hJ
      calc e J * p * (e J * p) = e J * (p * e J) * p := by noncomm_ring
        _ = e J * (e J * p) * p := by rw [hpc]
        _ = e J * p := by rw [← mul_assoc, hidem J hJ, mul_assoc, hpp]
    have hdich : ∀ J ∈ linkagePartition S, e J * p = 0 ∨ e J * p = p := by
      intro J hJ
      have hq : Central (p - e J * p) := by
        intro a; rw [sub_mul, mul_sub, hpc a, hcJ J hJ a]
      have hqq : (p - e J * p) * (p - e J * p) = p - e J * p := by
        have h1 : p * (e J * p) = e J * p := by rw [hpc, mul_assoc, hpp]
        have h2 : e J * p * p = e J * p := by rw [mul_assoc, hpp]
        calc (p - e J * p) * (p - e J * p) = p * p - p * (e J * p) - e J * p * p + e J * p * (e J * p) := by noncomm_ring
          _ = p - e J * p := by rw [hpp, h1, h2, hiJ J hJ]; abel
      have hpq : e J * p * (p - e J * p) = 0 := by
        rw [mul_sub, hiJ J hJ, mul_assoc, hpp, sub_self]
      have hqp : (p - e J * p) * (e J * p) = 0 := by
        rw [sub_mul, hiJ J hJ, hpc, mul_assoc, hpp, sub_self]
      rcases hprim (e J * p) (p - e J * p) (hcJ J hJ) hq (hiJ J hJ) hqq hpq hqp (by abel) with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h).symm
    have hex : ∃ J ∈ linkagePartition S, e J * p ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hp0
      rw [← one_mul p, ← hsum1, Finset.sum_mul]
      exact Finset.sum_eq_zero hcon
    obtain ⟨J, hJ, hJp⟩ := hex
    have hJp' : e J * p = p := (hdich J hJ).resolve_left hJp
    refine ⟨⟨J, hJ⟩, hJp', ?_⟩
    rintro ⟨U, hU⟩ hUp
    by_contra hne
    have hne' : U ≠ J := fun h => hne (Subtype.ext h)
    apply hp0
    calc p = e U * p := hUp.symm
      _ = e U * (e J * p) := by rw [hJp']
      _ = 0 := by rw [← mul_assoc, horth U hU J hJ hne', zero_mul]

end AppendixDefinitions

end

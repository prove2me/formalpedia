-- Prove2me | solution 1 for OPG37364.lps13Graph_regular14
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T14:10:18.274306+00:00
-- url     : https://prove2.me/submissions/5cd7397d-42aa-4aad-b8ce-29d615dffe60

import Definitions.Def_opg37364_lps13
import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option autoImplicit false
open scoped Quaternion

namespace OPG37364

theorem lps13Coords_injective : Function.Injective lps13Coords := by
  decide

theorem lps13Coords_bounds (a : Fin 14) (k : Fin 4) :
    -3 ≤ lps13Coords a k ∧ lps13Coords a k ≤ 3 := by
  revert a k
  decide

theorem lps13Coords_re_pos (a : Fin 14) : 0 < lps13Coords a 0 := by
  revert a
  decide

theorem lps13Coords_im_nonzero (a : Fin 14) :
    ∃ k : Fin 4, k ≠ 0 ∧ lps13Coords a k ≠ 0 := by
  revert a
  decide

theorem lps13ConjIndex_involutive : Function.Involutive lps13ConjIndex := by
  change ∀ a, lps13ConjIndex (lps13ConjIndex a) = a
  decide

theorem lps13Quaternion_conj (a : Fin 14) :
    lps13Quaternion (lps13ConjIndex a) = star (lps13Quaternion a) := by
  fin_cases a <;> rfl

theorem lps13Quaternion_injective : Function.Injective lps13Quaternion := by
  intro a b h
  apply lps13Coords_injective
  funext k
  fin_cases k
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h
  · exact congrArg QuaternionAlgebra.imJ h
  · exact congrArg QuaternionAlgebra.imK h

theorem lps13Root_nonempty {q : ℕ} [Fact q.Prime] (h4 : q % 4 = 1) :
    Nonempty (LPS13Root q) := by
  obtain ⟨i, hi⟩ := (isSquare_iff_exists_sq (-1 : ZMod q)).mp
    (ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : q % 4 ≠ 3))
  exact ⟨⟨i, hi.symm⟩⟩

section FiniteField

variable {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)

include hq in
private theorem small_intCast_inj {x y : ℤ}
    (hx : -3 ≤ x ∧ x ≤ 3) (hy : -3 ≤ y ∧ y ≤ 3)
    (h : (x : ZMod q) = y) : x = y := by
  have hq' : (13 : ℤ) < q := by exact_mod_cast hq
  have he : x + 3 = y + 3 :=
    CharP.intCast_injOn_Ico (ZMod q) q
      (by constructor <;> omega) (by constructor <;> omega)
      (by push_cast; rw [h])
  omega

include hq in
private theorem two_ne_zero : (2 : ZMod q) ≠ 0 := by
  simpa using (ZMod.natCast_eq_zero_iff 2 q).not.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))

private theorem root_ne_zero : i.val ≠ 0 := by
  intro h
  have hi := i.property
  rw [h] at hi
  simp at hi

include hq in
private theorem matrix_coordinates (a b : Quaternion ℤ) (r : ZMod q)
    (h : lps13QuaternionMatrix i.val a = r • lps13QuaternionMatrix i.val b) :
    (a.re : ZMod q) = r * b.re ∧ (a.imI : ZMod q) = r * b.imI ∧
    (a.imJ : ZMod q) = r * b.imJ ∧ (a.imK : ZMod q) = r * b.imK := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 0 0) h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 1 1) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 0 1) h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 1 0) h
  simp [lps13QuaternionMatrix, Matrix.smul_apply, smul_eq_mul] at h00 h11 h01 h10
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply mul_left_cancel₀ (two_ne_zero hq)
    linear_combination h00 + h11
  · apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero hq) (root_ne_zero i))
    linear_combination h00 - h11
  · apply mul_left_cancel₀ (two_ne_zero hq)
    linear_combination h01 - h10
  · apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero hq) (root_ne_zero i))
    linear_combination h01 + h10

include hq in
private theorem indexed_matrix_coordinates (a b : Fin 14) (r : ZMod q)
    (h : lps13Matrix i a = r • lps13Matrix i b) :
    ∀ k : Fin 4, (lps13Coords a k : ZMod q) = r * lps13Coords b k := by
  obtain ⟨h0, h1, h2, h3⟩ := matrix_coordinates hq i (lps13Quaternion a)
    (lps13Quaternion b) r h
  intro k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem lps13Matrix_det (a : Fin 14) : (lps13Matrix i a).det = 13 := by
  simp [lps13Matrix, lps13QuaternionMatrix_det, lps13Quaternion_norm]

private theorem projective_scalar (a b : Fin 14)
    (h : lps13Generator hq i a = lps13Generator hq i b) :
    ∃ r : (ZMod q)ˣ, lps13Matrix i b = (r : ZMod q) • lps13Matrix i a := by
  obtain ⟨r, hr⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  refine ⟨r, ?_⟩
  have hm := congrArg Units.val hr
  ext j k
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M j k) hm
  simpa [lps13GL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul, mul_comm] using he.symm

theorem lps13Generator_injective : Function.Injective (lps13Generator hq i) := by
  intro a b hab
  obtain ⟨r, hr⟩ := projective_scalar hq i a b hab
  have hd := congrArg Matrix.det hr
  rw [Matrix.det_smul, lps13Matrix_det, lps13Matrix_det] at hd
  have h13 : (13 : ZMod q) ≠ 0 := by
    simpa using (ZMod.natCast_eq_zero_iff 13 q).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) hq)
  have hs : (r : ZMod q) ^ 2 = 1 := by
    apply mul_right_cancel₀ h13
    simpa using hd.symm
  obtain hr1 | hrn := sq_eq_one_iff.mp hs
  · apply lps13Coords_injective
    funext k
    have hk := indexed_matrix_coordinates hq i b a r hr k
    rw [hr1, one_mul] at hk
    exact (small_intCast_inj hq (lps13Coords_bounds b k) (lps13Coords_bounds a k) hk).symm
  · have hk := indexed_matrix_coordinates hq i b a r hr 0
    rw [hrn, neg_one_mul] at hk
    have he : lps13Coords b 0 = -lps13Coords a 0 :=
      small_intCast_inj hq (lps13Coords_bounds b 0)
        (by have hb := lps13Coords_bounds a 0; constructor <;> omega)
        (by simpa using hk)
    have ha := lps13Coords_re_pos a
    have hb := lps13Coords_re_pos b
    omega

theorem lps13Generator_ne_one (a : Fin 14) : lps13Generator hq i a ≠ 1 := by
  intro h
  have h' : Matrix.ProjGenLinGroup.mk (lps13GL hq i a) =
      Matrix.ProjGenLinGroup.mk (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) := h
  obtain ⟨r, hr⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h'.symm
  have hm : lps13Matrix i a = (r : ZMod q) • lps13QuaternionMatrix i.val (1 : Quaternion ℤ) := by
    have he := congrArg Units.val hr
    ext j k
    have he' := (congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M j k) he).symm
    fin_cases j <;> fin_cases k <;>
      simpa [lps13GL, lps13QuaternionMatrix, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar, Matrix.diagonal] using he'
  obtain ⟨_, h1, h2, h3⟩ := matrix_coordinates hq i (lps13Quaternion a) 1 r hm
  have him : ∀ k : Fin 4, k ≠ 0 → (lps13Coords a k : ZMod q) = 0 := by
    intro k hk
    fin_cases k
    · exact (hk rfl).elim
    · simpa [lps13Quaternion] using h1
    · simpa [lps13Quaternion] using h2
    · simpa [lps13Quaternion] using h3
  obtain ⟨k, hk, hn⟩ := lps13Coords_im_nonzero a
  exact hn (small_intCast_inj hq (lps13Coords_bounds a k) (by norm_num)
    (by simpa using him k hk))

private theorem quaternionMatrix_mul_star (a : Quaternion ℤ) :
    lps13QuaternionMatrix i.val a * lps13QuaternionMatrix i.val (star a) =
      (((Quaternion.normSq a : ℤ) : ZMod q)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [lps13QuaternionMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Quaternion.normSq_def'] <;>
    first | ring1 | linear_combination -(a.imI : ZMod q)^2 * i.property -
      (a.imK : ZMod q)^2 * i.property

theorem lps13Matrix_mul_conj (a : Fin 14) :
    lps13Matrix i a * lps13Matrix i (lps13ConjIndex a) =
      (13 : ZMod q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  simpa [lps13Matrix, lps13Quaternion_conj, lps13Quaternion_norm] using
    quaternionMatrix_mul_star i (lps13Quaternion a)

theorem lps13Generator_conj (a : Fin 14) :
    lps13Generator hq i (lps13ConjIndex a) = (lps13Generator hq i a)⁻¹ := by
  have h13 : (13 : ZMod q) ≠ 0 := by
    simpa using (ZMod.natCast_eq_zero_iff 13 q).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) hq)
  have hgl : lps13GL hq i a * lps13GL hq i (lps13ConjIndex a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 13 h13) := by
    apply Units.ext
    have hm := lps13Matrix_mul_conj i a
    simp only [Units.val_mul, lps13GL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    rw [hm]
    ext j k
    by_cases hjk : j = k <;> simp [Matrix.scalar, Matrix.diagonal, hjk]
  apply eq_inv_of_mul_eq_one_right
  change Matrix.ProjGenLinGroup.mk (lps13GL hq i a) *
    Matrix.ProjGenLinGroup.mk (lps13GL hq i (lps13ConjIndex a)) = 1
  rw [← map_mul, hgl, Matrix.ProjGenLinGroup.mk_scalar]

theorem lps13Generators_card : (lps13Generators hq i).card = 14 := by
  classical
  rw [lps13Generators, Finset.card_image_of_injective _ (lps13Generator_injective hq i)]
  simp

theorem one_not_mem_lps13Generators : 1 ∉ lps13Generators hq i := by
  classical
  simp only [lps13Generators, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  exact lps13Generator_ne_one hq i

theorem lps13Generators_inv_mem {s : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)}
    (hs : s ∈ lps13Generators hq i) : s⁻¹ ∈ lps13Generators hq i := by
  classical
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
  exact Finset.mem_image.mpr ⟨lps13ConjIndex a, Finset.mem_univ _, lps13Generator_conj hq i a⟩

/-- Neighbors are exactly the right translates by the fourteen projective generators. -/
theorem lps13Graph_neighborSet (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :
    (lps13Graph hq i).neighborSet v = (v * ·) '' (lps13Generators hq i : Set _) := by
  classical
  ext w
  rw [SimpleGraph.mem_neighborSet, lps13Graph, SimpleGraph.mulCayley_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact ⟨v⁻¹ * w, h, by simp⟩
    · refine ⟨(w⁻¹ * v)⁻¹, lps13Generators_inv_mem hq i h, ?_⟩
      simp
  · rintro ⟨s, hs, rfl⟩
    refine ⟨?_, Or.inl (by simpa using hs)⟩
    intro he
    have hs1 : s = 1 := by
      apply mul_left_cancel (a := v)
      simpa using he.symm
    exact one_not_mem_lps13Generators hq i (hs1 ▸ hs)

/-- The fixed-13 PGL Cayley graph is 14-regular in the original OPG encard predicate. -/
theorem _root_.solution : IsRegularOfDegree (lps13Graph hq i) 14 := by
  intro v
  rw [lps13Graph_neighborSet, (mul_right_injective v).encard_image,
    Set.encard_coe_eq_coe_finsetCard, lps13Generators_card]

theorem lps13Graph_finite_vertices : Finite (Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

theorem lps13Graph_loopless (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :
    ¬ (lps13Graph hq i).Adj v v := SimpleGraph.irrefl _

end FiniteField

end OPG37364

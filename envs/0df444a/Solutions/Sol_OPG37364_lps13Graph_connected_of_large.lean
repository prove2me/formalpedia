-- Prove2me | solution 1 for OPG37364.lps13Graph_connected_of_large
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T14:11:41.025232+00:00
-- url     : https://prove2.me/submissions/9b379f02-4513-41b4-9736-0729dd537e7c

/- Coarse-threshold connectedness of the existing LPS13 graph. Reuses the completed prime-field subgroup theorem (whose uploaded proof preserves Qiuzhen-CFSG/CFSG commit 96b2a02085dc678f3e0a97b334c31ada599c55fd, Apache-2.0). All local word, determinant and closure proof bodies are replayed below. No spectral or connectedness assumption is imported. -/
import Definitions.Def_opg37364_lps13
import Definitions.Def_opg37364_lps13_eigenspaces
import Definitions.Def_opg37364_lps13_words
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Induction
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Theorems.Thm_OPG37364_psl2_prime_large_proper_subgroup_double_commutator_eq_one

set_option autoImplicit false

open _root_.OPG37364
namespace Closure14Pack

noncomputable section Closure14Source0
-- Source: OPG37364.LPS13Graph
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
theorem lps13Graph_regular14 : IsRegularOfDegree (lps13Graph hq i) 14 := by
  intro v
  rw [lps13Graph_neighborSet, (mul_right_injective v).encard_image,
    Set.encard_coe_eq_coe_finsetCard, lps13Generators_card]

theorem lps13Graph_finite_vertices : Finite (Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

theorem lps13Graph_loopless (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :
    ¬ (lps13Graph hq i).Adj v v := SimpleGraph.irrefl _

end FiniteField

end OPG37364


end Closure14Source0

noncomputable section Closure14Source1
-- Source: Theorems.Thm_OPG37364_lps13_reduced_word_not_all_coords_dvd13
set_option autoImplicit false

namespace OPG37364
namespace WordPrimitivity

abbrev F := ZMod 13
abbrev Mat := Matrix (Fin 2) (Fin 2) F
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- Auxiliary full matrix ring at the fixed modulus 13; no GL/PGL construction. -/
def theta (x : Quaternion ℤ) : Mat := lps13QuaternionMatrix (q := 13) 5 x

theorem five_sq : (5 : F) ^ 2 = -1 := by decide

theorem theta_one : theta 1 = 1 := by
  ext j k
  fin_cases j <;> fin_cases k <;> decide

theorem theta_mul (x y : Quaternion ℤ) : theta (x * y) = theta x * theta y := by
  have h25 : (25 : F) = -1 := by decide
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [theta, lps13QuaternionMatrix, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> rw [h25] <;> ring

theorem theta_zero_of_dvd (x : Quaternion ℤ)
    (h : (13 : ℤ) ∣ x.re ∧ 13 ∣ x.imI ∧ 13 ∣ x.imJ ∧ 13 ∣ x.imK) : theta x = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have h0' := (ZMod.intCast_zmod_eq_zero_iff_dvd x.re 13).mpr h0
  have h1' := (ZMod.intCast_zmod_eq_zero_iff_dvd x.imI 13).mpr h1
  have h2' := (ZMod.intCast_zmod_eq_zero_iff_dvd x.imJ 13).mpr h2
  have h3' := (ZMod.intCast_zmod_eq_zero_iff_dvd x.imK 13).mpr h3
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [theta, lps13QuaternionMatrix, h0', h1', h2', h3']

def U : Fin 14 → Fin 2 → F :=
  ![![11,8], ![11,1], ![11,12], ![11,5],
    ![4,8], ![4,1], ![4,12], ![4,5],
    ![0,6], ![6,0], ![3,11], ![3,2], ![3,10], ![3,3]]

def V : Fin 14 → Fin 2 → F :=
  ![![1,7], ![1,4], ![1,9], ![1,6],
    ![1,3], ![1,11], ![1,2], ![1,10],
    ![0,1], ![1,0], ![1,5], ![1,8], ![1,12], ![1,1]]

def outer (u v : Fin 2 → F) : Mat := fun j k => u j * v k
def pairing (a b : Fin 14) : F := (V a 0 * U b 0) + (V a 1 * U b 1)

theorem factors_nonzero : ∀ a : Fin 14, U a ≠ 0 ∧ V a ≠ 0 := by decide

theorem generator_factor : ∀ a : Fin 14,
    theta (lps13Quaternion a) = outer (U a) (V a) := by decide

theorem pairing_zero_iff : ∀ a b : Fin 14,
    pairing a b = 0 ↔ b = lps13ConjIndex a := by decide

theorem outer_mul (u v u' v' : Fin 2 → F) :
    outer u v * outer u' v' = (v 0 * u' 0 + v 1 * u' 1) • outer u v' := by
  ext j k
  simp [outer, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  ring

theorem smul_outer_ne_zero {t : F} (ht : t ≠ 0) {u v : Fin 2 → F}
    (hu : u ≠ 0) (hv : v ≠ 0) : t • outer u v ≠ 0 := by
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  intro h
  have he := congrArg (fun M : Mat => M j k) h
  exact (mul_ne_zero ht (mul_ne_zero hj hk)) (by simpa [outer, smul_eq_mul] using he)

/-- Symbolic invariant for every length: first/last outer factors and nonzero coefficient. -/
theorem word_factor (a : Fin 14) (w : List (Fin 14)) (h : lps13WordReduced (a :: w)) :
    ∃ (z : Fin 14) (t : F), (a :: w).getLast? = some z ∧ t ≠ 0 ∧
      theta (lps13WordProduct (a :: w)) = t • outer (U a) (V z) := by
  induction w generalizing a with
  | nil =>
    refine ⟨a, 1, by simp, (one_ne_zero : (1 : F) ≠ 0), ?_⟩
    simpa [lps13WordProduct] using generator_factor a
  | cons b w ih =>
    obtain ⟨hab, hw⟩ := h
    obtain ⟨z, t, hz, ht, he⟩ := ih b hw
    have hc : pairing a b ≠ 0 := (pairing_zero_iff a b).not.mpr hab
    refine ⟨z, t * pairing a b, ?_, mul_ne_zero ht hc, ?_⟩
    · simpa using hz
    · calc
        theta (lps13WordProduct (a :: b :: w)) =
            theta (lps13Quaternion a) * theta (lps13WordProduct (b :: w)) := by
          simp only [lps13WordProduct, List.map_cons, List.prod_cons, theta_mul]
        _ = outer (U a) (V a) * (t • outer (U b) (V z)) := by rw [generator_factor, he]
        _ = (t * pairing a b) • outer (U a) (V z) := by
          rw [Matrix.mul_smul, outer_mul, smul_smul]
          rfl

theorem theta_word_ne_zero (w : List (Fin 14)) (h : lps13WordReduced w) :
    theta (lps13WordProduct w) ≠ 0 := by
  cases w with
  | nil => simpa [lps13WordProduct, theta_one] using (one_ne_zero : (1 : Mat) ≠ 0)
  | cons a w =>
    obtain ⟨z, t, _, ht, he⟩ := word_factor a w h
    rw [he]
    exact smul_outer_ne_zero ht (factors_nonzero a).1 (factors_nonzero z).2

end WordPrimitivity

/-- Every reduced word is 13-primitive: its four coordinates are not all divisible by 13. -/
theorem lps13_reduced_word_not_all_coords_dvd13
    (w : List (Fin 14)) (h : lps13WordReduced w) :
    ¬ ((13 : ℤ) ∣ (lps13WordProduct w).re ∧
      13 ∣ (lps13WordProduct w).imI ∧ 13 ∣ (lps13WordProduct w).imJ ∧
      13 ∣ (lps13WordProduct w).imK) := by
  intro hd
  exact WordPrimitivity.theta_word_ne_zero w h (WordPrimitivity.theta_zero_of_dvd _ hd)

end OPG37364


end Closure14Source1

noncomputable section Closure14Source2
-- Source: OPG37364.LPS13ScaledWordInjectivity
set_option autoImplicit false

namespace OPG37364
namespace ScaledWordInjectivity

-- These two structural identities are reused from Stage 7, LPS13Graph.lean.
theorem conj_involutive : Function.Involutive lps13ConjIndex := by
  change ∀ a, lps13ConjIndex (lps13ConjIndex a) = a
  decide

theorem quaternion_conj (a : Fin 14) :
    lps13Quaternion (lps13ConjIndex a) = star (lps13Quaternion a) := by
  fin_cases a <;> rfl

theorem generator_mul_conj (a : Fin 14) :
    lps13Quaternion a * lps13Quaternion (lps13ConjIndex a) =
      (13 : ℤ) • (1 : Quaternion ℤ) := by
  rw [quaternion_conj, Quaternion.self_mul_star, lps13Quaternion_norm]
  rfl

-- The norm induction is reused from Stage 11, LPS13WordPrimitivity.lean.
theorem word_norm (w : List (Fin 14)) :
    Quaternion.normSq (lps13WordProduct w) = (13 : ℤ) ^ w.length := by
  induction w with
  | nil => simp [lps13WordProduct]
  | cons a w ih =>
    simpa [lps13WordProduct, map_mul, lps13Quaternion_norm, pow_succ, mul_comm] using
      congrArg (fun z : ℤ => 13 * z) ih

-- This interface to List.IsChain is reused from Stage 12, LPS13CycleWords.lean.
theorem reduced_iff_chain (w : List (Fin 14)) :
    lps13WordReduced w ↔ w.IsChain (fun a b => b ≠ lps13ConjIndex a) := by
  induction w with
  | nil => simp [lps13WordReduced]
  | cons a w ih =>
    cases w with
    | nil => simp [lps13WordReduced]
    | cons b w =>
      simpa only [lps13WordReduced, List.isChain_cons_cons] using and_congr Iff.rfl ih

theorem product_append (u v : List (Fin 14)) :
    lps13WordProduct (u ++ v) = lps13WordProduct u * lps13WordProduct v := by
  simp [lps13WordProduct]

theorem product_snoc (u : List (Fin 14)) (a : Fin 14) :
    lps13WordProduct (u ++ [a]) = lps13WordProduct u * lps13Quaternion a := by
  simp [lps13WordProduct]

theorem scalar_cancel {c : ℤ} (hc : c ≠ 0) {x y : Quaternion ℤ}
    (h : c • x = c • y) : x = y := by
  apply Quaternion.ext
  · exact mul_left_cancel₀ hc (congrArg (fun z : Quaternion ℤ => z.re) h)
  · exact mul_left_cancel₀ hc (congrArg (fun z : Quaternion ℤ => z.imI) h)
  · exact mul_left_cancel₀ hc (congrArg (fun z : Quaternion ℤ => z.imJ) h)
  · exact mul_left_cancel₀ hc (congrArg (fun z : Quaternion ℤ => z.imK) h)

theorem primitive_not_thirteen_smul (w : List (Fin 14)) (hw : lps13WordReduced w)
    (x : Quaternion ℤ) : lps13WordProduct w ≠ (13 : ℤ) • x := by
  intro h
  apply lps13_reduced_word_not_all_coords_dvd13 w hw
  rw [h]
  exact ⟨⟨x.re, rfl⟩, ⟨x.imI, rfl⟩, ⟨x.imJ, rfl⟩, ⟨x.imK, rfl⟩⟩

theorem product_snoc_mul_conj (u : List (Fin 14)) (a : Fin 14) :
    lps13WordProduct (u ++ [a]) * lps13Quaternion (lps13ConjIndex a) =
      (13 : ℤ) • lps13WordProduct u := by
  rw [product_snoc, mul_assoc, generator_mul_conj, mul_smul_comm, mul_one]

theorem reduced_prefix (u : List (Fin 14)) (a : Fin 14)
    (h : lps13WordReduced (u ++ [a])) : lps13WordReduced u :=
  (reduced_iff_chain u).2 ((reduced_iff_chain _).1 h).left_of_append

theorem reduced_extend (v : List (Fin 14)) (a b : Fin 14)
    (hv : lps13WordReduced (v ++ [b])) (hab : a ≠ b) :
    lps13WordReduced ((v ++ [b]) ++ [lps13ConjIndex a]) := by
  apply (reduced_iff_chain _).2
  apply ((reduced_iff_chain _).1 hv).append (by simp)
  simpa using fun (h : lps13ConjIndex a = lps13ConjIndex b) =>
    hab (conj_involutive.injective h)

theorem product_injective_of_length (u v : List (Fin 14))
    (hu : lps13WordReduced u) (hv : lps13WordReduced v)
    (hlen : u.length = v.length) (hprod : lps13WordProduct u = lps13WordProduct v) :
    u = v := by
  induction u using List.reverseRecOn generalizing v with
  | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | append_singleton u a ih =>
    have hvne : v ≠ [] := by intro h; simp [h] at hlen
    obtain ⟨v, b, rfl⟩ : ∃ t b, v = t ++ [b] :=
      ⟨v.dropLast, v.getLast hvne, (List.dropLast_concat_getLast hvne).symm⟩
    have hab : a = b := by
      by_contra hab
      apply primitive_not_thirteen_smul _ (reduced_extend v a b hv hab) (lps13WordProduct u)
      rw [product_snoc, ← hprod, product_snoc_mul_conj]
    subst b
    have hpref : lps13WordProduct u = lps13WordProduct v := by
      apply scalar_cancel (by norm_num : (13 : ℤ) ≠ 0)
      simpa only [product_snoc_mul_conj] using
        congrArg (fun x => x * lps13Quaternion (lps13ConjIndex a)) hprod
    have huv := ih v (reduced_prefix u a hu) (reduced_prefix v a hv)
      (by simpa using hlen) hpref
    rw [huv]

theorem exponent_not_lt (r s : ℕ) (u v : List (Fin 14))
    (hu : lps13WordReduced u)
    (h : (13 : ℤ)^r • lps13WordProduct u = (13 : ℤ)^s • lps13WordProduct v) :
    ¬ r < s := by
  intro hrs
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hrs)
  have hs : s = r + (d + 1) := by omega
  have he : lps13WordProduct u = (13 : ℤ) • ((13 : ℤ)^d • lps13WordProduct v) := by
    apply scalar_cancel (pow_ne_zero r (by norm_num : (13 : ℤ) ≠ 0))
    simpa only [hs, pow_add, pow_succ', mul_smul] using h
  exact primitive_not_thirteen_smul u hu _ he

end ScaledWordInjectivity

/-- Literal integral quaternion equality determines both the power of 13 and the reduced word. -/
theorem lps13_scaled_reduced_word_product_injective
    (r s : ℕ) (u v : List (Fin 14))
    (hu : lps13WordReduced u) (hv : lps13WordReduced v)
    (h : (13 : ℤ)^r • lps13WordProduct u = (13 : ℤ)^s • lps13WordProduct v) :
    r = s ∧ u = v := by
  have hrs : r = s := by
    have h₁ := ScaledWordInjectivity.exponent_not_lt r s u v hu h
    have h₂ := ScaledWordInjectivity.exponent_not_lt s r v u hv h.symm
    omega
  subst s
  have hp := ScaledWordInjectivity.scalar_cancel
    (pow_ne_zero r (by norm_num : (13 : ℤ) ≠ 0)) h
  have hn := congrArg Quaternion.normSq hp
  rw [ScaledWordInjectivity.word_norm, ScaledWordInjectivity.word_norm] at hn
  have hl := (pow_right_strictMono₀ (by norm_num : (1 : ℤ) < 13)).injective hn
  exact ⟨rfl, ScaledWordInjectivity.product_injective_of_length u v hu hv hl hp⟩

end OPG37364


end Closure14Source2

noncomputable section Closure14Source3
-- Source: OPG37364.LPS13CycleWords
set_option autoImplicit false

namespace OPG37364
namespace Girth13

theorem reduced_iff_chain (w : List (Fin 14)) :
    lps13WordReduced w ↔ w.IsChain (fun a b => b ≠ lps13ConjIndex a) := by
  induction w with
  | nil => simp [lps13WordReduced]
  | cons a w ih =>
    cases w with
    | nil => simp [lps13WordReduced]
    | cons b w => simpa only [lps13WordReduced, List.isChain_cons_cons] using and_congr Iff.rfl ih

variable {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
local notation "PGL" => Matrix.ProjGenLinGroup (Fin 2) (ZMod q)

theorem edge_label {u v : PGL} (h : (lps13Graph hq i).Adj u v) :
    ∃ a : Fin 14, v = u * lps13Generator hq i a := by
  classical
  rw [lps13Graph, SimpleGraph.mulCayley_adj] at h
  obtain ⟨_, h | h⟩ := h
  · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    exact ⟨a, by rw [ha]; simp⟩
  · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    exact ⟨lps13ConjIndex a, by rw [lps13Generator_conj, ha]; simp⟩

theorem telescope (v : ℕ → PGL) (a : ℕ → Fin 14) (m : ℕ)
    (he : ∀ j < m, v (j+1) = v j * lps13Generator hq i (a j)) :
    v 0 * (((List.range m).map a).map (lps13Generator hq i)).prod = v m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.prod_append]
    simp only [List.map_singleton, List.prod_singleton]
    rw [← mul_assoc, ih (fun j hj => he j (by omega)), ← he m (by omega)]

theorem cycle_word (vs : List PGL) (hc : IsCycleList (lps13Graph hq i) vs) :
    ∃ w : List (Fin 14), w.length = vs.length ∧ lps13WordReduced w ∧
      (w.map (lps13Generator hq i)).prod = 1 := by
  classical
  obtain ⟨x, y, middle, rfl, hlen, hnodup, hchain, hclose⟩ := hc
  let vs : List PGL := x :: (middle ++ [y])
  let m := vs.length
  have hm : 3 ≤ m := hlen
  have hn : vs.Nodup := hnodup
  let v : ℕ → PGL := fun j => if hj : j < m then vs[j] else x
  have v0 : v 0 = x := by simp [v, vs, m]
  have vm : v m = x := by simp [v]
  have edges : ∀ j < m, (lps13Graph hq i).Adj (v j) (v (j+1)) := by
    intro j hj
    by_cases hj1 : j + 1 < m
    · have he := (List.isChain_iff_getElem.mp hchain) j hj1
      simpa only [v, dif_pos hj, dif_pos hj1] using he
    · have heq : j = middle.length + 1 := by simp only [m, vs, List.length_cons,
        List.length_append, List.length_nil] at hj hj1; omega
      subst j
      simpa [v, m, vs] using hclose
  have distinct2 : ∀ j, j + 1 < m → v j ≠ v (j+2) := by
    intro j hj he
    have hj0 : j < m := by omega
    by_cases hj2 : j + 2 < m
    · have hi : (⟨j, hj0⟩ : Fin vs.length) = ⟨j+2, hj2⟩ := hn.injective_get
        (by simpa only [v, dif_pos hj0, dif_pos hj2, List.get_eq_getElem] using he)
      have hi' : j = j + 2 := congrArg Fin.val hi
      omega
    · have hx : v (j+2) = x := by simp only [v, dif_neg hj2]
      have hi : (⟨j, hj0⟩ : Fin vs.length) = ⟨0, by omega⟩ := hn.injective_get (by
        simpa only [v, dif_pos hj0, List.get_eq_getElem, vs, List.getElem_cons_zero] using he.trans hx)
      have hi' : j = 0 := congrArg Fin.val hi
      omega
  have labels : ∀ j : ℕ, ∃ a : Fin 14,
      j < m → v (j+1) = v j * lps13Generator hq i a := by
    intro j
    by_cases hj : j < m
    · obtain ⟨a, ha⟩ := edge_label hq i (edges j hj)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose a ha using labels
  refine ⟨(List.range m).map a, by simp [m, vs], ?_, ?_⟩
  · rw [reduced_iff_chain, List.isChain_iff_getElem]
    intro j hj
    simp only [List.length_map, List.length_range] at hj
    simp only [List.getElem_map, List.getElem_range]
    intro he
    apply distinct2 j hj
    calc
      v j = (v j * lps13Generator hq i (a j)) *
          lps13Generator hq i (lps13ConjIndex (a j)) := by rw [lps13Generator_conj]; simp
      _ = v (j+2) := by rw [← ha j (by omega), ← he, ← ha (j+1) hj]
  · have ht := telescope hq i v a m ha
    rw [v0, vm] at ht
    exact mul_left_cancel (by simpa using ht : x * _ = x * 1)

end Girth13
end OPG37364


end Closure14Source3

noncomputable section Closure14Source4
-- Source: OPG37364.LPS13GirthPlatform
set_option autoImplicit false
open scoped Quaternion

namespace OPG37364
namespace Girth13

theorem word_im_nonzero (w : List (Fin 14)) (hne : w ≠ [])
    (hr : lps13WordReduced w) :
    (lps13WordProduct w).imI ≠ 0 ∨ (lps13WordProduct w).imJ ≠ 0 ∨
      (lps13WordProduct w).imK ≠ 0 := by
  by_contra h
  push Not at h
  have hn := ScaledWordInjectivity.word_norm w
  rw [Quaternion.normSq_def', h.1, h.2.1, h.2.2] at hn
  have heq : (lps13WordProduct w).re ^ 2 = (13 : ℤ)^w.length := by simpa using hn
  have hd : (13 : ℤ) ∣ (lps13WordProduct w).re ^ 2 := by
    rw [heq]
    exact dvd_pow_self _ (List.length_pos_iff.mpr hne).ne'
  have hp : Prime (13 : ℤ) := by norm_num
  have hd' := hp.dvd_of_dvd_pow hd
  exact lps13_reduced_word_not_all_coords_dvd13 w hr
    ⟨hd', by simp [h.1], by simp [h.2.1], by simp [h.2.2]⟩

variable {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)

theorem matrix_one : lps13QuaternionMatrix i.val (1 : Quaternion ℤ) = 1 := by
  ext j k
  fin_cases j <;> fin_cases k <;> simp [lps13QuaternionMatrix]

theorem matrix_mul (x y : Quaternion ℤ) :
    lps13QuaternionMatrix i.val (x * y) =
      lps13QuaternionMatrix i.val x * lps13QuaternionMatrix i.val y := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [lps13QuaternionMatrix, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> rw [i.property] <;> ring

noncomputable def eval (w : List (Fin 14)) := (w.map (lps13Generator hq i)).prod
noncomputable def glEval (w : List (Fin 14)) := (w.map (lps13GL hq i)).prod

theorem glEval_val (w : List (Fin 14)) :
    (glEval hq i w).val = lps13QuaternionMatrix i.val (lps13WordProduct w) := by
  induction w with
  | nil => simp [glEval, lps13WordProduct, matrix_one]
  | cons a w ih =>
    simpa only [glEval, lps13WordProduct, List.map_cons, List.prod_cons,
      Units.val_mul, lps13GL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      lps13Matrix, matrix_mul] using
      congrArg (fun M => lps13Matrix i a * M) ih

theorem mk_glEval (w : List (Fin 14)) :
    Matrix.ProjGenLinGroup.mk (glEval hq i w) = eval hq i w := by
  change Matrix.ProjGenLinGroup.mk ((w.map (lps13GL hq i)).prod) =
    (w.map (fun a => Matrix.ProjGenLinGroup.mk (lps13GL hq i a))).prod
  rw [map_list_prod, List.map_map]
  rfl

theorem word_det (w : List (Fin 14)) :
    (lps13QuaternionMatrix i.val (lps13WordProduct w)).det = (13 : ZMod q) ^ w.length := by
  rw [lps13QuaternionMatrix_det, ScaledWordInjectivity.word_norm]
  norm_cast

include hq in
theorem word_det_ne_zero (w : List (Fin 14)) :
    (lps13QuaternionMatrix i.val (lps13WordProduct w)).det ≠ 0 := by
  rw [word_det]
  apply pow_ne_zero
  simpa using (ZMod.natCast_eq_zero_iff 13 q).not.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide) hq)

theorem closed_word_im_dvd (w : List (Fin 14)) (he : eval hq i w = 1) :
    (q : ℤ) ∣ (lps13WordProduct w).imI ∧
    (q : ℤ) ∣ (lps13WordProduct w).imJ ∧
    (q : ℤ) ∣ (lps13WordProduct w).imK := by
  have he' : Matrix.ProjGenLinGroup.mk (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) =
      Matrix.ProjGenLinGroup.mk (glEval hq i w) := by rw [mk_glEval, he]; rfl
  obtain ⟨r, hr⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he'
  have hm := congrArg Units.val hr
  rw [glEval_val] at hm
  simp only [one_mul, Matrix.GeneralLinearGroup.coe_scalar] at hm
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 0 0) hm
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 1 1) hm
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 0 1) hm
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 1 0) hm
  simp [lps13QuaternionMatrix, Matrix.scalar, Matrix.diagonal] at h00 h11 h01 h10
  have h2 : (2 : ZMod q) ≠ 0 := by
    simpa using (ZMod.natCast_eq_zero_iff 2 q).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have hi : i.val ≠ 0 := by intro hi; have hh := i.property; rw [hi] at hh; simp at hh
  have hI : ((lps13WordProduct w).imI : ZMod q) = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero h2 hi)
    linear_combination h11 - h00
  have hJ : ((lps13WordProduct w).imJ : ZMod q) = 0 := by
    apply mul_left_cancel₀ h2
    linear_combination h10 - h01
  have hK : ((lps13WordProduct w).imK : ZMod q) = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero h2 hi)
    linear_combination -h01 - h10
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hI,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hJ,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hK⟩

omit [Fact q.Prime] in
theorem sq_le_of_dvd_ne_zero {a : ℤ} (ha : a ≠ 0) (hd : (q : ℤ) ∣ a) :
    (q : ℤ)^2 ≤ a^2 := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k ≠ 0 := by intro h; simp [h] at ha
  have hk1 : (1 : ℤ) ≤ k^2 := by
    have : k ≤ -1 ∨ 1 ≤ k := by omega
    rcases this with h | h <;> nlinarith
  nlinarith [mul_nonneg (sq_nonneg (q : ℤ)) (sub_nonneg.mpr hk1)]

theorem closed_reduced_word_bound (w : List (Fin 14)) (hne : w ≠ [])
    (hr : lps13WordReduced w) (he : eval hq i w = 1) : q^2 ≤ 13^w.length := by
  obtain ⟨hI, hJ, hK⟩ := closed_word_im_dvd hq i w he
  have hn := ScaledWordInjectivity.word_norm w
  rw [Quaternion.normSq_def'] at hn
  have hh : (q : ℤ)^2 ≤ (13 : ℤ)^w.length := by
    obtain h | h | h := word_im_nonzero w hne hr
    · have hb := sq_le_of_dvd_ne_zero h hI
      nlinarith [sq_nonneg (lps13WordProduct w).re,
        sq_nonneg (lps13WordProduct w).imJ, sq_nonneg (lps13WordProduct w).imK]
    · have hb := sq_le_of_dvd_ne_zero h hJ
      nlinarith [sq_nonneg (lps13WordProduct w).re,
        sq_nonneg (lps13WordProduct w).imI, sq_nonneg (lps13WordProduct w).imK]
    · have hb := sq_le_of_dvd_ne_zero h hK
      nlinarith [sq_nonneg (lps13WordProduct w).re,
        sq_nonneg (lps13WordProduct w).imI, sq_nonneg (lps13WordProduct w).imJ]
  exact_mod_cast hh

end Girth13

/-- The original OPG cycle-list girth bound for the existing graph, uniformly in its root. -/
theorem lps13Graph_hasGirthAtLeast_of_pow_lt_sq
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
    (g : ℕ) (hbound : 13^g < q^2) : HasGirthAtLeast (lps13Graph hq i) g := by
  intro vs hc
  obtain ⟨w, hlen, hr, he⟩ := Girth13.cycle_word hq i vs hc
  have hv : 3 ≤ vs.length := by obtain ⟨_, _, _, _, hh, _⟩ := hc; exact hh
  have hw : w ≠ [] := by intro h; simp [h] at hlen; omega
  have hb := Girth13.closed_reduced_word_bound hq i w hw hr he
  rw [hlen] at hb
  by_contra h
  have hm : vs.length ≤ g := by omega
  have hp : 13^vs.length ≤ 13^g := Nat.pow_le_pow_right (by decide) hm
  omega

/-- A deliberately coarse integer threshold for eventual prime selection. -/
theorem lps13Graph_hasGirthAtLeast_of_pow_lt
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
    (g : ℕ) (hbound : 13^g < q) : HasGirthAtLeast (lps13Graph hq i) g := by
  apply lps13Graph_hasGirthAtLeast_of_pow_lt_sq hq i g
  have hsq : q ≤ q^2 := by nlinarith
  omega

end OPG37364




end Closure14Source4

noncomputable section Closure14Source5
-- Source: OPG37364.LPS13Bipartite
set_option autoImplicit false

namespace OPG37364

variable {q : ℕ} [Fact q.Prime]

/-- The quadratic character of the determinant on GL₂. -/
noncomputable def lps13GLDetChar :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod q) →* ℤ :=
  (quadraticChar (ZMod q)).toMonoidHom.comp
    ((Units.coeHom (ZMod q)).comp Matrix.GeneralLinearGroup.det)

/-- Scalar matrices have square determinant, so their character is trivial. -/
theorem lps13GLDetChar_scalar (r : (ZMod q)ˣ) :
    lps13GLDetChar (Matrix.GeneralLinearGroup.scalar (Fin 2) r) = 1 := by
  change quadraticChar (ZMod q) ((Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin 2) r) : (ZMod q)ˣ) : ZMod q) = 1
  simpa only [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
    Units.val_pow_eq_pow_val] using quadraticChar_sq_one' r.ne_zero

/-- Determinant square class on PGL₂, with values +1 and -1. -/
noncomputable def lps13DetChar :
    Matrix.ProjGenLinGroup (Fin 2) (ZMod q) →* ℤ :=
  Matrix.ProjGenLinGroup.lift lps13GLDetChar (by
    ext r
    exact lps13GLDetChar_scalar r)

theorem lps13DetChar_mk (v : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) :
    lps13DetChar (Matrix.ProjGenLinGroup.mk v) =
      quadraticChar (ZMod q) (v.det : ZMod q) := rfl

theorem lps13DetChar_dichotomy (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :
    lps13DetChar v = 1 ∨ lps13DetChar v = -1 := by
  induction v using Matrix.ProjGenLinGroup.induction_on with
  | mk v => exact quadraticChar_dichotomy v.det.ne_zero

theorem lps13DetChar_ne_zero (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :
    lps13DetChar v ≠ 0 := by
  rcases lps13DetChar_dichotomy v with h | h <;> simp [h]

/-- True is the square-determinant class; false is the nonsquare class. -/
noncomputable def lps13Side (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) : Bool :=
  decide (lps13DetChar v = 1)

theorem lps13Side_mk_eq_true_iff (v : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) :
    lps13Side (Matrix.ProjGenLinGroup.mk v) = true ↔ IsSquare (v.det : ZMod q) := by
  change decide (quadraticChar (ZMod q) (v.det : ZMod q) = 1) = true ↔ _
  rw [decide_eq_true_eq]
  exact quadraticChar_one_iff_isSquare v.det.ne_zero

variable (hq : 13 < q) (i : LPS13Root q)

/-- Reuse the norm/determinant certificates in the published Stage 7 definitions. -/
theorem lps13GL_det_val (a : Fin 14) :
    ((lps13GL hq i a).det : ZMod q) = 13 := by
  change (lps13Matrix i a).det = 13
  rw [lps13Matrix, lps13QuaternionMatrix_det, lps13Quaternion_norm]
  norm_num

theorem lps13DetChar_generator (a : Fin 14) :
    lps13DetChar (lps13Generator hq i a) = legendreSym q 13 := by
  rw [lps13Generator, lps13DetChar_mk, lps13GL_det_val]
  simp [legendreSym]

theorem lps13Side_mul_generator (hnr : legendreSym q 13 = -1)
    (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) (a : Fin 14) :
    lps13Side (v * lps13Generator hq i a) ≠ lps13Side v := by
  rcases lps13DetChar_dichotomy v with hv | hv <;>
    simp [lps13Side, map_mul, lps13DetChar_generator, hnr, hv]

/-- The fixed-p=13 PGL Cayley graph is bipartite when 13 is a nonresidue modulo q. -/
theorem lps13Graph_bipartite (hnr : legendreSym q 13 = -1) :
    IsBipartite (lps13Graph hq i) := by
  classical
  refine ⟨lps13Side, ?_⟩
  intro u v huv
  obtain ⟨_, s, hs, hmul⟩ := (SimpleGraph.mulCayley_adj' _ u v).mp huv
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
  rcases hmul with hmul | hmul
  · subst v
    exact (lps13Side_mul_generator hq i hnr u a).symm
  · subst u
    exact lps13Side_mul_generator hq i hnr v a

end OPG37364


end Closure14Source5

noncomputable section Closure14Source6
-- Source: OPG37364.LPS13Eigenspaces
set_option autoImplicit false

namespace OPG37364

/-- Every ordinary adjacency eigenspace of the fixed-p=13 PGL Cayley graph
is preserved by the natural PSL₂ left action. The eigenspace may be zero. -/
theorem lps13_adjacency_eigenspace_invariant
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q) (μ : ℝ) :
    ∀ g : LPS13ActingGroup q,
      Set.MapsTo (lps13LeftRepresentation g)
        ((lps13AdjacencyEnd hq i).eigenspace (μ : ℂ))
        ((lps13AdjacencyEnd hq i).eigenspace (μ : ℂ)) := by
  intro g f hf
  have hf' := Module.End.mem_eigenspace_iff.mp hf
  apply Module.End.mem_eigenspace_iff.mpr
  calc
    lps13AdjacencyEnd hq i (lps13LeftRepresentation g f) =
        lps13LeftRepresentation g (lps13AdjacencyEnd hq i f) :=
      LinearMap.congr_fun (lps13AdjacencyEnd_commute hq i g).eq f
    _ = (μ : ℂ) • lps13LeftRepresentation g f := by
      rw [hf', map_smul]

end OPG37364


end Closure14Source6

noncomputable section Closure14Source7
-- Source: OPG37364.PSL2RepresentationDegree
/-
The representation-degree bound of DSV Theorem 3.5.1.
No graph-existence or spectral hypothesis is used in this file.
-/
set_option autoImplicit false
open scoped MatrixGroups
open Matrix Matrix.SpecialLinearGroup Module

namespace OPG37364
namespace RepresentationBound

variable {q : ℕ} [Fact q.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Simplicity rules out every kernel except the identity subgroup. -/
theorem faithful_of_nontrivial (hq5 : 5 ≤ q)
    (ρ : Representation ℂ (PSL(2, ZMod q)) V) (hρ : ∃ g, ρ g ≠ 1) :
    Function.Injective ρ := by
  have : IsSimpleGroup PSL(2, ZMod q) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simpa using (show 4 ≤ q by omega))
  apply ρ.ker_eq_bot_iff.mp
  rcases Subgroup.Normal.eq_bot_or_eq_top (inferInstance : ρ.ker.Normal) with h | h
  · exact h
  · obtain ⟨g, hg⟩ := hρ
    have hr : ρ = 1 := MonoidHom.ker_eq_top_iff.mp h
    exact False.elim (hg (by simp [hr]))

/-- The canonical quotient, explicitly from SL₂ to PSL₂. -/
abbrev quotientMap : SL(2, ZMod q) →* PSL(2, ZMod q) :=
  QuotientGroup.mk' (Subgroup.center SL(2, ZMod q))

/-- Upper unipotents, as elements of PSL₂. -/
def unipotent (b : ZMod q) : PSL(2, ZMod q) :=
  quotientMap (transvection (show (0 : Fin 2) ≠ 1 by decide) b)

theorem unipotent_add (b c : ZMod q) :
    unipotent (b + c) = unipotent b * unipotent c := by
  simp only [unipotent, transvection_add, map_mul]

@[simp] theorem unipotent_zero : unipotent (0 : ZMod q) = 1 := by
  simp [unipotent, transvection_coeff_zero]

theorem unipotent_eq_one_iff (b : ZMod q) : unipotent b = 1 ↔ b = 0 := by
  change (QuotientGroup.mk _ : PSL(2, ZMod q)) = 1 ↔ b = 0
  rw [QuotientGroup.eq_one_iff, transvection_mem_center_iff]

theorem unipotent_one_pow (k : ℕ) :
    unipotent (1 : ZMod q) ^ k = unipotent (k : ZMod q) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, unipotent_add]

theorem unipotent_one_order : orderOf (unipotent (1 : ZMod q)) = q := by
  apply orderOf_eq_prime
  · simp [unipotent_one_pow]
  · exact (unipotent_eq_one_iff 1).not.mpr one_ne_zero

noncomputable def diagonal (a : ZMod q) (ha : a ≠ 0) : PSL(2, ZMod q) :=
  quotientMap (diag2 a ha)

/-- The SL identity is proved on matrices and then mapped to the PSL quotient. -/
theorem diagonal_conjugates (a : ZMod q) (ha : a ≠ 0) :
    diagonal a ha * unipotent (1 : ZMod q) * (diagonal a ha)⁻¹ =
      unipotent (a ^ 2) := by
  have hSL : diag2 a ha * transvection (show (0 : Fin 2) ≠ 1 by decide) 1 *
      (diag2 a ha)⁻¹ = transvection (show (0 : Fin 2) ≠ 1 by decide) (a ^ 2) := by
    rw [diag2_inv]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diag2_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
        mul_inv_cancel₀ ha, inv_mul_cancel₀ ha, pow_two]
  simpa only [diagonal, unipotent, map_mul, map_inv] using congrArg quotientMap hSL

variable [FiniteDimensional ℂ V]

/-- Finite order is used via a separable annihilating polynomial, not merely via eigenvalue
existence. This rules out a nonidentity unipotent complex Jordan block. -/
theorem exists_nontrivial_eigenvalue (T : End ℂ V) (hpow : T ^ q = 1) (hne : T ≠ 1) :
    ∃ ζ : ℂ, T.HasEigenvalue ζ ∧ ζ ≠ 1 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hsemi : T.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (Polynomial.separable_X_pow_sub_C (1 : ℂ) hq0 one_ne_zero).squarefree
      (by simpa using sub_eq_zero.mpr hpow)
  by_contra! h
  have htop : T.eigenspace 1 = ⊤ := by
    apply top_unique
    rw [← hsemi.iSup_eigenspace_eq_top]
    apply iSup_le
    intro ζ
    by_cases hz : T.HasEigenvalue ζ
    · rw [h ζ hz]
    · have hb : T.eigenspace ζ = ⊥ := not_not.mp hz
      simp [hb]
  apply hne
  ext v
  have hv : v ∈ T.eigenspace 1 := htop ▸ Submodule.mem_top
  simpa using Module.End.mem_eigenspace_iff.mp hv

omit [FiniteDimensional ℂ V] in
theorem primitive_eigenvalue (T : End ℂ V) (hpow : T ^ q = 1)
    {ζ : ℂ} (hζ : T.HasEigenvalue ζ) (hne : ζ ≠ 1) : IsPrimitiveRoot ζ q := by
  obtain ⟨v, hv⟩ := hζ.exists_hasEigenvector
  have hp : ζ ^ q = 1 := by
    apply smul_left_injective ℂ hv.2
    simpa [hpow] using (hv.pow_apply q).symm
  apply isPrimitiveRoot_of_mem_nthRootsFinset (Fact.out : q.Prime) _ hne
  exact (Polynomial.mem_nthRootsFinset (Fact.out : q.Prime).pos 1).mpr hp

omit [FiniteDimensional ℂ V] in
/-- Conjugation gives the square-exponent orbit of a nontrivial eigenvalue. -/
theorem square_eigenvalue (ρ : Representation ℂ (PSL(2, ZMod q)) V)
    {ζ : ℂ} (hζ : Module.End.HasEigenvalue (ρ (unipotent (1 : ZMod q))) ζ)
    (a : ZMod q) (ha : a ≠ 0) :
    Module.End.HasEigenvalue (ρ (unipotent (1 : ZMod q))) (ζ ^ (a ^ 2).val) := by
  obtain ⟨v, hv⟩ := hζ.exists_hasEigenvector
  let d := diagonal a ha
  have hc : unipotent (1 : ZMod q) * d⁻¹ =
      d⁻¹ * unipotent (1 : ZMod q) ^ (a ^ 2).val := by
    have hh := congrArg (fun x : PSL(2, ZMod q) => d⁻¹ * x) (diagonal_conjugates a ha)
    simpa [d, unipotent_one_pow, ZMod.natCast_zmod_val, mul_assoc] using hh
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := ρ d⁻¹ v)
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    calc
      ρ (unipotent 1) (ρ d⁻¹ v) = ρ (unipotent 1 * d⁻¹) v := by
        rw [map_mul, Module.End.mul_apply]
      _ = ρ (d⁻¹ * unipotent 1 ^ (a ^ 2).val) v := by rw [hc]
      _ = ρ d⁻¹ ((ρ (unipotent 1) ^ (a ^ 2).val) v) := by
        rw [map_mul, map_pow, Module.End.mul_apply]
      _ = ζ ^ (a ^ 2).val • ρ d⁻¹ v := by rw [hv.pow_apply, map_smul]
  · intro hz
    apply hv.2
    exact (ρ.apply_bijective d⁻¹).injective (by simpa using hz)

/-- Nonzero square residues; no character or spectral condition is hidden here. -/
def squareResidues : Finset (ZMod q) :=
  (Finset.univ.erase 0).image (fun a : ZMod q => a ^ 2)

/-- Each square has at most the two preimages `a` and `-a`. This cardinal inequality
is precisely enough for the division-free dimension bound. -/
theorem squareResidues_card_lower : q - 1 ≤ 2 * (squareResidues (q := q)).card := by
  classical
  let A : Finset (ZMod q) := Finset.univ.erase 0
  have hfib : ∀ b ∈ A.image (fun a => a ^ 2),
      (A.filter fun a => a ^ 2 = b).card ≤ 2 := by
    intro b hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
    apply (Finset.card_le_card (show (A.filter fun x => x ^ 2 = a ^ 2) ⊆ {a, -a} from ?_)).trans
      Finset.card_le_two
    intro x hx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      sq_eq_sq_iff_eq_or_eq_neg.mp (Finset.mem_filter.mp hx).2
  calc
    q - 1 = A.card := by simp [A]
    _ = ∑ b ∈ A.image (fun a => a ^ 2), (A.filter fun a => a ^ 2 = b).card :=
      Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ _b ∈ A.image (fun a => a ^ 2), 2 := Finset.sum_le_sum hfib
    _ = 2 * (squareResidues (q := q)).card := by simp [squareResidues, A, Nat.mul_comm]

theorem squareResidues_card_le_finrank
    (ρ : Representation ℂ (PSL(2, ZMod q)) V) {ζ : ℂ}
    (hζ : Module.End.HasEigenvalue (ρ (unipotent (1 : ZMod q))) ζ)
    (hprim : IsPrimitiveRoot ζ q) :
    (squareResidues (q := q)).card ≤ Module.finrank ℂ V := by
  classical
  let S := squareResidues (q := q)
  have hev : ∀ x : S, Module.End.HasEigenvalue (ρ (unipotent (1 : ZMod q)))
      (ζ ^ (x : ZMod q).val) := by
    intro x
    obtain ⟨a, ha, hx⟩ := Finset.mem_image.mp x.property
    rw [← hx]
    exact square_eigenvalue ρ hζ a (Finset.mem_erase.mp ha).1
  have hinj : Function.Injective (fun x : S => ζ ^ (x : ZMod q).val) := by
    intro x y hxy
    apply Subtype.ext
    apply ZMod.val_injective q
    exact hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hxy
  choose v hv using fun x : S => (hev x).exists_hasEigenvector
  have hli := Module.End.eigenvectors_linearIndependent' (ρ (unipotent (1 : ZMod q)))
    (fun x : S => ζ ^ (x : ZMod q).val) hinj v hv
  simpa [S] using hli.fintype_card_le_finrank

end RepresentationBound

/-- DSV Theorem 3.5.1, for every nontrivial finite-dimensional complex representation.
Nontriviality refers to the action. Faithfulness and irreducibility are not hypotheses. -/
theorem psl2_complex_rep_finrank_lower_bound
    (q : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (PSL(2, ZMod q)) V) (hρ : ∃ g, ρ g ≠ 1) :
    q - 1 ≤ 2 * Module.finrank ℂ V := by
  let : Fact q.Prime := ⟨hq⟩
  have hinj := RepresentationBound.faithful_of_nontrivial hq5 ρ hρ
  let u := RepresentationBound.unipotent (1 : ZMod q)
  let T : Module.End ℂ V := ρ u
  have hu : orderOf u = q := RepresentationBound.unipotent_one_order
  have hpow : T ^ q = 1 := by
    have hupow : u ^ q = 1 := by simpa only [hu] using pow_orderOf_eq_one u
    simpa only [map_pow, map_one] using congrArg ρ hupow
  have hne : T ≠ 1 := by
    intro hh
    have heq : u = 1 := hinj (hh.trans ρ.map_one.symm)
    have : (1 : ZMod q) = 0 := (RepresentationBound.unipotent_eq_one_iff 1).mp heq
    exact one_ne_zero this
  obtain ⟨ζ, hζ, hζ1⟩ := RepresentationBound.exists_nontrivial_eigenvalue T hpow hne
  have hprim := RepresentationBound.primitive_eigenvalue T hpow hζ hζ1
  exact RepresentationBound.squareResidues_card_lower.trans
    (Nat.mul_le_mul_left 2 (RepresentationBound.squareResidues_card_le_finrank ρ hζ hprim))

end OPG37364


end Closure14Source7

noncomputable section Closure14Source8
-- Source: OPG37364.LPS13Multiplicity
set_option autoImplicit false

noncomputable section
open scoped Classical
open Matrix

namespace OPG37364
namespace Multiplicity

variable {q : ℕ} [Fact q.Prime]

theorem detChar_toPGL (g : LPS13ActingGroup q) :
    lps13DetChar (lps13PSLToPGL g) = 1 := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    change quadraticChar (ZMod q) ((Matrix.SpecialLinearGroup.toGL g).det : ZMod q) = 1
    simp

theorem exists_toPGL_of_detChar (v : LPS13Vertex q) (hv : lps13DetChar v = 1) :
    ∃ g : LPS13ActingGroup q, lps13PSLToPGL g = v := by
  induction v using Matrix.ProjGenLinGroup.induction_on with
  | mk M =>
    have hs : IsSquare (M.det : ZMod q) :=
      (quadraticChar_one_iff_isSquare M.det.ne_zero).mp hv
    obtain ⟨t, ht⟩ := hs
    have ht0 : t ≠ 0 := by
      intro he
      apply M.det.ne_zero
      simp [he] at ht
      exact ht
    let r : (ZMod q)ˣ := Units.mk0 t ht0
    have hr : r ^ 2 = M.det := by
      apply Units.ext
      simpa [r, pow_two] using ht.symm
    have hi : r⁻¹ ^ Fintype.card (Fin 2) * M.det = 1 := by
      rw [Fintype.card_fin, ← hr]
      simp
    simp only [Units.ext_iff, Units.val_mul, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_smul M.1 (r⁻¹).1,
      Units.val_one] at hi
    use QuotientGroup.mk ⟨(r⁻¹).1 • M.1, hi⟩
    change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
      ⟨(r⁻¹).1 • M.1, hi⟩) = Matrix.ProjGenLinGroup.mk M
    rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨r, Units.ext ?_⟩
    change ((r⁻¹ : (ZMod q)ˣ) : ZMod q) • (M : Matrix (Fin 2) (Fin 2) (ZMod q)) *
      Matrix.diagonal (fun _ => (r : ZMod q)) = (M : Matrix (Fin 2) (Fin 2) (ZMod q))
    ext j k
    simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    rw [mul_right_comm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem mem_range_iff_detChar (v : LPS13Vertex q) :
    v ∈ lps13PSLToPGL.range ↔ lps13DetChar v = 1 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact detChar_toPGL g
  · exact exists_toPGL_of_detChar v

theorem invariant_eq_of_detChar (f : LPS13Functions q)
    (hf : ∀ g : LPS13ActingGroup q, lps13LeftRepresentation g f = f)
    {v w : LPS13Vertex q} (hvw : lps13DetChar v = lps13DetChar w) : f v = f w := by
  have hker : lps13DetChar (v * w⁻¹) = 1 := by
    apply mul_right_cancel₀ (lps13DetChar_ne_zero w)
    rw [← map_mul]
    simpa [mul_assoc] using hvw
  obtain ⟨g, hg⟩ := exists_toPGL_of_detChar (v * w⁻¹) hker
  have h := congrFun (hf g⁻¹) w
  simpa [lps13LeftRepresentation_apply, hg, mul_assoc] using h

variable (hq : 13 < q) (i : LPS13Root q) (hnr : legendreSym q 13 = -1)
include hnr

theorem detChar_adj {v w : LPS13Vertex q} (h : (lps13Graph hq i).Adj v w) :
    lps13DetChar w = -lps13DetChar v := by
  obtain ⟨_, s, hs, hm⟩ := (SimpleGraph.mulCayley_adj' _ v w).mp h
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
  rcases hm with rfl | rfl <;>
    simp [map_mul, lps13DetChar_generator, hnr]

/-- The minimal two-coset characterization: equal determinant classes give equal values. -/
theorem invariant_two_values (f : LPS13Functions q)
    (hf : ∀ g : LPS13ActingGroup q, lps13LeftRepresentation g f = f) :
    ∀ v, f v = if lps13DetChar v = 1 then f 1 else f (lps13Generator hq i 0) := by
  intro v
  split_ifs with hv
  · apply invariant_eq_of_detChar f hf
    simpa using hv
  · apply invariant_eq_of_detChar f hf
    rcases lps13DetChar_dichotomy v with h | h
    · exact (hv h).elim
    · simpa [lps13DetChar_generator, hnr] using h

theorem adjacency_on_invariant (f : LPS13Functions q)
    (hf : ∀ g : LPS13ActingGroup q, lps13LeftRepresentation g f = f)
    (v : LPS13Vertex q) :
    lps13AdjacencyEnd hq i f v = 14 * f (v * lps13Generator hq i 0) := by
  have hc : ((lps13Graph hq i).neighborFinset v).card = 14 := by
    have h := lps13Graph_regular14 hq i v
    rw [← SimpleGraph.coe_neighborFinset, Set.encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  change (((lps13Graph hq i).adjMatrix ℂ) *ᵥ f) v = _
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  calc
    ∑ w ∈ (lps13Graph hq i).neighborFinset v, f w =
        ∑ _w ∈ (lps13Graph hq i).neighborFinset v, f (v * lps13Generator hq i 0) := by
      apply Finset.sum_congr rfl
      intro w hw
      apply invariant_eq_of_detChar f hf
      rw [detChar_adj hq i hnr ((SimpleGraph.mem_neighborFinset _ _ _).mp hw)]
      simp [map_mul, lps13DetChar_generator, hnr]
    _ = 14 * f (v * lps13Generator hq i 0) := by simp [hc, nsmul_eq_mul]

theorem invariant_eigenvalue_eq (μ : ℝ) (f : lps13AdjacencyEigenspace hq i μ)
    (hf : f ≠ 0)
    (hinv : ∀ g : LPS13ActingGroup q,
      lps13LeftRepresentation g (f : LPS13Functions q) = f) :
    μ = 14 ∨ μ = -14 := by
  have hfne : (f : LPS13Functions q) ≠ 0 := by
    intro he
    exact hf (Subtype.ext he)
  obtain ⟨v, hv⟩ : ∃ v, (f : LPS13Functions q) v ≠ 0 := by
    by_contra h
    push Not at h
    exact hfne (funext h)
  let s := lps13Generator hq i 0
  have htwice : (f : LPS13Functions q) ((v * s) * s) = (f : LPS13Functions q) v := by
    apply invariant_eq_of_detChar (f : LPS13Functions q) hinv
    simp [s, map_mul, lps13DetChar_generator, hnr]
  have he := Module.End.mem_eigenspace_iff.mp f.property
  have h1 := congrFun he v
  have h2 := congrFun he (v * s)
  rw [adjacency_on_invariant hq i hnr _ hinv] at h1 h2
  change 14 * (f : LPS13Functions q) (v * s) = (μ : ℂ) * (f : LPS13Functions q) v at h1
  change 14 * (f : LPS13Functions q) ((v * s) * s) = (μ : ℂ) * (f : LPS13Functions q) (v * s) at h2
  rw [htwice] at h2
  have heq : ((μ : ℂ) ^ 2 - 14 ^ 2) * (f : LPS13Functions q) v = 0 := by
    linear_combination -(μ : ℂ) * h1 - 14 * h2
  have hsq : (μ : ℂ) ^ 2 = 14 ^ 2 := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right hv)
  have hr : μ ^ 2 = (14 : ℝ) ^ 2 := by exact_mod_cast hsq
  have hfac : (μ - 14) * (μ + 14) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · left; linarith
  · right; linarith

end Multiplicity

theorem lps13_eigenspace_rep_nontrivial
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
    (hnr : legendreSym q 13 = -1) (μ : ℝ) (hμ14 : μ ≠ 14) (hμneg14 : μ ≠ -14)
    (hE : Nontrivial (lps13AdjacencyEigenspace hq i μ)) :
    ∃ g : LPS13ActingGroup q, lps13EigenspaceRepresentation hq i μ g ≠ 1 := by
  by_contra h
  push Not at h
  let := hE
  obtain ⟨f, hf⟩ := exists_ne (0 : lps13AdjacencyEigenspace hq i μ)
  have hinv : ∀ g : LPS13ActingGroup q,
      lps13LeftRepresentation g (f : LPS13Functions q) = f := by
    intro g
    have he := LinearMap.congr_fun (h g) f
    exact congrArg (fun x : lps13AdjacencyEigenspace hq i μ => (x : LPS13Functions q)) he
  rcases Multiplicity.invariant_eigenvalue_eq hq i hnr μ f hf hinv with he | he
  · exact hμ14 he
  · exact hμneg14 he

/-- The fixed-p=13, nonsquare-determinant case of DSV Proposition 4.4.3. -/
theorem lps13_eigenspace_finrank_lower_bound
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
    (hnr : legendreSym q 13 = -1) (μ : ℝ) (hμ14 : μ ≠ 14) (hμneg14 : μ ≠ -14)
    (hE : Nontrivial (lps13AdjacencyEigenspace hq i μ)) :
    q - 1 ≤ 2 * Module.finrank ℂ (lps13AdjacencyEigenspace hq i μ) := by
  exact psl2_complex_rep_finrank_lower_bound q Fact.out (by omega)
    (lps13EigenspaceRepresentation hq i μ)
    (lps13_eigenspace_rep_nontrivial hq i hnr μ hμ14 hμneg14 hE)

end OPG37364

end

end Closure14Source8

noncomputable section Closure14Source9
-- Source: OPG37364.LPS13ConnectedPlatform
/- Stage 14: coarse-threshold connectedness assembly.
Reuses Stage 12 and Stage 13 proved sources. No spectral hypotheses.
External classification provenance: Qiuzhen-CFSG/CFSG,
96b2a02085dc678f3e0a97b334c31ada599c55fd, Apache-2.0. -/
set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement
namespace OPG37364
namespace Connected13

/-- Minimal closure-to-reachability bridge; independent of matrix representations. -/
private theorem cayley_reachable_mul {Γ : Type*} [Group Γ] (S : Set Γ)
    {z : Γ} (hz : z ∈ Subgroup.closure S) :
    ∀ x, Relation.ReflTransGen (SimpleGraph.mulCayley S).Adj x (x * z) := by
  let : Std.Symm (SimpleGraph.mulCayley S).Adj := ⟨fun _ _ h => h.symm⟩
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    intro x
    by_cases he : x = x * z
    · rw [← he]
    · exact .single ((SimpleGraph.mulCayley_adj' S x (x*z)).mpr ⟨he,z,hz,Or.inl rfl⟩)
  | one => intro x; simpa only [mul_one] using
      (Relation.ReflTransGen.refl (r := (SimpleGraph.mulCayley S).Adj) (a := x))
  | mul z w _ _ ihz ihw =>
    intro x
    simpa only [mul_assoc] using (ihz x).trans (ihw (x*z))
  | inv z _ ih =>
    intro x
    have hh := ih (x * z⁻¹)
    simp only [inv_mul_cancel_right] at hh
    exact symm hh


variable {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)

def K : Subgroup (LPS13Vertex q) :=
  Subgroup.closure (lps13Generators hq i : Set _)

def H : Subgroup (LPS13ActingGroup q) := (K hq i).comap lps13PSLToPGL

theorem generator_mem (a : Fin 14) : lps13Generator hq i a ∈ K hq i :=
  Subgroup.subset_closure (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)

theorem lift_pair (hnr : legendreSym q 13 = -1) (a b : Fin 14) :
    ∃ t : H hq i, lps13PSLToPGL t.val = lps13Generator hq i a * lps13Generator hq i b := by
  have hc : lps13DetChar (lps13Generator hq i a * lps13Generator hq i b) = 1 := by
    simp [map_mul, lps13DetChar_generator, hnr]
  obtain ⟨t, ht⟩ := Multiplicity.exists_toPGL_of_detChar _ hc
  have hm : t ∈ H hq i := by
    change lps13PSLToPGL t ∈ K hq i
    rw [ht]
    exact (K hq i).mul_mem (generator_mem hq i a) (generator_mem hq i b)
  exact ⟨⟨t, hm⟩, ht⟩

omit [Fact q.Prime] in
theorem threshold_sq (hlarge : 13^60 < q) : 13^120 < q^2 := by
  have he : (13 : ℕ)^120 = (13^60)^2 := by rw [← pow_mul]
  rw [he]
  nlinarith

theorem short_word_not_closed (hlarge : 13^60 < q) (w : List (Fin 14))
    (hne : w ≠ []) (hr : lps13WordReduced w) (hlen : w.length ≤ 120) :
    Girth13.eval hq i w ≠ 1 := by
  intro he
  have hb := Girth13.closed_reduced_word_bound hq i w hne hr he
  have hp : 13^w.length ≤ 13^120 := Nat.pow_le_pow_right (by decide) hlen
  have ht := threshold_sq hlarge
  omega

theorem card_H_gt (hlarge : 13^60 < q) (hnr : legendreSym q 13 = -1) :
    60 < Nat.card (H hq i) := by
  by_contra hcard
  have hle : Nat.card (H hq i) ≤ 60 := by omega
  obtain ⟨t, ht⟩ := lift_pair hq i hnr 0 0
  have hpos : 0 < Nat.card (H hq i) := Nat.card_pos
  have hp : t ^ Nat.card (H hq i) = 1 := pow_card_eq_one'
  have hmap := congrArg (fun z : H hq i => lps13PSLToPGL z.val) hp
  have he : lps13Generator hq i 0 ^ (2 * Nat.card (H hq i)) = 1 := by
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one, ht, ← pow_two,
      ← pow_mul] using hmap
  let w : List (Fin 14) := List.replicate (2 * Nat.card (H hq i)) 0
  have hne : w ≠ [] := by simp [w, List.replicate_eq_nil_iff]
  have hr : lps13WordReduced w := by
    rw [Girth13.reduced_iff_chain]
    exact List.isChain_replicate_of_rel _ (by decide)
  have hlen : w.length ≤ 120 := by
    rw [List.length_replicate]
    omega
  apply short_word_not_closed hq i hlarge w hne hr hlen
  simpa [Girth13.eval, w] using he

/-- The exact 24-letter word in the existing index convention. -/
def doubleWord : List (Fin 14) :=
  [0,2,1,7,5,6,0,1,2,7,6,5,1,2,0,6,5,7,2,1,0,5,6,7]

theorem doubleWord_length : doubleWord.length = 24 := rfl
theorem doubleWord_nonempty : doubleWord ≠ [] := by decide
theorem doubleWord_reduced : lps13WordReduced doubleWord := by
  simp only [doubleWord, lps13WordReduced]
  decide

theorem doubleWord_eval : Girth13.eval hq i doubleWord =
    ⁅⁅lps13Generator hq i 0 * lps13Generator hq i 2,
        lps13Generator hq i 1 * lps13Generator hq i 2⁆,
      ⁅lps13Generator hq i 0 * lps13Generator hq i 1,
        lps13Generator hq i 2 * lps13Generator hq i 1⁆⁆ := by
  have h7 : lps13Generator hq i 7 = (lps13Generator hq i 0)⁻¹ :=
    lps13Generator_conj hq i 0
  have h6 : lps13Generator hq i 6 = (lps13Generator hq i 1)⁻¹ :=
    lps13Generator_conj hq i 1
  have h5 : lps13Generator hq i 5 = (lps13Generator hq i 2)⁻¹ :=
    lps13Generator_conj hq i 2
  simp only [Girth13.eval, doubleWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, h7, h6, h5, commutatorElement_def]
  group

theorem exists_nontrivial_double_commutator (hlarge : 13^60 < q)
    (hnr : legendreSym q 13 = -1) :
    ∃ a b c d : H hq i, ⁅⁅a,b⁆,⁅c,d⁆⁆ ≠ 1 := by
  obtain ⟨a, ha⟩ := lift_pair hq i hnr 0 2
  obtain ⟨b, hb⟩ := lift_pair hq i hnr 1 2
  obtain ⟨c, hc⟩ := lift_pair hq i hnr 0 1
  obtain ⟨d, hd⟩ := lift_pair hq i hnr 2 1
  refine ⟨a,b,c,d, ?_⟩
  intro he
  let j : H hq i →* LPS13Vertex q := lps13PSLToPGL.comp (H hq i).subtype
  have hm := congrArg j he
  simp only [map_commutatorElement, map_one] at hm
  change ⁅⁅lps13PSLToPGL a.val, lps13PSLToPGL b.val⁆,
    ⁅lps13PSLToPGL c.val, lps13PSLToPGL d.val⁆⁆ = 1 at hm
  rw [ha, hb, hc, hd, ← doubleWord_eval hq i] at hm
  exact short_word_not_closed hq i hlarge doubleWord doubleWord_nonempty
    doubleWord_reduced (by decide) hm

theorem H_eq_top (hlarge : 13^60 < q) (hnr : legendreSym q 13 = -1) : H hq i = ⊤ := by
  by_contra hproper
  obtain ⟨a,b,c,d, hne⟩ := exists_nontrivial_double_commutator hq i hlarge hnr
  exact hne (psl2_prime_large_proper_subgroup_double_commutator_eq_one q (by omega)
    (H hq i) hproper (card_H_gt hq i hlarge hnr) a b c d)

theorem range_le_K (hlarge : 13^60 < q) (hnr : legendreSym q 13 = -1) :
    lps13PSLToPGL.range ≤ K hq i := by
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ H hq i := by rw [H_eq_top hq i hlarge hnr]; trivial
  exact hg

theorem K_eq_top (hlarge : 13^60 < q) (hnr : legendreSym q 13 = -1) : K hq i = ⊤ := by
  apply top_unique
  intro x _
  have hr := range_le_K hq i hlarge hnr
  rcases lps13DetChar_dichotomy x with hs | hn
  · exact hr ((Multiplicity.mem_range_iff_detChar x).mpr hs)
  · let s := lps13Generator hq i 0
    have hc : lps13DetChar (x * s⁻¹) = 1 := by
      apply mul_right_cancel₀ (lps13DetChar_ne_zero s)
      rw [← map_mul]
      simpa [s, mul_assoc, lps13DetChar_generator, hnr] using hn
    have hm := hr ((Multiplicity.mem_range_iff_detChar _).mpr hc)
    simpa [s] using (K hq i).mul_mem hm (generator_mem hq i 0)


theorem reachable_mul_of_mem_K {z : LPS13Vertex q} (hz : z ∈ K hq i) :
    ∀ x, Relation.ReflTransGen (lps13Graph hq i).Adj x (x * z) := by
  unfold K at hz
  unfold lps13Graph
  with_reducible exact (cayley_reachable_mul (Γ := LPS13Vertex q) (lps13Generators hq i : Set _) (z := z) hz)

theorem connected_of_K_eq_top (hk : K hq i = ⊤) : IsConnected (lps13Graph hq i) := by
  refine ⟨inferInstance, ?_⟩
  intro x y
  have hm : x⁻¹ * y ∈ K hq i := by rw [hk]; trivial
  simpa using reachable_mul_of_mem_K hq i hm x

end Connected13

/-- The original fixed-13 LPS graph is connected above a deliberately coarse threshold.
No connectedness, girth, spectral, or generation hypothesis is assumed. -/
theorem _root_.solution
    {q : ℕ} [Fact q.Prime] (hqLarge : 13^60 < q)
    (i : LPS13Root q) (hnr : legendreSym q 13 = -1) :
    IsConnected (lps13Graph (show 13 < q by omega) i) := by
  exact Connected13.connected_of_K_eq_top _ i (Connected13.K_eq_top _ i hqLarge hnr)

end OPG37364

end

end Closure14Source9

end Closure14Pack

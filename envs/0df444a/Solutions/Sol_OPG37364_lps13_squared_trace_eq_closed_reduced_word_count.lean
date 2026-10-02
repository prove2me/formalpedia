-- Prove2me | solution 1 for OPG37364.lps13_squared_trace_eq_closed_reduced_word_count
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T05:42:25.590797+00:00
-- url     : https://prove2.me/submissions/1b9f939a-c2bc-4c1f-9a7e-c37205a608f6

/- Stage 16 exact fixed-13 trace bridge.
Stage 7 construction proofs are reused from arexychen’s accepted source,
theorem a1b44539-4a01-4515-b3fe-7e0b60624a02,
submission 5cd7397d-42aa-4aad-b8ce-29d615dffe60.
New Stage 16 proofs establish recurrences and identities for all natural lengths.
-/
import Definitions.Def_opg37364_lps13_trace
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

noncomputable section Stage16Source0

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

end Stage16Source0

noncomputable section Stage16Source1

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace OPG37364.Trace13
local notation "P" => lps13NonbacktrackingPolynomial

theorem P_zero : P 0 = 1 := rfl
theorem P_one : P 1 = X := rfl
theorem P_rec (n : ℕ) : P (n+2) = X * P (n+1) - 13 * P n := rfl

theorem P_add (n m : ℕ) :
    P (n+m+2) = P (n+1) * P (m+1) - 13 * P n * P m := by
  induction m using Nat.twoStepInduction with
  | zero =>
    change P (n+2) = P (n+1) * X - 13 * P n * 1
    rw [P_rec]
    ring
  | one =>
    change P (n+3) = P (n+1) * (X*X-13*1) - 13 * P n * X
    rw [show n+3 = (n+1)+2 by omega, P_rec (n+1), P_rec n]
    ring
  | more m ih₀ ih₁ =>
    rw [show n+(m+2)+2 = (n+m+2)+2 by omega, P_rec]
    rw [show n+m+2+1 = n+(m+1)+2 by omega, ih₁, ih₀]
    rw [show m+2+1 = (m+1)+2 by omega, P_rec (m+1), P_rec m]
    ring

theorem P_square_step (m : ℕ) :
    P (m+1)^2 = P (2*(m+1)) + 13 * P m^2 := by
  have h := P_add m m
  rw [show m+m+2 = 2*(m+1) by omega] at h
  linear_combination -h

theorem P_square (m : ℕ) :
    P m^2 = ∑ j ∈ Finset.range (m+1), (13 : Polynomial ℝ)^j * P (2*m-2*j) := by
  induction m with
  | zero => simp [P_zero]
  | succ m ih =>
    rw [P_square_step, ih, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.mul_zero, Nat.sub_zero, pow_zero, one_mul]
    rw [add_comm (P (2*(m+1)))]
    apply congrArg (fun z => z + P (2*(m+1)))
    apply Finset.sum_congr rfl
    intro j hj
    rw [show 2*(m+1)-2*(j+1) = 2*m-2*j by omega, pow_succ']
    ring

/-- Parity sum in increasing index order, avoiding subtraction in its summands. -/
def paritySum {R : Type*} [AddCommMonoid R] (b : ℕ → R) (m : ℕ) : R :=
  ∑ j ∈ Finset.range (m/2+1), b (m%2+2*j)

theorem parity_zero {R : Type*} [AddCommMonoid R] (b : ℕ → R) :
    paritySum b 0 = b 0 := by simp [paritySum]

theorem parity_one {R : Type*} [AddCommMonoid R] (b : ℕ → R) :
    paritySum b 1 = b 1 := by simp [paritySum]

theorem parity_rec {R : Type*} [AddCommMonoid R] (b : ℕ → R) (m : ℕ) :
    paritySum b (m+2) = paritySum b m + b (m+2) := by
  have hd : (m+2)/2 = m/2+1 := by omega
  have hm : (m+2)%2 = m%2 := by omega
  have he : m%2+2*(m/2+1) = m+2 := by omega
  simp only [paritySum, hd, hm, Finset.sum_range_succ, he]

end OPG37364.Trace13

end Stage16Source1

noncomputable section Stage16Source2

set_option autoImplicit false
open scoped Classical BigOperators

namespace OPG37364.Trace13

theorem sum_words_succ {R : Type*} [AddCommMonoid R]
    (n : ℕ) (f : List (Fin 14) → R) :
    (∑ w : Fin (n+1) → Fin 14, f (List.ofFn w)) =
      ∑ a : Fin 14, ∑ w : Fin n → Fin 14, f (a :: List.ofFn w) := by
  simpa [Fintype.sum_prod_type, Fin.consEquiv, List.ofFn_cons] using
    (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Fin 14))
      (fun w => f (List.ofFn w))).symm

theorem conj_eq_iff (a b : Fin 14) :
    b = lps13ConjIndex a ↔ a = lps13ConjIndex b := by
  constructor
  · intro h
    exact ((congrArg lps13ConjIndex h).trans (lps13ConjIndex_involutive a)).symm
  · intro h
    exact ((congrArg lps13ConjIndex h).trans (lps13ConjIndex_involutive b)).symm

variable {q : ℕ} [Fact q.Prime]
local notation "G" => LPS13Vertex q
local notation "Mat" => Matrix G G ℝ
local notation "T" => lps13TranslationMatrix (q := q)

theorem translation_one : T 1 = (1 : Mat) := by
  ext x y
  simp [lps13TranslationMatrix, Matrix.one_apply]

theorem translation_mul (s t : G) : T (s*t) = T s * T t := by
  ext x y
  simp only [lps13TranslationMatrix, Matrix.mul_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc]

theorem translation_trace (s : G) :
    Matrix.trace (T s) = if s=1 then (Fintype.card G : ℝ) else 0 := by
  simp [Matrix.trace, Matrix.diag, lps13TranslationMatrix, mul_eq_left]

variable (hq : 13 < q) (i : LPS13Root q)
local notation "ev" => lps13ProjectiveWordProduct hq i
local notation "gen" => lps13Generator hq i
local notation "B" => lps13ReducedWordMatrix hq i
local notation "A" => SimpleGraph.adjMatrix ℝ (lps13Graph hq i)

theorem eval_nil : ev [] = 1 := rfl
theorem eval_cons (a : Fin 14) (w : List (Fin 14)) :
    ev (a::w) = gen a * ev w := by simp [lps13ProjectiveWordProduct]

def wordTerm (w : List (Fin 14)) : Mat :=
  if lps13WordReduced w then T (ev w) else 0

theorem B_zero : B 0 = 1 := by
  simp [lps13ReducedWordMatrix, List.ofFn_zero, lps13WordReduced, eval_nil, translation_one]

theorem B_one_sum : B 1 = ∑ a : Fin 14, T (gen a) := by
  change (∑ w : Fin 1 → Fin 14, wordTerm hq i (List.ofFn w)) = _
  rw [sum_words_succ 0 (wordTerm hq i)]
  simp [wordTerm, List.ofFn_zero, lps13WordReduced, eval_cons, eval_nil]

theorem adjacency_sum : A = ∑ a : Fin 14, T (gen a) := by
  ext x y
  have hadj : (lps13Graph hq i).Adj x y ↔ ∃ a, x * gen a = y := by
    rw [← SimpleGraph.mem_neighborSet, lps13Graph_neighborSet]
    simp [lps13Generators]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [ha]; simp⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [← ha]; simp⟩
  simp only [SimpleGraph.adjMatrix_apply, Matrix.sum_apply, lps13TranslationMatrix]
  by_cases he : ∃ a, x * gen a = y
  · obtain ⟨a, rfl⟩ := he
    have heq : ∀ b, x * gen b = x * gen a ↔ b=a := by
      intro b
      exact (mul_left_cancel_iff).trans (lps13Generator_injective hq i).eq_iff
    have ha := hadj.mpr ⟨a, rfl⟩
    simp [ha, heq]
  · have hn : ¬ (lps13Graph hq i).Adj x y := fun h => he (hadj.mp h)
    simp [hn, show ∀ a, x * gen a ≠ y from not_exists.mp he]

theorem B_one : B 1 = A := (B_one_sum hq i).trans (adjacency_sum hq i).symm

theorem term_partition (a b : Fin 14) (w : List (Fin 14)) :
    T (gen a) * wordTerm hq i (b::w) = wordTerm hq i (a::b::w) +
      if b = lps13ConjIndex a ∧ lps13WordReduced (b::w) then T (ev w) else 0 := by
  by_cases hr : lps13WordReduced (b::w)
  · by_cases hb : b = lps13ConjIndex a
    · subst b
      have hn : ¬ lps13WordReduced (a::lps13ConjIndex a::w) := by
        change ¬ (lps13ConjIndex a ≠ lps13ConjIndex a ∧ _)
        simp
      simp only [wordTerm, if_neg hn, true_and, if_pos hr, zero_add]
      rw [eval_cons, translation_mul, ← mul_assoc, ← translation_mul,
        lps13Generator_conj, mul_inv_cancel, translation_one, one_mul]
    · have hg : lps13WordReduced (a::b::w) := ⟨hb, hr⟩
      simp only [wordTerm, if_pos hr, if_pos hg, hb, false_and, if_false, add_zero]
      simp only [eval_cons, translation_mul]
  · have hn : ¬ lps13WordReduced (a::b::w) := fun h => hr h.2
    simp [wordTerm, hr, hn]

def correction (n : ℕ) : Mat :=
  ∑ w : Fin n → Fin 14, ∑ b : Fin 14,
    if lps13WordReduced (b :: List.ofFn w) then T (ev (List.ofFn w)) else 0

theorem forbidden_sum (n : ℕ) :
    (∑ a : Fin 14, ∑ b : Fin 14, ∑ w : Fin n → Fin 14,
      if b=lps13ConjIndex a ∧ lps13WordReduced (b::List.ofFn w)
      then T (ev (List.ofFn w)) else 0) = correction hq i n := by
  rw [Finset.sum_comm]
  unfold correction
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  trans ∑ a : Fin 14, if a=lps13ConjIndex b ∧ lps13WordReduced (b::List.ofFn w)
    then T (ev (List.ofFn w)) else 0
  · apply Finset.sum_congr rfl
    intro a _
    simp only [conj_eq_iff a b]
  · by_cases hr : lps13WordReduced (b::List.ofFn w) <;> simp [hr]

theorem B_partition (n : ℕ) : A * B (n+1) = B (n+2) + correction hq i n := by
  rw [adjacency_sum]
  change (∑ a : Fin 14, T (gen a)) *
    (∑ w : Fin (n+1) → Fin 14, wordTerm hq i (List.ofFn w)) = _
  rw [sum_words_succ n (wordTerm hq i)]
  change (∑ a : Fin 14, T (gen a)) *
    (∑ b : Fin 14, ∑ w : Fin n → Fin 14, wordTerm hq i (b::List.ofFn w)) = _
  simp_rw [Finset.sum_mul, Finset.mul_sum, term_partition, Finset.sum_add_distrib]
  rw [forbidden_sum]
  congr 1
  change _ = ∑ w : Fin (n+2) → Fin 14, wordTerm hq i (List.ofFn w)
  rw [sum_words_succ (n+1) (wordTerm hq i)]
  apply Finset.sum_congr rfl
  intro a _
  exact (sum_words_succ n (fun w => wordTerm hq i (a::w))).symm

theorem correction_zero : correction hq i 0 = (14 : Mat) := by
  simp [correction, List.ofFn_zero, lps13WordReduced, eval_nil, translation_one,
    nsmul_eq_mul]

theorem thirteen_sum (c : Fin 14) (M : Mat) :
    (∑ b : Fin 14, if c ≠ lps13ConjIndex b then M else 0) = 13 * M := by
  have ht : ∀ b : Fin 14, (if c ≠ lps13ConjIndex b then M else 0) =
      M - (if b=lps13ConjIndex c then M else 0) := by
    intro b
    have hc := conj_eq_iff b c
    by_cases hb : b=lps13ConjIndex c
    · simp only [if_neg (not_not_intro (hc.mpr hb)), if_pos hb, sub_self]
    · have hn : c ≠ lps13ConjIndex b := fun h => hb (hc.mp h)
      simp only [if_pos hn, if_neg hb, sub_zero]
  simp_rw [ht, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change (14 : Mat) * M - M = 13 * M
  noncomm_ring

theorem correction_succ (n : ℕ) : correction hq i (n+1) = 13 * B (n+1) := by
  rw [correction, sum_words_succ n (fun w => ∑ b : Fin 14,
    if lps13WordReduced (b::w) then T (ev w) else 0)]
  change _ = 13 * (∑ w : Fin (n+1) → Fin 14, wordTerm hq i (List.ofFn w))
  rw [sum_words_succ n (wordTerm hq i)]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro w _
  by_cases hr : lps13WordReduced (c::List.ofFn w)
  · simp only [wordTerm, lps13WordReduced, hr, and_true, if_true]
    exact thirteen_sum c _
  · simp [wordTerm, lps13WordReduced, hr]

theorem B_two : B 2 = A^2 - 14 := by
  have h := B_partition hq i 0
  rw [B_one, correction_zero] at h
  exact eq_sub_of_add_eq (by simpa [pow_two] using h.symm)

theorem B_rec (n : ℕ) : B (n+3) = A * B (n+2) - 13 * B (n+1) := by
  have h := B_partition hq i (n+1)
  rw [correction_succ] at h
  exact eq_sub_of_add_eq h.symm

theorem closed_count_sum (m : ℕ) :
    (lps13ClosedReducedWordCount hq i m : ℝ) =
    ∑ w : Fin m → Fin 14,
      if lps13WordReduced (List.ofFn w) ∧ ev (List.ofFn w)=1 then (1 : ℝ) else 0 := by
  rw [lps13ClosedReducedWordCount, Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem trace_B (m : ℕ) :
    Matrix.trace (B m) = (Fintype.card G : ℝ) * lps13ClosedReducedWordCount hq i m := by
  rw [lps13ReducedWordMatrix, Matrix.trace_sum, closed_count_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hr : lps13WordReduced (List.ofFn w) <;>
    by_cases he : ev (List.ofFn w)=1 <;>
      simp [hr, he, translation_trace]

end OPG37364.Trace13

end Stage16Source2

noncomputable section Stage16Source3

set_option autoImplicit false
open scoped Classical BigOperators
open Polynomial

namespace OPG37364.Trace13

variable {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
local notation "G" => LPS13Vertex q
local notation "Mat" => Matrix G G ℝ
local notation "A" => SimpleGraph.adjMatrix ℝ (lps13Graph hq i)
local notation "P" => lps13NonbacktrackingPolynomial
local notation "B" => lps13ReducedWordMatrix hq i
local notation "C" => lps13ClosedReducedWordCount hq i

def evalP (m : ℕ) : Mat := aeval A (P m)
local notation "E" => evalP hq i

theorem evalP_zero : E 0 = 1 := by simp [evalP, P_zero]
theorem evalP_one : E 1 = A := by simp [evalP, P_one]
theorem evalP_rec (m : ℕ) : E (m+2) = A * E (m+1) - 13 * E m := by
  simp only [evalP, P_rec, map_sub, map_mul, map_ofNat, Polynomial.aeval_X]

theorem B_eq_difference (m : ℕ) : B (m+2) = E (m+2) - E m := by
  induction m using Nat.twoStepInduction with
  | zero =>
    rw [B_two, evalP_rec, evalP_one, evalP_zero]
    have hn : (14 : Mat) = 13 + 1 := by norm_num
    simp only [pow_two, mul_one, hn, sub_add_eq_sub_sub]
  | one =>
    rw [B_rec, B_two, B_one, evalP_rec _ _ 1, evalP_rec _ _ 0,
      evalP_one, evalP_zero]
    noncomm_ring
  | more m ih₀ ih₁ =>
    rw [B_rec _ _ (m+1), ih₁, ih₀, evalP_rec _ _ (m+2), evalP_rec _ _ m]
    noncomm_ring

theorem evalP_parity (m : ℕ) : E m = paritySum B m := by
  induction m using Nat.twoStepInduction with
  | zero => rw [parity_zero, B_zero, evalP_zero]
  | one => rw [parity_one, B_one, evalP_one]
  | more m ih₀ ih₁ =>
    rw [parity_rec, ← ih₀, B_eq_difference]
    abel

theorem trace_evalP (m : ℕ) :
    Matrix.trace (E m) = (Fintype.card G : ℝ) *
      ∑ r ∈ Finset.range (m/2+1), (C (m%2+2*r) : ℝ) := by
  rw [evalP_parity, paritySum, Matrix.trace_sum]
  simp_rw [trace_B]
  rw [Finset.mul_sum]

theorem trace_thirteen_pow_mul (j : ℕ) (M : Mat) :
    Matrix.trace ((13 : Mat)^j * M) = (13 : ℝ)^j * Matrix.trace M := by
  have hs : (13 : Mat)^j * M = (13 : ℝ)^j • M := by
    rw [Algebra.smul_def, map_pow, map_ofNat]
  rw [hs, Matrix.trace_smul]
  rfl

theorem squared_trace (m : ℕ) :
    Matrix.trace ((E m)^2) =
      (Fintype.card G : ℝ) * ∑ j ∈ Finset.range (m+1),
        (13 : ℝ)^j * ∑ r ∈ Finset.range (m-j+1), (C (2*r) : ℝ) := by
  have hs := congrArg (fun p : Polynomial ℝ => aeval A p) (P_square m)
  simp only [map_pow, map_sum, map_mul, map_ofNat] at hs
  change (E m)^2 = ∑ j ∈ Finset.range (m+1), (13 : Mat)^j * E (2*m-2*j) at hs
  rw [hs, Matrix.trace_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [trace_thirteen_pow_mul, trace_evalP]
  have hmod : (2*m-2*j)%2 = 0 := by omega
  have hdiv : (2*m-2*j)/2 = m-j := by omega
  simp only [hmod, hdiv, zero_add]
  ring

end OPG37364.Trace13

namespace OPG37364

/-- The square is a matrix square. Counts are of adjacent-reduced closed generator words,
and the vertex-cardinality factor is retained explicitly. -/
theorem _root_.solution
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q) (m : ℕ) :
    Matrix.trace
      ((Polynomial.aeval ((lps13Graph hq i).adjMatrix ℝ)
        (lps13NonbacktrackingPolynomial m))^2) =
      (Fintype.card (LPS13Vertex q) : ℝ) * ∑ j ∈ Finset.range (m+1),
        (13 : ℝ)^j * ∑ r ∈ Finset.range (m-j+1),
          (lps13ClosedReducedWordCount hq i (2*r) : ℝ) :=
  Trace13.squared_trace hq i m

end OPG37364

end Stage16Source3

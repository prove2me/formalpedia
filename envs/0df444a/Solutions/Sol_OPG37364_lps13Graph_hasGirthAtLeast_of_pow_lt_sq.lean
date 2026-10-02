-- Prove2me | solution 1 for OPG37364.lps13Graph_hasGirthAtLeast_of_pow_lt_sq
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-11T00:23:53.174742+00:00
-- url     : https://prove2.me/submissions/d9ab554c-297f-478c-8ada-7c0717562395

import Definitions.Def_opg37364_lps13_words
import Theorems.Thm_OPG37364_lps13_reduced_word_not_all_coords_dvd13

set_option autoImplicit false
open scoped Quaternion

namespace OPG37364

-- Exact reused Stage 7 proof helpers; no new graph conventions.
theorem lps13Quaternion_conj (a : Fin 14) :
    lps13Quaternion (lps13ConjIndex a) = star (lps13Quaternion a) := by
  fin_cases a <;> rfl


section
variable {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
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


end

-- Complete Stage 11 norm proof, not a separate platform theorem.
theorem lps13WordProduct_norm (w : List (Fin 14)) :
    Quaternion.normSq (lps13WordProduct w) = (13 : ℤ) ^ w.length := by
  induction w with
  | nil => simp [lps13WordProduct]
  | cons a w ih =>
    simpa [lps13WordProduct, map_mul, lps13Quaternion_norm, pow_succ, mul_comm] using
      congrArg (fun z : ℤ => 13 * z) ih


end OPG37364

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

namespace OPG37364
namespace Girth13

theorem word_im_nonzero (w : List (Fin 14)) (hne : w ≠ [])
    (hr : lps13WordReduced w) :
    (lps13WordProduct w).imI ≠ 0 ∨ (lps13WordProduct w).imJ ≠ 0 ∨
      (lps13WordProduct w).imK ≠ 0 := by
  by_contra h
  push Not at h
  have hn := lps13WordProduct_norm w
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
  rw [lps13QuaternionMatrix_det, lps13WordProduct_norm]
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
  have hn := lps13WordProduct_norm w
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
theorem _root_.solution
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


end OPG37364

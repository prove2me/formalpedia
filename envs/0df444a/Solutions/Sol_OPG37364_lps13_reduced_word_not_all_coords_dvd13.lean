-- Prove2me | solution 1 for OPG37364.lps13_reduced_word_not_all_coords_dvd13
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-10T12:13:56.035015+00:00
-- url     : https://prove2.me/submissions/eff9b353-2b19-4fdc-860f-06240a14b8fa

import Definitions.Def_opg37364_lps13_words

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
theorem _root_.solution
    (w : List (Fin 14)) (h : lps13WordReduced w) :
    ¬ ((13 : ℤ) ∣ (lps13WordProduct w).re ∧
      13 ∣ (lps13WordProduct w).imI ∧ 13 ∣ (lps13WordProduct w).imJ ∧
      13 ∣ (lps13WordProduct w).imK) := by
  intro hd
  exact WordPrimitivity.theta_word_ne_zero w h (WordPrimitivity.theta_zero_of_dvd _ hd)

theorem lps13WordProduct_norm (w : List (Fin 14)) :
    Quaternion.normSq (lps13WordProduct w) = (13 : ℤ) ^ w.length := by
  induction w with
  | nil => simp [lps13WordProduct]
  | cons a w ih =>
    simpa [lps13WordProduct, map_mul, lps13Quaternion_norm, pow_succ, mul_comm] using
      congrArg (fun z : ℤ => 13 * z) ih

end OPG37364

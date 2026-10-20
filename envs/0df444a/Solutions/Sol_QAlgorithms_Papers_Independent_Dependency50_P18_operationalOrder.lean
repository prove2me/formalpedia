-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P18.operationalOrder
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:58:12.785411+00:00
-- url     : https://prove2.me/submissions/032e4c86-ab3e-416b-80ac-9d9e6f530cd8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

lemma h54d_oneShot_mono {A B : Type} (eps : ℝ) (rho : Matrix (A × B) (A × B) ℂ) :
    oneShot false eps rho ≤ oneShot true eps rho := by
  unfold oneShot
  apply sSup_le_sSup
  rintro r ⟨d, hd, P, hP, _, hf, hr⟩
  exact ⟨d, hd, P, hP, Or.inl rfl, hf, hr⟩

lemma h54d_rate_mono {A B : Type} (eps : ℝ) (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) :
    randomnessBlockRate false eps rho n ≤ randomnessBlockRate true eps rho n := by
  unfold randomnessBlockRate
  apply mul_le_mul_of_nonneg_left (h54d_oneShot_mono _ _)
  apply EReal.inv_nonneg_of_nonneg
  exact_mod_cast (Nat.cast_nonneg (n + 1) : (0:ℝ) ≤ ((n+1 : ℕ) : ℝ))

lemma h54d_ord_le_sc {A B : Type} (t : Bool) (rho : Matrix (A × B) (A × B) ℂ) :
    ordinaryRate t rho ≤ strongConverseRate t rho := by
  unfold ordinaryRate strongConverseRate
  have h1 : sInf {r | ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      r = Filter.liminf (randomnessBlockRate t eps rho) Filter.atTop} ≤
      Filter.liminf (randomnessBlockRate t (1/2) rho) Filter.atTop :=
    sInf_le ⟨1/2, by norm_num, by norm_num, rfl⟩
  have h2 : Filter.limsup (randomnessBlockRate t (1/2) rho) Filter.atTop ≤
      sSup {r | ∃ eps : ℝ, 0 ≤ eps ∧ eps < 1 ∧
      r = Filter.limsup (randomnessBlockRate t eps rho) Filter.atTop} :=
    le_sSup ⟨1/2, by norm_num, by norm_num, rfl⟩
  exact h1.trans ((Filter.liminf_le_limsup (f := Filter.atTop)).trans h2)

theorem solution (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) (eps : ℝ)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    oneShot false eps rho ≤ oneShot true eps rho ∧
    ordinaryRate false rho ≤ ordinaryRate true rho ∧
    strongConverseRate false rho ≤ strongConverseRate true rho ∧
    ordinaryRate false rho ≤ strongConverseRate false rho ∧
    ordinaryRate true rho ≤ strongConverseRate true rho := by
  refine ⟨h54d_oneShot_mono _ _, ?_, ?_, h54d_ord_le_sc _ _, h54d_ord_le_sc _ _⟩
  · unfold ordinaryRate
    apply le_sInf
    rintro r ⟨e, he0, he1, rfl⟩
    exact (sInf_le (s := {r | ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      r = Filter.liminf (randomnessBlockRate false eps rho) Filter.atTop}) ⟨e, he0, he1, rfl⟩).trans
      (Filter.liminf_le_liminf (Filter.Eventually.of_forall (h54d_rate_mono e rho)))
  · unfold strongConverseRate
    apply sSup_le
    rintro r ⟨e, he0, he1, rfl⟩
    exact (Filter.limsup_le_limsup (Filter.Eventually.of_forall (h54d_rate_mono e rho))).trans
      (le_sSup (s := {r | ∃ eps : ℝ, 0 ≤ eps ∧ eps < 1 ∧
      r = Filter.limsup (randomnessBlockRate true eps rho) Filter.atTop}) ⟨e, he0, he1, rfl⟩)

end

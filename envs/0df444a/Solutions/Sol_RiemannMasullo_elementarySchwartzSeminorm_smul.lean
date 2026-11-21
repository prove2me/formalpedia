-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartzSeminorm_smul
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:04:09.75218+00:00
-- url     : https://prove2.me/submissions/53a6f444-25eb-4191-9793-16f193ffbe05

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L396-L399
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzSubmodule
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}
private theorem bound_smul {f : ElementaryLieGroup m n r F → ℂ} (c : ℂ)
    (hf : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) (i : ElementarySchwartzIndex m n r) :
    elementarySchwartzBound (c • f) i = (‖c‖₊ : ℝ≥0∞) * elementarySchwartzBound f i := by
  let E := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let dirs : List E :=
    (List.ofFn (fun k : Fin m ↦ List.replicate (i.2.1 k) (EuclideanSpace.single k 1, 0))).flatten ++
    (List.ofFn (fun k : Fin n ↦ List.replicate (i.2.2.1 k) (0, EuclideanSpace.single k 1))).flatten
  let M (x : E) (a : Fin r → ℤ) : ℂ :=
    (∏ k, (x.1 k : ℂ)^i.1 k) * ∏ k, (a k : ℂ)^i.2.2.2 k
  let term (h : ElementaryLieGroup m n r F → ℂ) (x : E) (a : Fin r → ℤ) (b : F) : ℂ :=
    M x a * iteratedFDeriv ℝ dirs.length (fun v ↦ h (elementaryCover v a b)) x dirs.get
  unfold elementarySchwartzBound
  simp_rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro x
  apply iSup_congr
  intro a
  apply iSup_congr
  intro b
  change (‖term (c • f) x a b‖₊ : ℝ≥0∞) = (‖c‖₊ : ℝ≥0∞) * ‖term f x a b‖₊
  have he : term (c • f) x a b = c * term f x a b := by
    unfold term
    have hd := iteratedFDeriv_const_smul_apply (a := c) (x := x)
      (((hf a b).of_le (show (dirs.length : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast (le_top : (dirs.length : ℕ∞) ≤ ⊤))).contDiffAt)
    change M x a * iteratedFDeriv ℝ dirs.length
      (c • (fun v ↦ f (elementaryCover v a b))) x dirs.get = _
    rw [hd, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    ring
  rw [he, nnnorm_mul, ENNReal.coe_mul]


theorem solution (i : ElementarySchwartzIndex m n r)
    (c : ℂ) (f : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (c • f).val i).toReal =
      ‖c‖ * (elementarySchwartzBound f.val i).toReal := by
  change (elementarySchwartzBound (c • f.val) i).toReal = _
  rw [bound_smul c f.property.1 i, ENNReal.toReal_mul]
  rfl

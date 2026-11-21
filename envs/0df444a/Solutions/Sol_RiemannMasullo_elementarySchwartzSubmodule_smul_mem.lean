-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartzSubmodule_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:01:00.77298+00:00
-- url     : https://prove2.me/submissions/f4321f49-c585-40f6-9d70-beb55c0338bc

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L351-L355
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}
theorem solution (c : ℂ) {f : ElementaryLieGroup m n r F → ℂ}
    (hf : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)) :
    c • f ∈ {h | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ h (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound h i < (⊤ : ℝ≥0∞)} := by
  constructor
  · exact fun a b ↦ (hf.1 a b).const_smul c
  intro i
  let E := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let dirs : List E :=
    (List.ofFn (fun k : Fin m ↦ List.replicate (i.2.1 k) (EuclideanSpace.single k 1, 0))).flatten ++
    (List.ofFn (fun k : Fin n ↦ List.replicate (i.2.2.1 k) (0, EuclideanSpace.single k 1))).flatten
  let M (x : E) (a : Fin r → ℤ) : ℂ :=
    (∏ k, (x.1 k : ℂ)^i.1 k) * ∏ k, (a k : ℂ)^i.2.2.2 k
  let term (h : ElementaryLieGroup m n r F → ℂ) (x : E) (a : Fin r → ℤ) (b : F) : ℂ :=
    M x a * iteratedFDeriv ℝ dirs.length (fun v ↦ h (elementaryCover v a b)) x dirs.get
  have bound (h : ElementaryLieGroup m n r F → ℂ) (x : E) (a : Fin r → ℤ) (b : F) :
      (‖term h x a b‖₊ : ℝ≥0∞) ≤ elementarySchwartzBound h i :=
    le_iSup_of_le x (le_iSup_of_le a (le_iSup_of_le b le_rfl))
  apply lt_of_le_of_lt _ (ENNReal.mul_lt_top (ENNReal.coe_lt_top (r := ‖c‖₊)) (hf.2 i))
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  change (‖term (c • f) x a b‖₊ : ℝ≥0∞) ≤ (‖c‖₊ : ℝ≥0∞) * elementarySchwartzBound f i
  have he : term (c • f) x a b = c * term f x a b := by
    unfold term
    have hd := iteratedFDeriv_const_smul_apply (a := c) (x := x)
      (((hf.1 a b).of_le (show (dirs.length : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast (le_top : (dirs.length : ℕ∞) ≤ ⊤))).contDiffAt)
    change M x a * iteratedFDeriv ℝ dirs.length
      (c • (fun v ↦ f (elementaryCover v a b))) x dirs.get = _
    rw [hd, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    ring
  rw [he, nnnorm_mul, ENNReal.coe_mul]
  exact mul_le_mul_of_nonneg_left (bound f x a b) (by positivity)


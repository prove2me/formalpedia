-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartzSubmodule_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T01:57:59.525059+00:00
-- url     : https://prove2.me/submissions/7ceb4207-51fe-4d13-b366-f6d2547d1db7

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L341-L347
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}
theorem solution {f g : ElementaryLieGroup m n r F → ℂ}
    (hf : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞))
    (hg : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ g (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound g i < (⊤ : ℝ≥0∞)) :
    f + g ∈ {h | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ h (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound h i < (⊤ : ℝ≥0∞)} := by
  constructor
  · exact fun a b ↦ (hf.1 a b).add (hg.1 a b)
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
  apply lt_of_le_of_lt _ (ENNReal.add_lt_top.mpr ⟨hf.2 i, hg.2 i⟩)
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  change (‖term (f+g) x a b‖₊ : ℝ≥0∞) ≤ _
  have he : term (f+g) x a b = term f x a b + term g x a b := by
    unfold term
    have hd := iteratedFDeriv_add_apply (x := x)
      (((hf.1 a b).of_le (show (dirs.length : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast (le_top : (dirs.length : ℕ∞) ≤ ⊤))).contDiffAt)
      (((hg.1 a b).of_le (show (dirs.length : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast (le_top : (dirs.length : ℕ∞) ≤ ⊤))).contDiffAt)
    change M x a * iteratedFDeriv ℝ dirs.length
      ((fun v ↦ f (elementaryCover v a b)) + (fun v ↦ g (elementaryCover v a b))) x dirs.get = _
    rw [hd, ContinuousMultilinearMap.add_apply, mul_add]
  rw [he]
  exact (ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _)).trans (by
    simpa only [ENNReal.coe_add] using add_le_add (bound f x a b) (bound g x a b))


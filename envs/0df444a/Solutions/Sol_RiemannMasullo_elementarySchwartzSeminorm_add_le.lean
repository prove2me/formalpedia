-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartzSeminorm_add_le
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:04:08.961375+00:00
-- url     : https://prove2.me/submissions/daad46d5-ffae-4ec3-8046-4e3165fc635f

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L388-L392
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzSubmodule
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*}
private theorem bound_add {f g : ElementaryLieGroup m n r F → ℂ}
    (hf : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b)))
    (hg : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ g (elementaryCover xt a b)))
    (i : ElementarySchwartzIndex m n r) :
    elementarySchwartzBound (f+g) i ≤ elementarySchwartzBound f i + elementarySchwartzBound g i := by
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
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  change (‖term (f+g) x a b‖₊ : ℝ≥0∞) ≤ _
  have he : term (f+g) x a b = term f x a b + term g x a b := by
    unfold term
    have hd := iteratedFDeriv_add_apply (x := x)
      (((hf a b).of_le (show (dirs.length : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast (le_top : (dirs.length : ℕ∞) ≤ ⊤))).contDiffAt)
      (((hg a b).of_le (show (dirs.length : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast (le_top : (dirs.length : ℕ∞) ≤ ⊤))).contDiffAt)
    change M x a * iteratedFDeriv ℝ dirs.length
      ((fun v ↦ f (elementaryCover v a b)) + (fun v ↦ g (elementaryCover v a b))) x dirs.get = _
    rw [hd, ContinuousMultilinearMap.add_apply, mul_add]
  rw [he]
  exact (ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _)).trans (by
    simpa only [ENNReal.coe_add] using add_le_add (bound f x a b) (bound g x a b))

theorem solution (i : ElementarySchwartzIndex m n r)
    (f g : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (f + g).val i).toReal ≤
      (elementarySchwartzBound f.val i).toReal + (elementarySchwartzBound g.val i).toReal :=
  by
  rw [← ENNReal.toReal_add (f.property.2 i).ne (g.property.2 i).ne]
  exact ENNReal.toReal_mono (ENNReal.add_lt_top.mpr ⟨f.property.2 i, g.property.2 i⟩).ne
    (bound_add f.property.1 g.property.1 i)

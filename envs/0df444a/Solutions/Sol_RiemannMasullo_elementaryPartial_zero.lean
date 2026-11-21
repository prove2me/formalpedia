-- Prove2me | solution 1 for RiemannMasullo.elementaryPartial_zero
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T01:41:40.030051+00:00
-- url     : https://prove2.me/submissions/4c558a30-19b8-4f92-8fbf-d0145bb7aa04

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L296-L298
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
theorem solution (f : ElementaryLieGroup m n r F → ℂ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    elementaryPartial f 0 0 xt a b = f (elementaryCover xt a b) := by
  classical
  let E := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  have h (k : ℕ) : (List.ofFn (fun _ : Fin k ↦ ([] : List E))).flatten = [] := by
    apply List.flatten_eq_nil_iff.mpr
    simp
  let dirs : List E :=
    (List.ofFn (fun i : Fin m ↦ List.replicate (0 : ℕ) (EuclideanSpace.single i 1, 0))).flatten ++
    (List.ofFn (fun i : Fin n ↦ List.replicate (0 : ℕ) (0, EuclideanSpace.single i 1))).flatten
  change iteratedFDeriv ℝ dirs.length (fun v ↦ f (elementaryCover v a b)) xt dirs.get = _
  have hd : dirs = [] := by
    change (List.ofFn (fun _ : Fin m ↦ ([] : List E))).flatten ++
      (List.ofFn (fun _ : Fin n ↦ ([] : List E))).flatten = []
    simp only [h m, h n, List.nil_append]
  have eval (l : List E) (hl : l = []) :
      iteratedFDeriv ℝ l.length (fun v ↦ f (elementaryCover v a b)) xt l.get =
        f (elementaryCover xt a b) := by
    subst l
    rfl
  exact eval dirs hd

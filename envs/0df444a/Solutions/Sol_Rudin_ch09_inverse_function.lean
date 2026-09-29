-- Prove2me | solution 1 for Rudin.ch09_inverse_function
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:38:58.84433+00:00
-- url     : https://prove2.me/submissions/e066e366-3697-41bd-a7a4-c79f5f87b8a9

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NormNum
open Filter Topology


/-- Rudin, Theorem 9.24 (inverse function theorem): let `f` be a `C'`-mapping of an open set
`E ⊆ ℝⁿ` into `ℝⁿ` whose derivative at `a ∈ E` is invertible.  Then there are open sets
`U ∋ a` and `V ∋ f a` such that `f` is one-to-one on `U` with `f(U) = V`, and the inverse
mapping `g` of `f` restricted to `U` is a `C'`-mapping on `V`. -/
theorem solution (n : ℕ) (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsOpen E)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : ContDiffOn ℝ 1 f E)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ E)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : HasFDerivAt f A a)
    (hAinv : Function.Bijective A) :
    ∃ (U V : Set (EuclideanSpace ℝ (Fin n)))
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ U ⊆ E ∧ f a ∈ V ∧ Set.InjOn f U ∧ f '' U = V ∧
        (∀ x ∈ U, g (f x) = x) ∧ (∀ y ∈ V, f (g y) = y) ∧ ContDiffOn ℝ 1 g V := by
  let eA := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hAinv.1) (LinearMap.range_eq_top.mpr hAinv.2)
  have hAe : HasFDerivAt f (eA : _ →L[ℝ] _) a := by
    simpa only [eA,ContinuousLinearEquiv.coe_ofBijective] using hA
  have hfa : ContDiffAt ℝ 1 f a := hf.contDiffAt (hE.mem_nhds ha)
  let e := hfa.toOpenPartialHomeomorph f hAe (by norm_num)
  have hea : a ∈ e.source := hfa.mem_toOpenPartialHomeomorph_source hAe (by norm_num)
  have hg : ContDiffAt ℝ 1 (e.symm : _ → _) (f a) := hfa.to_localInverse hAe (by norm_num)
  obtain ⟨W,hW,hgW⟩ := hg.contDiffOn (le_refl 1) (by norm_num)
  let e0 := e.restrOpen E hE
  let e1 := (e0.symm.restrOpen (interior W) isOpen_interior).symm
  have ha0 : a ∈ e0.source := ⟨hea,ha⟩
  have hfaint : f a ∈ interior W := mem_interior_iff_mem_nhds.mpr hW
  have hfa1 : f a ∈ e1.target := ⟨e0.mapsTo ha0,hfaint⟩
  have ha1 : a ∈ e1.source := by
    have hh := e1.symm.mapsTo hfa1
    change e.symm (f a) ∈ e1.source at hh
    have heq : e.symm (f a) = a := e.left_inv hea
    rwa [heq] at hh
  refine ⟨e1.source,e1.target,e1.symm,e1.open_source,e1.open_target,ha1,?_,hfa1,?_,?_,?_,?_,?_⟩
  · intro x hx
    exact hx.1.2
  · exact e1.injOn
  · exact e1.image_source_eq_target
  · exact fun x hx => e1.left_inv hx
  · exact fun y hy => e1.right_inv hy
  · exact hgW.mono (fun y hy => interior_subset hy.2)



#print axioms solution

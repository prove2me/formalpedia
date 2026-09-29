-- Prove2me | solution 1 for Rudin.ch09_implicit_function
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T20:24:22.870846+00:00
-- url     : https://prove2.me/submissions/1e7dc7d6-f124-47a6-9471-d31c3588902d

import Mathlib
set_option autoImplicit false
open Filter Topology
theorem solution (n m : ℕ)
    (E : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))) (hE : IsOpen E)
    (f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (hf : ContDiffOn ℝ 1 f E)
    (a : EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin m)) (hab : (a, b) ∈ E)
    (hfab : f (a, b) = 0)
    (A : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : HasFDerivAt f A (a, b))
    (hAx : Function.Bijective fun h : EuclideanSpace ℝ (Fin n) => A (h, 0)) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)))
      (W : Set (EuclideanSpace ℝ (Fin m)))
      (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)),
      IsOpen U ∧ IsOpen W ∧ (a, b) ∈ U ∧ U ⊆ E ∧ b ∈ W ∧ ContDiffOn ℝ 1 g W ∧ g b = a ∧
        ∀ y ∈ W, (g y, y) ∈ U ∧ f (g y, y) = 0 ∧
          ∀ x : EuclideanSpace ℝ (Fin n), (x, y) ∈ U → f (x, y) = 0 → x = g y := by
  let F := fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) => f (p.2, p.1)
  have hc : ContDiffAt ℝ 1 F (b, a) :=
    (hf.contDiffAt (hE.mem_nhds hab)).comp (b, a) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hd : HasFDerivAt F
      (A.comp ((ContinuousLinearMap.snd ℝ _ _).prod (ContinuousLinearMap.fst ℝ _ _))) (b, a) :=
    hA.comp (b, a) (hasFDerivAt_snd.prodMk hasFDerivAt_fst)
  have hi : (fderiv ℝ F (b, a) ∘L ContinuousLinearMap.inr ℝ _ _).IsInvertible := by
    rw [hd.fderiv]
    let B := A.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
    let e := ContinuousLinearEquiv.ofBijective B
      (LinearMap.ker_eq_bot.mpr hAx.1) (LinearMap.range_eq_top.mpr hAx.2)
    refine ⟨e, ?_⟩
    ext x
    rfl
  let g := hc.implicitFunction (by norm_num) hi
  have hgb : g b = a := hc.implicitFunction_apply_self (by norm_num) hi
  have hgc : ContDiffAt ℝ 1 g b := hc.contDiffAt_implicitFunction (by norm_num) hi
  have heq : ∀ᶠ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) in 𝓝 (a, b),
      f p = 0 ↔ g p.2 = p.1 := by
    have ht : Tendsto (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) => (p.2, p.1))
        (𝓝 (a, b)) (𝓝 (b, a)) := (continuousAt_snd.prodMk continuousAt_fst).tendsto
    have hh := ht (hc.eventually_apply_eq_iff_implicitFunction (by norm_num) hi)
    filter_upwards [hh] with p hp
    change f p = f (a, b) ↔ g p.2 = p.1 at hp
    simpa only [hfab] using hp
  obtain ⟨U, hUs, hU, habU⟩ := mem_nhds_iff.mp (heq.and (hE.mem_nhds hab))
  have hUE : U ⊆ E := fun p hp => (hUs hp).2
  obtain ⟨V, hV, hgV⟩ := hgc.contDiffOn (le_refl 1) (by norm_num)
  have hgraph : Tendsto (fun y => (g y, y)) (𝓝 b) (𝓝 (a, b)) := by
    simpa [hgb] using hgc.continuousAt.tendsto.prodMk_nhds tendsto_id
  obtain ⟨W, hWs, hW, hbW⟩ := mem_nhds_iff.mp
    (Filter.inter_mem hV (hgraph (hU.mem_nhds habU)))
  refine ⟨U, W, g, hU, hW, habU, hUE, hbW, hgV.mono (fun y hy => (hWs hy).1), hgb, ?_⟩
  intro y hy
  have hgy : (g y, y) ∈ U := (hWs hy).2
  refine ⟨hgy, (hUs hgy).1.mpr rfl, ?_⟩
  intro x hxy hzero
  exact ((hUs hxy).1.mp hzero).symm
#print axioms solution

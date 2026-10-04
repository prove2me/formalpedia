-- Prove2me | solution 1 for PolyakovAction.wave_equation_lightcone_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T08:33:28.433432+00:00
-- url     : https://prove2.me/submissions/798aff32-3ca8-45f6-8fb2-c47428574d2a

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

set_option autoImplicit false

open PolyakovAction in
theorem solution {D : ℕ} (X : Worldsheet → Spacetime D)
    (hX : ContDiff ℝ 2 X)
    (hwave : ∀ σ : Worldsheet, ∀ μ : Fin D,
      secondPartialDeriv X 0 0 μ σ - secondPartialDeriv X 1 1 μ σ = 0) :
    ∃ XL XR : ℝ → Spacetime D, ContDiff ℝ 2 XL ∧ ContDiff ℝ 2 XR ∧
      ∀ τ s : ℝ, X ![τ, s] = XL (τ + s) + XR (τ - s) := by
  have hdiff : Differentiable ℝ X := hX.differentiable (by norm_num)
  have hF : ContDiff ℝ 1 (fderiv ℝ X) := hX.fderiv_right (by norm_num)
  have hFd : Differentiable ℝ (fderiv ℝ X) := hF.differentiable (by norm_num)
  have hsymm : ∀ σ v w, fderiv ℝ (fderiv ℝ X) σ v w = fderiv ℝ (fderiv ℝ X) σ w v := by
    intro σ v w
    exact (hX.contDiffAt.isSymmSndFDerivAt (by simp)) v w
  have hsec : ∀ σ a b μ, secondPartialDeriv X a b μ σ =
      fderiv ℝ (fderiv ℝ X) σ (Pi.single a 1) (Pi.single b 1) μ := by
    intro σ a b μ
    unfold secondPartialDeriv
    rw [fderiv_clm_apply (hFd σ) (differentiableAt_const _)]
    simp
  have hw : ∀ σ, fderiv ℝ (fderiv ℝ X) σ (Pi.single 0 1) (Pi.single 0 1) =
      fderiv ℝ (fderiv ℝ X) σ (Pi.single 1 1) (Pi.single 1 1) := by
    intro σ; funext μ
    have := hwave σ μ
    rw [hsec, hsec] at this
    linarith
  set ep : Worldsheet := ![1/2, 1/2] with hep
  set em : Worldsheet := ![1/2, -1/2] with hem
  have h1 : ep = (1/2:ℝ) • ((Pi.single 0 1 : Worldsheet) + Pi.single 1 1) := by
    ext i; fin_cases i <;> simp [hep]
  have h2 : em = (1/2:ℝ) • ((Pi.single 0 1 : Worldsheet) - Pi.single 1 1) := by
    ext i; fin_cases i <;> simp [hem] <;> norm_num
  have hmix : ∀ σ, fderiv ℝ (fderiv ℝ X) σ em ep = 0 := by
    intro σ
    rw [h1, h2]
    simp only [map_smul, map_add, map_sub, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
    rw [hw σ, hsymm σ (Pi.single 1 1) (Pi.single 0 1)]
    rw [← smul_add, sub_add_sub_cancel, sub_self, smul_zero, smul_zero]
  let A : ℝ → ℝ → Worldsheet := fun u v => u • ep + v • em
  have hAv : ∀ u v, HasDerivAt (fun v => A u v) em v := by
    intro u v
    have := ((hasDerivAt_id' v).smul_const em).const_add (u • ep)
    rw [one_smul] at this
    exact this
  have hAu : ∀ u v, HasDerivAt (fun u => A u v) ep u := by
    intro u v
    have := ((hasDerivAt_id' u).smul_const ep).add_const (v • em)
    rw [one_smul] at this
    exact this
  -- step 4: the ep-derivative is independent of v
  have hP : ∀ u v, fderiv ℝ X (A u v) ep = fderiv ℝ X (A u 0) ep := by
    intro u
    have hd : ∀ v, HasDerivAt (fun v => fderiv ℝ X (A u v) ep)
        (fderiv ℝ (fderiv ℝ X) (A u v) em ep) v := by
      intro v
      have hc := (hFd (A u v)).hasFDerivAt.comp_hasDerivAt v (hAv u v)
      have := (ContinuousLinearMap.apply ℝ (Spacetime D) ep).hasFDerivAt.comp_hasDerivAt v hc
      exact this
    have key := is_const_of_deriv_eq_zero (f := fun v => fderiv ℝ X (A u v) ep)
      (fun v => (hd v).differentiableAt) (fun v => by rw [(hd v).deriv, hmix])
    intro v
    exact key v 0
  -- step 5
  have hZ : ∀ u v, X (A u v) - X (A u 0) = X (A 0 v) - X (A 0 0) := by
    intro u v
    have hd : ∀ u, HasDerivAt (fun u => X (A u v) - X (A u 0))
        (fderiv ℝ X (A u v) ep - fderiv ℝ X (A u 0) ep) u := by
      intro u
      exact ((hdiff (A u v)).hasFDerivAt.comp_hasDerivAt u (hAu u v)).sub
        ((hdiff (A u 0)).hasFDerivAt.comp_hasDerivAt u (hAu u 0))
    have key := is_const_of_deriv_eq_zero (f := fun u => X (A u v) - X (A u 0))
      (fun u => (hd u).differentiableAt) (fun u => by rw [(hd u).deriv, hP u v, sub_self])
    exact key u 0
  have hAc : ∀ v, ContDiff ℝ 2 (fun u : ℝ => A u v) := fun v =>
    (contDiff_id.smul contDiff_const).add contDiff_const
  have hAc' : ∀ u, ContDiff ℝ 2 (fun v : ℝ => A u v) := fun u =>
    contDiff_const.add (contDiff_id.smul contDiff_const)
  refine ⟨fun w => X (A w 0), fun w => X (A 0 w) - X (A 0 0),
    hX.comp (hAc 0), (hX.comp (hAc' 0)).sub contDiff_const, ?_⟩
  intro τ s
  have hA : A (τ + s) (τ - s) = ![τ, s] := by
    ext i; fin_cases i <;> simp [A, hep, hem] <;> ring
  rw [← hA]
  have := hZ (τ + s) (τ - s)
  simp only at this ⊢
  rw [← this]
  abel

-- Prove2me | solution 1 for SteerableE2CNN.steerable_conv_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T12:42:24.420685+00:00
-- url     : https://prove2.me/submissions/abbab512-5754-4590-9bfc-f5613a4b0849

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic
set_option autoImplicit false
open Matrix MeasureTheory
namespace SteerableE2CNN

theorem steerable_conv_equivariant (G : Subgroup O2)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ρin : MatRep G n) (ρout : MatRep G m) (k : Plane → Matrix m n ℝ)
    (hk : IsSteerable G ρin ρout k) (f : Plane → n → ℝ)
    (hf : ∀ x : Plane, Integrable (fun y : Plane => k y *ᵥ f (x + y))) (t : Plane) (g : G) :
    steerConv k (indAct G ρin t g f) = indAct G ρout t g (steerConv k f) := by
  set Gm : Matrix (Fin 2) (Fin 2) ℝ := gMat g with hGm
  set Gi : Matrix (Fin 2) (Fin 2) ℝ := gMat g⁻¹ with hGi
  have hGG : Gi * Gm = 1 := by
    simp only [hGi, hGm, gMat]
    rw [← Submonoid.coe_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hGG' : Gm * Gi = 1 := by
    simp only [hGi, hGm, gMat]
    rw [← Submonoid.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hR : (repMat ρin g)⁻¹ * repMat ρin g = 1 := by
    have h : ((ρin g)⁻¹ : Matrix.GeneralLinearGroup n ℝ).val * (ρin g).val = 1 := (ρin g).inv_mul
    have h2 : (repMat ρin g)⁻¹ = ((ρin g)⁻¹ : Matrix.GeneralLinearGroup n ℝ).val :=
      Matrix.inv_eq_left_inv h
    rw [h2]; exact h
  have hdet : Gm.det * Gm.det = 1 := by
    have hm : Gm ∈ Matrix.orthogonalGroup (Fin 2) ℝ := ((g : O2)).2
    rw [Matrix.mem_orthogonalGroup_iff'] at hm
    have := congrArg Matrix.det hm
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  let e : Plane ≃ᵐ Plane :=
    { toFun := fun z => Gm *ᵥ z
      invFun := fun z => Gi *ᵥ z
      left_inv := fun z => by simp only [Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]
      right_inv := fun z => by simp only [Matrix.mulVec_mulVec, hGG', Matrix.one_mulVec]
      measurable_toFun := (Matrix.toLin' Gm).continuous_of_finiteDimensional.measurable
      measurable_invFun := (Matrix.toLin' Gi).continuous_of_finiteDimensional.measurable }
  have hmp : MeasurePreserving e volume volume := by
    refine ⟨e.measurable, ?_⟩
    have hd : LinearMap.det (Matrix.toLin' Gm) ≠ 0 := by
      rw [LinearMap.det_toLin']; intro h; rw [h] at hdet; simp at hdet
    have := Real.map_linearMap_volume_pi_eq_smul_volume_pi hd
    have he : (e : Plane → Plane) = Matrix.toLin' Gm := by
      funext z; rfl
    rw [he, this, LinearMap.det_toLin']
    have habs : |(Gm.det)⁻¹| = 1 := by
      have : |Gm.det| * |Gm.det| = 1 := by rw [← abs_mul, hdet, abs_one]
      have hpos : 0 ≤ |Gm.det| := abs_nonneg _
      have h1 : |Gm.det| = 1 := by nlinarith
      rw [abs_inv, h1, inv_one]
    rw [habs, ENNReal.ofReal_one, one_smul]
  funext x
  unfold steerConv indAct
  rw [← hmp.integral_comp' (fun y => k y *ᵥ (repMat ρin g *ᵥ f (Gi *ᵥ (x + y - t))))]
  have hpt : ∀ z : Plane, k (e z) *ᵥ (repMat ρin g *ᵥ f (Gi *ᵥ (x + e z - t))) =
      repMat ρout g *ᵥ (k z *ᵥ f (Gi *ᵥ (x - t) + z)) := by
    intro z
    have hez : e z = Gm *ᵥ z := rfl
    rw [hez, hk g z]
    have : x + Gm *ᵥ z - t = (x - t) + Gm *ᵥ z := by abel
    rw [this, Matrix.mulVec_add, Matrix.mulVec_mulVec z Gi Gm, hGG, Matrix.one_mulVec]
    set w := f (Gi *ᵥ (x - t) + z)
    rw [Matrix.mulVec_mulVec w _ (repMat ρin g), Matrix.mul_assoc (repMat ρout g * k z),
      hR, Matrix.mul_one, Matrix.mulVec_mulVec]
  simp only [hpt]
  let L : (m → ℝ) →L[ℝ] (m → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin (repMat ρout g))
  have hL : ∀ v, L v = repMat ρout g *ᵥ v := fun v => rfl
  simp only [← hL]
  exact L.integral_comp_comm (hf (Gi *ᵥ (x - t)))

end SteerableE2CNN
open SteerableE2CNN in
theorem solution (G : Subgroup O2)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ρin : MatRep G n) (ρout : MatRep G m) (k : Plane → Matrix m n ℝ)
    (hk : IsSteerable G ρin ρout k) (f : Plane → n → ℝ)
    (hf : ∀ x : Plane, Integrable (fun y : Plane => k y *ᵥ f (x + y))) (t : Plane) (g : G) :
    steerConv k (indAct G ρin t g f) = indAct G ρout t g (steerConv k f) :=
  steerable_conv_equivariant G ρin ρout k hk f hf t g

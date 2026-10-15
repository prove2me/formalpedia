-- Prove2me | solution 1 for Plasticity.Topology.isOpen_image_of_injOn_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:38:06.007959+00:00
-- url     : https://prove2.me/submissions/3e76e7fd-bd24-4b0c-a7e2-3064bffe1997

import Theorems.Thm_Plasticity_Ext_InvarianceOfDomain
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousOn

namespace Sol_Plasticity_Topology_isOpen_image_of_injOn_of_finrank_eq

end Sol_Plasticity_Topology_isOpen_image_of_injOn_of_finrank_eq

theorem solution {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W)
    (U : Set V) (hU : IsOpen U) (f : V → W) (hf : ContinuousOn f U) (hinj : Set.InjOn f U) :
    IsOpen (f '' U) := by
  set n := Module.finrank ℝ V with hn
  let eV : V ≃L[ℝ] (Fin n → ℝ) :=
    (LinearEquiv.ofFinrankEq V (Fin n → ℝ) (by simp [hn])).toContinuousLinearEquiv
  let eW : W ≃L[ℝ] (Fin n → ℝ) :=
    (LinearEquiv.ofFinrankEq W (Fin n → ℝ) (by simp [hn, ← hdim])).toContinuousLinearEquiv
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun y => eW (f (eV.symm y))
  have hU' : IsOpen (eV.symm ⁻¹' U) := hU.preimage eV.symm.continuous
  have hg : ContinuousOn g (eV.symm ⁻¹' U) :=
    eW.continuous.comp_continuousOn (hf.comp eV.symm.continuous.continuousOn (fun y hy => hy))
  have hginj : Set.InjOn g (eV.symm ⁻¹' U) := by
    intro y₁ h₁ y₂ h₂ h
    exact eV.symm.injective (hinj h₁ h₂ (eW.injective h))
  have hopen := Plasticity.Ext.InvarianceOfDomain _ hU' g hg hginj
  have heq : f '' U = eW ⁻¹' (g '' (eV.symm ⁻¹' U)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨eV x, by simpa using hx, by simp [g]⟩
    · rintro ⟨y, hy, hyz⟩
      exact ⟨eV.symm y, hy, eW.injective hyz⟩
  rw [heq]
  exact hopen.preimage eW.continuous

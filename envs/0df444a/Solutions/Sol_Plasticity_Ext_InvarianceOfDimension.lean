-- Prove2me | solution 1 for Plasticity.Ext.InvarianceOfDimension
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T18:44:06.509278+00:00
-- url     : https://prove2.me/submissions/9b585334-161f-438a-acac-e225a31efe56

import Theorems.Thm_Plasticity_Ext_InvarianceOfDomain
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.ContinuousOn

namespace Sol_Plasticity_Ext_InvarianceOfDimension

/-- Padding by zeros: `ℝ^m → ℝ^n`. -/
noncomputable def pad (m n : ℕ) (y : Fin m → ℝ) : Fin n → ℝ :=
  fun i => if h : (i : ℕ) < m then y ⟨i, h⟩ else 0

lemma continuous_pad (m n : ℕ) : Continuous (pad m n) := by
  refine continuous_pi fun i => ?_
  by_cases h : (i : ℕ) < m
  · simp only [pad, h, dite_true]
    exact continuous_apply _
  · simp only [pad, h, dite_false]
    exact continuous_const

lemma pad_injective {m n : ℕ} (hmn : m ≤ n) : Function.Injective (pad m n) := by
  intro y₁ y₂ hy
  funext j
  have h := congrFun hy ⟨j, lt_of_lt_of_le j.2 hmn⟩
  simpa [pad, j.2] using h

lemma pad_apply_of_le {m n : ℕ} (y : Fin m → ℝ) (i : Fin n) (hi : m ≤ (i : ℕ)) :
    pad m n y i = 0 := by
  simp [pad, not_lt.mpr hi]

/-- A nonempty open subset of `ℝ^n` is not contained in a coordinate hyperplane. -/
lemma not_subset_hyperplane {n : ℕ} (S : Set (Fin n → ℝ)) (hS : IsOpen S) (hne : S.Nonempty)
    (k : Fin n) (hk : ∀ p ∈ S, p k = 0) : False := by
  obtain ⟨p, hp⟩ := hne
  let γ : ℝ → Fin n → ℝ := fun t => Function.update p k t
  have hγ : Continuous γ := by
    refine continuous_pi fun i => ?_
    by_cases h : i = k
    · subst h
      simp only [γ, Function.update_self]
      exact continuous_id
    · simp only [γ, Function.update_of_ne h]
      exact continuous_const
  have hopen : IsOpen (γ ⁻¹' S) := hS.preimage hγ
  have h0 : (0 : ℝ) ∈ γ ⁻¹' S := by
    have : γ 0 = p := by
      have hpk := hk p hp
      simp only [γ]
      rw [← hpk, Function.update_eq_self]
    simp only [Set.mem_preimage, this]
    exact hp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
  have hmem : ε / 2 ∈ γ ⁻¹' S := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have := hk _ hmem
  simp only [γ, Function.update_self] at this
  exact (half_pos hε).ne' this

end Sol_Plasticity_Ext_InvarianceOfDimension

open Sol_Plasticity_Ext_InvarianceOfDimension in
theorem solution {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (U : Set V) (hU : IsOpen U) (hne : U.Nonempty) (f : V → W)
    (hf : ContinuousOn f U) (hinj : Set.InjOn f U) :
    Module.finrank ℝ V ≤ Module.finrank ℝ W := by
  by_contra hlt
  push Not at hlt
  set n := Module.finrank ℝ V with hn
  set m := Module.finrank ℝ W with hm
  let eV : V ≃L[ℝ] (Fin n → ℝ) :=
    (LinearEquiv.ofFinrankEq V (Fin n → ℝ) (by simp [hn])).toContinuousLinearEquiv
  let eW : W ≃L[ℝ] (Fin m → ℝ) :=
    (LinearEquiv.ofFinrankEq W (Fin m → ℝ) (by simp [hm])).toContinuousLinearEquiv
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun z => pad m n (eW (f (eV.symm z)))
  let U' : Set (Fin n → ℝ) := eV.symm ⁻¹' U
  have hU' : IsOpen U' := hU.preimage eV.symm.continuous
  have hne' : U'.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    exact ⟨eV v, by simpa [U'] using hv⟩
  have hg : ContinuousOn g U' := by
    have h1 : ContinuousOn (fun z => f (eV.symm z)) U' :=
      hf.comp eV.symm.continuous.continuousOn (fun z hz => hz)
    exact (continuous_pad m n).comp_continuousOn (eW.continuous.comp_continuousOn h1)
  have hginj : Set.InjOn g U' := by
    intro z₁ hz₁ z₂ hz₂ h
    have h1 := pad_injective hlt.le h
    have h2 : f (eV.symm z₁) = f (eV.symm z₂) := eW.injective h1
    exact eV.symm.injective (hinj hz₁ hz₂ h2)
  have himg : IsOpen (g '' U') := Plasticity.Ext.InvarianceOfDomain U' hU' g hg hginj
  refine not_subset_hyperplane (g '' U') himg (hne'.image g) ⟨m, hlt⟩ ?_
  rintro p ⟨z, -, rfl⟩
  exact pad_apply_of_le _ _ le_rfl

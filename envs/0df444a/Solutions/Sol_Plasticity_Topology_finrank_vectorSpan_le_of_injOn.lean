-- Prove2me | solution 1 for Plasticity.Topology.finrank_vectorSpan_le_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:37:34.52485+00:00
-- url     : https://prove2.me/submissions/9e1904ff-e8fb-4886-950c-37c51d5be28a

import Theorems.Thm_Plasticity_Ext_InvarianceOfDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Sol_Plasticity_Topology_finrank_vectorSpan_le_of_injOn

end Sol_Plasticity_Topology_finrank_vectorSpan_le_of_injOn

open Set Module in
theorem solution {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (D : Set E) (hconv : Convex ℝ D)
    (f : E → E') (hf : ContinuousOn f D) (hinj : Set.InjOn f D)
    (W : Submodule ℝ E') (hW : FiniteDimensional ℝ W) (c : E') (hc : ∀ x ∈ D, f x - c ∈ W) :
    FiniteDimensional ℝ (vectorSpan ℝ D) ∧
      Module.finrank ℝ (vectorSpan ℝ D) ≤ Module.finrank ℝ W := by
  have := hW
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional W
  rcases D.eq_empty_or_nonempty with rfl | ⟨d₀, hd₀⟩
  · rw [vectorSpan_empty]
    exact ⟨inferInstance, by simp⟩
  have key : ∀ (m : ℕ) (v : Fin m → E), LinearIndependent ℝ v → (∀ i, d₀ + v i ∈ D) →
      m ≤ finrank ℝ W := by
    intro m v hli hv
    rcases Nat.eq_zero_or_pos m with hm | hm
    · omega
    set U : Set (Fin m → ℝ) := {l | (∀ i, 0 < l i) ∧ ∑ i, l i < 1} with hU
    have hUo : IsOpen U := by
      have h1 : U = (⋂ i, {l : Fin m → ℝ | 0 < l i}) ∩ {l | ∑ i, l i < 1} := by
        ext
        simp [U]
      rw [h1]
      exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
        (isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
    have hUne : U.Nonempty := by
      refine ⟨fun _ => 1 / ((m : ℝ) + 1), fun i => by positivity, ?_⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    let p : (Fin m → ℝ) → E := fun l => d₀ + ∑ i, l i • v i
    have hpD : ∀ l ∈ U, p l ∈ D := by
      rintro l ⟨hpos, hsum⟩
      set s := ∑ i, l i with hs
      have hs0 : 0 < s := Finset.sum_pos (fun i _ => hpos i) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      have hq : ∑ i, (l i / s) • (d₀ + v i) ∈ D := by
        refine hconv.sum_mem (fun i _ => (div_pos (hpos i) hs0).le) ?_ (fun i _ => hv i)
        rw [← Finset.sum_div, div_self hs0.ne']
      have hcomb := hconv hd₀ hq (sub_nonneg.mpr hsum.le) hs0.le (by ring)
      have e1 : s • ∑ i, (l i / s) • (d₀ + v i) = s • d₀ + ∑ i, l i • v i := by
        rw [Finset.smul_sum]
        have h2 : ∀ i, s • ((l i / s) • (d₀ + v i)) = l i • d₀ + l i • v i := by
          intro i
          rw [smul_smul, mul_div_cancel₀ _ hs0.ne', smul_add]
        simp_rw [h2, Finset.sum_add_distrib, ← Finset.sum_smul]
        rfl
      rw [e1, sub_smul, one_smul] at hcomb
      convert hcomb using 1
      simp only [p]
      abel
    let g : (Fin m → ℝ) → W := fun l => P (f (p l) - c)
    have hgval : ∀ l ∈ U, (g l : E') = f (p l) - c := by
      intro l hl
      have h1 := hP ⟨_, hc _ (hpD l hl)⟩
      simp only [g]
      rw [h1]
    have hpc : Continuous p :=
      continuous_const.add (continuous_finsetSum _ fun i _ => (continuous_apply i).smul
        continuous_const)
    have hgc : ContinuousOn g U :=
      P.continuous.comp_continuousOn ((hf.comp hpc.continuousOn hpD).sub continuousOn_const)
    have hginj : InjOn g U := by
      intro l₁ h₁ l₂ h₂ h
      have h' : (g l₁ : E') = g l₂ := by rw [h]
      rw [hgval l₁ h₁, hgval l₂ h₂] at h'
      have hp := hinj (hpD l₁ h₁) (hpD l₂ h₂) (sub_left_injective h')
      have hsum : ∑ i, (l₁ i - l₂ i) • v i = 0 := by
        simp only [p] at hp
        have h3 := add_left_cancel hp
        simp [sub_smul, Finset.sum_sub_distrib, h3]
      funext i
      have h4 := Fintype.linearIndependent_iff.mp hli _ hsum i
      linarith
    have h5 := Plasticity.Ext.InvarianceOfDimension U hUo hUne g hgc hginj
    simpa using h5
  rw [vectorSpan_eq_span_vsub_set_right ℝ hd₀]
  set S := (fun x => x -ᵥ d₀) '' D with hS
  obtain ⟨b, hbS, hspan, hbli⟩ := exists_linearIndependent ℝ S
  have hcard : ∀ t : Finset E, (t : Set E) ⊆ b → t.card ≤ finrank ℝ W := by
    intro t ht
    have hlit : LinearIndepOn ℝ id (t : Set E) := LinearIndepOn.mono hbli ht
    let v : Fin t.card → E := fun i => (t.equivFin.symm i : E)
    have hliv : LinearIndependent ℝ v := hlit.comp _ t.equivFin.symm.injective
    refine key t.card v hliv fun i => ?_
    obtain ⟨d, hd, hdv⟩ := hbS (ht (t.equivFin.symm i).2)
    simp only [vsub_eq_sub] at hdv
    simp only [v]
    rw [← hdv]
    simpa using hd
  have hbfin : b.Finite := by
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (finrank ℝ W + 1)
    have := hcard t ht
    omega
  have := hbfin.fintype
  rw [← hspan]
  refine ⟨FiniteDimensional.span_of_finite ℝ hbfin, ?_⟩
  calc finrank ℝ (Submodule.span ℝ b) ≤ b.toFinset.card := finrank_span_le_card b
    _ ≤ finrank ℝ W := hcard _ (by simp)

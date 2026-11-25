-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TBDisc.fg_of_unifDiscrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:11:02.735865+00:00
-- url     : https://prove2.me/submissions/5c2296ee-2ad7-4ab0-a50a-838981e701bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_RatIntUnifDiscrete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete
import Theorems.Thm_PI_UnitaryGroupMassFormula_TBDisc_norm_le_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TBDisc
open NumberField ReciprocityTheory.ChartRestriction.G.TB
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
namespace PI.UnitaryGroupMassFormula.TBDisc
theorem _root_.solution [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Nf : NormFam K V)
    (M : Submodule (𝓞 K) V) (hM : UnifDiscrete Nf M) : M.FG := by
  obtain ⟨ε, hε, hsmall⟩ := hM
  set C : ℝ := ∑ σ : K →+* ℂ, ∑ i, Nf.N σ (Module.finBasis K V i) + 1 with hC
  have hS : ∀ σ, ∑ i, Nf.N σ (Module.finBasis K V i) ≤ C - 1 := fun σ => by
    rw [hC, add_sub_cancel_right]
    exact Finset.single_le_sum (f := fun σ => ∑ i, Nf.N σ (Module.finBasis K V i))
      (fun τ _ => Finset.sum_nonneg (fun i _ => Nf.nonneg _ _)) (Finset.mem_univ σ)
  have hCpos : 0 < C := by
    have : 0 ≤ C - 1 :=
      (Finset.sum_nonneg (fun i _ => Nf.nonneg _ _)).trans (hS (Classical.arbitrary _))
    linarith
  have hδ : 0 < ε / C := div_pos hε hCpos
  have key : ∀ f ∈ M, ‖coordMap (K := K) f‖ < ε / C → f = 0 := by
    intro f hf hlt
    refine hsmall f hf (fun σ => ?_)
    have h1 := norm_le_coord Nf σ f
    have h2 : ‖coordMap (K := K) f‖ * ∑ i, Nf.N σ (Module.finBasis K V i) ≤
        ‖coordMap (K := K) f‖ * C :=
      mul_le_mul_of_nonneg_left (by linarith [hS σ]) (norm_nonneg _)
    have h3 : ‖coordMap (K := K) f‖ * C < ε := by
      rwa [lt_div_iff₀ hCpos] at hlt
    linarith
  let P : Submodule ℤ V := M.restrictScalars ℤ
  let Ψ : P →ₗ[ℤ] ((K →+* ℂ) → Fin (Module.finrank K V) → ℂ) :=
    (coordMap (K := K) (V := V)).toIntLinearMap.comp P.subtype
  have hΨ : ∀ x : P, ‖Ψ x‖ < ε / C → x = 0 := fun x hx => Subtype.ext (key x x.2 hx)
  have hinj : Function.Injective Ψ := by
    intro x y hxy
    have : x - y = 0 := hΨ _ (by rw [map_sub, hxy, sub_self, norm_zero]; exact hδ)
    exact sub_eq_zero.mp this
  have : DiscreteTopology (LinearMap.range Ψ) := by
    refine discreteTopology_iff_isOpen_singleton.mpr (fun z => Metric.isOpen_singleton_iff.mpr
      ⟨ε / C, hδ, fun y hy => ?_⟩)
    obtain ⟨_, ⟨x, rfl⟩⟩ := z
    obtain ⟨_, ⟨x', rfl⟩⟩ := y
    rw [Subtype.dist_eq, dist_eq_norm, ← map_sub] at hy
    have := hΨ _ hy
    rw [sub_eq_zero] at this
    subst this
    rfl
  have : Module.Finite ℤ P := Module.Finite.equiv (LinearEquiv.ofInjective Ψ hinj).symm
  obtain ⟨s, hs⟩ : P.FG := Module.Finite.iff_fg.mp inferInstance
  refine ⟨s, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro x hx
    have : x ∈ P := by rw [← hs]; exact Submodule.subset_span hx
    exact this
  · intro x hx
    have hxP : x ∈ P := hx
    rw [← hs] at hxP
    exact Submodule.span_le_restrictScalars ℤ (𝓞 K) (s : Set V) hxP
end PI.UnitaryGroupMassFormula.TBDisc

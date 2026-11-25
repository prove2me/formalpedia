-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dc_symm_nodal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:00.859126+00:00
-- url     : https://prove2.me/submissions/f99faf0c-71c4-4596-af67-f45af2490de9

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_mem_cplxPts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_aeval_eigen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_symm_eig_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_symm_semisimple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y] {T : Module.End ℂ Y} {S W : Submodule ℂ Y}
  {Q : Y →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hpos : ∀ f ∈ S, f ≠ 0 → 0 < (Q f f).re)
    (hsym : ∀ f ∈ S, ∀ g ∈ S, Q (T f) g = Q f (T g)) (hTS : ∀ f ∈ S, T f ∈ S) (hWS : W ≤ S)
    (hW : FiniteDimensional ℂ W) (hTW : ∀ f ∈ W, T f ∈ W) :
    ∃ B : Finset ℝ, ∀ w ∈ W, aeval T (Lagrange.nodal (dc_cplxPts B) id) w = 0 := by
  classical
  set T' : Module.End ℂ W := T.restrict hTW with hT'
  have hfin := Module.End.finite_hasEigenvalue T'
  refine ⟨hfin.toFinset.image Complex.re, fun w hw => ?_⟩
  have key : ∀ μ : ℂ, ∀ x ∈ T'.maxGenEigenspace μ, aeval T (Lagrange.nodal (dc_cplxPts (hfin.toFinset.image Complex.re)) id) (x : Y) = 0 := by
    intro μ x hx
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T' μ x).mp hx
    have hk' : ((T - μ • 1) ^ k) (x : Y) = 0 := by
      have : ∀ j : ℕ, (((T' - μ • 1) ^ j) x : Y) = ((T - μ • 1) ^ j) (x : Y) := by
        intro j
        induction j with
        | zero => simp
        | succ j ih => rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]; simp [hT']
      rw [← this, hk]; simp
    have he := dc_symm_semisimple hpos hsym hTS μ k (x : Y) (hWS x.2) hk'
    by_cases hx0 : (x : Y) = 0
    · rw [hx0, map_zero]
    have hr := dc_symm_eig_real hpos hsym (hWS x.2) hx0 he
    rw [dc_aeval_eigen he, Lagrange.eval_nodal]
    have hmem : μ ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ⟨?_, fun h => hx0 (by simp [h])⟩
      rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (by simpa [hT'] using he)
    have : μ ∈ dc_cplxPts (hfin.toFinset.image Complex.re) :=
      dc_mem_cplxPts.mpr ⟨μ.re, Finset.mem_image_of_mem _ hmem, hr⟩
    rw [Finset.prod_eq_zero this (by simp), zero_smul]
  have htop := Module.End.iSup_maxGenEigenspace_eq_top T'
  have gen : ∀ y : W, y ∈ ⨆ μ, T'.maxGenEigenspace μ →
      aeval T (Lagrange.nodal (dc_cplxPts (hfin.toFinset.image Complex.re)) id) (y : Y) = 0 := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem μ x hx => exact key μ x hx
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
  exact gen ⟨w, hw⟩ (by rw [htop]; trivial)
end ReciprocityTheory.ChartRestriction.DS

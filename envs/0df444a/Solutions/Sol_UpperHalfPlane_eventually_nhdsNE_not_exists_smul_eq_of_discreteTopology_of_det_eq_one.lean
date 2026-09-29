-- Prove2me | solution 1 for UpperHalfPlane.eventually_nhdsNE_not_exists_smul_eq_of_discreteTopology_of_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4cb516b8-cf48-542a-b8c7-f04ed623af0d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_eventually_nhdsNE_not_exists_smul_eq_of_discreteTopology_of_det_eq_one

set_option autoImplicit false

open scoped MatrixGroups Topology
open Filter

theorem solution
    (Γ : Subgroup (GL (Fin 2) ℝ)) [DiscreteTopology ↥Γ]
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (τ τ' : UpperHalfPlane) :
    ∀ᶠ z in 𝓝[≠] τ, ¬ ∃ γ ∈ Γ, γ • τ' = z := by
  classical

  set φ : Matrix.SpecialLinearGroup (Fin 2) ℝ →* GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.toGL with hφ
  set 𝒢 : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) := Γ.comap φ with h𝒢

  have hact : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : UpperHalfPlane), g • z = (φ g) • z := by
    intro g z
    rw [MulAction.compHom_smul_def]
    congr 1

  have hlift : ∀ γ ∈ Γ, ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, φ g = γ := by
    intro γ hγ
    have hd : ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
      have := congrArg Units.val (hdet γ hγ)
      simpa using this
    exact ⟨⟨(γ : Matrix (Fin 2) (Fin 2) ℝ), hd⟩, Units.ext rfl⟩

  haveI : DiscreteTopology ↥𝒢 := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun g : ↥𝒢 => (⟨φ g, (Subgroup.mem_comap.mp g.2)⟩ : ↥Γ)) ?_ ?_
    · exact (Matrix.SpecialLinearGroup.continuous_toGL.comp continuous_subtype_val).subtype_mk _
    · intro a b h
      apply Subtype.ext
      exact Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val h)

  obtain ⟨L, hLc, hLn⟩ := exists_compact_mem_nhds τ
  have hfin : {g : ↥𝒢 | ((fun w : UpperHalfPlane => g • w) '' {τ'} ∩ L).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image isCompact_singleton hLc
  set S : Set UpperHalfPlane := (fun g : ↥𝒢 => g • τ') '' {g : ↥𝒢 | ((fun w : UpperHalfPlane => g • w) '' {τ'} ∩ L).Nonempty}
    with hS
  have hSfin : S.Finite := hfin.image _

  have h1 : ∀ᶠ z in 𝓝[≠] τ, z ∈ L := mem_nhdsWithin_of_mem_nhds hLn
  have h2 : ∀ᶠ z in 𝓝[≠] τ, z ≠ τ := self_mem_nhdsWithin
  have h3' : ∀ᶠ z in 𝓝 τ, ∀ s ∈ S, s ≠ τ → z ≠ s := by
    rw [Filter.eventually_all_finite hSfin]
    intro s _
    by_cases hs : s = τ
    · exact Filter.Eventually.of_forall fun z h => (h hs).elim
    · filter_upwards [compl_singleton_mem_nhds (Ne.symm hs)] with z hz
      exact fun _ => hz
  have h3 : ∀ᶠ z in 𝓝[≠] τ, ∀ s ∈ S, s ≠ τ → z ≠ s := h3'.filter_mono nhdsWithin_le_nhds
  filter_upwards [h1, h2, h3] with z hzL hzτ hzS
  rintro ⟨γ, hγ, rfl⟩
  obtain ⟨g, hg⟩ := hlift γ hγ
  have hg𝒢 : g ∈ 𝒢 := by rw [h𝒢, Subgroup.mem_comap, hg]; exact hγ
  have hmem : γ • τ' ∈ S := by
    refine ⟨⟨g, hg𝒢⟩, ?_, ?_⟩
    · refine ⟨γ • τ', ⟨τ', rfl, ?_⟩, hzL⟩
      show (⟨g, hg𝒢⟩ : ↥𝒢) • τ' = γ • τ'
      rw [Subgroup.mk_smul, hact, hg]
    · show (⟨g, hg𝒢⟩ : ↥𝒢) • τ' = γ • τ'
      rw [Subgroup.mk_smul, hact, hg]
  exact hzS _ hmem hzτ rfl

end S_UpperHalfPlane_eventually_nhdsNE_not_exists_smul_eq_of_discreteTopology_of_det_eq_one
end P2MW
export P2MW.S_UpperHalfPlane_eventually_nhdsNE_not_exists_smul_eq_of_discreteTopology_of_det_eq_one (solution)

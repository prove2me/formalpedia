-- Prove2me | solution 1 for WLight.exists_twist_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/38c94858-b157-562c-8a21-b30838148c53

import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.Geometry.Manifold.Notation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WLight_exists_twist_of_flat

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Complex UpperHalfPlane Function
open scoped Topology Manifold ModularForm

namespace WLightR11aSol

section FunctionDescent

theorem exists_twist_of_flat (K : IntermediateField ℚ ℂ) (M : Submodule ↥K (ℍ → ℂ))
    (hflat : ∀ s : Finset (ℍ → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) →
      LinearIndependent ↥K (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) →
      LinearIndependent ℂ (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)))
    (σ : ℂ ≃ₐ[↥K] ℂ) :
    ∃ T : (ℍ → ℂ) → (ℍ → ℂ), ∀ (ι : Type) [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ),
      (∀ i, e i ∈ M) → T (∑ i, c i • e i) = ∑ i, σ (c i) • e i := by
  classical

  set bM := Module.Basis.ofVectorSpace ↥K ↥M with hbM_def
  set e : Module.Basis.ofVectorSpaceIndex ↥K ↥M → ℍ → ℂ := fun i => ((bM i : ↥M) : ℍ → ℂ) with he_def
  have he_mem : ∀ i, e i ∈ M := fun i => (bM i : ↥M).2
  have he_inj : Function.Injective e := Subtype.val_injective.comp bM.injective
  have halg : ∀ (a : ↥K) (f : ℍ → ℂ), a • f = (a : ℂ) • f := fun a f => rfl

  have heK : LinearIndependent ↥K e :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)

  have heC : LinearIndependent ℂ e := by
    rw [← linearIndepOn_id_range_iff he_inj]
    refine linearIndepOn_of_finite _ fun t htsub htfin => ?_
    have hcoe : (↑htfin.toFinset : Set (ℍ → ℂ)) = t := htfin.coe_toFinset
    have hsM : (↑htfin.toFinset : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) := by
      rw [hcoe]
      intro w hw
      obtain ⟨j, rfl⟩ := htsub hw
      exact he_mem j
    have hsK : LinearIndependent ↥K
        (fun w : ↥(↑htfin.toFinset : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) := by
      have h2 : LinearIndepOn ↥K id t := heK.linearIndepOn_id.mono htsub
      show LinearIndepOn ↥K id (↑htfin.toFinset : Set (ℍ → ℂ))
      rwa [hcoe]
    have h3 := hflat htfin.toFinset hsM hsK
    show LinearIndepOn ℂ id t
    rw [← hcoe]
    exact h3

  have hM_rep : ∀ (m : ℍ → ℂ) (hm : m ∈ M)
      (S : Finset (Module.Basis.ofVectorSpaceIndex ↥K ↥M)), (bM.repr ⟨m, hm⟩).support ⊆ S →
      m = ∑ i ∈ S, ((bM.repr ⟨m, hm⟩ i : ℂ)) • e i := by
    intro m hm S hS
    have h1 := bM.linearCombination_repr ⟨m, hm⟩
    have h2 := congrArg (fun z : ↥M => (z : ℍ → ℂ)) h1
    simp only [Finsupp.linearCombination_apply] at h2
    rw [Finsupp.sum_of_support_subset (bM.repr ⟨m, hm⟩) hS (fun i a => a • bM i)
      (fun i _ => by simp)] at h2
    conv_lhs => rw [← h2]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, halg]

  have hext : ∀ (S' S : Finset (Module.Basis.ofVectorSpaceIndex ↥K ↥M)) (_ : S' ⊆ S)
      (a : Module.Basis.ofVectorSpaceIndex ↥K ↥M → ℂ),
      (∑ i ∈ S', a i • e i) = ∑ i ∈ S, (if i ∈ S' then a i else 0) • e i := by
    intro S' S hsub a
    rw [← Finset.sum_subset hsub (fun i _ hi => by rw [if_neg hi, zero_smul])]
    exact Finset.sum_congr rfl fun i hi => by rw [if_pos hi]

  have hwellDefE : ∀ (S₁ S₂ : Finset ↥(Module.Basis.ofVectorSpaceIndex ↥K ↥M))
      (a₁ a₂ : ↥(Module.Basis.ofVectorSpaceIndex ↥K ↥M) → ℂ),
      (∑ i ∈ S₁, a₁ i • e i) = (∑ i ∈ S₂, a₂ i • e i) →
      (∑ i ∈ S₁, σ (a₁ i) • e i) = (∑ i ∈ S₂, σ (a₂ i) • e i) := by
    intro S₁ S₂ a₁ a₂ hEq
    set S := S₁ ∪ S₂ with hS_def
    rw [hext S₁ S Finset.subset_union_left a₁,
      hext S₂ S Finset.subset_union_right a₂] at hEq
    have hdiff : (∑ i ∈ S, ((if i ∈ S₁ then a₁ i else 0) - (if i ∈ S₂ then a₂ i else 0)) • e i)
        = 0 := by
      have h1 : ∀ i ∈ S, ((if i ∈ S₁ then a₁ i else 0) - (if i ∈ S₂ then a₂ i else 0)) • e i =
          (if i ∈ S₁ then a₁ i else 0) • e i - (if i ∈ S₂ then a₂ i else 0) • e i :=
        fun i _ => sub_smul _ _ _
      rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, hEq, sub_self]
    have hcoords := linearIndependent_iff'.mp heC S
      (fun i => (if i ∈ S₁ then a₁ i else 0) - (if i ∈ S₂ then a₂ i else 0)) hdiff
    rw [hext S₁ S Finset.subset_union_left (fun i => σ (a₁ i)),
      hext S₂ S Finset.subset_union_right (fun i => σ (a₂ i))]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hbi := sub_eq_zero.mp (hcoords i hi)
    by_cases h1 : i ∈ S₁ <;> by_cases h2 : i ∈ S₂ <;>
      simp only [h1, h2, if_true, if_false] at hbi ⊢
    · rw [hbi]
    · rw [hbi, map_zero, zero_smul]
    · rw [← hbi, map_zero, zero_smul]

  have hfam_rep : ∀ (ι' : Type) (_ : Fintype ι') (c : ι' → ℂ)
      (f : ι' → ℍ → ℂ) (hf : ∀ j, f j ∈ M),
      ∃ (S : Finset ↥(Module.Basis.ofVectorSpaceIndex ↥K ↥M))
        (A : ↥(Module.Basis.ofVectorSpaceIndex ↥K ↥M) → ℂ),
        (∑ j, c j • f j) = (∑ i ∈ S, A i • e i) ∧
        (∑ j, σ (c j) • f j) = (∑ i ∈ S, σ (A i) • e i) := by
    intro ι' _ c f hf
    set L : ι' → Module.Basis.ofVectorSpaceIndex ↥K ↥M →₀ ↥K := fun j => bM.repr ⟨f j, hf j⟩
      with hL_def
    set S := Finset.univ.biUnion fun j : ι' => (L j).support with hS_def
    have hfj : ∀ j, f j = ∑ i ∈ S, ((L j i : ℂ)) • e i := fun j =>
      hM_rep (f j) (hf j) S
        (Finset.subset_biUnion_of_mem (fun j' : ι' => (L j').support) (Finset.mem_univ j))
    have hassemble : ∀ (g : ι' → ℂ),
        (∑ j, g j • f j) = ∑ i ∈ S, (∑ j, g j * (L j i : ℂ)) • e i := by
      intro g
      calc ∑ j, g j • f j = ∑ j, ∑ i ∈ S, (g j * (L j i : ℂ)) • e i := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hfj j, Finset.smul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
        _ = ∑ i ∈ S, (∑ j, g j * (L j i : ℂ)) • e i := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_smul]
    refine ⟨S, fun i => ∑ j, c j * (L j i : ℂ), hassemble c, ?_⟩
    rw [hassemble (fun j => σ (c j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    congr 1
    exact (σ.commutes ((L j) i)).symm

  have hwellDefFam : ∀ (ι₁ : Type) (_ : Fintype ι₁) (c₁ : ι₁ → ℂ)
      (f₁ : ι₁ → ℍ → ℂ) (hf₁ : ∀ j, f₁ j ∈ M) (ι₂ : Type) (_ : Fintype ι₂) (c₂ : ι₂ → ℂ)
      (f₂ : ι₂ → ℍ → ℂ) (hf₂ : ∀ j, f₂ j ∈ M),
      (∑ j, c₁ j • f₁ j) = (∑ j, c₂ j • f₂ j) →
      (∑ j, σ (c₁ j) • f₁ j) = (∑ j, σ (c₂ j) • f₂ j) := by
    intro ι₁ h₁ c₁ f₁ hf₁ ι₂ h₂ c₂ f₂ hf₂ hEq
    obtain ⟨S₁, A₁, hA₁, hA₁'⟩ := hfam_rep ι₁ h₁ c₁ f₁ hf₁
    obtain ⟨S₂, A₂, hA₂, hA₂'⟩ := hfam_rep ι₂ h₂ c₂ f₂ hf₂
    rw [hA₁', hA₂']
    exact hwellDefE S₁ S₂ A₁ A₂ (by rw [← hA₁, ← hA₂, hEq])

  have hrep_span : ∀ v : ℍ → ℂ, v ∈ Submodule.span ℂ (M : Set (ℍ → ℂ)) →
      ∃ (s : Finset (ℍ → ℂ)) (c : (ℍ → ℂ) → ℂ),
        (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) ∧ v = ∑ w ∈ s, c w • w := by
    intro v₀ hvs
    obtain ⟨T₀, hT₀M, hvT₀⟩ := Submodule.mem_span_finite_of_mem_span hvs
    obtain ⟨cf, hcf⟩ := Submodule.mem_span_finset.mp hvT₀
    exact ⟨T₀, cf, hT₀M, hcf.2.symm⟩

  set T : (ℍ → ℂ) → (ℍ → ℂ) := fun w =>
    if h : w ∈ Submodule.span ℂ (M : Set (ℍ → ℂ)) then
      ∑ u ∈ (hrep_span w h).choose, σ ((hrep_span w h).choose_spec.choose u) • u
    else 0 with hT_def

  have hattach : ∀ (s : Finset (ℍ → ℂ)) (g : (ℍ → ℂ) → ℂ),
      (∑ w ∈ s, g w • w) = ∑ j : ↥s, g (j : ℍ → ℂ) • (j : ℍ → ℂ) := by
    intro s g
    rw [Finset.sum_coe_sort s (fun w => g w • w)]
  have hchosen_twist : ∀ (w : ℍ → ℂ)
      (h : w ∈ Submodule.span ℂ (M : Set (ℍ → ℂ)))
      (ι' : Type) (_ : Fintype ι') (c : ι' → ℂ) (f : ι' → ℍ → ℂ) (hf : ∀ j, f j ∈ M),
      w = (∑ j, c j • f j) → T w = ∑ j, σ (c j) • f j := by
    intro w h ι' hfin c f hf hw
    obtain ⟨hsM', hseq'⟩ := (hrep_span w h).choose_spec.choose_spec
    simp only [hT_def, dif_pos h]
    rw [hattach _ (fun u => σ ((hrep_span w h).choose_spec.choose u))]
    refine hwellDefFam _ _ _ _ (fun j => hsM' j.2) ι' hfin c f hf ?_
    rw [← hattach _ ((hrep_span w h).choose_spec.choose), ← hseq', ← hw]

  refine ⟨T, fun ι' hfin c f hf => ?_⟩
  have hmem : (∑ j, c j • f j) ∈ Submodule.span ℂ (M : Set (ℍ → ℂ)) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hf j))
  exact hchosen_twist _ hmem ι' hfin c f hf rfl

end FunctionDescent

end WLightR11aSol

theorem solution (K : IntermediateField ℚ ℂ) (M : Submodule ↥K (ℍ → ℂ))
    (hflat : ∀ s : Finset (ℍ → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) →
      LinearIndependent ↥K (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) →
      LinearIndependent ℂ (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)))
    (σ : ℂ ≃ₐ[↥K] ℂ) :
    ∃ T : (ℍ → ℂ) → (ℍ → ℂ), ∀ (ι : Type) [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ),
      (∀ i, e i ∈ M) → T (∑ i, c i • e i) = ∑ i, σ (c i) • e i :=
  WLightR11aSol.exists_twist_of_flat K M hflat σ

end

end S_WLight_exists_twist_of_flat
end P2MW
export P2MW.S_WLight_exists_twist_of_flat (solution)

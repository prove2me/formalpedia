-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P35.finitelyGenerated_integerProduct_discrete
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:51:04.211961+00:00
-- url     : https://prove2.me/submissions/cd851652-d179-4349-b5ee-83499f0804a5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35
open QAlgorithms.Papers.Independent.Next46.P35

open Set Filter Topology

open scoped Manifold ContDiff

universe u v w z

theorem g62i_key {J : Type u} (S : Finset (J → ℤ)) (F : Finset (S → ℤ))
    (hspan : Submodule.span ℤ (Set.range (fun j : J => fun s : S => (s : J → ℤ) j)) =
      Submodule.span ℤ (F : Set (S → ℤ)))
    (c : F → J) (hc : ∀ f : F, (fun s : S => (s : J → ℤ) (c f)) = f)
    (x : J → ℤ) (hx : x ∈ AddSubgroup.closure (S : Set (J → ℤ)))
    (h0 : ∀ f : F, x (c f) = 0) : x = 0 := by
  rw [← Submodule.span_int_eq_addSubgroupClosure] at hx
  have hx' : x ∈ Submodule.span ℤ (S : Set (J → ℤ)) := hx
  obtain ⟨a, -, rfl⟩ := (Submodule.mem_span_finset).1 hx'
  let φ : (S → ℤ) →ₗ[ℤ] ℤ :=
    { toFun := fun v => ∑ s : S, a s * v s
      map_add' := by intro v w; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r v; simp [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  have hle : Submodule.span ℤ (F : Set (S → ℤ)) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    intro f hf
    have := h0 ⟨f, hf⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    have e : φ f = φ (fun s : S => (s : J → ℤ) (c ⟨f, hf⟩)) := by rw [hc ⟨f, hf⟩]
    rw [e]
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← this, Finset.sum_apply]
    rw [← Finset.sum_coe_sort S]
    simp [smul_eq_mul]
  funext j
  have hj : (fun s : S => (s : J → ℤ) j) ∈ Submodule.span ℤ (F : Set (S → ℤ)) := by
    rw [← hspan]; exact Submodule.subset_span ⟨j, rfl⟩
  have := hle hj
  simp only [LinearMap.mem_ker, φ, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [Finset.sum_apply, Pi.zero_apply, ← this, ← Finset.sum_coe_sort S]
  simp [smul_eq_mul]

theorem solution
    {J : Type u} (D : AddSubgroup (J → ℤ)) (hFG : D.FG) :
    DiscreteTopology D := by
  obtain ⟨S, hS⟩ := hFG
  have hfg : (Submodule.span ℤ (Set.range (fun j : J => fun s : S => (s : J → ℤ) j))).FG :=
    IsNoetherian.noetherian _
  obtain ⟨F, hFsub, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hmem : ∀ f : F, ∃ j : J, (fun s : S => (s : J → ℤ) j) = f := fun f => hFsub f.2
  choose c hc using hmem
  apply discreteTopology_of_isOpen_singleton_zero
  have hU : IsOpen {x : J → ℤ | ∀ f : F, x (c f) = 0} := by
    have : {x : J → ℤ | ∀ f : F, x (c f) = 0} = ⋂ f : F, (fun x : J → ℤ => x (c f)) ⁻¹' {0} := by
      ext x; simp
    rw [this]
    exact isOpen_iInter_of_finite fun f => (isOpen_discrete _).preimage (continuous_apply _)
  have : ({0} : Set D) = Subtype.val ⁻¹' {x : J → ℤ | ∀ f : F, x (c f) = 0} := by
    ext ⟨x, hx⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · intro h f
      have : x = 0 := congrArg Subtype.val h
      simp [this]
    · intro h
      apply Subtype.ext
      rw [← hS] at hx
      exact g62i_key S F hspan c hc x hx h
  rw [this]
  exact hU.preimage continuous_subtype_val

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.open_quasipoint_cluster_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T17:25:12.494011+00:00
-- url     : https://prove2.me/submissions/e8334a4e-e77d-46a0-a473-bc0ed150deb1

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_nonmember_has_disjoint_member
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Intakethird100.P20

theorem solution {M : Type*} [TopologicalSpace M] [T2Space M]
    (B : StoneSpectrum (Opens M)) (x : M) :
    (LiesOver B x ↔ x ∈ ⋂ U : {U : Opens M // U ∈ B.val}, closure (U.val : Set M)) ∧
    (LiesOver B x ↔ ∀ U : Opens M, x ∈ (U : Set M) → U ∈ B.val) := by
  classical
  let I : Set M := ⋂ U : {U : Opens M // U ∈ B.val}, closure (U.val : Set M)
  have hu := quasipoint_upward_and_meet_closed B.val B.property
  have hnh (x : M) (hx : x ∈ I) (U : Opens M) (hxU : x ∈ (U : Set M)) : U ∈ B.val := by
    by_contra hU
    obtain ⟨V, hV, hVU⟩ := quasipoint_nonmember_has_disjoint_member B.val B.property U hU
    have hxV := Set.mem_iInter.mp hx (⟨V, hV⟩ : {U : Opens M // U ∈ B.val})
    obtain ⟨y, hyU, hyV⟩ := mem_closure_iff.mp hxV (U : Set M) U.isOpen hxU
    have hy : y ∈ (V ⊓ U : Opens M) := ⟨hyV, hyU⟩
    rw [hVU] at hy
    exact hy
  have hcl (x : M) (hn : ∀ U : Opens M, x ∈ (U : Set M) → U ∈ B.val) : x ∈ I := by
    apply Set.mem_iInter.mpr
    intro U
    apply mem_closure_iff.mpr
    intro V hV hxV
    let W : Opens M := ⟨V, hV⟩
    have hWB := hn W hxV
    have hUW := hu.2 U.val U.property W hWB
    have hzero : U.val ⊓ W ≠ ⊥ := fun h => B.property.1.2.1 (h ▸ hUW)
    obtain ⟨y, hyU, hyW⟩ := (Opens.ne_bot_iff_nonempty (U.val ⊓ W)).mp hzero
    exact ⟨y, hyW, hyU⟩
  have huniq (x y : M) (hx : x ∈ I) (hy : y ∈ I) : x = y := by
    by_contra hxy
    obtain ⟨u, v, huopen, hvopen, hxu, hyv, hdisj⟩ := t2_separation hxy
    let U : Opens M := ⟨u, huopen⟩
    let V : Opens M := ⟨v, hvopen⟩
    have hUV := hu.2 U (hnh x hx U hxu) V (hnh y hy V hyv)
    have hz : U ⊓ V = ⊥ := SetLike.coe_injective (disjoint_iff.mp hdisj)
    exact B.property.1.2.1 (hz ▸ hUV)
  have hfirst : LiesOver B x ↔ x ∈ I := by
    constructor
    · intro h
      change I = {x} at h
      rw [h]
      exact Set.mem_singleton x
    · intro hx
      change I = {x}
      apply Set.Subset.antisymm
      · intro y hy
        exact Set.mem_singleton_iff.mpr (huniq y x hy hx)
      · exact Set.singleton_subset_iff.mpr hx
  exact ⟨hfirst, hfirst.trans ⟨fun hx U hxU => hnh x hx U hxU, hcl x⟩⟩

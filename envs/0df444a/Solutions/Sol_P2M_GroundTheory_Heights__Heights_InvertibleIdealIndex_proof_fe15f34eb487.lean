-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_InvertibleIdealIndex_proof_fe15f34eb487
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:36.940944+00:00
-- url     : https://prove2.me/submissions/192f73a6-e20e-4513-a49b-7706a542236c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsOrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_apply_3d722f96a277
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_genIndex_eq_793276f70c85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mul_mem_of_mem_156f7ffd60e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mem_one_of_mem_62c5ae2e4464
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mem_span_of_local_c35ca71026c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_relIndex_map_subtype_1ba93abccb64
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_ba0dcb3ccb8a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_span_e21061b2c6b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_card_one_eq_zero_894d9c562d28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_card_subring_eq_zero_d68f59a0f2c9
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt.mulBy_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open InvertibleIdealIndexAlt
namespace GroundTheory.Heights₂.Heights
namespace InvertibleIdealIndex
theorem _root_.solution (h1 : OrderIdealIndexExtension.Statement)
    (h2 : LocallyPrincipalCoprime.Statement) : InvertibleIdealIndex.Statement := by
  intro L _ _ B M ι _ a hB hBM haM hden hloc
  have := hB
  by_cases hM0 : M = ⊥
  · have ha0 : ∀ i, a i = 0 := fun i => by simpa [hM0] using haM i
    have hT0 : Submodule.span (𝓞 L) (Set.range a) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      exact ha0 i
    simp only [hM0, hT0, Submodule.bot_toAddSubgroup, genIndex, AddSubgroup.relIndex_bot_left,
      AddSubgroup.relIndex_bot_right, card_subring_eq_zero, card_one_eq_zero]
    simp
  obtain ⟨r, s, hs, hrank, hfin, hidx⟩ := h1 L B hB
  obtain ⟨β, δ, I, hβ, hδ, hIs, hMI⟩ := h2 L B M ι a hB hBM haM hden hloc hM0 s hs
  have hβL : (β : L) ≠ 0 := fun h => hβ (Subtype.ext h)
  have hδL : (δ : L) ≠ 0 := fun h => hδ (Subtype.ext h)
  have hI0 : I ≠ ⊥ := by
    intro hI
    obtain ⟨⟨x, hxM⟩, hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hM0
    obtain ⟨y, hy, hxy⟩ := (hMI x).1 hxM
    rw [hI, Ideal.mem_bot] at hy
    subst hy
    have hx : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    simp [hβL, hx] at hxy
  have hspanβ : Ideal.span {β} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hβ
  have hspanδ : Ideal.span {δ} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hδ

  have g1 := genIndex_eq (X := B.toAddSubgroup) (J := I.toAddSubgroup.map B.subtype.toAddMonoidHom)
    (M := M) hβL hδL
    (by rintro _ ⟨y, _, rfl⟩; exact y.2)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem β.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem δ.2 hy)
    (by rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨β * y, I.mul_mem_left β hy, rfl⟩)
    (by
      intro x
      rw [hMI x]
      constructor
      · rintro ⟨y, hy, h⟩
        exact ⟨y, ⟨y, hy, rfl⟩, h⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
        exact ⟨y, hy, h⟩)
    (by rw [relIndex_map_subtype]; exact hfin I hI0)
    (by rw [map_mul_eq, relIndex_map_subtype]; exact hfin _ hspanδ)
  rw [map_mul_eq, map_mul_eq, relIndex_map_subtype, relIndex_map_subtype, relIndex_map_subtype]
    at g1

  have hJ2 : Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B)) ≤ 1 :=
    Submodule.span_le.mpr (by rintro _ ⟨y, _, rfl⟩; exact mem_one_of_mem y.2)
  have hTJ : (Submodule.span (𝓞 L) (Set.range a)).map (LinearMap.mulLeft (𝓞 L) (β : L)) =
      (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).map
        (LinearMap.mulLeft (𝓞 L) (δ : L)) := by
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨y, hy, h⟩ := (hMI (a i)).1 (haM i)
      show (LinearMap.mulLeft (𝓞 L) (β : L)) (a i) ∈ Submodule.map _ _
      rw [LinearMap.mulLeft_apply, h]
      exact ⟨y, Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      have hx : (δ : L) * y / β ∈ M := (hMI _).2 ⟨y, hy, by field_simp⟩
      show (LinearMap.mulLeft (𝓞 L) (δ : L)) (y : L) ∈ Submodule.map _ _
      exact ⟨_, mem_span_of_local hloc hx, by simp only [LinearMap.mulLeft_apply]; field_simp⟩
  have g2 := genIndex_eq (X := (1 : Submodule (𝓞 L) L).toAddSubgroup)
    (J := (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).toAddSubgroup)
    (M := (Submodule.span (𝓞 L) (Set.range a)).toAddSubgroup) hβL hδL
    (fun x hx => hJ2 hx)
    (by rintro _ ⟨y, hy, rfl⟩; exact mul_mem_of_mem β.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact mul_mem_of_mem δ.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact mul_mem_of_mem β.2 hy)
    (by
      intro x
      simp only [Submodule.mem_toAddSubgroup]
      constructor
      · intro hx
        have hm := Submodule.mem_map_of_mem (f := LinearMap.mulLeft (𝓞 L) (β : L)) hx
        rw [hTJ] at hm
        obtain ⟨y, hy, h⟩ := hm
        exact ⟨y, hy, by simpa using h.symm⟩
      · rintro ⟨y, hy, h⟩
        have hm := Submodule.mem_map_of_mem (f := LinearMap.mulLeft (𝓞 L) (δ : L)) hy
        rw [← hTJ] at hm
        obtain ⟨x', hx', h'⟩ := hm
        simp only [LinearMap.mulLeft_apply] at h'
        have hxx : x' = x := mul_left_cancel₀ hβL (h'.trans h.symm)
        exact hxx ▸ hx')
    (by rw [hidx I hI0 (Or.inr hIs)]; exact pow_ne_zero _ (hfin I hI0))
    (by
      rw [map_mul_eq_span δ, hidx _ hspanδ (Or.inl ⟨⟨δ, rfl⟩⟩)]
      exact pow_ne_zero _ (hfin _ hspanδ))
  rw [map_mul_eq_span β, map_mul_eq_span δ, hidx _ hspanβ (Or.inl ⟨⟨β, rfl⟩⟩),
    hidx _ hspanδ (Or.inl ⟨⟨δ, rfl⟩⟩), hidx I hI0 (Or.inr hIs)] at g2
  rw [g1, g2, hrank]
  push_cast
  rw [← mul_pow, ← div_pow, Real.log_pow]
  ring
end InvertibleIdealIndex
end GroundTheory.Heights₂.Heights

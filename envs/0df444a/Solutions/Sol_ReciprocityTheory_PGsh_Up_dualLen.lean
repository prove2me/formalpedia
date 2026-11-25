-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.dualLen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:41:33.385433+00:00
-- url     : https://prove2.me/submissions/5c23d1e9-dc08-4add-b567-05f9a46c0711

import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Theorems.Thm_ReciprocityTheory_PGsh_Up_dualLen_fin
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : DualLenStatement := by
  intro C _ v R _ _ hv d κ _ _ A c hc hkill c₁ hc₁
  classical
  let e := Fintype.equivFin κ
  let A' : Matrix (Fin d) (Fin (Fintype.card κ)) R := A.submatrix id e.symm
  have hmv : ∀ t : Fin (Fintype.card κ) → R, A' *ᵥ t = A *ᵥ (t ∘ e) := by
    intro t
    funext i
    simp only [Matrix.mulVec, dotProduct]
    exact (Fintype.sum_equiv e (fun j => A i j * t (e j)) _ (fun j => by simp [A'])).symm
  have hmv' : ∀ y : Fin d → R, A'ᵀ *ᵥ y = (Aᵀ *ᵥ y) ∘ e.symm := fun y => by funext k; rfl
  have hrange : LinearMap.range A'.mulVecLin = LinearMap.range A.mulVecLin := by
    ext x
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t ∘ e, (hmv t).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨t ∘ e.symm, ?_⟩
      rw [hmv]
      congr 1
      funext j
      simp
  have hz : zSub A' c = zSub A c := by
    ext y
    show (∃ z, A'ᵀ *ᵥ y = c • z) ↔ (∃ z, Aᵀ *ᵥ y = c • z)
    rw [hmv']
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z ∘ e, ?_⟩
      funext j
      have h1 := congrFun hz (e j)
      simpa using h1
    · rintro ⟨z, hz⟩
      refine ⟨z ∘ e.symm, ?_⟩
      rw [hz]
      rfl
  have hk : ∀ w : Fin d → R, ∃ t, A' *ᵥ t = c • w := by
    intro w
    obtain ⟨t, ht⟩ := hkill w
    have h1 : (t ∘ e.symm) ∘ e = t := by funext j; simp
    exact ⟨t ∘ e.symm, by rw [hmv, h1, ht]⟩
  have hc₁' : HasLen v R ((Fin d → R) ⧸ LinearMap.range A'.mulVecLin) c₁ := by
    rw [hrange]; exact hc₁
  obtain ⟨y, hy, hyc⟩ := dualLen_fin hv A' c hc hk hc₁'
  rw [hz] at hy
  exact ⟨y, hy, hyc⟩
end ReciprocityTheory.PGsh.Up

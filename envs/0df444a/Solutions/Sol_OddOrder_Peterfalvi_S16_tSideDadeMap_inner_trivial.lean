-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.tSideDadeMap_inner_trivial
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:37:14.21231+00:00
-- url     : https://prove2.me/submissions/b2a4c417-3b24-419d-8503-1d54dee471b7

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapPrimeTI.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapPrimeTI.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped Classical in
/-- **Peterfalvi (2.7), specialised to the T-side Dade map.**  A class function
supported on `A₁(T) = supportInSubgroup (sigmaSharp T) T` has the same
trivial-character multiplicity before and after applying `τ_T`. -/
theorem _root_.solution [Finite G]
    (hyp : Hypothesis (G := G)) [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφ : φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (tSideDadeMap hyp hG φ) (trivialClassFunction G) =
      ClassFunction.inner φ (trivialClassFunction ↥hyp.base.T) := by
  let side := (tSideDadeSupport_nonempty hG hyp).some
  have hmem : φ ∈ ClassFunction.supportedSubmodule
      (G := ↥hyp.base.T) (k := ℂ)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :=
    (ClassFunction.mem_supportedSubmodule).mpr hφ
  have he : tSideDadeMap hyp hG φ =
      side.dade.dadeMap (k := ℂ) ⟨φ, hmem⟩ := by
    change OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap side.dade
        (side.dade.fullDadeIsometryData) φ =
      side.dade.dadeMap (k := ℂ) ⟨φ, hmem⟩
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
      side.dade _ hφ]
  have hψ : ∀ a : {a : G //
      a ∈ OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T},
      (trivialClassFunction ↥hyp.base.T)
          ⟨a.1, side.dade.subset_L a.2⟩ =
        OddOrder.Peterfalvi.S04.adjointAverageFun side.dade
          (trivialClassFunction G) ⟨a.1, side.dade.subset_L a.2⟩ := by
    intro a
    rw [OddOrder.Peterfalvi.S04.adjointAverageFun, dif_pos a.2]
    simp only [trivialClassFunction_apply, Finset.sum_const, nsmul_eq_mul,
      mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rw [inv_mul_cancel₀]
    exact_mod_cast Nat.card_pos.ne'
  rw [he]
  exact OddOrder.Peterfalvi.S04.adjoint_formula side.dade
    side.dade.dadeMap
    (side.dade.isDadeMap_dadeMap (k := ℂ))
    ⟨φ, hmem⟩ (trivialClassFunction G)
    (trivialClassFunction ↥hyp.base.T) hψ

end OddOrder.Peterfalvi.S16

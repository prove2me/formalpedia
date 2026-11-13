-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.tSideDelta_isReal
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:34:54.967906+00:00
-- url     : https://prove2.me/submissions/e903aaa9-80e6-4142-aa60-b40249af6c94

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapDelta.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapDelta.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical in
/-- The genuine T-side Dade map commutes with complex conjugation on its
supported domain. -/
theorem tSideDadeMap_conj_of_support [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφ : φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    (tSideDadeMap hyp hG φ).conj = tSideDadeMap hyp hG φ.conj := by
  let side := (tSideDadeSupport_nonempty hG hyp).some
  have hbridgeG : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g
    rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]
    rfl
  have hbridgeT : ∀ X : ClassFunction ↥hyp.base.T ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext t
    rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]
    rfl
  change (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap side.dade
      (side.dade.fullDadeIsometryData) φ).conj =
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap side.dade
      (side.dade.fullDadeIsometryData) φ.conj
  rw [hbridgeG, hbridgeT]
  exact (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm
    side.dade (side.dade.fullDadeIsometryData)
    Complex.conjAe.toRingEquiv hφ).symm

open scoped Classical in
/-- **Peterfalvi (14.9): reality of the T-side residual**
`Δ = τ_T(ν₀ - ζ) - 1_G + τ₁ζ`.

The Dade image commutes with conjugation, while coherence identifies the
supported difference `τ_T(ζ - ζ̄)` with `τ₁ζ - τ₁ζ̄`; these two differences
cancel in `Δ̄ - Δ`. -/
theorem _root_.solution [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent
      (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    {ν0 ζ : ClassFunction ↥hyp.base.T ℂ}
    (hζ : ζ ∈ S) (hζc : ζ.conj ∈ S)
    (hβsupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hdiffSupp : (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hβconj : (ν0 - ζ).conj = ν0 - ζ.conj)
    (hExtConj : (coh.extension ζ).conj = coh.extension ζ.conj) :
    ClassFunction.IsReal
      (tSideDadeMap hyp hG (ν0 - ζ) -
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
        coh.extension ζ) := by
  have hdiffSupported : ζ - ζ.conj ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.base.T) S
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :=
    ⟨Submodule.sub_mem _ (Submodule.subset_span hζ)
      (Submodule.subset_span hζc), hdiffSupp⟩
  have hagree : tSideDadeMap hyp hG (ζ - ζ.conj) =
      coh.extension ζ - coh.extension ζ.conj := by
    rw [← coh.extends_on_supported (ζ - ζ.conj) hdiffSupported, map_sub]
  have hτconjSub : (tSideDadeMap hyp hG (ν0 - ζ)).conj -
        tSideDadeMap hyp hG (ν0 - ζ) =
      coh.extension ζ - coh.extension ζ.conj := by
    rw [tSideDadeMap_conj_of_support hyp hG hβsupp]
    calc
      tSideDadeMap hyp hG (ν0 - ζ).conj - tSideDadeMap hyp hG (ν0 - ζ) =
          tSideDadeMap hyp hG ((ν0 - ζ).conj - (ν0 - ζ)) :=
        (map_sub (tSideDadeMap hyp hG) (ν0 - ζ).conj (ν0 - ζ)).symm
      _ = tSideDadeMap hyp hG (ζ - ζ.conj) := by
        congr 1
        rw [hβconj]
        abel
      _ = coh.extension ζ - coh.extension ζ.conj := hagree
  have hτconjEq : (tSideDadeMap hyp hG (ν0 - ζ)).conj =
      (coh.extension ζ - coh.extension ζ.conj) + tSideDadeMap hyp hG (ν0 - ζ) :=
    (sub_eq_iff_eq_add).mp hτconjSub
  rw [ClassFunction.IsReal, ClassFunction.conj_add, ClassFunction.conj_sub,
    hExtConj, hτconjEq]
  have hOneReal :
      (trivialIrreducibleCharacter G : ClassFunction G ℂ).conj =
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) :=
    trivialClassFunction_isReal
  rw [hOneReal]
  abel

end OddOrder.Peterfalvi.S16

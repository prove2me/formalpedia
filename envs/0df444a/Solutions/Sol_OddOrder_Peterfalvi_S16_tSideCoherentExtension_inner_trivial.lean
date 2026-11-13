-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.tSideCoherentExtension_inner_trivial
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:37:13.540486+00:00
-- url     : https://prove2.me/submissions/dde17e69-6e96-407b-81e2-f2d36b0296a6

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_Coherence/NormInequalities.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapDelta.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Theorems.Thm_OddOrder_Peterfalvi_S16_tSideDadeMap_inner_trivial

-- ===== OddOrder/Peterfalvi/S07_Coherence/NormInequalities.lean =====
namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

namespace Hypothesis

variable {S : Set (ClassFunction L ℂ)} {A : Set L}

variable [Fintype L] [Fintype G]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

theorem not_isReal {hyp : Hypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    ¬ χ.IsReal :=
  hyp.no_real_characters hχ

theorem ne_conj {hyp : Hypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    χ ≠ χ.conj := by
  intro hχ_eq
  exact hyp.not_isReal hχ hχ_eq.symm

end Hypothesis

end OddOrder.Peterfalvi.S07

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapDelta.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical in
/-- **Peterfalvi (7.8.a), specialised to the T-side coherent extension.**
If `ζ` and `ζ̄` are distinct orthonormal members of the T-side family, their
difference is `A₁(T)`-supported, and `ζ ⟂ 1_T`, then the coherent image
`τ₁ ζ` is orthogonal to `1_G`.

The proof combines the genuine T-side (2.7) adjoint identity with the generic
equal-degree coherent-pair argument; no cross-maximal input is used. -/
theorem _root_.solution [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (hyp07 : OddOrder.Peterfalvi.S07.Hypothesis
      (L := ↥hyp.base.T) (G := G) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (coh : OddOrder.Peterfalvi.S07.IsCoherent
      (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    {ζ : ClassFunction ↥hyp.base.T ℂ}
    (hζ : ζ ∈ S)
    (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ClassFunction.inner ζ (trivialClassFunction ↥hyp.base.T) = 0)
    (hsupp : (ζ.conj - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (coh.extension ζ) (trivialClassFunction G) = 0 := by
  let side := (tSideDadeSupport_nonempty hG hyp).some
  have hτ_smul : ∀ (c : ℂ) (x : ClassFunction ↥hyp.base.T ℂ),
      tSideDadeMap hyp hG (c • x) = c • tSideDadeMap hyp hG x := by
    intro c x
    simpa only [tSideDadeMap] using
      (OddOrder.Peterfalvi.S09.Cert.dadeIntegralCharacterMap_smul_complex
        side.dade (side.dade.fullDadeIsometryData) c x)
  have hconstG :
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne G =
        trivialClassFunction G := by
    ext g
    simp [OddOrder.Peterfalvi.S09.Hypothesis71.constOne]
  have hconstT :
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne ↥hyp.base.T =
        trivialClassFunction ↥hyp.base.T := by
    ext t
    simp [OddOrder.Peterfalvi.S09.Hypothesis71.constOne]
  have htau1 : ∀ φ : ClassFunction ↥hyp.base.T ℂ,
      φ.support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup
            (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T →
        ClassFunction.inner (tSideDadeMap hyp hG φ)
            (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) =
          ClassFunction.inner φ
            (OddOrder.Peterfalvi.S09.Hypothesis71.constOne ↥hyp.base.T) := by
    intro φ hφ
    rw [hconstG, hconstT]
    exact tSideDadeMap_inner_trivial hyp hG hφ
  have hζc : ζ.conj ∈ S := hyp07.conjugate_closed hζ
  have hζne : ζ ≠ ζ.conj := hyp07.ne_conj hζ
  have hζc1 : ClassFunction.inner ζ.conj
      (trivialClassFunction ↥hyp.base.T) = 0 := by
    rw [← trivialClassFunction_isReal,
      OddOrder.RepresentationTheory.inner_conj_conj, hζ1, star_zero]
  have h :=
    OddOrder.Peterfalvi.S09.Cert.coherence_extension_orthogonal_constOne
      coh hτ_smul htau1 hζ hζc hζirr.inner_self_eq_one
      hζirr.conj.inner_self_eq_one
      (hyp07.pairwise_orthogonal hζ hζc hζne) hsupp
      (by rw [hconstT]; exact hζ1)
      (by rw [hconstT]; exact hζc1)
  rwa [hconstG] at h

end OddOrder.Peterfalvi.S16

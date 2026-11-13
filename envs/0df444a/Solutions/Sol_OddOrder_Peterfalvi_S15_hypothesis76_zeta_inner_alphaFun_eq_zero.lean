-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.hypothesis76_zeta_inner_alphaFun_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:47:27.376713+00:00
-- url     : https://prove2.me/submissions/ca012014-6397-4ec1-8c83-aeaa15d1818b

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section GenericAlpha

variable {A : Set G} {L : Subgroup G}

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **Generic (13.5.a) `P'`-kernel orthogonality**: the full-`↥L` pairing of a `P'`-non-kernel
family member `ζ_{i₁}` against the `P'`-kernel tail `α` vanishes — each tail constituent is a
family member of a *different* fibre (the kernel property separates them), and distinct-fibre
induced characters are orthogonal (`inner_induce_eq_zero_of_not_conj` via `zeta_induced`). -/
theorem _root_.solution [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) (i₁ : Fin (H76.n + 1))
    (hi₁ker : ¬ ((P' : Set ↥L) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i₁))) :
    ∑ x : ↥L, H76.zeta i₁ x * (starRingEnd ℂ) (hypothesis76AlphaFun H76 P' χ x) = 0 := by
  classical
  have hKn : (H76.H.subgroupOf L).Normal :=
    OddOrder.Peterfalvi.S09.Cert.subgroupOf_normal_of_conj H76.H_normal_in_L
  -- The sum is `|L|·⟨ζ_{i₁}, alphaCF⟩` with `alphaCF` the class-function form of the tail.
  set alphaCF : ClassFunction ↥L ℂ :=
    ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
          (fun i => (P' : Set ↥L) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
        (star (H76.cCoeff χ i) / H76.zetaNormSq i) • H76.zeta i with halphaCF
  have happly : ∀ x : ↥L, alphaCF x = hypothesis76AlphaFun H76 P' χ x := by
    intro x
    rw [halphaCF, OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply,
      hypothesis76AlphaFun]
    exact Finset.sum_congr rfl (fun i _ => by rw [ClassFunction.smul_apply])
  have hsum : ∑ x : ↥L, H76.zeta i₁ x * (starRingEnd ℂ)
      (hypothesis76AlphaFun H76 P' χ x)
      = ClassFunction.innerSum (H76.zeta i₁) alphaCF := by
    rw [ClassFunction.innerSum]
    exact Finset.sum_congr rfl (fun x _ => by rw [happly, starRingEnd_apply])
  rw [hsum, ← ClassFunction.card_mul_inner]
  have hinner0 : ClassFunction.inner (H76.zeta i₁) alphaCF = 0 := by
    rw [halphaCF, inner_sum_right]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [OddOrder.RepresentationTheory.inner_smul_right]
    have hjker := (Finset.mem_filter.mp hj).2
    have hzne : H76.zeta i₁ ≠ H76.zeta j := fun heq => hi₁ker (heq ▸ hjker)
    obtain ⟨θ, hθ⟩ := H76.zeta_induced i₁
    obtain ⟨θ', hθ'⟩ := H76.zeta_induced j
    have hz0 : ClassFunction.inner (H76.zeta i₁) (H76.zeta j) = 0 := by
      rw [hθ, hθ']
      refine OddOrder.RepresentationTheory.inner_induce_eq_zero_of_not_conj θ θ'
        (fun g hconj => ?_)
      refine hzne ?_
      rw [hθ, hθ', ← hconj, OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy,
        OddOrder.RepresentationTheory.ClassFunction.induce_conjBy_eq]
    rw [hz0, mul_zero]
  rw [hinner0, mul_zero]

end GenericAlpha

end OddOrder.Peterfalvi.S15

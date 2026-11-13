-- Prove2me | solution 1 for OddOrder.Peterfalvi.S09.Hypothesis79.zetaImage_cross_eq_zero_of_conjIndex
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T08:22:17.337207+00:00
-- url     : https://prove2.me/submissions/27bfdee9-e6b2-4501-9685-8984d98be1c6

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_FrobeniusCrossOrtho.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_CrossOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusHypothesis79
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterProduct
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional

-- ===== OddOrder/Peterfalvi/S09_FrobeniusCrossOrtho.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

/-- **Distinct irreducible characters are orthogonal** (bundling helper for the conjIndex bridge).
`⟨χ, ψ⟩ = 0` when `χ, ψ` are irreducible class functions with `χ ≠ ψ`. -/
private theorem inner_eq_zero_of_ne_of_isIrreducible {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] {χ ψ : ClassFunction L ℂ}
    (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ) (hne : χ ≠ ψ) :
    ClassFunction.inner χ ψ = 0 := by
  have h := irreducibleCharacter_inner_eq_ite (⟨χ, hχ⟩ : IrreducibleCharacter L) ⟨ψ, hψ⟩
  rwa [if_neg (fun heq => hne (congrArg Subtype.val heq))] at h

namespace Hypothesis79

variable {G : Type*} [Group G] [Fintype G]

variable {A₁ : Set G} {L₁ : Subgroup G} [Fintype L₁] [Invertible (Nat.card L₁ : ℂ)]

variable {A₂ : Set G} {L₂ : Subgroup G} [Fintype L₂]

variable [Invertible (Nat.card L₂ : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- **Cross-orthogonality of the two distinguished coherent images** (Peterfalvi (7.9);
coq `disjoint_coherent_ortho`).  Given the conjugate images `b = ζ̄₁^{ν₁}`, `d = ζ̄₂^{ν₂}` with

* `b, d ∈ ℤ[Irr G]`, both of norm `1`, orthogonal to `ζ₁^{ν₁}`, `ζ₂^{ν₂}` respectively
  (`{ζ_i^ν, ζ̄_i^ν}` orthonormal — the isometry of `ν`), and
* the differences `ζ_i^ν − ζ̄_i^ν` supported in the two **disjoint** Dade supports
  `A_i^{τ_i}` (`Hypothesis79.dadeSupport_disjoint`; the coherent extension agrees with `τ_i` on the
  equal-degree difference),

the two distinguished images are orthogonal: `⟨ζ₁^{ν₁}, ζ₂^{ν₂}⟩ = 0`.  The `hzeta_cross` input of
the (7.9) `conclusion` producers, discharged via `orthonormal_vchar_diff_ortho`. -/
theorem zetaImage_cross_eq_zero_of_conjugate_images (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {b d : ClassFunction G ℂ}
    (haZ : H79.firstZetaImage ∈ ZIrr G) (hbZ : b ∈ ZIrr G)
    (hcZ : H79.secondZetaImage ∈ ZIrr G) (hdZ : d ∈ ZIrr G)
    (han : ClassFunction.inner H79.firstZetaImage H79.firstZetaImage = 1)
    (hbn : ClassFunction.inner b b = 1)
    (hcn : ClassFunction.inner H79.secondZetaImage H79.secondZetaImage = 1)
    (hdn : ClassFunction.inner d d = 1)
    (hab : ClassFunction.inner H79.firstZetaImage b = 0)
    (hcd : ClassFunction.inner H79.secondZetaImage d = 0)
    (hab_supp :
      (H79.firstZetaImage - b).support ⊆ H79.first.hyp76.hyp71.hyp.dadeSupport)
    (hcd_supp :
      (H79.secondZetaImage - d).support ⊆ H79.second.hyp76.hyp71.hyp.dadeSupport) :
    ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0 := by
  refine orthonormal_vchar_diff_ortho haZ hbZ hcZ hdZ han hbn hcn hdn hab hcd ?_ ?_ ?_
  · -- `⟨ζ₁^ν − ζ̄₁^ν, ζ₂^ν − ζ̄₂^ν⟩ = 0`: the two differences live in disjoint Dade supports.
    apply ClassFunction.inner_eq_zero_of_disjoint_support
    rw [Set.disjoint_left]
    intro g hg₁ hg₂
    exact Set.disjoint_left.mp H79.dadeSupport_disjoint (hab_supp hg₁) (hcd_supp hg₂)
  · -- `ζ₁^ν 1 = ζ̄₁^ν 1`: the difference vanishes at `1` since `1 ∉ A₁^{τ₁}`.
    have hz : (H79.firstZetaImage - b) (1 : G) = 0 := by
      by_contra h
      exact H79.first.hyp76.hyp71.hyp.one_notMem_dadeSupport
        (hab_supp (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz
  · -- `ζ₂^ν 1 = ζ̄₂^ν 1`, symmetrically.
    have hz : (H79.secondZetaImage - d) (1 : G) = 0 := by
      by_contra h
      exact H79.second.hyp76.hyp71.hyp.one_notMem_dadeSupport
        (hcd_supp (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz

/-- **`hzeta_cross` from a conjugate family index** (Peterfalvi (7.9), the isometry half of coq
`disjoint_coherent_ortho`).  The conjugate image `b = ζ̄₁^{ν₁}` is `ν₁` applied to a *family member*
`ζ_{j₁} = ζ̄₁` (index `j₁ ≠ ind1H`), so its orthonormality against `ζ₁^{ν₁}` is supplied by the
`ν`-isometry (`nu_isometry`): `⟨b,b⟩ = ⟨ζ̄₁,ζ̄₁⟩ = 1`, `⟨ζ₁^ν, b⟩ = ⟨ζ₁, ζ̄₁⟩ = 0` (distinct
irreducibles, `ζ₁ ≠ ζ̄₁`).  Reduces `hzeta_cross` to just the conjugate-index data plus the two
Dade-agreement supports — the residual Frobenius-level inputs (`hj₁`, `hζ₁ne_conj`, `hab_supp`
discharged from `coherence_hagree_dadeMap`, `not_isReal_of_ne_trivial_of_odd_card'`, `conj_induce`
+ `placedInducedFamily.cover`). -/
theorem _root_.solution (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {A_prime₁ : Set L₁} {τ₁ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₁ G}
    (hcoh₁ : OddOrder.Peterfalvi.S07.IsCoherent τ₁ H79.first.sourceSet A_prime₁)
    (hnu₁ : H79.first.nu = hcoh₁.extension)
    {A_prime₂ : Set L₂} {τ₂ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L₂ G}
    (hcoh₂ : OddOrder.Peterfalvi.S07.IsCoherent τ₂ H79.second.sourceSet A_prime₂)
    (hnu₂ : H79.second.nu = hcoh₂.extension)
    (hz₁irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))
    (hz₂irr : IsIrreducibleCharacter (H79.second.hyp76.zeta H79.second.zetaDistinct))
    {j₁ : Fin (H79.first.hyp76.n + 1)} (hj₁ne_ind : j₁ ≠ H79.first.ind1H)
    (hj₁ : H79.first.hyp76.zeta j₁
        = (H79.first.hyp76.zeta H79.first.zetaDistinct).conj)
    (hζ₁ne_conj : H79.first.hyp76.zeta H79.first.zetaDistinct
        ≠ (H79.first.hyp76.zeta H79.first.zetaDistinct).conj)
    {j₂ : Fin (H79.second.hyp76.n + 1)} (hj₂ne_ind : j₂ ≠ H79.second.ind1H)
    (hj₂ : H79.second.hyp76.zeta j₂
        = (H79.second.hyp76.zeta H79.second.zetaDistinct).conj)
    (hζ₂ne_conj : H79.second.hyp76.zeta H79.second.zetaDistinct
        ≠ (H79.second.hyp76.zeta H79.second.zetaDistinct).conj)
    (hab_supp :
      (H79.firstZetaImage - H79.first.nu (H79.first.hyp76.zeta j₁)).support
        ⊆ H79.first.hyp76.hyp71.hyp.dadeSupport)
    (hcd_supp :
      (H79.secondZetaImage - H79.second.nu (H79.second.hyp76.zeta j₂)).support
        ⊆ H79.second.hyp76.hyp71.hyp.dadeSupport) :
    ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0 := by
  refine H79.zetaImage_cross_eq_zero_of_conjugate_images
    (H79.first.nu_zetaDistinct_mem_ZIrr_of_isCoherent hcoh₁ hnu₁)
    (H79.first.nu_zeta_mem_ZIrr_of_isCoherent hcoh₁ hnu₁ hj₁ne_ind)
    (H79.second.nu_zetaDistinct_mem_ZIrr_of_isCoherent hcoh₂ hnu₂)
    (H79.second.nu_zeta_mem_ZIrr_of_isCoherent hcoh₂ hnu₂ hj₂ne_ind)
    ?_ ?_ ?_ ?_ ?_ ?_ hab_supp hcd_supp
  · -- `⟨ζ₁^ν, ζ₁^ν⟩ = ⟨ζ₁, ζ₁⟩ = 1`.
    rw [show H79.firstZetaImage
        = H79.first.nu (H79.first.hyp76.zeta H79.first.zetaDistinct) from rfl,
      H79.first.nu_isometry _ _ H79.first.zetaDistinct_ne_ind1H H79.first.zetaDistinct_ne_ind1H]
    exact IsIrreducibleCharacter.inner_self_eq_one hz₁irr
  · -- `⟨ζ̄₁^ν, ζ̄₁^ν⟩ = ⟨ζ̄₁, ζ̄₁⟩ = 1`.
    rw [H79.first.nu_isometry _ _ hj₁ne_ind hj₁ne_ind, hj₁]
    exact IsIrreducibleCharacter.inner_self_eq_one (IsIrreducibleCharacter.conj hz₁irr)
  · -- `⟨ζ₂^ν, ζ₂^ν⟩ = 1`.
    rw [show H79.secondZetaImage
        = H79.second.nu (H79.second.hyp76.zeta H79.second.zetaDistinct) from rfl,
      H79.second.nu_isometry _ _ H79.second.zetaDistinct_ne_ind1H H79.second.zetaDistinct_ne_ind1H]
    exact IsIrreducibleCharacter.inner_self_eq_one hz₂irr
  · -- `⟨ζ̄₂^ν, ζ̄₂^ν⟩ = 1`.
    rw [H79.second.nu_isometry _ _ hj₂ne_ind hj₂ne_ind, hj₂]
    exact IsIrreducibleCharacter.inner_self_eq_one (IsIrreducibleCharacter.conj hz₂irr)
  · -- `⟨ζ₁^ν, ζ̄₁^ν⟩ = ⟨ζ₁, ζ̄₁⟩ = 0` (distinct irreducibles `ζ₁ ≠ ζ̄₁`).
    rw [show H79.firstZetaImage
        = H79.first.nu (H79.first.hyp76.zeta H79.first.zetaDistinct) from rfl,
      H79.first.nu_isometry _ _ H79.first.zetaDistinct_ne_ind1H hj₁ne_ind, hj₁]
    exact inner_eq_zero_of_ne_of_isIrreducible hz₁irr
      (IsIrreducibleCharacter.conj hz₁irr) hζ₁ne_conj
  · -- `⟨ζ₂^ν, ζ̄₂^ν⟩ = 0`.
    rw [show H79.secondZetaImage
        = H79.second.nu (H79.second.hyp76.zeta H79.second.zetaDistinct) from rfl,
      H79.second.nu_isometry _ _ H79.second.zetaDistinct_ne_ind1H hj₂ne_ind, hj₂]
    exact inner_eq_zero_of_ne_of_isIrreducible hz₂irr
      (IsIrreducibleCharacter.conj hz₂irr) hζ₂ne_conj

end Hypothesis79

end OddOrder.Peterfalvi.S09

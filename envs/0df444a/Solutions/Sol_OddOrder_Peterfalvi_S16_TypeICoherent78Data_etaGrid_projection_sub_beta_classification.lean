-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.TypeICoherent78Data.etaGrid_projection_sub_beta_classification
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:08:15.525931+00:00
-- url     : https://prove2.me/submissions/328c7e30-c33b-4364-889b-424c41af4ee5

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean
--   OddOrder/Peterfalvi/S16_GridExpansion.lean
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/CoherentProjectionRigidity.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- The source difference `Ind 1_H - ζ` is virtual when the `Ind 1_H`
source term is virtual and the distinguished `ζ` is irreducible. -/
theorem sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L :=
  Submodule.sub_mem _ hindZ hzeta_irr.mem_ZIrr

/-- Virtuality of `Ind 1_H` and irreducibility of `ζ` supply the
virtual-character input needed by the Dade bridge for `β`. -/
theorem beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.beta ∈ ZIrr G :=
  H78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr
    (H78.sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible hindZ hzeta_irr)

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S16_GridExpansion.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Signed-irreducible two-term classification.**  Let `α`, `β`, and `χ` be norm-one
virtual characters, with `α ⊥ β`.  If `⟨α - β, χ⟩ = 1`, then `χ = α` or `χ = -β`.

This is the Lean form of the `cfdot_add_dirr_eq1` step at the end of Peterfalvi (14.11.2):
after the orthogonal projection has produced a norm-one virtual residual `χ`, its pairing with
`ψ^{τ₁} - ψ̄^{τ₁}` determines which of the two signed irreducibles it is. -/
theorem eq_left_or_neg_right_of_inner_sub_eq_one [Finite G]
    {α β χ : ClassFunction G ℂ}
    (hαZ : α ∈ ZIrr G) (hβZ : β ∈ ZIrr G) (hχZ : χ ∈ ZIrr G)
    (hα1 : ClassFunction.inner α α = 1)
    (hβ1 : ClassFunction.inner β β = 1)
    (hχ1 : ClassFunction.inner χ χ = 1)
    (hαβ : ClassFunction.inner α β = 0)
    (hpair : ClassFunction.inner (α - β) χ = 1) :
    χ = α ∨ χ = -β := by
  have hrel : ClassFunction.inner α χ - ClassFunction.inner β χ = 1 := by
    rwa [ClassFunction.inner_sub_left] at hpair
  by_cases hαχ : ClassFunction.inner α χ = 0
  · right
    have hβχ : ClassFunction.inner β χ = -1 := by
      rw [hαχ, zero_sub] at hrel
      linear_combination -hrel
    have hβχ_ne : ClassFunction.inner β χ ≠ 0 := by rw [hβχ]; norm_num
    have hχeq := eq_inner_smul_of_inner_ne_zero hβZ hχZ hβ1 hχ1 hβχ_ne
    rw [hβχ] at hχeq
    simpa using hχeq
  · left
    have hβχ : ClassFunction.inner β χ = 0 := by
      by_contra hβχ_ne
      have hχeq := eq_inner_smul_of_inner_ne_zero hβZ hχZ hβ1 hχ1 hβχ_ne
      apply hαχ
      rw [hχeq, OddOrder.RepresentationTheory.inner_smul_right, hαβ, mul_zero]
    have hαχ_eq : ClassFunction.inner α χ = 1 := by
      rwa [hβχ, sub_zero] at hrel
    have hχeq := eq_inner_smul_of_inner_ne_zero hαZ hχZ hα1 hχ1 hαχ
    rw [hαχ_eq] at hχeq
    simpa using hχeq

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_PairingCoherence.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- The zeta family of `h78` is the placed induced family (definitional). -/
theorem h78_zeta_eq (i : Fin (data.n + 1)) :
    (data.h78 hG).hyp76.zeta i = data.zeta i := rfl

/-- The distinguished index of `h78` is `0` (definitional). -/
theorem h78_zetaDistinct_eq : (data.h78 hG).zetaDistinct = 0 := rfl

/-- The principal index of `h78` is `ind1H` (definitional). -/
theorem h78_ind1H_eq : (data.h78 hG).ind1H = data.ind1H := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The distinguished `ζ_0` is irreducible** (Frobenius kernel induction,
[Is] Thm 6.34). -/
theorem h78_zeta_irreducible :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct) := by
  have := data.kernelIn_normal
  rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ 0)
    data.theta_zero_ne_trivial

/-- **The induced principal `ζ_{ind1H} = Ind 1_H` is a virtual character.** -/
theorem h78_ind_mem_ZIrr :
    (data.h78 hG).hyp76.zeta (data.h78 hG).ind1H ∈ ZIrr ↥L := by
  have := data.kernelIn_normal
  rw [data.h78_ind1H_eq, data.h78_zeta_eq]
  exact ClassFunction.induce_mem_ZIrr _ (data.θ data.ind1H).property.mem_ZIrr

/-- **The `(7.8)` coherent source set equals the (12.1) family `S`.** -/
theorem h78_sourceSet_eq : (data.h78 hG).sourceSet = data.typeIHyp.Sset := by
  have := data.kernelIn_normal
  ext φ
  constructor
  · rintro ⟨idx, hidx, rfl⟩
    exact data.zeta_mem_Sset hidx
  · rintro ⟨θ', hθ'_ne, rfl⟩
    obtain ⟨j, hj⟩ := data.cover θ'
    have hj' : data.zeta j = ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ) := hj
    refine ⟨j, ?_, hj'⟩
    intro hjind
    apply induce_ne_trivialChar_induce data.kernelIn θ' hθ'_ne
    rw [← hj', show j = data.ind1H from hjind]
    change ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
      = ClassFunction.induce data.kernelIn
        ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
          ClassFunction _ ℂ)
    rw [data.triv]

/-- **The bundle coherence as an `IsCoherent` over the `(7.8)` `sourceSet`** (transport along
`h78_sourceSet_eq`, keeping the same extension `ν`). -/
noncomputable def isCoherentSourceSet :
    OddOrder.Peterfalvi.S07.IsCoherent data.typeIHyp.tau (data.h78 hG).sourceSet
      data.typeIHyp.A where
  nonzero := (data.h78_sourceSet_eq hG).symm ▸ data.coh.nonzero
  extension := data.coh.extension
  extension_inner_eq := fun φ ψ hφ hψ => data.coh.extension_inner_eq φ ψ
    (data.h78_sourceSet_eq hG ▸ hφ) (data.h78_sourceSet_eq hG ▸ hψ)
  extends_on_supported := fun φ hφ => data.coh.extends_on_supported φ
    (data.h78_sourceSet_eq hG ▸ hφ)
  extension_mem_ZIrr := fun φ hφ => data.coh.extension_mem_ZIrr φ
    (data.h78_sourceSet_eq hG ▸ hφ)

set_option backward.isDefEq.respectTransparency false in
/-- **The conjugate `ζ̄_0` is a family member**: there is `j₁ ≠ ind1H` with
`ζ_{j₁} = ζ̄_0` (`conjPerm` of the distinguished source is covered). -/
theorem exists_conjIndex :
    ∃ j₁, j₁ ≠ (data.h78 hG).ind1H ∧
      (data.h78 hG).hyp76.zeta j₁
        = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
  have := data.kernelIn_normal
  have hconj_eq : ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj
      = ClassFunction.induce data.kernelIn
          ((IrreducibleCharacter.conjPerm _ (data.θ 0)) : ClassFunction _ ℂ) := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq, conj_induce]
    exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe (data.θ 0)).symm
  obtain ⟨j₁, hj₁_range⟩ := data.cover (IrreducibleCharacter.conjPerm _ (data.θ 0))
  have hj₁_conj : (data.h78 hG).hyp76.zeta j₁
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
    rw [data.h78_zeta_eq, hconj_eq]; exact hj₁_range
  refine ⟨j₁, ?_, hj₁_conj⟩
  intro hj1
  apply data.ind1H_ne_zero
  have hzeta_inj : Function.Injective (data.h78 hG).hyp76.zeta := data.inj
  refine (hzeta_inj ?_).symm
  -- `ζ_{ind1H}` is real (`Ind 1_H`), and `ζ_{ind1H} = ζ_{j₁} = ζ̄_0`.
  have e1 : (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
    rw [← show j₁ = (data.h78 hG).ind1H from hj1]; exact hj₁_conj
  have e2 : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    change (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)).conj
      = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
    rw [data.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  calc (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)
      = ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj := by
        rw [e1, ClassFunction.conj_conj]
    _ = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := e2

/-- **No nontrivial family member is real** (odd order): `ζ_i ≠ ζ̄_i` for `i ≠ ind1H`. -/
theorem zeta_ne_conj_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hodd : Odd (Nat.card G)) :
    (data.h78 hG).hyp76.zeta i ≠ ((data.h78 hG).hyp76.zeta i).conj := by
  have := data.kernelIn_normal
  have hirr : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
    rw [data.h78_zeta_eq]
    exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
      (data.theta_ne_trivial hi)
  have hodd_L : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hK_ne_top : data.kernelIn ≠ ⊤ := by
    intro hKtop
    refine data.hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := data.hFrob.isComplement.disjoint
    rw [show (data.typeIHyp.typeI.typeF.H).subgroupOf L = data.kernelIn from rfl, hKtop]
      at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < (data.kernelIn).index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  -- `ζ_i(1) = [L:H]·θ_i(1) ≥ [L:H] > 1`, so `ζ_i` is nontrivial.
  obtain ⟨di, hdi_pos, hdi⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (data.θ i)
  have hdeg : (data.h78 hG).hyp76.zeta i (1 : ↥L)
      = ((data.kernelIn).index : ℂ) * (di : ℂ) := by
    rw [data.h78_zeta_eq]
    change ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) = _
    rw [ClassFunction.induce_apply_one, hdi]
  have hne_triv : (⟨(data.h78 hG).hyp76.zeta i, hirr⟩ :
      IrreducibleCharacter ↥L) ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : (data.h78 hG).hyp76.zeta i = trivialClassFunction ↥L := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : ((data.kernelIn).index : ℂ) * (di : ℂ) = 1 := by
      rw [← hdeg, hcf, trivialClassFunction_apply]
    have : (data.kernelIn).index * di = 1 := by exact_mod_cast hone
    have h1 : (data.kernelIn).index = 1 := by
      rcases Nat.eq_one_of_mul_eq_one_right this with h; omega
    omega
  intro h
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv h.symm

/-- **Each `ζ_i^ν` (`i ≠ ind1H`) is a unit-norm virtual character.** -/
theorem nu_zeta_norm_one {i : Fin (data.n + 1)} (hi : i ≠ (data.h78 hG).ind1H) :
    ClassFunction.inner ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i))
      ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i)) = 1 := by
  have := data.kernelIn_normal
  rw [(data.h78 hG).nu_isometry i i hi hi]
  have hirr : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
    rw [data.h78_zeta_eq]
    exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
      (data.theta_ne_trivial (by rw [← data.h78_ind1H_eq hG]; exact hi))
  exact IsIrreducibleCharacter.inner_self_eq_one hirr

/-- **Each nontrivial family member induces irreducibly** (general-index form of
`h78_zeta_irreducible`). -/
theorem zeta_irreducible_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
  have := data.kernelIn_normal
  rw [data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
    (data.theta_ne_trivial hi)

/-- **`⟨ζ_i^ν, ζ̄_i^ν⟩ = 0`**: the conjugate pair is orthonormal (`ν`-isometry +
distinct irreducibles). -/
theorem nu_zeta_inner_nu_conj_eq_zero (hodd : Odd (Nat.card G))
    {i i' : Fin (data.n + 1)} (hi : i ≠ data.ind1H)
    (hi'_ne : i' ≠ (data.h78 hG).ind1H)
    (hi' : (data.h78 hG).hyp76.zeta i' = ((data.h78 hG).hyp76.zeta i).conj) :
    ClassFunction.inner ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i))
      ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta i')) = 0 := by
  rw [(data.h78 hG).nu_isometry i i' hi hi'_ne]
  have hirr_i := data.zeta_irreducible_at hG hi
  have hirr_i' : IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i') :=
    data.zeta_irreducible_at hG (by rw [← data.h78_ind1H_eq hG]; exact hi'_ne)
  have hne : (data.h78 hG).hyp76.zeta i ≠ (data.h78 hG).hyp76.zeta i' := by
    rw [hi']
    exact data.zeta_ne_conj_at hG hi hodd
  have h := irreducibleCharacter_inner_eq_ite
    (⟨_, hirr_i⟩ : IrreducibleCharacter ↥L) ⟨_, hirr_i'⟩
  rwa [if_neg (fun heq => hne (congrArg Subtype.val heq))] at h

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/CoherentProjectionRigidity.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped BigOperators

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (14.11.2), classification of the removed unit-norm character.**
Let `X` be an integral `eta`-grid sum and `chi = X - beta`.  If every coherent family image is
orthogonal to the grid and `chi` has norm one, then `chi` is the distinguished coherent image or
the negative coherent image of its conjugate.  The proof pairs `chi` with the orthonormal
conjugate pair.  The (7.8.a) decomposition gives pairings `a - 1` and `a` against `beta`, so their
difference pairs with `chi` as one; norm-one rigidity in `Z[Irr G]` then gives the two alternatives.
-/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L : Subgroup G} (data : TypeICoherent78Data L)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin hyp.q → Fin hyp.p → ℤ)
    (heta : ∀ (t : Fin (data.n + 1)), t ≠ data.ind1H →
      ∀ i j, ClassFunction.inner
        ((data.h78 hG).nu ((data.h78 hG).hyp76.zeta t)) (hyp.eta i j) = 0)
    (hchi1 : ClassFunction.inner
      (etaGridProjection hyp m - (data.h78 hG).beta)
      (etaGridProjection hyp m - (data.h78 hG).beta) = 1) :
    let χ := etaGridProjection hyp m - (data.h78 hG).beta
    χ = (data.h78 hG).nu ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct) ∨
    χ = -((data.h78 hG).nu
      ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj) := by
  classical
  let := data.kernelIn_normal
  let H78 := data.h78 hG
  let A : ClassFunction G ℂ := H78.nu (H78.hyp76.zeta H78.zetaDistinct)
  obtain ⟨j₁, hj₁ne, hj₁⟩ := data.exists_conjIndex hG
  let B : ClassFunction G ℂ := H78.nu (H78.hyp76.zeta j₁)
  let X : ClassFunction G ℂ := etaGridProjection hyp m
  let χ : ClassFunction G ℂ := X - H78.beta
  let BD := data.betaDecomp hG
  have hzd_ne : H78.zetaDistinct ≠ data.ind1H := by
    rw [← data.h78_ind1H_eq hG]
    exact H78.zetaDistinct_ne_ind1H
  have hj₁ne_data : j₁ ≠ data.ind1H := by
    rw [← data.h78_ind1H_eq hG]
    exact hj₁ne
  have hAZ : A ∈ ZIrr G := by
    change H78.nu (H78.hyp76.zeta H78.zetaDistinct) ∈ ZIrr G
    exact H78.nu_zetaDistinct_mem_ZIrr_of_isCoherent
      (data.isCoherentSourceSet hG) rfl
  have hBZ : B ∈ ZIrr G := by
    change H78.nu (H78.hyp76.zeta j₁) ∈ ZIrr G
    exact H78.nu_zeta_mem_ZIrr_of_isCoherent
      (data.isCoherentSourceSet hG) rfl hj₁ne
  have hA1 : ClassFunction.inner A A = 1 := by
    change ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1
    exact data.nu_zeta_norm_one hG H78.zetaDistinct_ne_ind1H
  have hB1 : ClassFunction.inner B B = 1 := by
    change ClassFunction.inner (H78.nu (H78.hyp76.zeta j₁))
      (H78.nu (H78.hyp76.zeta j₁)) = 1
    exact data.nu_zeta_norm_one hG hj₁ne
  have hAB : ClassFunction.inner A B = 0 := by
    change ClassFunction.inner (H78.nu (H78.hyp76.zeta H78.zetaDistinct))
      (H78.nu (H78.hyp76.zeta j₁)) = 0
    exact data.nu_zeta_inner_nu_conj_eq_zero hG hG.odd hzd_ne hj₁ne hj₁
  have hXZ : X ∈ ZIrr G := by
    change etaGridProjection hyp m ∈ ZIrr G
    rw [etaGridProjection]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro j _
    rw [Int.cast_smul_eq_zsmul]
    exact (ZIrr G).smul_mem (m i j) (eta_mem_ZIrr hyp i j)
  have hbetaZ : H78.beta ∈ ZIrr G :=
    H78.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
      (data.h78_ind_mem_ZIrr hG) (data.h78_zeta_irreducible hG)
  have hchiZ : χ ∈ ZIrr G := Submodule.sub_mem (ZIrr G) hXZ hbetaZ
  have hchi1' : ClassFunction.inner χ χ = 1 := by
    change ClassFunction.inner (etaGridProjection hyp m - H78.beta)
      (etaGridProjection hyp m - H78.beta) = 1
    exact hchi1
  have hAX : ClassFunction.inner A X = 0 := by
    change ClassFunction.inner A (etaGridProjection hyp m) = 0
    rw [etaGridProjection, inner_sum_right]
    apply Finset.sum_eq_zero
    intro i _
    rw [inner_sum_right]
    apply Finset.sum_eq_zero
    intro j _
    rw [ClassFunction.inner_smul_right,
      heta H78.zetaDistinct hzd_ne i j, mul_zero]
  have hBX : ClassFunction.inner B X = 0 := by
    change ClassFunction.inner B (etaGridProjection hyp m) = 0
    rw [etaGridProjection, inner_sum_right]
    apply Finset.sum_eq_zero
    intro i _
    rw [inner_sum_right]
    apply Finset.sum_eq_zero
    intro j _
    rw [ClassFunction.inner_smul_right, heta j₁ hj₁ne_data i j, mul_zero]
  have hsource_orth : ∀ i j : Fin (H78.hyp76.n + 1), i ≠ j →
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta j) = 0 := by
    intro i j hij
    rw [data.h78_zeta_eq hG, data.h78_zeta_eq hG]
    exact (induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj) i j hij
  have hsource_nonzero : ∀ i : Fin (H78.hyp76.n + 1),
      ClassFunction.inner (H78.hyp76.zeta i) (H78.hyp76.zeta i) ≠ 0 := by
    intro i
    rw [data.h78_zeta_eq hG]
    exact induce_norm_ne_zero data.kernelIn (data.θ i)
  have hzeta0_ne : H78.hyp76.zeta 0 (1 : ↥L) ≠ 0 := by
    obtain ⟨θ0, hθ0⟩ := H78.hyp76.zeta_induced 0
    rw [hθ0]
    exact induce_apply_one_ne_zero _ θ0
  have hzd0 : H78.zetaDistinct = 0 := data.h78_zetaDistinct_eq hG
  have hconj_degree : H78.hyp76.zeta j₁ (1 : ↥L) =
      H78.hyp76.zeta 0 (1 : ↥L) := by
    rw [hj₁, ClassFunction.conj_apply, hzd0, data.h78_zeta_eq hG]
    exact induce_apply_one_star data.kernelIn (data.θ 0)
  have hWA : ClassFunction.inner H78.weightedNuSum A = 1 := by
    have h := inner_weightedNuSum_nu_gen H78.hyp76.zeta hsource_orth
      hsource_nonzero hzeta0_ne H78.nu H78.nu_isometry
      (j := H78.zetaDistinct) H78.zetaDistinct_ne_ind1H
    rw [hzd0] at h
    change ClassFunction.inner H78.weightedNuSum
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 1
    rw [Hypothesis78.weightedNuSum, hzd0, h, div_self hzeta0_ne]
  have hWB : ClassFunction.inner H78.weightedNuSum B = 1 := by
    have h := inner_weightedNuSum_nu_gen H78.hyp76.zeta hsource_orth
      hsource_nonzero hzeta0_ne H78.nu H78.nu_isometry (j := j₁) hj₁ne
    change ClassFunction.inner H78.weightedNuSum (H78.nu (H78.hyp76.zeta j₁)) = 1
    rw [Hypothesis78.weightedNuSum, hzd0, h, hconj_degree, div_self hzeta0_ne]
  have hOneA : ClassFunction.inner (Hypothesis71.constOne G) A = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]
    change star (ClassFunction.inner
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) (Hypothesis71.constOne G)) = 0
    rw [BD.orth_one H78.zetaDistinct H78.zetaDistinct_ne_ind1H, star_zero]
  have hOneB : ClassFunction.inner (Hypothesis71.constOne G) B = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm]
    change star (ClassFunction.inner
      (H78.nu (H78.hyp76.zeta j₁)) (Hypothesis71.constOne G)) = 0
    rw [BD.orth_one j₁ hj₁ne, star_zero]
  have hGammaA : ClassFunction.inner BD.Gamma A = 0 := by
    change ClassFunction.inner BD.Gamma
      (H78.nu (H78.hyp76.zeta H78.zetaDistinct)) = 0
    exact BD.Gamma_orth_nu H78.zetaDistinct H78.zetaDistinct_ne_ind1H
  have hGammaB : ClassFunction.inner BD.Gamma B = 0 := by
    change ClassFunction.inner BD.Gamma (H78.nu (H78.hyp76.zeta j₁)) = 0
    exact BD.Gamma_orth_nu j₁ hj₁ne
  have hbetaA : ClassFunction.inner H78.beta A = (BD.a : ℂ) - 1 := by
    rw [BD.beta_eq, ClassFunction.inner_add_left, ClassFunction.inner_add_left,
      ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
      hOneA, hA1, hWA, hGammaA]
    ring
  have hbetaB : ClassFunction.inner H78.beta B = (BD.a : ℂ) := by
    rw [BD.beta_eq, ClassFunction.inner_add_left, ClassFunction.inner_add_left,
      ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
      hOneB, hAB, hWB, hGammaB]
    ring
  have hbetaBA : ClassFunction.inner H78.beta (B - A) = 1 := by
    rw [ClassFunction.inner_sub_right, hbetaB, hbetaA]
    ring
  have hABbeta : ClassFunction.inner (A - B) H78.beta = -1 := by
    have hBA : ClassFunction.inner (B - A) H78.beta = 1 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hbetaBA, star_one]
    rw [show A - B = -(B - A) by abel, ClassFunction.inner_neg_left, hBA]
  have hpair : ClassFunction.inner (A - B) χ = 1 := by
    change ClassFunction.inner (A - B) (X - H78.beta) = 1
    rw [ClassFunction.inner_sub_right, ClassFunction.inner_sub_left,
      hAX, hBX, sub_zero, hABbeta]
    norm_num
  have hclass := eq_left_or_neg_right_of_inner_sub_eq_one
    hAZ hBZ hchiZ hA1 hB1 hchi1' hAB hpair
  have hBconj : B = H78.nu (H78.hyp76.zeta H78.zetaDistinct).conj := by
    change H78.nu (H78.hyp76.zeta j₁) =
      H78.nu (H78.hyp76.zeta H78.zetaDistinct).conj
    exact congrArg H78.nu hj₁
  simpa [χ, X, A, B, H78, hBconj] using hclass

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.T_typeIII_calT1_difference_support
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:06:31.145029+00:00
-- url     : https://prove2.me/submissions/44499faa-222a-4907-ace6-9a79f81ea69b

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/LocalTaxonomy.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TTypeIICoherence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity

-- ===== OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/LocalTaxonomy.lean =====
namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open OddOrder.BG.Ch4.S15

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Support-set bridge (all types)**: Peterfalvi's `A_1(M) = M_s#` coincides with BG's
`\widetilde M = M_σ#` (`sigmaSharp`) for a maximal subgroup of its classified type.  Immediate from
`A_1(M) = M_s#`, `M_s = M_σ` (`mainSubgroup_eq_Msigma`, Peterfalvi (8.10)), and `M̃ = M_σ#`.
Generalises the type-I/II support bridge to all five types; supplies the BG↔Pf support
identification
behind `BGTheoremECoverData`'s `thickenedA1`/covering fields (issue 8020). -/
theorem A1_eq_sigmaSharp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {tau : PeterfalviType} (htau : HasPeterfalviType tau M) :
    A1 M tau = sigmaSharp M := by
  change sharpSubgroup (mainSubgroup M tau) = sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)
  rw [mainSubgroup_eq_Msigma hG hM htau]

end OddOrder.BG.Ch4.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **`(QV = T')` is normal in `↥T` with index `p`** (`T = T' ⋊ W₂`, `p = |W₂|`).  The
`↥T`-side normal subgroup and the `[T:QV] = p` degree/orbit factor consumed by the `calT1` count,
repackaged from `T_derived_index_eq_p` as a statement about `(derivedInG T).subgroupOf T`
(the shape `card_image_induce_eq_div` needs: `H.index` for `H ◁ ↥T`). -/
theorem T_derivedSubgroupOf_normal (hyp : Hypothesis (G := G)) :
    ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal := by
  rw [show (derivedInG hyp.base.T).subgroupOf hyp.base.T = _root_.commutator ↥hyp.base.T by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective hyp.base.T.subtype_injective]]
  infer_instance

/-- **The T-side Dade support `A₁(T) = T_σ^#` is exactly `(T')^# = QV^#`** (issue 9072, step 3
support identity).  For type-III `T`, the Peterfalvi "main subgroup" `T_s = T'` (`mainSubgroup .III
=
derivedInG`), and the support bridge `A1_eq_sigmaSharp`
(Peterfalvi (8.10) + `mainSubgroup_eq_Msigma`,
here `T' = M_σ(T)` for the type-`P₁` regime that type-III inhabits) gives
`sigmaSharp T = A₁(T) = (T_s)^# = (T')^#`.  Concretely
`sigmaSharp T = (derivedInG T : Set G) \ {1}`.

This is the linchpin making the (14.9) coherence support facts derivable *without* any cross-lane
type-`P` char structure: the induced members `Ind_{QV}^T θ` vanish off the normal `QV = T' =
derivedInG T`, so their differences are automatically supported in `sigmaSharp T =
(T')^#` — matching
the Dade domain of `tSideDadeMap`.  (Coq `FTcore_eq_der1`: for `FTtype T > 2`, `T_s = T^{(1)}`; the
member differences `nu_0 − zeta ∈ 'CF(T, QV^#) = 'CF(T, 'A1(T))`, PFsection14.v:785--790.) -/
theorem T_typeIII_sigmaSharp_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T) :
    OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T = (derivedInG hyp.base.T : Set G) \ {1} := by
  have := hyp.base.finiteG
  -- `A1 T .III = sigmaSharp T` (support bridge), and `A1 T .III = sharpSubgroup (derivedInG T)`
  -- since `mainSubgroup .III = derivedInG`.
  have hA1 : OddOrder.GroupTheory.A1 hyp.base.T OddOrder.GroupTheory.PeterfalviType.III
      = OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T :=
    OddOrder.BG.Ch4.S16.A1_eq_sigmaSharp hG hyp.base.T_maximal hIII
  rw [← hA1]
  rfl

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TTypeIICoherence.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped Classical in
/-- T-side calT1 member differences are supported on A₁(T) = (T')#.

This is the source-support input shared by the coherence construction and the (5.3.b)
eta-orthogonality argument.  Normality of T' makes each induced character vanish off T',
while the common linear source degree makes a member difference vanish at 1. -/
theorem _root_.solution [Finite G] (hyp : Hypothesis (G := G))
    [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hlinear : ∀ θ ∈ 𝒯, (θ.toClassFunction :
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1)
    (calT1_set : Set (ClassFunction ↥hyp.base.T ℂ))
    (hcalT1 : calT1_set = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))) :
    ∀ a ∈ calT1_set, ∀ b ∈ calT1_set,
      (a - b).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by
  classical
  have := hyp.base.finiteG
  have : Fintype G := Fintype.ofFinite G
  have : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Fintype.ofFinite _
  have hAK : OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T =
      (derivedInG hyp.base.T : Set G) \ {1} :=
    T_typeIII_sigmaSharp_eq hG hyp hIII
  have hmemA : ∀ x : ↥hyp.base.T,
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T ↔
        (x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T ∧ x ≠ 1) := fun x =>
    OddOrder.Peterfalvi.S09.Cert.mem_supportInSubgroup_sharp_subgroupOf_iff
      (derivedInG hyp.base.T) hAK x
  have : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal :=
    T_derivedSubgroupOf_normal hyp
  intro a ha b hb
  rw [hcalT1, Finset.mem_coe, Finset.mem_image] at ha hb
  obtain ⟨θa, hθa, rfl⟩ := ha
  obtain ⟨θb, hθb, rfl⟩ := hb
  intro x hx
  have hx0 : (ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
        θa.toClassFunction
      - ClassFunction.induce ((derivedInG hyp.base.T).subgroupOf hyp.base.T)
        θb.toClassFunction) x ≠ 0 := ClassFunction.mem_support.mp hx
  rw [ClassFunction.sub_apply] at hx0
  have hxK : x ∈ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
    by_contra h
    apply hx0
    rw [ClassFunction.induce_eq_zero_of_not_mem_normal θa.toClassFunction h,
      ClassFunction.induce_eq_zero_of_not_mem_normal θb.toClassFunction h, sub_zero]
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hx0
    rw [ClassFunction.induce_apply_one, ClassFunction.induce_apply_one,
      hlinear θa hθa, hlinear θb hθb, sub_self]
  rw [hmemA x]
  exact ⟨hxK, hx1⟩

end OddOrder.Peterfalvi.S16

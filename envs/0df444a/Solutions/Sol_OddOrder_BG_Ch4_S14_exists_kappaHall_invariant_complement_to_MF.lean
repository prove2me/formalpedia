-- Prove2me | solution 1 for OddOrder.BG.Ch4.S14.exists_kappaHall_invariant_complement_to_MF
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T10:23:41.198377+00:00
-- url     : https://prove2.me/submissions/3a0501f4-e61c-4490-9b35-9849c2afd35a

/-
Copyright (c) 2026 OddOrder contributors. All rights reserved.
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_Basics
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_LocalStructure
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_SigmaLengthOne
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_TypePDuality
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_GlobalCounting
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_SetupLemma151
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Theorem152Helpers
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Corollary155
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_TIFailure
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_WitnessPGroup
import Definitions.Def_OddOrder_GroupTheory_AInvariantComplement

-- ===== OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePComplement.lean =====
namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch4.S15

variable {G : Type*} [Group G] [Finite G]

/-- **Peterfalvi (13.1.b), the semidirect factor `U` with `K ≤ N_G(U)`.**  The derived subgroup of a
type-`P` maximal subgroup `M` is `M' = M_F U` for a complement `U` normalised by the (cyclic) κ-Hall
`K`. -/
theorem _root_.solution (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) [IsCyclic ↥K] :
    ∃ U : Subgroup G, derivedInG M = maxNilpotentNormalHall M ⊔ U ∧
      K ≤ Subgroup.normalizer (U : Set G) ∧ maxNilpotentNormalHall M ⊓ U = ⊥ := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- `M' ≤ M` is solvable.
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have : Group.IsSolvable ↥(derivedInG M) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hM'le)
  -- `M_F ≤ M' ≤ M`.
  have hMFle' : maxNilpotentNormalHall M ≤ derivedInG M := maxNilpotentNormalHall_le_derived hG hM
  have hMFleM : maxNilpotentNormalHall M ≤ M := maxNilpotentNormalHall_le M
  -- `M` normalises both `M_F` and `M'`.
  have hM_norm_MF : M ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).mp
      (maxNilpotentNormalHall_subgroupOf_normal M)
  have hM'_subgroupOf_normal : ((derivedInG M).subgroupOf M).Normal := by
    rw [show (derivedInG M).subgroupOf M = commutator ↥M by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
    infer_instance
  have hM_norm_M' : M ≤ Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hM'le).mp hM'_subgroupOf_normal
  -- Inputs to the ambient invariant complement.
  have hM'_norm_MF : derivedInG M ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    hM'le.trans hM_norm_MF
  have hK_norm_M' : K ≤ Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) :=
    hKM.trans hM_norm_M'
  have hK_norm_MF : K ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    hKM.trans hM_norm_MF
  -- `M_F` is a Hall subgroup of `M'` (restrict from Hall in `M`: the relative index divides
  -- `[M:M_F]`).
  have hMF_hallM := maxNilpotentNormalHall_isHall M
  have hMF_hall' : Ch03.IsHallSubgroup (Nat.card ↥(maxNilpotentNormalHall M)).primeFactors
      ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)) := by
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMFle').toEquiv] at hr
    · refine hMF_hallM.2 r ?_
      rw [Nat.mem_primeFactors] at hr ⊢
      refine ⟨hr.1, hr.2.1.trans ?_, Subgroup.index_ne_zero_of_finite⟩
      exact ⟨(derivedInG M).relIndex M,
        (Subgroup.relIndex_mul_relIndex (maxNilpotentNormalHall M) (derivedInG M) M
          hMFle' hM'le).symm⟩
  -- `|K|` is coprime to `|M'|`: `K` complements `M'` in `M`, so `[M : K] = |M'|`.
  have hcompl := typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hK
  have hidx : (K.subgroupOf M).index = Nat.card ↥(derivedInG M) := by
    rw [hcompl.index_eq_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
  have hCop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(derivedInG M)) := by
    have hco := hK.coprime_index
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hidx] at hco
  -- Invariant Schur–Zassenhaus.
  obtain ⟨U, -, hUsup, hUnorm, hUinf⟩ :=
    OddOrder.GroupTheory.exists_aInvariant_complement_within_normal hMFle' hM'_norm_MF
      hK_norm_M' hK_norm_MF hMF_hall' hCop
  exact ⟨U, hUsup.symm, hUnorm, hUinf⟩

end OddOrder.BG.Ch4.S14

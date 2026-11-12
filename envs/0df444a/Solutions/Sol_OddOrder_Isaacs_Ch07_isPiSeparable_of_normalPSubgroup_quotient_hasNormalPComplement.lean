-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.isPiSeparable_of_normalPSubgroup_quotient_hasNormalPComplement
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:55:20.004246+00:00
-- url     : https://prove2.me/submissions/331c4ce3-7a5a-4cb6-a517-194c5c9ddf44

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch03_SplitExtensions/Theorem315.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Basic
import Definitions.Def_OddOrder_GroupTheory_OpResidual
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Theorem315
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

-- ===== OddOrder/Isaacs/Ch03_SplitExtensions/Theorem315.lean =====
namespace OddOrder.Isaacs.Ch03

open SemidirectProduct

open scoped Pointwise

section

variable {G : Type*} [Group G]

/-- A `π`-subgroup remains a `π`-subgroup after mapping to a quotient. -/
theorem Subgroup.IsPiGroup.map_quotient {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {N K : Subgroup G} [N.Normal] (hK : Subgroup.IsPiGroup π K) :
    Subgroup.IsPiGroup π (K.map (QuotientGroup.mk' N)) := by
  intro p hp
  apply hK
  rw [Nat.mem_primeFactors] at hp ⊢
  exact ⟨hp.1, hp.2.1.trans (Subgroup.card_map_dvd _ _), Nat.card_pos.ne'⟩

end

end OddOrder.Isaacs.Ch03

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section MinimalCounterexampleStepTwo

/-- **Isaacs Theorem 7.1, Step 2 (p-separability consequence).**

If U ◁ G is a p-group and G/U has a normal p-complement, then G
is {p}-separable.  The proof exhibits three layers of the canonical
π-Fitting series: the first absorbs U, the second absorbs the inverse
image of the normal p′-complement, and the third absorbs the remaining
p-group quotient. -/
theorem _root_.solution
    [Finite G] {p : ℕ} [Fact p.Prime] {U : Subgroup G} [U.Normal]
    (hU_p : IsPGroup p U)
    (hQ : OddOrder.Isaacs.Ch05.HasNormalPComplement p (G ⧸ U)) :
    OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G := by
  classical
  let F1 : Subgroup G :=
    OddOrder.Isaacs.Ch03.piFittingSeries ({p} : Set ℕ) G 1
  have hF1_normal : F1.Normal := by
    dsimp [F1]
    infer_instance
  have hU_pi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) U :=
    Subgroup.isPiSubgroup_of_isPGroup_of_mem hU_p (by simp)
  have hU_le_F1 : U ≤ F1 := by
    dsimp [F1]
    rw [show 1 = 0 + 1 by omega,
      OddOrder.Isaacs.Ch03.piFittingSeries_succ,
      ← Subgroup.map_le_iff_le_comap]
    exact
      (OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.map_quotient
        (N := OddOrder.Isaacs.Ch03.piFittingSeries
          ({p} : Set ℕ) G 0) hU_pi).le_oPiCore.trans le_sup_left
  obtain ⟨Nbar, hNbar_normal, hNbar_complement⟩ := hQ
  let : Nbar.Normal := hNbar_normal
  obtain ⟨Pbar⟩ := (inferInstance : Nonempty (Sylow p (G ⧸ U)))
  have hNbar_card :
      Nat.card Nbar = (Pbar : Subgroup (G ⧸ U)).index :=
    ((hNbar_complement Pbar).index_eq_card).symm
  have hNbar_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup
        {q | q ∉ ({p} : Set ℕ)} Nbar := by
    intro q hq
    rw [hNbar_card] at hq
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    rintro rfl
    exact Pbar.not_dvd_index (Nat.dvd_of_mem_primeFactors hq)
  let qU : G →* G ⧸ U := QuotientGroup.mk' U
  have hqU : Function.Surjective qU := QuotientGroup.mk'_surjective U
  let K : Subgroup G := Nbar.comap qU
  have hK_normal : K.Normal := hNbar_normal.comap qU
  have hU_le_K : U ≤ K := by
    intro x hx
    change qU x ∈ Nbar
    rw [show qU x = 1 from by
      dsimp [qU]
      exact (QuotientGroup.eq_one_iff x).2 hx]
    exact Nbar.one_mem
  have hK_map_qU : K.map qU = Nbar := by
    dsimp [K]
    exact Subgroup.map_comap_eq_self_of_surjective hqU Nbar
  have hK_map_qU_normal : (K.map qU).Normal :=
    Subgroup.Normal.map hK_normal qU hqU
  let q1 : G →* G ⧸ F1 := QuotientGroup.mk' F1
  have hq1 : Function.Surjective q1 := QuotientGroup.mk'_surjective F1
  have hU_le_ker_q1 : U ≤ q1.ker := by
    simpa only [q1, QuotientGroup.ker_mk'] using hU_le_F1
  let r1 : G ⧸ U →* G ⧸ F1 :=
    QuotientGroup.lift U q1 hU_le_ker_q1
  have hr1_comp : r1.comp qU = q1 := by
    ext x
    change QuotientGroup.lift U q1 hU_le_ker_q1
      (QuotientGroup.mk' U x) = q1 x
    exact QuotientGroup.lift_mk' _ _ x
  have hK_map_q1 : K.map q1 = Nbar.map r1 := by
    calc
      K.map q1 = K.map (r1.comp qU) := by rw [hr1_comp]
      _ = (K.map qU).map r1 := by rw [Subgroup.map_map]
      _ = Nbar.map r1 := by rw [hK_map_qU]
  have hK_map_q1_normal : (K.map q1).Normal :=
    Subgroup.Normal.map hK_normal q1 hq1
  have hNbar_map_r1_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup
        {q | q ∉ ({p} : Set ℕ)} (Nbar.map r1) := by
    intro q hq
    exact hNbar_pi' q
      (Nat.primeFactors_mono (Nbar.card_map_dvd r1) Nat.card_pos.ne' hq)
  have hK_map_q1_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup
        {q | q ∉ ({p} : Set ℕ)} (K.map q1) := by
    rw [hK_map_q1]
    exact hNbar_map_r1_pi'
  let F2 : Subgroup G :=
    OddOrder.Isaacs.Ch03.piFittingSeries ({p} : Set ℕ) G 2
  have hF2_normal : F2.Normal := by
    dsimp [F2]
    infer_instance
  have hK_le_F2 : K ≤ F2 := by
    dsimp [F2]
    rw [show 2 = 1 + 1 by omega,
      OddOrder.Isaacs.Ch03.piFittingSeries_succ]
    change K ≤ Subgroup.comap q1
      (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) (G ⧸ F1) ⊔
        OddOrder.Isaacs.Ch03.oPiCore
          {q | q ∉ ({p} : Set ℕ)} (G ⧸ F1))
    rw [← Subgroup.map_le_iff_le_comap]
    exact hK_map_q1_pi'.le_oPiCore.trans le_sup_right
  have hQ_quotient_p : IsPGroup p ((G ⧸ U) ⧸ Nbar) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Pbar.isPGroup'
    refine IsPGroup.of_card (n := n) ?_
    calc
      Nat.card ((G ⧸ U) ⧸ Nbar) = Nbar.index :=
        (Subgroup.index_eq_card Nbar).symm
      _ = Nat.card (Pbar : Subgroup (G ⧸ U)) :=
        (hNbar_complement Pbar).symm.index_eq_card
      _ = p ^ n := hn
  let e : ((G ⧸ U) ⧸ Nbar) ≃* (G ⧸ K) :=
    (QuotientGroup.quotientMulEquivOfEq hK_map_qU.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient U K hU_le_K)
  have hGK_p : IsPGroup p (G ⧸ K) := hQ_quotient_p.of_equiv e
  let q2 : G →* G ⧸ F2 := QuotientGroup.mk' F2
  have hq2 : Function.Surjective q2 := QuotientGroup.mk'_surjective F2
  have hK_le_ker_q2 : K ≤ q2.ker := by
    simpa only [q2, QuotientGroup.ker_mk'] using hK_le_F2
  let r2 : G ⧸ K →* G ⧸ F2 :=
    QuotientGroup.lift K q2 hK_le_ker_q2
  have hr2_surjective : Function.Surjective r2 := by
    dsimp [r2]
    exact QuotientGroup.lift_surjective_of_surjective K q2 hq2 hK_le_ker_q2
  have hGF2_p : IsPGroup p (G ⧸ F2) :=
    hGK_p.of_surjective r2 hr2_surjective
  have htop_pi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)
        (⊤ : Subgroup (G ⧸ F2)) :=
    Subgroup.isPiSubgroup_of_isPGroup_of_mem
      (hGF2_p.to_subgroup ⊤) (by simp)
  refine ⟨3, top_le_iff.mp ?_⟩
  rw [show 3 = 2 + 1 by omega,
    OddOrder.Isaacs.Ch03.piFittingSeries_succ]
  change (⊤ : Subgroup G) ≤ Subgroup.comap q2
    (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) (G ⧸ F2) ⊔
      OddOrder.Isaacs.Ch03.oPiCore
        {q | q ∉ ({p} : Set ℕ)} (G ⧸ F2))
  rw [← Subgroup.map_le_iff_le_comap,
    Subgroup.map_top_of_surjective q2 hq2]
  exact htop_pi.le_oPiCore.trans le_sup_left

end MinimalCounterexampleStepTwo

end OddOrder.Isaacs.Ch07

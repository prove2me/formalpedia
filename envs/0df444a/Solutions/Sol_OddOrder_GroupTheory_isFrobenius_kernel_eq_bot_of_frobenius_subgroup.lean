-- Prove2me | solution 1 for OddOrder.GroupTheory.isFrobenius_kernel_eq_bot_of_frobenius_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:49:19.221243+00:00
-- url     : https://prove2.me/submissions/8e0fa8eb-1104-4468-b8eb-10eb7d80bba6

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/WielandtFixedPoint.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_CoprimeAction
import Definitions.Def_OddOrder_GroupTheory_WielandtPerFactorDischarge
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_WielandtElabFrobenius
import Definitions.Def_OddOrder_GroupTheory_WielandtFixedPoint

-- ===== OddOrder/GroupTheory/WielandtFixedPoint.lean =====
namespace OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.Isaacs.Ch03 (IsAInvariant)

section WielandtFixedPoint

/-- **Peterfalvi (9.1), the fixed-point-free corollary**: if *both* the Frobenius kernel `U` and
the complement `E` act fixed-point-freely on `H` (`C_H(U) = C_H(E) = 1`), then `H` is trivial.
This is the form used in Peterfalvi (13.17.b): a Frobenius group `U W₁` acting fixed-point-freely
on the Fitting kernel `H = L_F` forces `|L_F| = 1`. -/
theorem coprimeFrobeniusAction_card_eq_one {L H : Type*} [Group L] [Group H]
    [Finite L] [Finite H] (act : CoprimeFrobeniusAction L H)
    (hE : act.fixedByE = ⊥) (hU : act.fixedByU = ⊥) :
    Nat.card H = 1 := by
  have key := wielandt_fixedPoint_trivial_U_fixed act hU
  rw [hE, Subgroup.card_bot, one_pow] at key
  exact key

end WielandtFixedPoint

section FrobeniusCentralizer

/-- **Peterfalvi (13.17.b), the fixed-point-free engine**: let `Lsub ≤ G` be a finite Frobenius
group with kernel `N` (`N ≤ Lsub`, `N.subgroupOf Lsub` normal).  If a *Frobenius subgroup*
`U E ≤ Lsub` (kernel `U`, complement `E`, with its own Frobenius structure on `↥(U ⊔ E)`) meets `N`
trivially (`U ⊓ N = E ⊓ N = ⊥`) and acts coprimely (`|N| ⟂ |UE|`), then `N = ⊥`.

Both `U` and `E` act fixed-point-freely on `N`: every nontrivial element, lifted into the Frobenius
group `↥Lsub`, lies outside the kernel, so `centralizer_inf_kernel_eq_bot_of_not_mem` makes its
centralizer meet `N` trivially.  Hence the fixed-point subgroups vanish and Wielandt's formula
(`coprimeFrobeniusAction_card_eq_one`) forces `|N| = 1`.  This is exactly the step that, in
(13.17.b), derives `|L_F| = 1` from `U ∩ L_F = 1`, contradicting `L_F ≠ 1`.  Phrasing the Frobenius
subgroup `U E` in the ambient `G` (rather than inside `↥Lsub`) lets callers supply
`basic_structure`'s `UW1_frobenius` directly, with no `subgroupOf` transfer. -/
theorem _root_.solution {G : Type*} [Group G] [Finite G]
    {Lsub N U E : Subgroup G} (hNL : N ≤ Lsub) (hUL : U ⊔ E ≤ Lsub)
    (hFrob : ∃ A : Subgroup ↥Lsub, Ch06.IsFrobeniusGroup ↥Lsub (N.subgroupOf Lsub) A)
    (hUE : Ch06.IsFrobeniusGroup ↥(U ⊔ E) (U.subgroupOf (U ⊔ E)) (E.subgroupOf (U ⊔ E)))
    (hUN : U ⊓ N = ⊥) (hEN : E ⊓ N = ⊥) (hsolv : Group.IsSolvable ↥N)
    (hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥(U ⊔ E))) :
    N = ⊥ := by
  classical
  obtain ⟨A, hFrobA⟩ := hFrob
  -- `U ⊔ E ≤ Lsub ≤ N_G(N)` (the latter because `N` is normal in the Frobenius group `↥Lsub`).
  have hUEnorm : (U ⊔ E) ≤ Subgroup.normalizer (N : Set G) :=
    hUL.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mp hFrobA.isNormal)
  let act : MulDistribMulAction ↥(U ⊔ E) ↥N :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (N : Set G))) ↥N
      (Subgroup.inclusion hUEnorm)
  set φ : ↥(U ⊔ E) →* MulAut ↥N := MulDistribMulAction.toMulAut ↥(U ⊔ E) ↥N with hφ
  have hφ_coe : ∀ (a : ↥(U ⊔ E)) (x : ↥N), ((φ a) x : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  let act' : CoprimeFrobeniusAction ↥(U ⊔ E) ↥N :=
    { U := U.subgroupOf (U ⊔ E), E := E.subgroupOf (U ⊔ E), frobenius := hUE,
      H_solvable := hsolv, φ := φ, coprime_order := hcop }
  -- Each factor's nontrivial elements lie outside `N`, hence (lifted into the Frobenius group
  -- `↥Lsub`) centralize nothing nontrivial in `N`: the fixed-point subgroup is trivial.
  have key : ∀ {K : Subgroup G}, K ⊓ N = ⊥ → K ≠ ⊥ → K ≤ U ⊔ E →
      fixedSubgroup φ (K.subgroupOf (U ⊔ E)) = ⊥ := by
    intro K hKN hKne hKle
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    by_contra hne
    have hnG : (n : G) ≠ 1 := fun h => hne (Subtype.ext h)
    obtain ⟨k, hkK, hkne⟩ := (K.bot_or_exists_ne_one).resolve_left hKne
    have hkUE : k ∈ U ⊔ E := hKle hkK
    have hfix := (mem_fixedSubgroup.mp hn) ⟨k, hkUE⟩ (Subgroup.mem_subgroupOf.mpr hkK)
    have hcomm : k * (n : G) * k⁻¹ = (n : G) := by
      have hc : ((φ ⟨k, hkUE⟩) n : G) = (n : G) := Subtype.ext_iff.mp hfix
      rwa [hφ_coe] at hc
    have hkN : k ∉ N := fun h =>
      hkne (Subgroup.disjoint_def.mp (disjoint_iff.mpr hKN) hkK h)
    -- Lift `k`, `n` into the Frobenius group `↥Lsub` and apply the kernel-centralizer engine.
    have hk_notmem : (⟨k, hUL hkUE⟩ : ↥Lsub) ∉ N.subgroupOf Lsub :=
      fun h => hkN (Subgroup.mem_subgroupOf.mp h)
    have hcb := IsFrobeniusGroup.centralizer_inf_kernel_eq_bot_of_not_mem hFrobA hk_notmem
    have hkn : k * (n : G) = (n : G) * k := by rwa [mul_inv_eq_iff_eq_mul] at hcomm
    have hn_cent : (⟨(n : G), hNL n.2⟩ : ↥Lsub) ∈
        Subgroup.centralizer ({(⟨k, hUL hkUE⟩ : ↥Lsub)} : Set ↥Lsub) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hkn.symm
    have hn_in : (⟨(n : G), hNL n.2⟩ : ↥Lsub) ∈
        Subgroup.centralizer ({(⟨k, hUL hkUE⟩ : ↥Lsub)} : Set ↥Lsub) ⊓ N.subgroupOf Lsub :=
      ⟨hn_cent, Subgroup.mem_subgroupOf.mpr n.2⟩
    exact hnG (congrArg Subtype.val (Subgroup.mem_bot.mp (hcb.le hn_in)))
  have hUne : U ≠ ⊥ := fun hb => hUE.ne_bot_kernel (by rw [hb, Subgroup.bot_subgroupOf])
  have hEne : E ≠ ⊥ := fun hb => hUE.ne_bot_complement (by rw [hb, Subgroup.bot_subgroupOf])
  have hfixU : act'.fixedByU = ⊥ := key hUN hUne le_sup_left
  have hfixE : act'.fixedByE = ⊥ := key hEN hEne le_sup_right
  have hcard := coprimeFrobeniusAction_card_eq_one act' hfixE hfixU
  exact Subgroup.card_eq_one.mp hcard

end FrobeniusCentralizer

end OddOrder.GroupTheory

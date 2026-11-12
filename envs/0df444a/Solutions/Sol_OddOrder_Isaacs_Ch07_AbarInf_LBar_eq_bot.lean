-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.AbarInf_LBar_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:49:54.967632+00:00
-- url     : https://prove2.me/submissions/26f03cc7-e25e-4f03-aa36-8f22f8a9d46c

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Thm 7.6 Step 5 prep** (mmd L3873): for any `p`-subgroup `A ≤ G`,
the image `Ā = A.map (mk' U)` is disjoint from `L̅ = O_{p'}(G̅)` in `G̅ = G/U`.

`Ā` is a `p`-group (image of `p`-group `A`), and `L̅` is a `{q | q ≠ p}`-group
by `oPiCore.isPiGroup`.  Their cardinalities are coprime, hence the
intersection is trivial. -/
theorem _root_.solution
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA_pg : IsPGroup p A) :
    A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ⊓
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) = ⊥ := by
  -- A̅ is a p-group, hence {p}-IsPiGroup.
  have hAbar_pg : IsPGroup p
      (A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))) :=
    hA_pg.map _
  have hAbar_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)
      (A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))) := by
    intro q hq
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hq_dvd : q ∣ Nat.card
        (A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))) :=
      Nat.dvd_of_mem_primeFactors hq
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAbar_pg
    rw [hk] at hq_dvd
    have hq_eq_p : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq_prime Fact.out).mp
        (hq_prime.dvd_of_dvd_pow hq_dvd)
    simp [hq_eq_p]
  -- L̅ is a {q | q ≠ p}-group; rewrite as `{q | q ∉ {p}}` for the coprime lemma.
  have hLbar_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup
      ({q : ℕ | q ∉ ({p} : Set ℕ)} : Set ℕ)
      (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) := by
    have hLbar_pi := OddOrder.Isaacs.Ch03.oPiCore.isPiGroup
      (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) ({q | q ≠ p} : Set ℕ)
    have hπeq : ({q : ℕ | q ∉ ({p} : Set ℕ)} : Set ℕ) = {q | q ≠ p} := by
      ext q; simp
    rw [hπeq]; exact hLbar_pi
  -- Apply `disjoint_of_coprime_natCard` + `coprime_of_isPiGroup_of_isPiGroup_compl`.
  apply Disjoint.eq_bot
  apply Subgroup.disjoint_of_coprime_natCard
  exact OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    Nat.card_pos.ne' Nat.card_pos.ne' hAbar_pi hLbar_pi'

end OddOrder.Isaacs.Ch07

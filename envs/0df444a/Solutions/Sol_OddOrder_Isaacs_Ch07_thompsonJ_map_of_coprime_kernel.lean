-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.thompsonJ_map_of_coprime_kernel
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:53:41.998257+00:00
-- url     : https://prove2.me/submissions/7b32a8ba-f701-4e74-a013-c27a064ea892

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped commutatorElement

/-- Thompson's `J` commutes with quotient by a normal `p'`-kernel on `p`-subgroups.

The quotient map is not injective on all of `G`, but it is injective on any
`p`-subgroup `P` because `P ∩ N = 1`.  This is the `J(P)` identification needed
when Steps 2 and 3 pass Thompson-normalizer hypotheses to `G/N`. -/
theorem _root_.solution
    [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P) :
    Subgroup.thompsonJ (P.map (QuotientGroup.mk' N)) p =
      (Subgroup.thompsonJ P p).map (QuotientGroup.mk' N) := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let qP : ↥P →* G ⧸ N := q.comp P.subtype
  obtain ⟨k, hP_card⟩ : ∃ k, Nat.card ↥P = p ^ k := IsPGroup.iff_card.mp hP_pgroup
  have hp_prime : p.Prime := Fact.out
  have h_coprime_PN : Nat.Coprime (Nat.card ↥P) (Nat.card ↥N) := by
    rw [hP_card]
    exact Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hp_coprime)
  have hP_inf_N : P ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard h_coprime_PN).eq_bot
  have hqP_inj : Function.Injective qP := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx_N : (x : G) ∈ N := by
      have : (x : G) ∈ (QuotientGroup.mk' N).ker := hx
      rw [QuotientGroup.ker_mk'] at this
      exact this
    have hx_inf : (x : G) ∈ P ⊓ N := ⟨x.property, hx_N⟩
    rw [hP_inf_N, Subgroup.mem_bot] at hx_inf
    exact Subtype.ext hx_inf
  have htop_qP : (⊤ : Subgroup ↥P).map qP = P.map q := by
    ext y
    constructor
    · rintro ⟨x, _hx_top, rfl⟩
      exact ⟨(x : G), x.property, rfl⟩
    · rintro ⟨x, hxP, rfl⟩
      exact ⟨⟨x, hxP⟩, trivial, rfl⟩
  have htop_subtype : (⊤ : Subgroup ↥P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hJ_subtype :
      (Subgroup.thompsonJ (⊤ : Subgroup ↥P) p).map P.subtype =
        Subgroup.thompsonJ P p := by
    have h :=
      Subgroup.thompsonJ_map_of_injective P.subtype_injective (⊤ : Subgroup ↥P) p
    rw [htop_subtype] at h
    exact h.symm
  have hJ_qP :
      Subgroup.thompsonJ ((⊤ : Subgroup ↥P).map qP) p =
        (Subgroup.thompsonJ (⊤ : Subgroup ↥P) p).map qP :=
    Subgroup.thompsonJ_map_of_injective hqP_inj (⊤ : Subgroup ↥P) p
  change Subgroup.thompsonJ (P.map q) p = (Subgroup.thompsonJ P p).map q
  rw [← htop_qP, hJ_qP]
  change (Subgroup.thompsonJ (⊤ : Subgroup ↥P) p).map (q.comp P.subtype) =
    (Subgroup.thompsonJ P p).map q
  rw [← Subgroup.map_map, hJ_subtype]

end OddOrder.Isaacs.Ch07

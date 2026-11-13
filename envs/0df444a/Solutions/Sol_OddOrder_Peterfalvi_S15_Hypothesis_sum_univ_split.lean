-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.sum_univ_split
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:53:26.192774+00:00
-- url     : https://prove2.me/submissions/2430d66a-c3d7-4958-bf3e-1e80c4de203e

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/PairStructure.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Theorems.Thm_OddOrder_GroupTheory_IsTISubset_sum_conjClassSet
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_q_not_dvd_card_H

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/PairStructure.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section PairStructure

open OddOrder.GroupTheory

/-- Elements of the set-normalizer of `(K : Set G)` stabilize the sharp `K^# = K − 1` under
conjugation — the `hstab` input shape of `IsTISubset.sum_conjClassSet`. -/
theorem conj_smul_sharpSubgroup_eq {K N : Subgroup G}
    (hnorm : Subgroup.normalizer (K : Set G) = N) {l : G} (hl : l ∈ N) :
    MulAut.conj l • sharpSubgroup K = sharpSubgroup K := by
  have hlnorm : l ∈ Subgroup.normalizer (K : Set G) := hnorm ▸ hl
  rw [Subgroup.mem_set_normalizer_iff] at hlnorm
  ext x
  simp only [Set.mem_smul_set, MulAut.smul_def, MulAut.conj_apply, sharpSubgroup, Set.mem_sdiff,
    Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨v, ⟨hvK, hv1⟩, rfl⟩
    refine ⟨(hlnorm v).mp hvK, fun heq => hv1 ?_⟩
    calc v = l⁻¹ * (l * v * l⁻¹) * l := by group
      _ = 1 := by rw [heq]; group
  · rintro ⟨hxK, hx1⟩
    refine ⟨l⁻¹ * x * l, ⟨?_, fun heq => hx1 ?_⟩, by group⟩
    · have := (hlnorm (l⁻¹ * x * l)).mpr
      rw [show l * (l⁻¹ * x * l) * l⁻¹ = x from by group] at this
      exact this hxK
    · calc x = l * (l⁻¹ * x * l) * l⁻¹ := by group
        _ = 1 := by rw [heq]; group

/-- **`N_G(H) = S`** (Peterfalvi (8.5.a)): `H = PC = F(S)` (`H_eq_fittingInG`) and
`N_G(F(S)) = S` (`normalizer_fittingInAmbient_eq_self`). -/
theorem normalizer_H_eq_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.H : Set G) = hyp.S := by
  have hHF : hyp.H = OddOrder.BG.Ch2.S08.fittingInG hyp.S := hyp.H_eq_fittingInG
  have hnorm : Subgroup.normalizer (OddOrder.BG.Ch4.S15.fittingInAmbient hyp.S : Set G) = hyp.S :=
    OddOrder.BG.Ch4.S16.normalizer_fittingInAmbient_eq_self hG hyp.S_maximal
  rw [hHF]; exact hnorm

end PairStructure

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section CountingLayer

open OddOrder.GroupTheory

/-- **`(H^#)^G` and `(Q^#)^G` are disjoint**: a common element would be conjugate both to a
nonidentity element of `H` (order dividing `|H|`, so prime to `q` by `q_not_dvd_card_H`) and to
a nonidentity element of `Q` (order a positive power of `q`, `|Q| = q^p`). -/
theorem disjoint_conjClassSet_sharp_H_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) :
    ∀ x : G, x ∈ conjClassSet (sharpSubgroup hyp.H) →
      x ∈ conjClassSet (sharpSubgroup hyp.Q) → False := by
  intro x hxH hxQ
  obtain ⟨a, ⟨haH, ha1⟩, g, rfl⟩ := mem_conjClassSet.mp hxH
  obtain ⟨b, ⟨hbQ, hb1⟩, h, hab⟩ := mem_conjClassSet.mp hxQ
  -- Conjugation preserves orders: `orderOf a = orderOf b`.
  have horder : orderOf a = orderOf b := by
    have h1 : orderOf (g * a * g⁻¹) = orderOf a := by
      rw [show g * a * g⁻¹ = (MulAut.conj g) a from rfl]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
    have h2 : orderOf (h * b * h⁻¹) = orderOf b := by
      rw [show h * b * h⁻¹ = (MulAut.conj h) b from rfl]
      exact orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective b
    rw [← h1, ← hab, h2]
  -- `orderOf b` is a positive power of `q`, so `q ∣ orderOf a ∣ |H|`.
  have hbdvd : orderOf b ∣ hyp.q ^ hyp.p := by
    have h1 : orderOf (⟨b, hbQ⟩ : ↥hyp.Q) ∣ Nat.card ↥hyp.Q := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk b hbQ, hcardQ] at h1
  obtain ⟨i, hip, hbord⟩ := (Nat.dvd_prime_pow hyp.q_prime).mp hbdvd
  have hi0 : i ≠ 0 := by
    intro hi0
    rw [hi0, pow_zero] at hbord
    exact hb1 (orderOf_eq_one_iff.mp hbord)
  have hqdvd_a : hyp.q ∣ orderOf a := by
    rw [horder, hbord]
    exact dvd_pow_self hyp.q hi0
  have hadvd : orderOf a ∣ Nat.card ↥hyp.H := by
    have h1 : orderOf (⟨a, SetLike.mem_coe.mp haH⟩ : ↥hyp.H) ∣ Nat.card ↥hyp.H :=
      orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk a (SetLike.mem_coe.mp haH)] at h1
  exact hyp.q_not_dvd_card_H hG (hqdvd_a.trans hadvd)

/-- Membership in the generic set `G₀`, unfolded: nonidentity and in neither saturation. -/
theorem Hypothesis.mem_G0_iff (hyp : Hypothesis (G := G)) (x : G) :
    x ∈ hyp.G0 ↔ x ≠ 1 ∧ x ∉ conjClassSet (sharpSubgroup hyp.H)
      ∧ x ∉ conjClassSet (sharpSubgroup hyp.Q) := by
  change x ∈ sharpSubgroup (⊤ : Subgroup G) \ _ ↔ _
  simp only [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_top, true_and, Set.mem_union, not_or]

open scoped Classical in
/-- **The four-piece split of a conjugation-invariant sum** (the (13.10) counting skeleton):
for a conjugation-invariant `f`,

  `∑_G f = f(1) + ∑_{G₀} f + [G:S]·∑_{H^#} f + [G:T]·∑_{Q^#} f`.

`G` is the disjoint union of `{1}`, `G₀`, `(H^#)^G`, and `(Q^#)^G` (the saturations are disjoint
by `disjoint_conjClassSet_sharp_H_Q` and miss `1`; `G₀` is *defined* as the complement), and each
saturation sum collapses by `IsTISubset.sum_conjClassSet` (issue 9011) via the proven TI
structure (`H_sharp_isTISubset` / `Q_sharp_isTISubset`).  Instantiations: `f = ‖χ(·)‖²` gives the
Parseval splits (13.10.1)/(13.10.2); `f = 1` the cover count (13.10.3). -/
theorem _root_.solution [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) {M : Type*} [AddCommMonoid M] (f : G → M)
    (hf : ∀ g x : G, f (g * x * g⁻¹) = f x)
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    ∑ x : G, f x
      = f 1 + (∑ x ∈ hyp.G0Finset, f x)
        + hyp.S.index • ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, f x
        + hyp.T.index • ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, f x := by
  classical
  -- TI structure and stabilization on both sides.
  have hTIH : OddOrder.GroupTheory.IsTISubset (sharpSubgroup hyp.H) hyp.S :=
    H_sharp_isTISubset hG hyp
  have hTIQ : OddOrder.GroupTheory.IsTISubset (sharpSubgroup hyp.Q) hyp.T :=
    Q_sharp_isTISubset hG hyp hvd
  have hstabH : ∀ l ∈ hyp.S, MulAut.conj l • sharpSubgroup hyp.H = sharpSubgroup hyp.H :=
    fun l hl => conj_smul_sharpSubgroup_eq (normalizer_H_eq_S hG hyp) hl
  have hstabQ : ∀ l ∈ hyp.T, MulAut.conj l • sharpSubgroup hyp.Q = sharpSubgroup hyp.Q :=
    fun l hl => conj_smul_sharpSubgroup_eq (normalizer_Q_eq_T hG hyp) hl
  -- The four Finset pieces.
  set CH : Finset G := (Set.toFinite (conjClassSet (sharpSubgroup hyp.H))).toFinset with hCHdef
  set CQ : Finset G := (Set.toFinite (conjClassSet (sharpSubgroup hyp.Q))).toFinset with hCQdef
  have hmemCH : ∀ x : G, x ∈ CH ↔ x ∈ conjClassSet (sharpSubgroup hyp.H) := fun x =>
    (Set.toFinite _).mem_toFinset
  have hmemCQ : ∀ x : G, x ∈ CQ ↔ x ∈ conjClassSet (sharpSubgroup hyp.Q) := fun x =>
    (Set.toFinite _).mem_toFinset
  have hmemG0 : ∀ x : G, x ∈ hyp.G0Finset ↔ x ∈ hyp.G0 := fun x =>
    (Set.toFinite _).mem_toFinset
  -- Nonidentity: conjugates of nonidentity elements are nonidentity.
  have hne1 : ∀ (K : Subgroup G) (x : G), x ∈ conjClassSet (sharpSubgroup K) → x ≠ 1 := by
    rintro K x hx rfl
    obtain ⟨a, ⟨-, ha1⟩, g, hg⟩ := mem_conjClassSet.mp hx
    refine ha1 ?_
    change a = 1
    have ha : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [ha, hg]
    group
  have hne1H : ∀ x ∈ CH, x ≠ 1 := fun x hx => hne1 hyp.H x ((hmemCH x).mp hx)
  have hne1Q : ∀ x ∈ CQ, x ≠ 1 := fun x hx => hne1 hyp.Q x ((hmemCQ x).mp hx)
  -- `G₀` misses `1` and both saturations (definitional).
  have hG0iff := hyp.mem_G0_iff
  -- The partition: `univ = {1} ∪ G₀ ∪ CH ∪ CQ`, pairwise disjoint.
  have hcover : (Finset.univ : Finset G) = insert 1 (hyp.G0Finset ∪ CH ∪ CQ) := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, true_iff]
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · refine Or.inr ?_
      by_cases hxH : x ∈ conjClassSet (sharpSubgroup hyp.H)
      · exact Or.inl (Or.inr ((hmemCH x).mpr hxH))
      · by_cases hxQ : x ∈ conjClassSet (sharpSubgroup hyp.Q)
        · exact Or.inr ((hmemCQ x).mpr hxQ)
        · exact Or.inl (Or.inl ((hmemG0 x).mpr ((hG0iff x).mpr ⟨hx1, hxH, hxQ⟩)))
  have hdisjHQ : Disjoint CH CQ := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact disjoint_conjClassSet_sharp_H_Q hG hyp hcardQ x ((hmemCH x).mp hx) ((hmemCQ x).mp hx')
  have hdisjG0 : Disjoint hyp.G0Finset (CH ∪ CQ) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨-, hxH, hxQ⟩ := (hG0iff x).mp ((hmemG0 x).mp hx)
    rcases Finset.mem_union.mp hx' with h | h
    · exact hxH ((hmemCH x).mp h)
    · exact hxQ ((hmemCQ x).mp h)
  have hone_notin : (1 : G) ∉ hyp.G0Finset ∪ CH ∪ CQ := by
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact ((hG0iff 1).mp ((hmemG0 1).mp h')).1 rfl
      · exact hne1H 1 h' rfl
    · exact hne1Q 1 h rfl
  -- Assemble the split.
  rw [hcover, Finset.sum_insert hone_notin, Finset.union_assoc, Finset.sum_union hdisjG0,
    Finset.sum_union hdisjHQ, hCHdef, hCQdef,
    OddOrder.GroupTheory.IsTISubset.sum_conjClassSet f hTIH hstabH hf,
    OddOrder.GroupTheory.IsTISubset.sum_conjClassSet f hTIQ hstabQ hf]
  abel

end CountingLayer

end OddOrder.Peterfalvi.S15

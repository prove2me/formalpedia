-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.complement_inf_Q_eq_W1
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:10:00.949612+00:00
-- url     : https://prove2.me/submissions/216ed65f-0774-4272-a610-96ece2d879ce

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean
--   OddOrder/Peterfalvi/S15_SAndTBasic.lean
--   OddOrder/Peterfalvi/S15_ComplementStructure.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Theorems.Thm_OddOrder_Peterfalvi_S15_Q_elementaryAbelian_T

-- ===== OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean =====
namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

open scoped commutatorElement

open OddOrder.Isaacs.Ch04

variable {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
  [MulDistribMulAction A U]

/-- **Z-group property, subgroup-pair form** (Step 1 for a bundled Frobenius group): in a finite
Frobenius group `G = N ⋊ A` whose complement `A` has **odd order**, `A` is a Z-group — every
Sylow subgroup of `A` is cyclic ([BG] Proposition 3.9 for the complement; the conjugation action
of `A` on the kernel `N` is Frobenius, and `isZGroup_of_isFrobeniusAction_of_odd` applies).
Combined with mathlib's `IsPGroup.isCyclic_of_isZGroup` (and the `Subgroup` instance), every
prime-power-order subgroup of `A` is cyclic. -/
theorem isZGroup_complement_of_isFrobeniusGroup_of_odd
    {G : Type*} [Group G] [Finite G] {N A : Subgroup G}
    (hFrob : IsFrobeniusGroup G N A) (hodd : Odd (Nat.card ↥A)) :
    IsZGroup ↥A := by
  let : N.Normal := hFrob.isNormal
  let : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom ↥N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hFrob.ne_bot_kernel
  exact isZGroup_of_isFrobeniusAction_of_odd hFrob.toFrobeniusAction hodd

end OddOrder.Isaacs.Ch06

-- ===== OddOrder/Peterfalvi/S15_SAndTBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.2.b)/(14.2.a), `T`-side dual of `W2_le_P`: `W₁ ≤ Q`.**  The cyclic factor `W₁`
(of prime order `q`) lies in `Q = T_F`, the maximal nilpotent normal Hall subgroup of `T`.  Dual to
`W2_le_P` (`W₂ ≤ P`), but read off the `T`-side type-`P` decomposition (`reconciled_typePData_T`)
rather than the coprime-index order count: the intrinsic dual cyclic factor
`data.W2 = C_{T'}(W₂#) = W₁` sits inside `data.H = maxNilpotentNormalHall T = Q`
(`data.W2_le`, `data.H_eq`, `Q_eq_TF`).  This is conjunct (1) of the (13.16)
`normalizer_W1_structure_of_D_eq_bot`
and is consumed by the `W₁`-side Maschke/Wielandt confinement (the dual of the `W₂`-side, where
`normalizer_U_inf_W2_eq_bot_of_data` uses `W2_le_P` at the analogous step). -/
theorem W1_le_Q [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.W1 ≤ hyp.Q := by
  obtain ⟨tpd, _, _, htpdW1⟩ := reconciled_typePData_T hG hyp
  have hHeq : tpd.H = hyp.Q := by rw [tpd.H_eq, hyp.Q_eq_TF]
  rw [← htpdW1, ← hHeq]
  exact le_trans tpd.W2_le inf_le_left

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_ComplementStructure.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.17.c), `E ∩ Q = W₁`** (Pf p.82) — the proven half of the §13 intersection
structure.  `W₁ ≤ E ⊓ Q` from `hW1E` and `W1_le_Q` ((13.2.b) `T`-side).  Conversely `E ⊓ Q` is a
`q`-subgroup of the elementary abelian `Q` (`Q_elementaryAbelian_T`, (13.2.a) `T`-side) sitting
inside the odd-order Frobenius complement `E`, which is a Z-group ([BG] Prop 3.9 via
Isaacs 6.9–6.11, `isZGroup_complement_of_isFrobeniusGroup_of_odd`); so `E ⊓ Q` is cyclic
(`IsPGroup.isCyclic_of_isZGroup`), and a cyclic group of exponent `q` has order dividing `q` —
with `|W₁| = q` from below, equality. -/
theorem _root_.solution [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTTypeII : IsTypeII hyp.T) {L : Subgroup G}
    (frob : OddOrder.Peterfalvi.S14.TypeIFrobeniusData L)
    (hW1E : hyp.W1 ≤ frob.complement.map L.subtype) :
    frob.complement.map L.subtype ⊓ hyp.Q = hyp.W1 := by
  classical
  set Em := frob.complement.map L.subtype with hEm
  have hW1le : hyp.W1 ≤ Em ⊓ hyp.Q := le_inf hW1E (W1_le_Q hG hyp)
  -- `E` is a Z-group (odd Frobenius complement), and `Em ≅ E`.
  have hodd : Odd (Nat.card ↥frob.complement) := hG.odd.of_dvd_nat
    ((Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card L))
  have hZE : _root_.IsZGroup ↥frob.complement :=
    OddOrder.Isaacs.Ch06.isZGroup_complement_of_isFrobeniusGroup_of_odd frob.frobenius hodd
  have hZEm : _root_.IsZGroup ↥Em := _root_.IsZGroup.of_injective
    (f := ((Subgroup.equivMapOfInjective frob.complement L.subtype
      Subtype.coe_injective).symm : ↥Em ≃* ↥frob.complement).toMonoidHom)
    (MulEquiv.injective _)
  -- `R := (Em ⊓ Q)` realized inside `Em` is a `q`-group (exponent `q` from `Q` elem.-abelian)
  have hQeA := Q_elementaryAbelian_T hG hyp hTTypeII
  set R : Subgroup ↥Em := (Em ⊓ hyp.Q).subgroupOf Em with hRdef
  have hexp : ∀ x : ↥R, x ^ hyp.q = 1 := by
    intro x
    have hgQ : ((x : ↥Em) : G) ∈ hyp.Q := (Subgroup.mem_subgroupOf.mp x.2).2
    have hq1 := hQeA.2 (⟨((x : ↥Em) : G), hgQ⟩ : ↥hyp.Q)
    have hg1 : (((x : ↥Em) : G)) ^ hyp.q = 1 := by
      simpa using congrArg Subtype.val hq1
    apply Subtype.ext; apply Subtype.ext
    push_cast
    exact hg1
  have hpg : IsPGroup hyp.q ↥R := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  have hFq : Fact hyp.q.Prime := ⟨hyp.q_prime⟩
  have hcyc : IsCyclic ↥R := hpg.isCyclic_of_isZGroup
  -- cyclic of exponent `q` ⟹ `|E ⊓ Q| ∣ q`
  obtain ⟨g, hgen⟩ := hcyc.exists_generator
  have hgq : g ^ hyp.q = 1 := hexp g
  have hcard_dvd : Nat.card ↥R ∣ hyp.q := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hgen]
    exact orderOf_dvd_of_pow_eq_one hgq
  have hcardR : Nat.card ↥(Em ⊓ hyp.Q) = Nat.card ↥R :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Em ⊓ hyp.Q ≤ Em)).toEquiv).symm
  -- `q = |W₁| ≤ |E ⊓ Q|` and `|E ⊓ Q| ∣ q` force `|E ⊓ Q| = q`
  have hqle : hyp.q ≤ Nat.card ↥(Em ⊓ hyp.Q) := by
    rw [hyp.q_eq_card_W1]
    exact Subgroup.card_le_of_le hW1le
  have hcard_eq : Nat.card ↥(Em ⊓ hyp.Q) = hyp.q :=
    le_antisymm (hcardR ▸ Nat.le_of_dvd hyp.q_prime.pos hcard_dvd) hqle
  exact (Subgroup.eq_of_le_of_card_ge hW1le
    (by rw [hcard_eq, hyp.q_eq_card_W1])).symm

end OddOrder.Peterfalvi.S15

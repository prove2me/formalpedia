-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.indPW1_apply_eq_one_of_mem_W1_sharp
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:17:10.81121+00:00
-- url     : https://prove2.me/submissions/18672d98-1d39-4675-ab64-59daff8bb365

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean
--   OddOrder/GroupTheory/RepresentationTheory/InflationInduction.lean
--   OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Theorems.Thm_OddOrder_Peterfalvi_S15_uW1_isComplement_P

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped Classical in
/-- **Permutation-character value**: `(Ind_H^G 1_H)(g) = |H|⁻¹ · |{x ∈ G : x⁻¹gx ∈ H}|`.

The induced trivial character is the permutation character of `G` acting on the cosets `G/H`; at
`g` its value is `|H|⁻¹` times the number of conjugators carrying `g` into `H`.  Every summand of
the induction sum over that conjugator set is `1` (the trivial character is constant `1`), so the
sum is the cardinality.  Foundation for the Frobenius induced-trivial-character norm of Peterfalvi
(13.18.b) `‖Ind_E^F 1‖² = (|K|−1)/|E| + 1` (via Frobenius reciprocity + the Frobenius
double-coset count). -/
theorem induce_one_apply {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    [Invertible (Nat.card ↥H : ℂ)] (g : G) :
    ClassFunction.induce H (trivialClassFunction ↥H) g
      = ⅟(Nat.card ↥H : ℂ) *
        ((Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ H)).card : ℂ) := by
  rw [ClassFunction.induce_apply_eq_sum_filter]
  congr 1
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ))
      (fun x hx => by
        rw [Finset.mem_filter] at hx
        rw [ClassFunction.induceTerm_of_mem (trivialClassFunction ↥H) hx.2]
        rfl),
    Finset.sum_const, nsmul_eq_mul, mul_one]

open scoped Classical in
/-- **Frobenius permutation char is `1` on the complement #** (third value case of (13.18.b)).

For a Frobenius group `G = N ⋊ A`, the induced trivial character `Ind_A^G 1` takes value `1` on
`A#`: the conjugator set `{x : x⁻¹ax ∈ A}` is exactly `A`.  `x ∈ A` clearly works; conversely
`x⁻¹ax ∈ A` puts `a ∈ A ⊓ A^x`, which is `⊥` for `x ∉ A` by the Frobenius trivial-intersection
property (`IsFrobeniusGroup.trivialIntersection`), forcing `a = 1`.  So the count is `|A|` and the
value is `⅟|A| · |A| = 1`. -/
theorem induce_one_eq_one_of_mem_complement {G : Type*} [Group G] [Fintype G]
    {N A : Subgroup G} (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G N A)
    [Invertible (Nat.card ↥A : ℂ)] {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    ClassFunction.induce A (trivialClassFunction ↥A) a = 1 := by
  rw [induce_one_apply]
  have hfilter : (Finset.univ.filter (fun x : G => x⁻¹ * a * x ∈ A))
      = Finset.univ.filter (fun x : G => x ∈ A) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · intro hmem
      by_contra hxA
      have hmemmap : a ∈ A ⊓ Subgroup.map (MulAut.conj x).toMonoidHom A := by
        rw [Subgroup.mem_inf]
        refine ⟨ha, Subgroup.mem_map.mpr ⟨x⁻¹ * a * x, hmem, ?_⟩⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
      rw [hFrob.trivialIntersection x hxA, Subgroup.mem_bot] at hmemmap
      exact ha1 hmemmap
    · intro hxA
      exact A.mul_mem (A.mul_mem (A.inv_mem hxA) ha) hxA
  rw [hfilter]
  have hcard : (Finset.univ.filter (fun x : G => x ∈ A)).card = Nat.card ↥A := by
    rw [Nat.card_eq_fintype_card]; simp [Fintype.card_subtype]
  rw [hcard, invOf_mul_self]

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/GroupTheory/RepresentationTheory/InflationInduction.lean =====
namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical in
/-- **Fiber cardinality of the quotient map.**  The number of `g : G` mapping to a fixed coset
`q : G ⧸ N` under `QuotientGroup.mk` equals `|N|` (every fiber is a coset of `N`,
`QuotientGroup.card_preimage_mk` with a singleton). -/
theorem card_filter_mk_eq {N : Subgroup G} [Fintype G] (q : G ⧸ N) :
    (Finset.univ.filter (fun g : G => (QuotientGroup.mk g : G ⧸ N) = q)).card = Nat.card ↥N := by
  have hcard : (Finset.univ.filter (fun g : G => (QuotientGroup.mk g : G ⧸ N) = q)).card
      = Nat.card ↥((QuotientGroup.mk : G → G ⧸ N) ⁻¹' ({q} : Set (G ⧸ N))) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine congrArg Finset.card ?_
    ext g
    simp [Set.mem_preimage]
  rw [hcard, QuotientGroup.card_preimage_mk N ({q} : Set (G ⧸ N))]
  simp

open scoped Classical in
/-- **Peterfalvi (1.6)(b)** (book p. 7): *induction commutes with inflation along a normal subgroup
contained in the kernel.*

Let `N ⊴ G` with `N ≤ H`, let `θ₁` be a class function on `H/N = H.map (mk' N)`, and let `θ` be the
class function on `H` it inflates to -- i.e. `θ(x) = θ₁(xN)` for all `x ∈ H` (`hinfl`).  Then

`Ind_H^G θ = (Ind_{H/N}^{G/N} θ₁) ∘ mk'`.

This is the book's statement: there `θ ∈ Irr(H)` is given with `N ⊆ Ker θ`, `θ₁` is *defined* by
`θ₁(xN) = θ(x)`, and `χ` -- the character of `G/N` with `χ(xN) = (Ind_H^G θ)(x)`, which exists by
(1.6)(a) -- is shown to equal `Ind_{H/N}^{G/N} θ₁`.  Saying "`χ` inflates to `Ind_H^G θ`" is the
same as the displayed equation, and stating it that way avoids having to construct `χ` (the
equation determines it, `mk'` being surjective).  Neither irreducibility of `θ` nor `N ⊆ Ker θ` is
needed beyond what `hinfl` already says: `hinfl` *is* the assertion that `θ` factors through `H/N`,
which for a character is exactly `N ⊆ Ker θ`.

*Proof* (the book's).  Both sides vanish off `H` resp. `H/N`, and the conjugator condition
`x⁻¹gx ∈ H` transports along `mk` (`N ≤ H`), so the two induction sums have matching terms:
`induceTerm H θ x g = induceTerm (H/N) θ₁ (mk x) (mk g)`.  Summing over `G` rather than `G/N`
overcounts by the constant fiber size `|N|` (`card_filter_mk_eq`), which the normalization
`⅟|H| = ⅟(|N|·|H/N|)` absorbs. -/
theorem induce_eq_compHom_induce_of_inflation {N H : Subgroup G} [N.Normal] (hNH : N ≤ H)
    [Fintype G] [Fintype (G ⧸ N)] [Invertible (Nat.card ↥H : ℂ)]
    [Invertible (Nat.card ↥(H.map (QuotientGroup.mk' N)) : ℂ)]
    (θ : ClassFunction ↥H ℂ) (θ₁ : ClassFunction ↥(H.map (QuotientGroup.mk' N)) ℂ)
    (hinfl : ∀ (x : G) (hx : x ∈ H),
      θ ⟨x, hx⟩ = θ₁ ⟨QuotientGroup.mk x, Subgroup.mem_map_of_mem _ hx⟩) :
    ClassFunction.induce H θ
      = ClassFunction.compHom (QuotientGroup.mk' N)
          (ClassFunction.induce (H.map (QuotientGroup.mk' N)) θ₁) := by
  classical
  -- Membership bridge: `mk y ∈ H/N ↔ y ∈ H` (uses `N ≤ H`).
  have hmem : ∀ y : G, (QuotientGroup.mk y : G ⧸ N) ∈ H.map (QuotientGroup.mk' N) ↔ y ∈ H := by
    intro y
    rw [← QuotientGroup.mk'_apply, ← Subgroup.mem_comap, Subgroup.comap_map_eq,
      QuotientGroup.ker_mk', sup_eq_left.mpr hNH]
  -- `|H| = |N| · |H/N|`: `H` is the `mk`-preimage of `H/N`, whose fibers all have size `|N|`.
  have hcardH : (Nat.card ↥H : ℂ)
      = (Nat.card ↥N : ℂ) * (Nat.card ↥(H.map (QuotientGroup.mk' N)) : ℂ) := by
    have hset : ((QuotientGroup.mk : G → G ⧸ N) ⁻¹'
        (H.map (QuotientGroup.mk' N) : Set (G ⧸ N))) = (H : Set G) := by
      ext y
      rw [Set.mem_preimage, SetLike.mem_coe, SetLike.mem_coe, hmem y]
    have h := QuotientGroup.card_preimage_mk N (H.map (QuotientGroup.mk' N) : Set (G ⧸ N))
    rw [hset, SetLike.coe_sort_coe, SetLike.coe_sort_coe] at h
    exact_mod_cast h
  have hneN : (Nat.card ↥N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  ext g
  -- Termwise match, the heart of the proof.
  have hterm : ∀ x : G, ClassFunction.induceTerm H θ x g
      = ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) θ₁
          (QuotientGroup.mk x) (QuotientGroup.mk g) := by
    intro x
    have hconj : ((QuotientGroup.mk x : G ⧸ N)⁻¹ * QuotientGroup.mk g * QuotientGroup.mk x)
        = (QuotientGroup.mk (x⁻¹ * g * x) : G ⧸ N) := by
      simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    by_cases hx : x⁻¹ * g * x ∈ H
    · rw [ClassFunction.induceTerm_of_mem θ hx,
        ClassFunction.induceTerm_of_mem θ₁ (by rw [hconj]; exact (hmem _).mpr hx)]
      rw [hinfl (x⁻¹ * g * x) hx]
      congr 1
    · rw [ClassFunction.induceTerm_of_not_mem θ hx,
        ClassFunction.induceTerm_of_not_mem θ₁ (by rw [hconj]; exact fun h => hx ((hmem _).mp h))]
  -- Sum over `G` = `|N|` × sum over `G ⧸ N` (constant fiber size).
  have hsum : (∑ x : G, ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) θ₁
        (QuotientGroup.mk x) (QuotientGroup.mk g))
      = (Nat.card ↥N : ℂ) * ∑ q : G ⧸ N,
          ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) θ₁ q (QuotientGroup.mk g) := by
    rw [← Finset.sum_fiberwise' (Finset.univ) (fun x : G => (QuotientGroup.mk x : G ⧸ N))
      (fun q => ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) θ₁ q
        (QuotientGroup.mk g)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_filter_mk_eq q]
  rw [ClassFunction.compHom_apply, QuotientGroup.mk'_apply, ClassFunction.induce_apply,
    ClassFunction.induce_apply, Finset.sum_congr rfl (fun x _ => hterm x), hsum, ← mul_assoc]
  -- `⅟|H| · |N| = ⅟|H/N|`.
  congr 1
  rw [invOf_eq_inv, invOf_eq_inv, hcardH, mul_inv, mul_comm ((Nat.card ↥N : ℂ))⁻¹,
    mul_assoc, inv_mul_cancel₀ hneN, mul_one]

open scoped Classical in
/-- **P2 — trivial-character induction–inflation commute**: the `θ = 1` case of Peterfalvi (1.6)(b)
(`induce_eq_compHom_induce_of_inflation`).  For a normal
subgroup `N ⊴ G` contained in `A ≤ G`, the induced trivial character of `A` is the inflation of the
induced trivial character of the quotient subgroup `A/N = A.map (mk' N) ≤ G ⧸ N`:
`Ind_A^G 1_A = (Ind_{A/N}^{G/N} 1) ∘ mk'`.

Both are permutation characters.  Pointwise at `g` (`induceTriv_apply`): the conjugator sets
`{x : x⁻¹gx ∈ A}` and `{xq : xq⁻¹ḡxq ∈ A/N}` correspond under `mk` (`x⁻¹gx ∈ A ↔ mk(x⁻¹gx) ∈ A/N`,
using `N ≤ A`), with every fiber of `mk` of size `|N|`; the `⅟|A| = ⅟(|N|·|A/N|)` normalization
absorbs the `|N|` fiber factor. -/
theorem induce_one_eq_compHom_induce_one_of_le {N A : Subgroup G} [N.Normal] (hNA : N ≤ A)
    [Fintype G] [Fintype (G ⧸ N)] [Invertible (Nat.card ↥A : ℂ)]
    [Invertible (Nat.card ↥(A.map (QuotientGroup.mk' N)) : ℂ)] :
    ClassFunction.induce A (trivialClassFunction ↥A)
      = ClassFunction.compHom (QuotientGroup.mk' N)
          (ClassFunction.induce (A.map (QuotientGroup.mk' N))
            (trivialClassFunction ↥(A.map (QuotientGroup.mk' N)))) :=
  induce_eq_compHom_induce_of_inflation hNA (trivialClassFunction ↥A)
    (trivialClassFunction ↥(A.map (QuotientGroup.mk' N))) (fun _ _ => rfl)

end OddOrder.RepresentationTheory

-- ===== OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs in
open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.a), the `W₁^#`-value of the induced trivial character** (Coq `gammaW1`):
`Ind_{P⋊W₁}^S 1 (x) = 1` for `x ∈ W₁^#`.  Mod-`P` inflation
(`induce_one_eq_compHom_induce_one_of_le`) turns the value into `γ(x̄)` for
`γ = Ind_{Ā}^{S̄} 1`; the `S̄ ≅ U ⋊ W₁` Frobenius transport (the `indPW1_inner_self_aux`
setup) and the Frobenius trivial-intersection complement value
(`induce_one_eq_one_of_mem_complement`) give `γ(x̄) = 1`, with `x̄ ≠ 1` because
`W₁ ⊓ P = ⊥` (`uW1_isComplement_P`). -/
theorem _root_.solution [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {x : ↥hyp.S} (hxW1 : (x : G) ∈ hyp.W1) (hx1 : x ≠ 1) :
    indPW1 hyp x = 1 := by
  classical
  -- Structural setup (the `indPW1_inner_self_aux` pattern).
  have hcompl := uW1_isComplement_P hyp
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_M'.trans hM'_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hU_le_M' : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
  have hUW1_le_S : hyp.U ⊔ hyp.W1 ≤ hyp.S := sup_le (hU_le_M'.trans hM'_le_S) hW1_le_S
  have hW1_le_UW1 : hyp.W1 ≤ hyp.U ⊔ hyp.W1 := le_sup_right
  have hW1_le_PW1 : hyp.W1 ≤ hyp.P ⊔ hyp.W1 := le_sup_right
  have hP_le_PW1 : hyp.P ≤ hyp.P ⊔ hyp.W1 := le_sup_left
  have hPW1_le_S : hyp.P ⊔ hyp.W1 ≤ hyp.S := sup_le hP_le_S hW1_le_S
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  have hNA : hyp.P.subgroupOf hyp.S ≤ (hyp.P ⊔ hyp.W1).subgroupOf hyp.S :=
    Subgroup.comap_mono hP_le_PW1
  -- Inflation: `indPW1 x = γ(x̄)`.
  rw [show indPW1 hyp = ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
        (trivialClassFunction _) from rfl,
    OddOrder.RepresentationTheory.induce_one_eq_compHom_induce_one_of_le hNA,
    OddOrder.RepresentationTheory.ClassFunction.compHom_apply]
  -- The `S̄ = Ū ⋊ W̄₁` Frobenius transport (`indPW1_inner_self_aux` pattern).
  have hSdataUne : hyp.Sdata.U ≠ ⊥ := (hyp.toTypesIIIIIIVSetupS _hG).nontrivial.1
  have hUW1frob : Ch06.IsFrobeniusGroup ↥(hyp.U ⊔ hyp.W1)
      (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1)) (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1)) := by
    have h := S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
    rw [hyp.Sdata_U_eq, hyp.Sdata_W1_eq] at h
    exact h
  set f : ↥(hyp.U ⊔ hyp.W1) →* (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) :=
    (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S)).comp (Subgroup.inclusion hUW1_le_S) with hf
  have he_apply : ∀ w : ↥(hyp.U ⊔ hyp.W1),
      f w = QuotientGroup.mk (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S) := by
    intro w
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    rw [he_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hw
    have hwUW1S : (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S) ∈ (hyp.U ⊔ hyp.W1).subgroupOf hyp.S := by
      rw [Subgroup.mem_subgroupOf]; exact w.2
    have hbot : (⟨(w : G), hUW1_le_S w.2⟩ : ↥hyp.S)
        ∈ ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) ⊓ (hyp.P.subgroupOf hyp.S) :=
      Subgroup.mem_inf.mpr ⟨hwUW1S, Subgroup.mem_subgroupOf.mpr hw⟩
    rw [disjoint_iff.mp hcompl.disjoint, Subgroup.mem_bot] at hbot
    exact Subtype.ext (by simpa using congrArg Subtype.val hbot)
  have hcard : Fintype.card ↥(hyp.U ⊔ hyp.W1)
      = Fintype.card (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      show Nat.card (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) = (hyp.P.subgroupOf hyp.S).index from rfl,
      hcompl.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW1_le_S).toEquiv]
  set e : ↥(hyp.U ⊔ hyp.W1) ≃* (↥hyp.S ⧸ hyp.P.subgroupOf hyp.S) :=
    MulEquiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩) with he
  have he_toMonoidHom : ∀ w, e.toMonoidHom w = f w := fun _ => rfl
  have hFrob := Ch06.isFrobeniusGroup_map_equiv hUW1frob e
  have hAmatch : (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1)).map e.toMonoidHom
      = ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).map
          (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S)) := by
    apply le_antisymm
    · rintro _ ⟨w, hwW1, rfl⟩
      have hwW1' : (w : G) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hwW1)
      refine Subgroup.mem_map.mpr ⟨⟨(w : G), hPW1_le_S (hW1_le_PW1 hwW1')⟩,
        Subgroup.mem_subgroupOf.mpr (hW1_le_PW1 hwW1'), ?_⟩
      rw [QuotientGroup.mk'_apply, he_toMonoidHom, he_apply]
    · rintro _ ⟨s, hsPW1, rfl⟩
      have hsG : (s : G) ∈ hyp.P ⊔ hyp.W1 :=
        Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hsPW1)
      have hsmem : (s : G) ∈ (↑(hyp.P ⊔ hyp.W1) : Set G) := hsG
      rw [Subgroup.coe_mul_of_right_le_normalizer_left hyp.P hyp.W1 (hW1_le_S.trans hS_norm_P)]
        at hsmem
      obtain ⟨p, hp, w, hw, hpw⟩ := Set.mem_mul.mp hsmem
      have hwW1 : w ∈ hyp.W1 := SetLike.mem_coe.mp hw
      have hpP : p ∈ hyp.P := SetLike.mem_coe.mp hp
      refine Subgroup.mem_map.mpr ⟨⟨w, hW1_le_UW1 hwW1⟩,
        Subgroup.mem_subgroupOf.mpr hwW1, ?_⟩
      have hs_eq : s = (⟨p, hP_le_S hpP⟩ : ↥hyp.S) * ⟨w, hW1_le_S hwW1⟩ :=
        Subtype.ext (by rw [Subgroup.coe_mul]; exact hpw.symm)
      have hp1 : QuotientGroup.mk' (hyp.P.subgroupOf hyp.S) ⟨p, hP_le_S hpP⟩ = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact Subgroup.mem_subgroupOf.mpr hpP
      rw [he_toMonoidHom, he_apply, ← QuotientGroup.mk'_apply, hs_eq, map_mul, hp1, one_mul]
  rw [hAmatch] at hFrob
  -- `x̄ ∈ Ā` and `x̄ ≠ 1`; conclude by the Frobenius complement value.
  have hxA : QuotientGroup.mk' (hyp.P.subgroupOf hyp.S) x
      ∈ ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).map
          (QuotientGroup.mk' (hyp.P.subgroupOf hyp.S)) :=
    Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr (hW1_le_PW1 hxW1), rfl⟩
  have hx1' : QuotientGroup.mk' (hyp.P.subgroupOf hyp.S) x ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hxUW1S : x ∈ (hyp.U ⊔ hyp.W1).subgroupOf hyp.S :=
      Subgroup.mem_subgroupOf.mpr (hW1_le_UW1 hxW1)
    have hbot : x ∈ ((hyp.U ⊔ hyp.W1).subgroupOf hyp.S) ⊓ (hyp.P.subgroupOf hyp.S) :=
      Subgroup.mem_inf.mpr ⟨hxUW1S, h1⟩
    rw [disjoint_iff.mp hcompl.disjoint, Subgroup.mem_bot] at hbot
    exact hx1 hbot
  exact induce_one_eq_one_of_mem_complement hFrob hxA hx1'

end OddOrder.Peterfalvi.S15

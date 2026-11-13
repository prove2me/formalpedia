-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.T_typeIII_calT1_family_galois
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:35:16.864409+00:00
-- url     : https://prove2.me/submissions/51d75dfe-75d0-460f-83cb-5a3eab447fdb

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CharacterProduct.lean
--   OddOrder/GroupTheory/RepresentationTheory/OrbitOnIrr.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP

-- ===== OddOrder/GroupTheory/RepresentationTheory/CharacterProduct.lean =====
set_option linter.unusedFintypeInType false

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **An abelian group has exactly `|G|` irreducible characters.**  For a finite commutative group
every conjugacy class is a singleton (`isConj_iff_eq`), so `|ConjClasses G| = |G|`, and the number
of
irreducible characters equals the number of conjugacy classes (`card_irreducibleCharacter_eq`).  In
Gallagher's theorem this counts `|Irr(I/H)| = [I:H]` — the number of linear characters `β` twisting
`χ` — so the `[I:H]` distinct constituents `χ·Inf(β)` exhaust `Ind_H^I θ`. -/
theorem card_irreducibleCharacter_eq_card_of_commGroup {G : Type*} [CommGroup G] [Finite G] :
    Nat.card (IrreducibleCharacter G) = Nat.card G := by
  rw [card_irreducibleCharacter_eq]
  exact (Nat.card_congr (Equiv.ofBijective ConjClasses.mk
    ⟨fun a b h => isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h),
      ConjClasses.mk_surjective⟩)).symm

end OddOrder.RepresentationTheory

-- ===== OddOrder/GroupTheory/RepresentationTheory/OrbitOnIrr.lean =====
namespace OddOrder.RepresentationTheory

open ClassFunction

variable {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]

variable [Fintype G] [Fintype ↥H] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
omit [Fintype ↥H] in
/-- **The irreducibly-induced image has cardinality `|T| / [G:H]`** (multiplied-out form).

For a conjugation-invariant Finset `T ⊆ Irr H` (`H ⊴ G`) whose every member `θ` has inertia
`I_G(θ) = H` — i.e. `Ind_H^G θ` is irreducible — the induction map `θ ↦ Ind_H^G θ` is `[G:H]`-to-one
onto its image, so `|image| · [G:H] = |T|`.

`Finset.card_eq_sum_card_image` writes `|T|` as the sum over the image of the fibre cardinalities,
and each fibre `{θ ∈ T | Ind θ = χ}` — being the `G`-conjugation orbit of any preimage `θ₀`
(`card_filter_induce_eq_index_inertia`) — has size `[G : I_G(θ₀)] = [G : H]` by the inertia
hypothesis.  A constant summand over the image then collapses to `|image| · [G:H]`. -/
theorem card_image_induce_mul_index_eq
    (T : Finset (IrreducibleCharacter H))
    (hT : ∀ θ ∈ T, ∀ g : G, IrreducibleCharacter.conjBy (G := G) (H := H) g θ ∈ T)
    (hinertia : ∀ θ ∈ T, IrreducibleCharacter.inertia (G := G) (H := H) θ = H) :
    (T.image (fun θ => induce H θ.toClassFunction)).card * H.index = T.card := by
  classical
  have : Fintype ↥H := Fintype.ofFinite _
  -- `|T| = ∑_{χ ∈ image} |fibre over χ|`, each fibre `= [G:H]`.
  rw [Finset.card_eq_sum_card_image (fun θ => induce H θ.toClassFunction) T]
  rw [Finset.sum_congr rfl (fun χ hχ => ?_), Finset.sum_const, smul_eq_mul, mul_comm]
  -- Fibre cardinality = `[G:H]` via `card_filter_induce_eq_index_inertia` + inertia = `H`.
  obtain ⟨θ₀, hθ₀T, hθ₀eq⟩ := Finset.mem_image.mp hχ
  have hfib : {a ∈ T | induce H a.toClassFunction = χ}
      = T.filter (fun θ => induce H θ.toClassFunction = induce H θ₀.toClassFunction) := by
    apply Finset.filter_congr
    intro θ _
    rw [hθ₀eq]
  rw [hfib, card_filter_induce_eq_index_inertia T hT θ₀ hθ₀T, hinertia θ₀ hθ₀T]

open scoped Classical in
omit [Fintype ↥H] in
/-- **The irreducibly-induced image has cardinality `|T| / [G:H]`** (division form).  Immediate
from `card_image_induce_mul_index_eq` and `[G:H] > 0`. -/
theorem card_image_induce_eq_div
    (T : Finset (IrreducibleCharacter H))
    (hT : ∀ θ ∈ T, ∀ g : G, IrreducibleCharacter.conjBy (G := G) (H := H) g θ ∈ T)
    (hinertia : ∀ θ ∈ T, IrreducibleCharacter.inertia (G := G) (H := H) θ = H) :
    (T.image (fun θ => induce H θ.toClassFunction)).card = T.card / H.index := by
  have : Fintype ↥H := Fintype.ofFinite _
  have hidx : 0 < H.index := Nat.pos_of_ne_zero fun h0 => by
    have hmc := H.index_mul_card
    rw [h0, zero_mul] at hmc
    exact (Nat.card_pos (α := G)).ne' hmc.symm
  rw [← card_image_induce_mul_index_eq T hT hinertia, Nat.mul_div_cancel _ hidx]

end OddOrder.RepresentationTheory

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **The `T`-side derived complement `T = T' ⋊ W₂`, index `[T : T'] = p`** (Coq
`index_sdprod defT`, `p = |W2|`).  From the base `W2_isComplement_T_deriv` (`T' ⋊ W₂ = T`, available
ungated at the §16 construction) and `p = |W2|` (`p_eq_card_W2`).  The degree factor of Coq
`calT1_1p` (`Ind_{QV}^T θ (1) = [T:QV]·θ(1) = p` for linear `θ`). -/
theorem T_derived_index_eq_p (hyp : Hypothesis (G := G)) :
    ((derivedInG hyp.base.T).subgroupOf hyp.base.T).index = hyp.base.p := by
  have hW2_le_T : hyp.base.W2 ≤ hyp.base.T := by
    have h1 : hyp.base.W2 ≤ hyp.base.W := by rw [hyp.base.W_eq_join]; exact le_sup_right
    have h2 : hyp.base.W ≤ hyp.base.T := by rw [hyp.base.W_eq_inter]; exact inf_le_right
    exact h1.trans h2
  rw [hyp.base.W2_isComplement_T_deriv.symm.index_eq_card,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2_le_T).toEquiv, hyp.base.p_eq_card_W2]

/-- **`Q.subgroupOf QV` is normal in `QV = T' = derivedInG T`** (`Q = T_F` normalized by `T ⊇ T'`).
The normality feeding the `QV/Q` quotient (Coq `nsQQV`). -/
theorem T_Q_subgroupOf_derived_normal (hyp : Hypothesis (G := G)) :
    (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).Normal := by
  have hQ_le : hyp.base.Q ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_left
  have hM'_le_T : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hT_le_NQ : hyp.base.T ≤ Subgroup.normalizer (hyp.base.Q : Set G) := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)

/-- **The `T`-side complement `Q ⋊ V = QV = T'`** (Coq `defQV`): `Q` (normal in `T'`, being `T_F`
restricted) and `V` complement inside `derivedInG T`, from `Q ⊔ V = T'` (`T_deriv_eq_QV`) and
`Q ⊓ V = ⊥` (`Q_inf_V_eq_bot`).  The `sdprod` giving `QV/Q ≅ V`.  Mirrors the complement built
inside
`S15.coprime_card_V_card_Q_of_disjoint`. -/
theorem T_Q_isComplement_V_derived [Finite G] (hyp : Hypothesis (G := G)) :
    Subgroup.IsComplement' (hyp.base.Q.subgroupOf (derivedInG hyp.base.T))
      (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) := by
  have hQ_le : hyp.base.Q ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.base.V ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right
  have := T_Q_subgroupOf_derived_normal hyp
  have hQnVn_inf : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) ⊓
      (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) = ⊥ := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
      OneMemClass.coe_one]
    refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
    have hxQV : x ∈ (hyp.base.Q ⊓ hyp.base.V : Subgroup G) := ⟨hxQ, hxV⟩
    rwa [hyp.base.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
  have hQnVn_sup : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) ⊔
      (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.base.T_deriv_eq_QV.symm,
      Subgroup.subgroupOf_self]
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hQnVn_inf)
  have hmul := Subgroup.normal_mul (hyp.base.Q.subgroupOf (derivedInG hyp.base.T))
    (hyp.base.V.subgroupOf (derivedInG hyp.base.T))
  rw [hQnVn_sup, Subgroup.coe_top] at hmul
  exact hmul.symm

/-- **`|QV/Q| = |V|`** (Coq `card_isog (sdprod_isog defQV)`): the quotient of `QV = T'` by `Q` has
the order of the complement `V`.  The source of the abelian-quotient irreducible count `v − 1`
(nonprincipal `QV/Q`-irreducibles) in Coq `size calT1 = (v.-1) %/ p`. -/
theorem T_card_quot_Q_derived_eq_card_V [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card (↥(derivedInG hyp.base.T) ⧸ (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)))
      = Nat.card ↥hyp.base.V := by
  have hV_le : hyp.base.V ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right
  have := T_Q_subgroupOf_derived_normal hyp
  -- `QV/Q ≅ V.subgroupOf QV` via the complement (`Q` normal in the `K`-slot).
  rw [Nat.card_congr (T_Q_isComplement_V_derived hyp).symm.QuotientMulEquiv.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le).toEquiv]

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

open scoped Classical in
/-- **The `calT1` orbit count, ungated engine** — Peterfalvi (14.9), Coq
`PFsection14.v:836--845` `size calT1 = (v.-1) %/ p`, the *cardinality* half.

Given any conjugation-invariant `Finset` `𝒯 ⊆ Irr(QV)` (`QV = T' = derivedInG T`, normal in `↥T`)
whose every member induces irreducibly to `T` (equivalently has inertia `I_T(θ) = QV`), the map
`θ ↦ Ind_{QV}^T θ` is exactly `[T:QV] = p`-to-one onto its image, so

  `|{Ind_{QV}^T θ | θ ∈ 𝒯}| = |𝒯| / p`.

This is the direct §16 specialization of the shared-infra orbit count
`RepresentationTheory.card_image_induce_eq_div` with `G := ↥T`, `H := QV.subgroupOf T`, and the
index `[T:QV] = p` plugged in via `T_derived_index_eq_p`. It is **ungated** (no
`IsTypeII`/`IsTypeP2`
input, no `sorry`): the two facts entering are supplied by the caller as `𝒯`'s
conjugation-invariance and irreducible-induction (inertia `= QV`) hypotheses.  For the `calT1`
assembly `𝒯` is the non-principal inflated `Irr(QV/Q)`-family, `|𝒯| = |V| − 1`
(the `|Irr(QV/Q)| = |QV/Q| = |V|` count, gated on `V` abelian — see the blocker map on
`T_typeIII_ratio_le`), yielding `|calT1| = (|V| − 1)/p`.

The `Fintype`/`Invertible` instances are taken explicitly (satisfiable from `Finite G`) so the
`induce`-image in the statement type-checks, matching the shared-infra convention. -/
theorem calT1_image_induce_card_eq [Finite G] (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T] [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hQVnormal : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal)
    (𝒯 : Finset (OddOrder.RepresentationTheory.IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hconj : ∀ θ ∈ 𝒯, ∀ g : ↥hyp.base.T,
      OddOrder.RepresentationTheory.IrreducibleCharacter.conjBy
        (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) g θ ∈ 𝒯)
    (hinertia : ∀ θ ∈ 𝒯,
      OddOrder.RepresentationTheory.IrreducibleCharacter.inertia
          (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
        = (derivedInG hyp.base.T).subgroupOf hyp.base.T) :
    (𝒯.image (fun θ => OddOrder.RepresentationTheory.ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)).card
      = 𝒯.card / hyp.base.p := by
  have : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Fintype.ofFinite _
  have := hQVnormal
  -- The shared-infra orbit count `|image| = |𝒯| / [T:QV]`, with `[T:QV] = p`.
  rw [OddOrder.RepresentationTheory.card_image_induce_eq_div 𝒯 hconj hinertia,
    T_derived_index_eq_p hyp]

/-- **Inflation-through-quotient inertia via a Frobenius quotient** (general reusable brick, the
Coq `irr_induced_Frobenius_ker` ∘ `injm_Frobenius_ker` core, PFsection14.v:757--762).

For `N ◁ G`, `H ◁ G` with `N ≤ H`, if the quotient `G/N` is a **Frobenius group** with kernel
`H/N = H.map (mk' N)` (any complement `A'`), then every *non-principal* `θ̄ ∈ Irr(H/N)` inflates
(along a quotient-corestriction `q : ↥H →* ↥(H/N)`, `(q x : G/N) = mk' N x`) to a character of `H`
whose inertia group in `G` is exactly `H`:

  `I_G(inflate_q θ̄) = H`.

Proof: `inertia_eq_of_frobeniusGroup` gives `I_{G/N}(θ̄) = H/N`; the inertia/inflation bridge
`mem_inertia_compHom_iff` transfers `g ∈ I_G(inflate θ̄) ↔ mk' N g ∈ I_{G/N}(θ̄) = H/N`, and
`comap (mk' N) (H.map (mk' N)) = H` (as `N = ker (mk' N) ≤ H`) closes the membership.

This is the inertia input feeding the `calT1` orbit count (`calT1_image_induce_card_eq`): with
`G := ↥T`, `N := Q.subgroupOf T`, `H := QV.subgroupOf T` (`QV = T'`), and the quotient Frobenius
`T/Q = (QV/Q) ⋊ (W₂Q/Q)` sourced *ungated* from the intrinsic type-III datum's `U ⋊ W₁` Frobenius
(`T_typeIII_UW1_frobenius`), it gives `I_T(inflate θ) = QV` for each non-principal inflated
`θ ∈ Irr(QV/Q)`. -/
theorem inertia_inflate_eq_of_frobeniusQuotient {Γ : Type*} [Group Γ] [Finite Γ]
    {N H : Subgroup Γ} [N.Normal] [H.Normal] (hNH : N ≤ H)
    {A' : Subgroup (Γ ⧸ N)}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (Γ ⧸ N)
      (H.map (QuotientGroup.mk' N)) A')
    (q : ↥H →* ↥(H.map (QuotientGroup.mk' N)))
    (hq : ∀ x : ↥H, ((q x : Γ ⧸ N)) = QuotientGroup.mk' N (x : Γ))
    (hqinj : Function.Injective (OddOrder.RepresentationTheory.ClassFunction.compHom q :
      OddOrder.RepresentationTheory.ClassFunction ↥(H.map (QuotientGroup.mk' N)) ℂ →
        OddOrder.RepresentationTheory.ClassFunction ↥H ℂ))
    (θbar : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(H.map (QuotientGroup.mk' N)))
    (hθne : θbar ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter _) :
    OddOrder.RepresentationTheory.ClassFunction.inertia (G := Γ) (H := H)
        (OddOrder.RepresentationTheory.ClassFunction.compHom q
          (θbar : OddOrder.RepresentationTheory.ClassFunction _ ℂ)) = H := by
  have : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  have : Fintype ↥(H.map (QuotientGroup.mk' N)) := Fintype.ofFinite _
  -- Frobenius ⟹ `I_{Γ/N}(θ̄) = H/N`.
  have hIbar : OddOrder.RepresentationTheory.ClassFunction.inertia
      (G := Γ ⧸ N) (H := H.map (QuotientGroup.mk' N))
      (θbar : OddOrder.RepresentationTheory.ClassFunction _ ℂ) = H.map (QuotientGroup.mk' N) :=
    OddOrder.RepresentationTheory.inertia_eq_of_frobeniusGroup hfrob hθne
  ext g
  rw [OddOrder.RepresentationTheory.mem_inertia_compHom_iff q hq hqinj
    (θbar : OddOrder.RepresentationTheory.ClassFunction _ ℂ) g, hIbar]
  constructor
  · intro hmem
    have hcm : g ∈ Subgroup.comap (QuotientGroup.mk' N) (H.map (QuotientGroup.mk' N)) := hmem
    rwa [Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hNH)] at hcm
  · intro hg
    exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩

/-- **The intrinsic type-III complement has order `|V|`** (ungated, canonical):
`|td.typeP.U| = |V|`.
`|td.typeP.U| = [T' : M_F]` (`card_U_eq_index`, `M_F = Q`), and `[T' : M_F] = |QV/Q| = |V|`
(`Subgroup.index_eq_card` + `T_card_quot_Q_derived_eq_card_V`).  The equality is **canonical** —
both
sides are the intrinsic index `[T':M_F]` — so it needs *no* reconciliation of `td.typeP.U` with the
abstract `V` (the source of `calT1`'s abelian-quotient count `size = (v−1)/p`). -/
theorem T_typeIII_card_U [Finite G] (hyp : Hypothesis (G := G))
    (td : OddOrder.GroupTheory.TypeIIIData hyp.base.T) :
    Nat.card ↥td.typeP.U = Nat.card ↥hyp.base.V := by
  rw [td.typeP.card_U_eq_index, ← hyp.base.Q_eq_TF, Subgroup.index_eq_card]
  exact T_card_quot_Q_derived_eq_card_V hyp

/-- **The complement-iso `↥T ⧸ Q ≃* ↥(U ⊔ W₁)` sends `U` onto `T'/Q`** (ungated).  The iso
`e := (subgroupOfEquivOfLe).symm.trans (QuotientMulEquiv).symm` built from the `Q`-complement
(`T_typeIII_Q_isComplement_UW1`) satisfies `e x = mk' Q ↑x` (definitionally), and carries the
Frobenius kernel `U.subgroupOf (U ⊔ W₁)` onto `(T'.subgroupOf T).map (mk' Q) = T'/Q`:

* `⊆`: `e x = mk' Q ↑x` with `↑x ∈ U ≤ T'`;
* `⊇`: a coset `mk' Q ↑t'` (`t' ∈ T'`) decomposes `t' = q·u` in `T' = Q ⋊ U`
  (`derived_complement`), so `mk' Q ↑t' = mk' Q ↑u` (`q ∈ Q` killed, `u⁻¹ q u ∈ Q` by normality),
  the image of `u ∈ U`.

This is the kernel identity feeding `isFrobeniusGroup_map_equiv` (on `T_typeIII_UW1_frobenius`) to
produce the quotient Frobenius `T/Q` with kernel `T'/Q` for
`inertia_inflate_eq_of_frobeniusQuotient`. -/
theorem T_typeIII_quotFrobenius_kernel_eq [Finite G] (hyp : Hypothesis (G := G))
    (td : OddOrder.GroupTheory.TypeIIIData hyp.base.T)
    (hQnormal : (hyp.base.Q.subgroupOf hyp.base.T).Normal)
    (hUW1leM : td.typeP.U ⊔ td.typeP.W1 ≤ hyp.base.T) :
    ((td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1)).map
      ((Subgroup.subgroupOfEquivOfLe hUW1leM).symm.trans
        (T_typeIII_Q_isComplement_UW1 hyp td).symm.QuotientMulEquiv.symm).toMonoidHom) =
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T).map
        (QuotientGroup.mk' (hyp.base.Q.subgroupOf hyp.base.T)) := by
  have := hQnormal
  have hHeqQ : td.typeP.H = hyp.base.Q := by rw [td.typeP.H_eq, hyp.base.Q_eq_TF]
  have hUleUW1 : td.typeP.U ≤ td.typeP.U ⊔ td.typeP.W1 := le_sup_left
  have hQleT : hyp.base.Q ≤ hyp.base.T := hHeqQ ▸ (td.typeP.H_le.trans (Subgroup.map_subtype_le _))
  set e : ↥(td.typeP.U ⊔ td.typeP.W1) ≃* (↥hyp.base.T ⧸ hyp.base.Q.subgroupOf hyp.base.T) :=
    (Subgroup.subgroupOfEquivOfLe hUW1leM).symm.trans
      (T_typeIII_Q_isComplement_UW1 hyp td).symm.QuotientMulEquiv.symm with he_def
  have he : ∀ x : ↥(td.typeP.U ⊔ td.typeP.W1),
      e x = QuotientGroup.mk' (hyp.base.Q.subgroupOf hyp.base.T)
          (⟨(x : G), hUW1leM x.2⟩ : ↥hyp.base.T) := fun x => rfl
  apply le_antisymm
  · rintro _ ⟨x, hxU, rfl⟩
    change e x ∈ _
    rw [he]
    exact Subgroup.mem_map.mpr ⟨⟨(x : G), hUW1leM x.2⟩,
      Subgroup.mem_subgroupOf.mpr (td.typeP.U_le (Subgroup.mem_subgroupOf.mp hxU)), rfl⟩
  · rintro _ ⟨t', ht', rfl⟩
    have ht'M' : (t' : G) ∈ derivedInG hyp.base.T := Subgroup.mem_subgroupOf.mp ht'
    obtain ⟨⟨qq, uu⟩, hdec⟩ :=
      (td.typeP.derived_complement.existsUnique ⟨(t':G), ht'M'⟩).exists
    have huuU : ((uu : ↥(derivedInG hyp.base.T)) : G) ∈ td.typeP.U :=
      Subgroup.mem_subgroupOf.mp uu.2
    have hqqQ : ((qq : ↥(derivedInG hyp.base.T)) : G) ∈ hyp.base.Q :=
      hHeqQ ▸ Subgroup.mem_subgroupOf.mp qq.2
    have hdecG : (t' : G) = ((qq : ↥(derivedInG hyp.base.T)) : G) *
        ((uu : ↥(derivedInG hyp.base.T)) : G) := by
      have := congrArg (Subtype.val) hdec; simpa using this.symm
    have huuT : ((uu : ↥(derivedInG hyp.base.T)) : G) ∈ hyp.base.T := hUW1leM (hUleUW1 huuU)
    set uUW1 : ↥(td.typeP.U ⊔ td.typeP.W1) := ⟨((uu : ↥(derivedInG hyp.base.T)) : G), hUleUW1 huuU⟩
      with huUW1def
    set uElt : ↥hyp.base.T := ⟨((uu : ↥(derivedInG hyp.base.T)) : G), huuT⟩ with huEltdef
    set qElt : ↥hyp.base.T := ⟨((qq : ↥(derivedInG hyp.base.T)) : G), hQleT hqqQ⟩ with hqEltdef
    have htElt : (⟨(t':G), t'.2⟩ : ↥hyp.base.T) = qElt * uElt := by
      apply Subtype.ext; simpa [hqEltdef, huEltdef] using hdecG
    refine Subgroup.mem_map.mpr ⟨uUW1, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mpr huuU), ?_⟩
    change e uUW1 = _
    rw [he]
    have hgoaleq : (⟨((uUW1 : ↥(td.typeP.U ⊔ td.typeP.W1)) : G), hUW1leM uUW1.2⟩ : ↥hyp.base.T)
        = uElt := rfl
    rw [hgoaleq]
    refine ((QuotientGroup.mk'_eq_mk' (hyp.base.Q.subgroupOf hyp.base.T)).mpr
      ⟨uElt⁻¹ * qElt * uElt, ?_, ?_⟩)
    · have hqQ' : qElt ∈ hyp.base.Q.subgroupOf hyp.base.T := by
        rw [Subgroup.mem_subgroupOf]; exact hqqQ
      have hconj := hQnormal.conj_mem qElt hqQ' uElt⁻¹
      simpa using hconj
    · have hg : uElt * (uElt⁻¹ * qElt * uElt) = qElt * uElt := by group
      rw [hg, ← htElt]

open scoped IsMulCommutative in
open scoped Classical in
/-- **Peterfalvi (14.9): the full `calT1` family data** (issue 9072, Stage-2 bridge) — the same
inflated `Irr(QV/Q)`-family `𝒯` as `T_typeIII_calT1_card`, but exposing *all* the predicates the
coherence assembler `T_typeIII_calT1_isCoherent` consumes, not just the count.  There *exists* a
`𝒯 ⊆ Irr(QV)` (the inflations of the non-principal `Irr(QV/Q)` along the quotient corestriction `q`)
with, for `θ ∈ 𝒯`:
* `hinertia : I_T(θ) = QV` (via `inertia_inflate_eq_of_frobeniusQuotient`, the quotient Frobenius);
* `hne : θ ≠ 1` (inflation of a non-principal `θ̄`, injective on `Irr`);
* `hlinear : θ(1) = 1` (inflation of a *linear* `θ̄`, since `QV/Q ≅ U` is abelian,
`td.U_commutative`);
* `hconj𝒯 : θ̄ ∈ 𝒯` (**complex** conjugate, `compHom` commutes with `star`, and `Irr(QV/Q)` is
  complex-conj-closed with non-principality preserved);
* `hgalois𝒯 : θ ∈ 𝒯 ⟹ σθ ∈ 𝒯` for every coefficient automorphism `σ`, since inflation
  commutes pointwise with `mapRingEquiv` and Galois transport preserves non-principality;
and with the count `|calT1_image| = (|V| − 1)/p`.  This packages the "pure transcription" `𝒯`-build
so the (14.9) coherence carrier `horth` is dischargeable end-to-end. -/
theorem _root_.solution [Finite G] (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.base.T] [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (td : TypeIIIData hyp.base.T) :
    ∃ 𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)),
      (∀ θ ∈ 𝒯,
        IrreducibleCharacter.inertia (G := ↥hyp.base.T)
            (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ
          = (derivedInG hyp.base.T).subgroupOf hyp.base.T) ∧
      (∀ θ ∈ 𝒯, θ ≠ trivialIrreducibleCharacter _) ∧
      (∀ θ ∈ 𝒯, (θ.toClassFunction :
        ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1) ∧
      (∀ θ ∈ 𝒯,
        (⟨(θ : ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ).conj,
          θ.isIrreducible.conj⟩ :
          IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)) ∈ 𝒯) ∧
      (∀ (σc : ℂ ≃+* ℂ) θ, θ ∈ 𝒯 →
        IrreducibleCharacter.galoisMap σc θ ∈ 𝒯) ∧
      (𝒯.image (fun θ => ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)).card
        = (Nat.card ↥hyp.base.V - 1) / hyp.base.p := by
  have := hyp.base.finiteG
  have hHnormal : ((derivedInG hyp.base.T).subgroupOf hyp.base.T).Normal :=
    T_derivedSubgroupOf_normal hyp
  have hQnormal : (hyp.base.Q.subgroupOf hyp.base.T).Normal := by
    have hQleT : hyp.base.Q ≤ hyp.base.T := by
      rw [hyp.base.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.base.T
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQleT).mpr ?_
    rw [hyp.base.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T
  have := hQnormal
  have hUW1leM : td.typeP.U ⊔ td.typeP.W1 ≤ hyp.base.T :=
    sup_le ((td.typeP.U_le).trans (Subgroup.map_subtype_le _)) td.typeP.W1_le
  have hNH : hyp.base.Q.subgroupOf hyp.base.T ≤ (derivedInG hyp.base.T).subgroupOf hyp.base.T := by
    intro x hx; rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hyp.base.T_deriv_eq_QV]; exact (le_sup_left : hyp.base.Q ≤ hyp.base.Q ⊔ hyp.base.V) hx
  set mkN := QuotientGroup.mk' (hyp.base.Q.subgroupOf hyp.base.T) with hmkN
  set Hbar := ((derivedInG hyp.base.T).subgroupOf hyp.base.T).map mkN with hHbar
  set q : ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) →* ↥Hbar :=
    (mkN.comp ((derivedInG hyp.base.T).subgroupOf hyp.base.T).subtype).codRestrict Hbar
      (fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩) with hq_def
  have hq : ∀ x : ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T),
      ((q x : ↥Hbar) : ↥hyp.base.T ⧸ hyp.base.Q.subgroupOf hyp.base.T) = mkN (x : ↥hyp.base.T) :=
    fun x => rfl
  have hq_surj : Function.Surjective q := by
    rintro ⟨z, hz⟩; rw [hHbar, Subgroup.mem_map] at hz
    obtain ⟨x, hxH, hxz⟩ := hz; exact ⟨⟨x, hxH⟩, Subtype.ext hxz⟩
  have hqinj : Function.Injective
      (ClassFunction.compHom q :
        ClassFunction ↥Hbar ℂ → ClassFunction ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) ℂ) :=
    ClassFunction.compHom_injective_of_surjective hq_surj
  set e : ↥(td.typeP.U ⊔ td.typeP.W1) ≃* (↥hyp.base.T ⧸ hyp.base.Q.subgroupOf hyp.base.T) :=
    (Subgroup.subgroupOfEquivOfLe hUW1leM).symm.trans
      (T_typeIII_Q_isComplement_UW1 hyp td).symm.QuotientMulEquiv.symm with he_def
  have hfrobUW1 := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius td.typeP td.common.1
  have hqfrob0 := OddOrder.Isaacs.Ch06.isFrobeniusGroup_map_equiv hfrobUW1 e
  have himg := T_typeIII_quotFrobenius_kernel_eq hyp td hQnormal hUW1leM
  rw [show ((Subgroup.subgroupOfEquivOfLe hUW1leM).symm.trans
      (T_typeIII_Q_isComplement_UW1 hyp td).symm.QuotientMulEquiv.symm) = e from rfl] at himg
  rw [himg] at hqfrob0
  set infl : IrreducibleCharacter ↥Hbar →
      IrreducibleCharacter ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) :=
    fun θbar => ⟨ClassFunction.compHom q (θbar : ClassFunction ↥Hbar ℂ),
      IsIrreducibleCharacter.compHom_of_surjective hq_surj θbar.isIrreducible⟩ with hinfl
  have hinfl_inj : Function.Injective infl := by
    intro a b hab
    have : ClassFunction.compHom q (a : ClassFunction ↥Hbar ℂ) =
        ClassFunction.compHom q (b : ClassFunction ↥Hbar ℂ) := congrArg Subtype.val hab
    exact IrreducibleCharacter.ext (hqinj this)
  set 𝒯 := (Finset.univ.filter (fun θbar : IrreducibleCharacter ↥Hbar =>
      θbar ≠ trivialIrreducibleCharacter ↥Hbar)).image infl with h𝒯
  refine ⟨𝒯, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- hinertia
  · intro θ hθ
    rw [h𝒯, Finset.mem_image] at hθ
    obtain ⟨θbar, hθbar, rfl⟩ := hθ
    rw [Finset.mem_filter] at hθbar
    exact inertia_inflate_eq_of_frobeniusQuotient (N := hyp.base.Q.subgroupOf hyp.base.T)
      (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) hNH hqfrob0 q hq hqinj θbar hθbar.2
  -- hne : `infl θbar ≠ 1` since `θbar ≠ 1` and `infl` is injective (`infl 1 = 1`).
  · intro θ hθ
    rw [h𝒯, Finset.mem_image] at hθ
    obtain ⟨θbar, hθbar, rfl⟩ := hθ
    rw [Finset.mem_filter] at hθbar
    intro hcontra
    apply hθbar.2
    -- `infl` injective + `infl (triv) = triv`, so `infl θbar = triv ⟹ θbar = triv`.
    apply hinfl_inj
    rw [hcontra]
    -- `infl (triv Hbar) = triv QV`: pointwise `compHom q (triv) x = triv (q x) = 1 = triv x`.
    apply IrreducibleCharacter.ext
    ext x
    simp [hinfl, ClassFunction.compHom_apply, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      trivialClassFunction_apply]
  -- hlinear : `(infl θbar)(1) = θbar (q 1) = θbar 1 = 1` (θbar linear, `Hbar` abelian).
  · intro θ hθ
    rw [h𝒯, Finset.mem_image] at hθ
    obtain ⟨θbar, hθbar, rfl⟩ := hθ
    -- `Hbar ≅ U` abelian.
    have hUcomm : IsMulCommutative ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) :=
      OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (le_sup_left)).symm td.U_commutative
    have hemap : ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) ≃* ↥Hbar :=
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr himg)
    have hHbarComm : IsMulCommutative ↥Hbar :=
      OddOrder.GroupTheory.isMulCommutative_of_mulEquiv hemap hUcomm
    change (ClassFunction.compHom q (θbar : ClassFunction ↥Hbar ℂ) :
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1
    rw [ClassFunction.compHom_apply, map_one]
    exact θbar.isIrreducible.apply_one_eq_one_of_isMulCommutative
  -- hconj𝒯 : `(infl θbar).conj = infl (θbar.conj)` and `θbar.conj` non-principal ∈ filter.
  · intro θ hθ
    rw [h𝒯, Finset.mem_image] at hθ ⊢
    obtain ⟨θbar, hθbar, rfl⟩ := hθ
    rw [Finset.mem_filter] at hθbar
    refine ⟨⟨(θbar : ClassFunction ↥Hbar ℂ).conj, θbar.isIrreducible.conj⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      -- `θbar̄ ≠ 1`: else `θbar = θbar̄̄ = 1̄ = 1`.
      intro hcontra
      apply hθbar.2
      have hcoe : (θbar : ClassFunction ↥Hbar ℂ).conj = trivialClassFunction ↥Hbar := by
        simpa using congrArg (fun c : IrreducibleCharacter ↥Hbar => (c : ClassFunction ↥Hbar ℂ))
          hcontra
      apply IrreducibleCharacter.ext
      change (θbar : ClassFunction ↥Hbar ℂ) = trivialClassFunction ↥Hbar
      rw [← ClassFunction.conj_conj (θbar : ClassFunction ↥Hbar ℂ), hcoe]
      exact trivialClassFunction_isReal
    · -- `infl (θbar̄) = (infl θbar)^`: pointwise `compHom q θbar̄ x = star (θbar (q x))`.
      apply IrreducibleCharacter.ext
      change ClassFunction.compHom q ((θbar : ClassFunction ↥Hbar ℂ).conj)
        = (ClassFunction.compHom q (θbar : ClassFunction ↥Hbar ℂ)).conj
      ext x
      simp [ClassFunction.compHom_apply, ClassFunction.conj_apply]
  -- Arbitrary coefficient automorphisms preserve the inflated non-principal family.
  · intro σc θ hθ
    rw [h𝒯, Finset.mem_image] at hθ ⊢
    obtain ⟨θbar, hθbar, rfl⟩ := hθ
    rw [Finset.mem_filter] at hθbar
    refine ⟨IrreducibleCharacter.galoisMap σc θbar, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hcontra
      apply hθbar.2
      apply IrreducibleCharacter.ext
      ext x
      have hx := congrArg (fun c : IrreducibleCharacter ↥Hbar =>
        ((c : ClassFunction ↥Hbar ℂ) x)) hcontra
      have hx' := congrArg σc.symm hx
      simpa [IrreducibleCharacter.galoisMap,
        IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        trivialClassFunction_apply] using hx'
    · apply IrreducibleCharacter.ext
      change ClassFunction.compHom q
          (IrreducibleCharacter.galoisMap σc θbar : ClassFunction ↥Hbar ℂ) =
        ClassFunction.mapRingEquiv σc
          (ClassFunction.compHom q (θbar : ClassFunction ↥Hbar ℂ))
      ext x
      simp [IrreducibleCharacter.galoisMap, ClassFunction.compHom_apply,
        ClassFunction.mapRingEquiv_apply]
  -- hcard : `|calT1_image| = (|V| − 1)/p`.
  · have hinertia : ∀ θ ∈ 𝒯,
        IrreducibleCharacter.inertia (G := ↥hyp.base.T)
            (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) θ
          = ((derivedInG hyp.base.T).subgroupOf hyp.base.T) := by
      intro θ hθ
      rw [h𝒯, Finset.mem_image] at hθ
      obtain ⟨θbar, hθbar, rfl⟩ := hθ
      rw [Finset.mem_filter] at hθbar
      exact inertia_inflate_eq_of_frobeniusQuotient (N := hyp.base.Q.subgroupOf hyp.base.T)
        (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) hNH hqfrob0 q hq hqinj θbar hθbar.2
    have hconj : ∀ θ ∈ 𝒯, ∀ g : ↥hyp.base.T,
        IrreducibleCharacter.conjBy
          (G := ↥hyp.base.T) (H := ((derivedInG hyp.base.T).subgroupOf hyp.base.T)) g θ ∈ 𝒯 := by
      intro θ hθ g
      rw [h𝒯, Finset.mem_image] at hθ ⊢
      obtain ⟨θbar, hθbar, rfl⟩ := hθ
      rw [Finset.mem_filter] at hθbar
      refine ⟨IrreducibleCharacter.conjBy (G := ↥hyp.base.T ⧸ hyp.base.Q.subgroupOf hyp.base.T)
        (H := Hbar) (mkN g) θbar, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hcontra
        apply hθbar.2
        have := congrArg (IrreducibleCharacter.conjBy (mkN g)⁻¹) hcontra
        rwa [← IrreducibleCharacter.conjBy_mul, mul_inv_cancel, IrreducibleCharacter.conjBy_one,
          show IrreducibleCharacter.conjBy (mkN g)⁻¹ (trivialIrreducibleCharacter ↥Hbar) =
            trivialIrreducibleCharacter ↥Hbar from ?_] at this
        · apply IrreducibleCharacter.ext
          rw [IrreducibleCharacter.coe_conjBy]; ext x
          simp [ClassFunction.conjBy_apply, trivialIrreducibleCharacter, trivialClassFunction_apply]
      · apply IrreducibleCharacter.ext
        change ClassFunction.compHom q _ = ClassFunction.conjBy g (ClassFunction.compHom q _)
        rw [conjBy_compHom_eq_compHom_conjBy q hq]
        rfl
    have hcard : 𝒯.card = Nat.card ↥hyp.base.V - 1 := by
      rw [h𝒯, Finset.card_image_of_injective _ hinfl_inj]
      have hUcomm : IsMulCommutative ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) :=
        OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe (le_sup_left)).symm td.U_commutative
      have hemap : ↥(td.typeP.U.subgroupOf (td.typeP.U ⊔ td.typeP.W1)) ≃* ↥Hbar :=
        (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
          (MulEquiv.subgroupCongr himg)
      have hHbarComm : IsMulCommutative ↥Hbar :=
        OddOrder.GroupTheory.isMulCommutative_of_mulEquiv hemap hUcomm
      have hIrrHbar : Nat.card (IrreducibleCharacter ↥Hbar) = Nat.card ↥hyp.base.V := by
        rw [card_irreducibleCharacter_eq_card_of_commGroup, ← Nat.card_congr hemap.toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
          T_typeIII_card_U hyp td]
      have hfilter : (Finset.univ.filter (fun θbar : IrreducibleCharacter ↥Hbar =>
          θbar ≠ trivialIrreducibleCharacter ↥Hbar)).card
          = Fintype.card (IrreducibleCharacter ↥Hbar) - 1 := by
        rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      rw [hfilter]
      have : Fintype.card (IrreducibleCharacter ↥Hbar) = Nat.card ↥hyp.base.V := by
        rw [Nat.card_eq_fintype_card] at hIrrHbar; exact hIrrHbar
      rw [this]
    rw [← hcard]
    exact calT1_image_induce_card_eq hyp hHnormal 𝒯 hconj hinertia

end OddOrder.Peterfalvi.S16

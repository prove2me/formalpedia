-- Prove2me | solution 1 for OddOrder.Peterfalvi.S14.theorem88_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:27:37.160913+00:00
-- url     : https://prove2.me/submissions/57835cf6-4293-4f63-b891-be99f9b2a6c7

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/TISubset.lean
--   OddOrder/Peterfalvi/S10_Theorem88CaseB.lean
--   OddOrder/Peterfalvi/S14_MaximalI/TypeICovering.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_TypeICovering
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

-- ===== OddOrder/GroupTheory/TISubset.lean =====
namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

namespace IsTISubset

variable {A : Set G} {L : Subgroup G}

/-- **A TI-subset inside an abelian host pins the normalizer of each of its nonempty pieces**:
if `A` is a TI-subset with normalizer-bound `L`, `A` sits inside `L`, and `L` is commutative,
then `N_G(X) = L` for *every* nonempty `X ⊆ A`.

Both inclusions are short.  For `N_G(X) ≤ L`, pick any `a ∈ X`; then `g·a·g⁻¹ ∈ X ⊆ A`, so the
TI condition places `g ∈ L`.  For `L ≤ N_G(X)`, conjugation by `w ∈ L` fixes every element of
`L` — and both `h ∈ X ⊆ L` and (in the converse direction) `h = w⁻¹·(w·h·w⁻¹)·w ∈ L` — so the
membership iff is an identity.

This is the abstract content of Peterfalvi (8.4.e) (`N_G(X) = W` for every nonempty
`X ⊆ W − (W₁ ∪ W₂)`): BG Theorem 14.7 delivers exactly `IsTISubset (zTilde K K*) (K ⊔ K*)`
together with the cyclicity of `K ⊔ K*`, and (8.4.e) is this lemma applied to them. -/
theorem set_normalizer_eq_of_subset_of_commute (hA : IsTISubset A L) (hAL : A ⊆ (L : Set G))
    (hcomm : ∀ x ∈ L, ∀ y ∈ L, Commute x y)
    {X : Set G} (hX : X.Nonempty) (hXA : X ⊆ A) :
    Subgroup.normalizer X = L := by
  -- Conjugation by an element of `L` fixes `L` pointwise.
  have hfix : ∀ w ∈ L, ∀ h ∈ L, w * h * w⁻¹ = h := by
    intro w hw h hh
    rw [(hcomm w hw h hh).eq, mul_inv_cancel_right]
  refine le_antisymm (fun g hg => ?_) (fun w hw => ?_)
  · obtain ⟨a, ha⟩ := hX
    exact hA g ⟨a, hXA ha, hXA ((Subgroup.mem_set_normalizer_iff.mp hg a).mp ha)⟩
  · rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh; rwa [hfix w hw h (hAL (hXA hh))]
    · intro hh
      -- `h` is a priori arbitrary, but `w·h·w⁻¹ ∈ X ⊆ L` forces `h ∈ L`.
      have hhL : h ∈ L := by
        have : w⁻¹ * (w * h * w⁻¹) * w ∈ L :=
          mul_mem (mul_mem (inv_mem hw) (hAL (hXA hh))) hw
        simpa [mul_assoc] using this
      rwa [hfix w hw h hhL] at hh

end IsTISubset

end OddOrder.GroupTheory

-- ===== OddOrder/Peterfalvi/S10_Theorem88CaseB.lean =====
namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **(8.4.e) from the BG §14 TI-set** — the route both producers of `Theorem88CaseBData` use.

BG Theorem 14.7 (`typeP_duality`) hands out two facts about the κ-Hall pair `K`, `K*` of a
type-`P` maximal subgroup: the join `K ⊔ K*` is cyclic, and `Ẑ = (K ⊔ K*) − (K ∪ K*)`
(`OddOrder.BG.Ch4.S14.zTilde`, definitionally the set below) is a TI-subset with
normalizer-bound `K ⊔ K*`.  Together these *are* (8.4.e): a cyclic host is commutative, so
`set_normalizer_eq_of_subset_of_commute` applies.

Note that neither conjunct mentions the dual maximal subgroup, so a producer holding only the
pair `(K, K*)` can supply (8.4.e) without identifying the `∃!` partner — and without a
`TypePData` carrier (which would additionally demand type-`P₂`-ness and a `K`-invariant
`(κ∪σ)′`-Hall complement). -/
theorem normalizer_V_of_isTISubset {A B : Subgroup G} (hcyc : IsCyclic ↥(A ⊔ B))
    (hTI : IsTISubset (((A ⊔ B : Subgroup G) : Set G) \ ((A : Set G) ∪ (B : Set G))) (A ⊔ B)) :
    ∀ X : Set G, X.Nonempty →
      X ⊆ ((A ⊔ B : Subgroup G) : Set G) \ ((A : Set G) ∪ (B : Set G)) →
      Subgroup.normalizer X = A ⊔ B := by
  have := hcyc
  let : CommGroup ↥(A ⊔ B) := IsCyclic.commGroup
  refine fun X hX hXV => hTI.set_normalizer_eq_of_subset_of_commute Set.sdiff_subset ?_ hX hXV
  exact fun x hx y hy => congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(A ⊔ B)) ⟨y, hy⟩)

end OddOrder.Peterfalvi.S10

-- ===== OddOrder/Peterfalvi/S14_MaximalI/TypeICovering.lean =====
namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Type-`P` ⟹ non-Type-I** (Proposition 16.1(b)(c)(d)): a type-`P` maximal subgroup of a minimal
simple group of odd order is one of the Types II–V.  Split `κ(M)` against `π(M) - σ(M)`: equal gives
`P₁`, which is Type V (`M_F = M_σ`) or Type III/IV (`M_F ≠ M_σ`); unequal gives `P₂` = Type II.
This
is the local `typeP_imp_nonI` of BG Theorem I's dichotomy proof, isolated here for
`theorem88_dichotomy`. -/
private theorem isTypeNonI_of_isTypeP [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {N : Subgroup G} (hN : N ∈ maximalSubgroups G)
    (hP : OddOrder.BG.Ch4.S14.IsTypeP N) : IsTypeNonI N := by
  obtain ⟨_, hbII, hcIII_IV, hdV, _, _⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hN
  by_cases hk : OddOrder.BG.Ch4.S14.kappa N = OddOrder.BG.Ch4.S14.sigmaComplementPrimes N
  · have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 N := ⟨hP, hk⟩
    by_cases hMF : OddOrder.BG.Ch4.S15.MF N = OddOrder.BG.Ch3.S10.Msigma N
    · exact Or.inr (Or.inr (Or.inr (hdV.mpr ⟨hP1, hMF⟩)))
    · rcases hcIII_IV.mpr ⟨hP1, hMF⟩ with hIII | hIV
      · exact Or.inr (Or.inl hIII)
      · exact Or.inr (Or.inr (Or.inl hIV))
  · exact Or.inl (hbII.mpr ⟨hP, hk⟩)

/-- **Theorem (8.8) dichotomy** (BG §16): for a minimal simple group of odd order, either every
maximal subgroup is of type I, or the case-(b) pairing data `Theorem88CaseBData` exists.

*Proof.*  If some maximal `S` is not type I, then it is type `P` (Proposition 16.1(a): `TypeI ⟺
TypeF`, and `TypeF ⟺ κ(S) = ∅`).  BG Theorem 14.7 duality (`typeP_duality`) applied to `S` with a
`κ(S)`-Hall subgroup `K` produces the complement `S = S' ⋊ K` (first conjunct), the dual maximal
`T = M*`, the cyclic factor `W = K ⊔ K*`, the type-II witness, and the `κ(M*)`-Hall `K*`.  Applying
the duality again at `M*` gives the second complement `T = T' ⋊ K*`.  The `κ`-Hall complement `K`
plays the role of the case-(b) factor `W₁` (both `K` and the type-`P` `W₁` complement `S'`,
Peterfalvi
(8.8.b1)).  Cites the merged BG §16 `typeP_duality` and `proposition_type_classification`; the
remaining hard content lives in their (issue-8015) residuals.

The remaining clauses of (8.8.b) come from the same two BG results.  The direct-product shape
`W = K × K*` and the intersection `S ∩ M* = K ⊔ K*` (8.8.b1, last clause) are
`typeP_pair_W_structure` (BG §16); the (8.4.e) normalizer law is the BG 14.7 TI-set
`Ẑ = (K ⊔ K*) − (K ∪ K*)` read through `normalizer_V_of_isTISubset`; the covering (8.8.b4) is
the last conjunct of `typeP_duality` (every type-`P` maximal is conjugate to one of the pair)
combined with `TypeI ⟺ ¬TypeP`. -/
theorem _root_.solution [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) ∨
      Nonempty (OddOrder.Peterfalvi.S10.Theorem88CaseBData G) := by
  classical
  -- Not type I ⟹ type `P` (Prop 16.1(a): `TypeI ⟺ TypeF`, `TypeF ⟺ κ = ∅`).  Used both to start
  -- the argument at `S` and, in the covering clause (8.8.b4), at an arbitrary maximal subgroup.
  have notTypeI_imp_typeP : ∀ N : Subgroup G, N ∈ maximalSubgroups G →
      ¬ IsTypeI N → OddOrder.BG.Ch4.S14.IsTypeP N := by
    intro N hN hnotI
    have hiff := (OddOrder.BG.Ch4.S16.proposition_type_classification hG hN).1
    have hnotF : ¬ OddOrder.BG.Ch4.S14.IsTypeF N := fun hF => hnotI (hiff.mpr hF)
    rw [OddOrder.BG.Ch4.S14.IsTypeP, Set.nonempty_iff_ne_empty]
    exact fun he => hnotF he
  by_cases hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M
  · exact Or.inl hall
  · refine Or.inr ?_
    push Not at hall
    obtain ⟨S, hS, hSnotI⟩ := hall
    have : Group.IsSolvable ↥S := hG.isSolvable_of_mem_maximalSubgroups hS
    have hSP : OddOrder.BG.Ch4.S14.IsTypeP S := notTypeI_imp_typeP S hS hSnotI
    -- A `κ(S)`-Hall subgroup `K` of `S` (Hall's theorem in the solvable `S`).
    obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥S) (OddOrder.BG.Ch4.S14.kappa S)
    set K : Subgroup G := K'.map S.subtype with hKdef
    have hKeq : K.subgroupOf S = K' :=
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective K'
    have hK : Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S) (K.subgroupOf S) := by
      rw [hKeq]; exact hK'
    set Kstar : Subgroup G :=
      OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) with hKstardef
    -- BG Theorem 14.7 duality at `S`: `S = S' ⋊ K` (`hScompl`), the dual `M*`, its data,
    -- the TI-set `Ẑ` (`hTI`) and the type-`P` covering (`hcover`).
    obtain ⟨hScompl, _, Mstar, ⟨hMstarMem, hMstarP, hSnconjMstar,
        ⟨hKstarMstar, hKstar_hall, hK_eq⟩, hcyc, hTI, hP2disj, hcover⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hS hSP (Subgroup.map_subtype_le K') hK hKstardef
    -- Apply duality again at `M*` with its `κ`-Hall `K*`: `M* = (M*)' ⋊ K*` (`hTcompl`).
    obtain ⟨hTcompl, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hMstarMem hMstarP hKstarMstar hKstar_hall hK_eq
    -- A `(κ(S) ∪ σ(S))′`-Hall subgroup `U` of the solvable `S`, the last input of
    -- `typeP_pair_W_structure` (which supplies `S ∩ M* = K ⊔ K*` and `K ⊓ K* = ⊥`).
    obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥S)
      ((OddOrder.BG.Ch4.S14.kappa S ∪ OddOrder.BG.Ch3.S10.sigma S)ᶜ)
    have hUeq : (U'.map S.subtype).subgroupOf S = U' :=
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective U'
    have hU : Ch03.IsHallSubgroup ((OddOrder.BG.Ch4.S14.kappa S ∪ OddOrder.BG.Ch3.S10.sigma S)ᶜ)
        ((U'.map S.subtype).subgroupOf S) := by
      rw [hUeq]; exact hU'
    obtain ⟨hWjoin, _, hbot, _⟩ :=
      OddOrder.BG.Ch4.S16.typeP_pair_W_structure hG hS hSP (Subgroup.map_subtype_le K') hK
        hKstardef hU hMstarMem hMstarP hSnconjMstar hKstarMstar hKstar_hall hcyc hK_eq
    exact ⟨{
      S := S, T := Mstar, W1 := K, W2 := Kstar, W := K ⊔ Kstar
      S_maximal := hS, T_maximal := hMstarMem
      S_ne_T := by
        intro hST
        rw [hST] at hSnconjMstar
        exact hSnconjMstar (OddOrder.BG.Ch4.S14.IsConjugateSubgroup.refl Mstar)
      W_eq := rfl, W_cyclic := hcyc
      -- `W = K × K*`: the factors meet trivially (coprime orders, BG 14.7).
      W1_inf_W2_eq_bot := hbot
      -- Both factors are nontrivial: a `κ`-Hall of a type-`P` maximal is `≠ 1`, at `S` and at `M*`.
      W1_nontrivial := fun h => OddOrder.BG.Ch4.S14.card_kappaHall_ne_one hSP
        (Subgroup.map_subtype_le K') hK (Subgroup.card_eq_one.mpr h)
      W2_nontrivial := fun h => OddOrder.BG.Ch4.S14.card_kappaHall_ne_one hMstarP hKstarMstar
        hKstar_hall (Subgroup.card_eq_one.mpr h)
      -- (8.4.e): the BG 14.7 TI-set `Ẑ = (K ⊔ K*) − (K ∪ K*)` inside the cyclic (hence abelian)
      -- host `K ⊔ K*` pins the normalizer of each of its nonempty pieces.
      normalizer_V := OddOrder.Peterfalvi.S10.normalizer_V_of_isTISubset hcyc hTI
      S_nonI := isTypeNonI_of_isTypeP hG hS hSP
      T_nonI := isTypeNonI_of_isTypeP hG hMstarMem hMstarP
      one_typeII := hP2disj.imp
        (fun h => (OddOrder.BG.Ch4.S16.proposition_type_classification hG hS).2.1.mpr h)
        (fun h => (OddOrder.BG.Ch4.S16.proposition_type_classification hG hMstarMem).2.1.mpr h)
      W1_le_S := Subgroup.map_subtype_le K'
      W2_le_T := hKstarMstar
      S_compl := hScompl
      T_compl := hTcompl
      -- (8.8.b1), last clause: `S ∩ M* = K ⊔ K*` (BG §16 `typeP_pair_W_structure`).
      S_inf_T_eq_W := hWjoin
      -- (8.8.b4): a maximal subgroup is type I, or type `P` and hence conjugate to `S` or `M*`.
      cover := fun M hM => by
        by_cases hMI : IsTypeI M
        · exact Or.inl hMI
        · exact Or.inr (hcover M hM (notTypeI_imp_typeP M hM hMI)) }⟩

end OddOrder.Peterfalvi.S14

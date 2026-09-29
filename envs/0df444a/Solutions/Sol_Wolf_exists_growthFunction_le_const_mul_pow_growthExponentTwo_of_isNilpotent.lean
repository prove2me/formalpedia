-- Prove2me | solution 1 for Wolf.exists_growthFunction_le_const_mul_pow_growthExponentTwo_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-23T10:46:12.537435+00:00
-- url     : https://prove2.me/submissions/0cad5f69-e109-4cfd-92f5-243b48d30d7e

import Definitions.Def_Chou_Growth
import Mathlib
import Definitions.Def_MilnorWolf_Growth
import Theorems.Thm_Wolf_exists_commutator_generating_sets_with_free_finiteIndex_subfamily_lowerCentralSeries

/-!
# Chou §3, p. 399: the growth rate of a finitely generated group

Milnor's observation that `|B(n)|^{1/n}` converges, and Wolf's observation that exponential
growth does not depend on the choice of finite generating set.  Both come from Fekete's lemma
applied to the subadditive sequence `n ↦ log |B(n)|`: Mathlib's `Subadditive.lim` is *defined*
as the infimum of `u n / n` over `n ≥ 1`, so the limit `v` satisfies `v ^ n ≤ |B(n)|` for
**every** `n`, not merely eventually — which is what the `∀ n` in `HasExponentialGrowth` needs.
-/

namespace Chou
namespace Lib

open Chou

variable {G : Type*} [Group G]

/-! ### Elementary properties of word balls -/

/-! ### Finiteness and cardinality of balls -/

/-! ### Fekete's lemma applied to `log |B(n)|` -/

/-! ### The two theorems -/

end Lib
end Chou

/-!
# Finite generation: the two directions across a finite-index subgroup

Mathlib has Schreier's lemma `Subgroup.fg_of_index_ne_zero`, that a finite-index subgroup of a
finitely generated group is finitely generated.  Wolf's Proposition 4.1 needs the converse as
well, that finite generation passes *up* from a finite-index subgroup, and the standard
"generators of the quotient together with the kernel" principle.
-/

namespace Wolf
namespace Lib

open Subgroup

/-- Transport finite generation along an isomorphism. -/
theorem fg_of_mulEquiv {A B : Type*} [Group A] [Group B] [Group.FG A] (e : A ≃* B) :
    Group.FG B :=
  Group.fg_of_surjective (f := (e : A →* B)) e.surjective

end Lib
end Wolf

/-!
# The lower central series: plumbing

The terms `Γ_k` of the lower central series, the canonical surjection `Γ_k → Γ_k/Γ_{k+1}` of the
definition bundle, and the consequence that a finitely generated factor is witnessed by finitely
many elements of `Γ_k` together with `Γ_{k+1}`.

These were part of the nilpotent-groups module, which imports Wolf's Theorem 3.2; they are
separated out because a solution *of* Theorem 3.2 needs them and cannot import it.
-/

namespace Wolf
namespace Lib

open Subgroup

variable {Γ : Type*} [Group Γ]

/-- The commutator subgroup of `Γ_k` lands inside `Γ_{k+1} = ⁅Γ_k, Γ⁆`. -/
theorem commutator_lcs_le (k : ℕ) :
    Subgroup.map (MilnorWolf.lcs Γ k).subtype (_root_.commutator ↥(MilnorWolf.lcs Γ k)) ≤
      MilnorWolf.lcs Γ (k + 1) := by
  have hmt : Subgroup.map (MilnorWolf.lcs Γ k).subtype ⊤ = MilnorWolf.lcs Γ k := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [_root_.commutator, Subgroup.map_commutator, hmt]
  show ⁅MilnorWolf.lcs Γ k, MilnorWolf.lcs Γ k⁆ ≤ ⁅MilnorWolf.lcs Γ k, (⊤ : Subgroup Γ)⁆
  exact Subgroup.commutator_mono le_rfl le_top

/-- The canonical surjection `Γ_k → Γ_k/Γ_{k+1}` of the definition bundle, which factors
through the abelianization of `Γ_k` because `⁅Γ_k, Γ_k⁆ ≤ Γ_{k+1}`. -/
noncomputable def toLcsFactor (k : ℕ) :
    ↥(MilnorWolf.lcs Γ k) →* MilnorWolf.lcsFactor Γ k :=
  (QuotientGroup.mk' _).comp Abelianization.of

theorem toLcsFactor_surjective (k : ℕ) : Function.Surjective (toLcsFactor (Γ := Γ) k) :=
  (QuotientGroup.mk'_surjective _).comp (fun x => Quot.inductionOn x fun y => ⟨y, rfl⟩)

theorem ker_toLcsFactor_le (k : ℕ) :
    (toLcsFactor (Γ := Γ) k).ker ≤
      (MilnorWolf.lcs Γ (k + 1)).subgroupOf (MilnorWolf.lcs Γ k) := by
  intro x hx
  rw [MonoidHom.mem_ker, toLcsFactor, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  obtain ⟨n, hn, hnx⟩ := hx
  have hcomm : n⁻¹ * x ∈ _root_.commutator ↥(MilnorWolf.lcs Γ k) := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel]
  have : ((n⁻¹ * x : ↥(MilnorWolf.lcs Γ k)) : Γ) ∈ MilnorWolf.lcs Γ (k + 1) :=
    commutator_lcs_le k ⟨n⁻¹ * x, hcomm, rfl⟩
  have hx' : x = n * (n⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem _ hn this

end Lib
end Wolf

/-!
# Words modulo a normal subgroup

Wolf's inductions in Theorem 3.2 (p. 425) never say that an element *is* a short word on the
generating set; they say it is one **modulo** the next term of the lower central series.  This
module gives that notion a name and the closure properties the inductions use: the image in
`Γ ⧸ N` of the ball of radius `L`.

Working in the quotient rather than with an explicit discrepancy keeps the bookkeeping short —
products and inverses are then inherited from the ball itself, and the length adds because a
product of a word of length `≤ L` and one of length `≤ L'` is a word of length `≤ L + L'`.
-/

namespace Wolf
namespace Lib

open Chou Chou.Lib
open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

variable {U : Set Γ} {N : Subgroup Γ} [N.Normal]

end Lib
end Wolf

/-!
# Counting along a descending chain, for Wolf's (3.8)

The lower bound of Theorem 3.2 counts the elements `∏_k ∏_i τ_{k,i}^{p_{k,i}}` and needs them to
be distinct.  Wolf gets that from the independence of the `τ_{k,i}` in each factor
`Γ_k/Γ_{k+1}`; the passage from "distinct in each factor" to "distinct in `Γ`" is the elementary
fact isolated here:

*if `D` is a set of elements pairwise distinct modulo `N`, and `C` is a subset of `N`, then
multiplication `D × C → Γ` is injective, so `|D · C| = |D| · |C|.*

Applied along the chain `Γ ⊇ Γ_1 ⊇ ⋯` this multiplies the counts of the individual factors,
which is exactly the product `∏_k (2m^{k+1}+1)^{n_k}` that Wolf's estimate produces.
-/

namespace Wolf
namespace Lib

open Chou Chou.Lib

variable {Γ : Type*} [Group Γ]

/-! ### Independence gives distinct exponent tuples -/

/-- If the cyclic subgroups generated by the `a i` are independent and each `a i` has infinite
order, then distinct exponent tuples give distinct products.  This is what Wolf's "independent
generating set" buys in the counting: the `(2m^{k+1}+1)^{n_k}` tuples give that many distinct
elements of `Γ_k/Γ_{k+1}`. -/
theorem injective_zpow_prod {ι : Type*} [Fintype ι] {A : Type*} [CommGroup A] (a : ι → A)
    (hind : iSupIndep (fun i => Subgroup.zpowers (a i)))
    (hinf : ∀ (i : ι) (n : ℤ), a i ^ n = 1 → n = 0) :
    Function.Injective (fun p : ι → ℤ => ∏ i, a i ^ p i) := by
  intro p q h
  simp only at h
  funext i
  have hdiv : ∏ i, a i ^ (p i - q i) = 1 := by
    simp only [zpow_sub, ← div_eq_mul_inv]
    rw [Finset.prod_div_distrib, h, div_self']
  have hnc : Finset.univ.noncommProd (fun i => a i ^ (p i - q i))
      (fun x _ y _ _ => Commute.all _ _) = 1 := by
    rw [Finset.noncommProd_eq_prod]
    exact hdiv
  have hone := Subgroup.eq_one_of_noncommProd_eq_one_of_iSupIndep Finset.univ
    (fun i => a i ^ (p i - q i)) (fun x _ y _ _ => Commute.all _ _)
    (fun i => Subgroup.zpowers (a i)) hind
    (fun x _ => Subgroup.zpow_mem_zpowers _ _) hnc i (Finset.mem_univ i)
  have := hinf i _ hone
  omega

/-! ### The rank counts only the infinite-order members

Wolf's `n_k` is the number of members of the adapted family of infinite order, while the
definition bundle's `lcsRank` is `finrank ℤ` of the factor.  These agree because the torsion
members contribute nothing: the submodule they span has torsion quotient, hence rank zero, and
rank is additive over that quotient because `ℤ` is a domain and so has rank–nullity.
-/

/-! ### Multiplying the levels together -/

/-! ### One level -/

/-! ### Transferring between the two quotients

Lemma 3.7 states independence in `Γ_k/Γ_{k+1}`, the quotient of the subgroup; the word lengths
of Theorem 3.2 live in `Γ/Γ_{k+1}`, the quotient of the whole group.  The comparison is cheap:
two elements of `K` are congruent modulo `N` in the big quotient exactly when they are in the
small one, because `N.subgroupOf K` is by definition the elements of `K` lying in `N`. -/

/-! ### The arithmetic of Wolf's count

`∏_k (2m^{k+1}+1)^{d_k} ≥ m^{∑ (k+1) n_k}` whenever `n_k ≤ d_k`: this is what turns the product
of the per-level counts into `m^{E₁}`. -/

/-! ### Infinite order, in the two forms the pieces want -/

/-- Not of finite order: no nonzero power is trivial.  This is the form `injective_zpow_prod`
asks for. -/
theorem zpow_eq_one_imp_eq_zero {A : Type*} [Group A] {x : A} (h : ¬ IsOfFinOrder x) (n : ℤ)
    (hn : x ^ n = 1) : n = 0 := by
  by_contra hne
  exact h (isOfFinOrder_iff_zpow_eq_one.2 ⟨n, hne, hn⟩)

/-- Independence and infinite order give `ℤ`-linear independence.  The lower bound needed only
`rank ≤ #J`, which a surjection supplies; the upper bound needs `rank ≥ #J`, and that comes from
here. -/
theorem linearIndependent_of_iSupIndep {A : Type*} [CommGroup A] {ι : Type*} [Fintype ι]
    (a : ι → A) (hind : iSupIndep fun i => Subgroup.zpowers (a i))
    (hinf : ∀ (i : ι) (n : ℤ), a i ^ n = 1 → n = 0) :
    LinearIndependent ℤ fun i => Additive.ofMul (a i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hone : (∏ i, a i ^ g i) = ∏ i, a i ^ (0 : ℤ) := by
    have h1 : Additive.ofMul (∏ i, a i ^ g i) = ∑ i, g i • Additive.ofMul (a i) := rfl
    have h2 : Additive.ofMul ((1 : A)) = (0 : Additive A) := rfl
    simp only [zpow_zero, Finset.prod_const_one]
    have : Additive.ofMul (∏ i, a i ^ g i) = Additive.ofMul ((1 : A)) := by
      rw [h1, hg, h2]
    exact this
  exact fun i => congrFun (injective_zpow_prod a hind hinf hone) i

/-! ### Covering along the chain

The lower bound *packs* the chain: per-level sets that are distinct modulo the next term give a
product at least as large as the product of their sizes.  The upper bound *covers* it: if every
element of `A k` is a member of `C k` times an element of `A (k+1)`, then `A 0` sits inside the
product of the `C k`, whose size is at most the product of theirs.  This is Wolf's (3.9), the
normal form, separated from the estimate (3.10) on the exponents. -/

/-- The product of `n` level-sets, starting at level `k`. -/
def prodSet (C : ℕ → Set Γ) (k : ℕ) : ℕ → Set Γ
  | 0 => {1}
  | n + 1 => (fun p : Γ × Γ => p.1 * p.2) '' (C k ×ˢ prodSet C (k + 1) n)

theorem prodSet_finite (C : ℕ → Set Γ) (hfin : ∀ k, (C k).Finite) :
    ∀ (n k : ℕ), (prodSet C k n).Finite := by
  intro n
  induction n with
  | zero => intro k; simp [prodSet]
  | succ n ih => exact fun k => ((hfin k).prod (ih (k + 1))).image _

theorem ncard_prodSet_le (C : ℕ → Set Γ) (hfin : ∀ k, (C k).Finite) :
    ∀ (n k : ℕ), (prodSet C k n).ncard ≤ ∏ j ∈ Finset.range n, (C (k + j)).ncard := by
  intro n
  induction n with
  | zero => intro k; simp [prodSet]
  | succ n ih =>
      intro k
      have hstep : (prodSet C k (n + 1)).ncard ≤ (C k).ncard * (prodSet C (k + 1) n).ncard := by
        refine le_trans (Set.ncard_image_le ((hfin k).prod (prodSet_finite C hfin n (k + 1)))) ?_
        exact le_of_eq Set.ncard_prod
      refine le_trans hstep ?_
      rw [Finset.prod_range_succ']
      simp only [Nat.add_zero]
      rw [Nat.mul_comm]
      refine Nat.mul_le_mul_right _ ?_
      refine le_trans (ih (k + 1)) (le_of_eq ?_)
      refine Finset.prod_congr rfl fun j _ => ?_
      congr 2
      omega

end Lib
end Wolf

/-!
# The lower-central factor in the shape Lemma 3.7 states it

Lemma 3.7 describes `Γ_k/Γ_{k+1}` as the quotient of the subgroup `Γ_k` by `Γ_{k+1}` sitting
inside it, while the published growth bundle's `lcsFactor` goes through the abelianization of
`Γ_k`.  This module holds the comparison, and the first half of Theorem 3.2 that follows from
it: every lower-central factor of a finitely generated nilpotent group is finitely generated.

Separated from the Theorem 3.2 module because that one imports the two published statements of
the growth bounds, so nothing in it could be used by a proof *of* either bound.
-/

namespace Wolf
namespace Lib

open Chou Chou.Lib

variable {Γ : Type*} [Group Γ]

/-- `Γ_k/Γ_{k+1}` in the shape Lemma 3.7 states it. -/
abbrev lcsQuot (Γ : Type*) [Group Γ] (k : ℕ) : Type _ :=
  ↥(MilnorWolf.lcs Γ k) ⧸ ((MilnorWolf.lcs Γ (k + 1)).subgroupOf (MilnorWolf.lcs Γ k))

/-- `Γ_{k+1}`, viewed inside `Γ_k`, is killed by the projection onto the definition bundle's
factor `lcsFactor Γ k`. -/
theorem subgroupOf_le_ker_toLcsFactor (k : ℕ) :
    (MilnorWolf.lcs Γ (k + 1)).subgroupOf (MilnorWolf.lcs Γ k) ≤
      (toLcsFactor (Γ := Γ) k).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, toLcsFactor, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact ⟨x, hx, rfl⟩

/-- The projection of `Γ_k/Γ_{k+1}` onto the definition bundle's `lcsFactor Γ k`. -/
noncomputable def lcsQuotToFactor (k : ℕ) : lcsQuot Γ k →* MilnorWolf.lcsFactor Γ k :=
  QuotientGroup.lift _ (toLcsFactor (Γ := Γ) k) (subgroupOf_le_ker_toLcsFactor k)

theorem lcsQuotToFactor_surjective (k : ℕ) :
    Function.Surjective (lcsQuotToFactor (Γ := Γ) k) := by
  intro y
  obtain ⟨x, rfl⟩ := toLcsFactor_surjective (Γ := Γ) k y
  exact ⟨QuotientGroup.mk' _ x, rfl⟩

/-- The definition bundle's `lcsFactor Γ k` is a quotient of `Γ_k/Γ_{k+1}`. -/
theorem fg_lcsFactor_of_fg_lcsQuot (k : ℕ) (h : Group.FG (lcsQuot Γ k)) :
    Group.FG (MilnorWolf.lcsFactor Γ k) :=
  Group.fg_of_surjective (f := lcsQuotToFactor (Γ := Γ) k) (lcsQuotToFactor_surjective k)

/-- The hypotheses Lemma 3.7 asks for, for a finitely generated nilpotent group. -/
theorem lcs_nilpotencyClass_eq_bot [Group.IsNilpotent Γ] :
    MilnorWolf.lcs Γ (Group.nilpotencyClass Γ) = ⊥ :=
  Subgroup.lowerCentralSeries_nilpotencyClass

theorem fg_lcsQuot_zero [Group.FG Γ] : Group.FG (lcsQuot Γ 0) := by
  haveI : Group.FG ↥(MilnorWolf.lcs Γ 0) :=
    fg_of_mulEquiv (Subgroup.topEquiv (G := Γ)).symm
  exact Group.fg_of_surjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

/-- **Theorem 3.2, first half**: every lower-central factor of a finitely generated nilpotent
group is finitely generated.  This is Lemma 3.7 (i). -/
theorem forall_fg_lcsFactor [Group.FG Γ] [Group.IsNilpotent Γ] (k : ℕ) :
    Group.FG (MilnorWolf.lcsFactor Γ k) := by
  obtain ⟨r, τ, hi, -, -⟩ :=
    _root_.Wolf.exists_commutator_generating_sets_with_free_finiteIndex_subfamily_lowerCentralSeries
      (Γ := Γ) (Group.nilpotencyClass Γ)
      (by
        have h := lcs_nilpotencyClass_eq_bot (Γ := Γ)
        have hle : MilnorWolf.lcs Γ (Group.nilpotencyClass Γ + 1) ≤
            MilnorWolf.lcs Γ (Group.nilpotencyClass Γ) :=
          (⊤ : Subgroup Γ).lowerCentralSeries_antitone (Nat.le_succ _)
        rw [h] at hle
        exact le_bot_iff.1 hle)
      fg_lcsQuot_zero
  exact fg_lcsFactor_of_fg_lcsQuot k (hi k).1

/-- The projection onto the bundle's factor is injective as well, because the kernel of
`toLcsFactor` is already contained in `Γ_{k+1}`.  So the two presentations of the factor are
isomorphic, and in particular have the same rank -- which the upper bound needs, the surjection
alone giving only one inequality. -/
theorem lcsQuotToFactor_injective (k : ℕ) :
    Function.Injective (lcsQuotToFactor (Γ := Γ) k) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker] at hx
  have hy : y ∈ (toLcsFactor (Γ := Γ) k).ker := MonoidHom.mem_ker.2 hx
  exact (QuotientGroup.eq_one_iff _).2 (ker_toLcsFactor_le k hy)

end Lib
end Wolf

/-!
# Graded words and Wolf's collection process, for the upper bound (3.10)

Wolf's proof of (3.10) (pp. 430–431) rewrites a word on the graded generating family
`T₀ ∪ T₁ ∪ ⋯ ∪ T_s`, pulling the letters of level `t` to the front one class at a time.  Moving
a letter `b` of level `t` to the left past a letter `a` of level `≥ t` replaces `a b` by
`b a ⁅a, b⁆'`, where the correction `a⁻¹ b⁻¹ a b` lies one level higher than `a`, so it is a
word of bounded length on the higher levels.

This module is the group-theory-free part of that argument.  A letter is a triple
`(level, index, inverted?)`, evaluated through an arbitrary family `τ : ℕ → ℕ → G`; everything
the group has to supply is packaged as a correction function `corr` (`UCorrOK`).  The results:

* `uconjAll_spec`: conjugating a word by a word of level-`t` letters, letter by letter, keeping
  track of how many letters of each level appear (`ucnt`), in terms of the letters of lower
  level (`ucntLt`);
* `upull`: pulling every letter of one class to the front, with the bound
  `#_ℓ(rest) ≤ #_ℓ(word) + (#pulled) · N · #_{<ℓ}(rest)`.

`W_upper_stage` continues with the reduction of the pulled powers, the solution of the count
recursion (where the exponents `2^ℓ` appear), and a whole level at a time.  The estimate is
cruder than Wolf's but of the same shape: it uses only that the correction for a letter of
level `j` lives at levels `> j`.
-/

namespace Wolf
namespace Lib

section UpperWords

variable {G : Type*} [Group G]

/-- A letter of a graded word: `(level, index, inverted?)`. -/
abbrev ULetter := ℕ × ℕ × Bool

/-- The value of a letter: `τ k i` or its inverse. -/
def uev (τ : ℕ → ℕ → G) (x : ULetter) : G := if x.2.2 then (τ x.1 x.2.1)⁻¹ else τ x.1 x.2.1

/-- The value of a word. -/
def uval (τ : ℕ → ℕ → G) (w : List ULetter) : G := (w.map (uev τ)).prod

/-- The number of letters of level `ℓ`. -/
def ucnt (ℓ : ℕ) (w : List ULetter) : ℕ := w.countP (fun x => decide (x.1 = ℓ))

/-- The number of letters of level `< ℓ`. -/
def ucntLt (ℓ : ℕ) (w : List ULetter) : ℕ := w.countP (fun x => decide (x.1 < ℓ))

theorem uval_nil (τ : ℕ → ℕ → G) : uval τ [] = 1 := rfl

theorem uval_cons (τ : ℕ → ℕ → G) (x : ULetter) (w : List ULetter) :
    uval τ (x :: w) = uev τ x * uval τ w := by
  simp [uval]

theorem uval_append (τ : ℕ → ℕ → G) (u v : List ULetter) :
    uval τ (u ++ v) = uval τ u * uval τ v := by
  simp [uval]

theorem ucnt_append (ℓ : ℕ) (u v : List ULetter) : ucnt ℓ (u ++ v) = ucnt ℓ u + ucnt ℓ v := by
  simp [ucnt]

theorem ucntLt_append (ℓ : ℕ) (u v : List ULetter) :
    ucntLt ℓ (u ++ v) = ucntLt ℓ u + ucntLt ℓ v := by
  simp [ucntLt]

theorem ucnt_le_length (ℓ : ℕ) (w : List ULetter) : ucnt ℓ w ≤ w.length :=
  List.countP_le_length

theorem ucnt_cons (ℓ : ℕ) (x : ULetter) (w : List ULetter) :
    ucnt ℓ (x :: w) = ucnt ℓ w + if x.1 = ℓ then 1 else 0 := by
  simp [ucnt, List.countP_cons]

theorem ucntLt_cons (ℓ : ℕ) (x : ULetter) (w : List ULetter) :
    ucntLt ℓ (x :: w) = ucntLt ℓ w + if x.1 < ℓ then 1 else 0 := by
  simp [ucntLt, List.countP_cons]

theorem ucnt_eq_zero {ℓ : ℕ} {w : List ULetter} (h : ∀ x ∈ w, x.1 ≠ ℓ) : ucnt ℓ w = 0 := by
  unfold ucnt
  rw [List.countP_eq_zero]
  intro x hx
  simpa using h x hx

/-- The letters of level `< ℓ` are the letters of the levels `j < ℓ`. -/
theorem ucntLt_eq_sum (w : List ULetter) :
    ∀ ℓ, ucntLt ℓ w = ∑ j ∈ Finset.range ℓ, ucnt j w := by
  intro ℓ
  induction ℓ with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      unfold ucntLt
      rw [List.countP_eq_zero]
      intro x _
      simp
  | succ ℓ ih =>
      rw [Finset.sum_range_succ, ← ih]
      clear ih
      induction w with
      | nil => simp [ucntLt, ucnt]
      | cons x w ihw =>
          rw [ucntLt_cons, ucntLt_cons, ucnt_cons, ihw]
          split_ifs <;> omega

theorem ucntLt_le_of_sublist {u v : List ULetter} (h : u.Sublist v) (ℓ : ℕ) :
    ucntLt ℓ u ≤ ucntLt ℓ v :=
  h.countP_le

/-- What the group must supply: for letters `a`, `b` with `b` of level at most that of `a`, a
word `corr a b` of length `≤ N` for the correction `a⁻¹ b⁻¹ a b`, on letters of level strictly
above that of `a`. -/
def UCorrOK (τ : ℕ → ℕ → G) (ok : ℕ → ℕ → Prop) (N : ℕ)
    (corr : ULetter → ULetter → List ULetter) : Prop :=
  ∀ a b : ULetter, ok a.1 a.2.1 → ok b.1 b.2.1 → b.1 ≤ a.1 →
    uval τ (corr a b) = (uev τ a)⁻¹ * (uev τ b)⁻¹ * uev τ a * uev τ b ∧
    (corr a b).length ≤ N ∧ ∀ x ∈ corr a b, ok x.1 x.2.1 ∧ a.1 < x.1

/-- Conjugation of a word by one letter, letter by letter: `b⁻¹ a b = a · (a⁻¹ b⁻¹ a b)`. -/
def uconj1 (corr : ULetter → ULetter → List ULetter) (u : List ULetter) (b : ULetter) :
    List ULetter :=
  u.flatMap fun a => a :: corr a b

/-- Conjugation of a word by a word, one letter at a time. -/
def uconjAll (corr : ULetter → ULetter → List ULetter) (u bs : List ULetter) : List ULetter :=
  bs.foldl (uconj1 corr) u

theorem sublist_uconj1 (corr : ULetter → ULetter → List ULetter) (u : List ULetter)
    (b : ULetter) : u.Sublist (uconj1 corr u b) := by
  induction u with
  | nil => simp [uconj1]
  | cons a u ih =>
      simp only [uconj1, List.flatMap_cons, List.cons_append]
      exact (ih.trans (List.sublist_append_right _ _)).cons_cons a

theorem uconj1_spec {τ : ℕ → ℕ → G} {ok : ℕ → ℕ → Prop} {N : ℕ}
    {corr : ULetter → ULetter → List ULetter} (hc : UCorrOK τ ok N corr) (t : ℕ) (b : ULetter)
    (hb : ok b.1 b.2.1 ∧ b.1 ≤ t) (u : List ULetter) (hu : ∀ a ∈ u, ok a.1 a.2.1 ∧ t ≤ a.1) :
    uval τ (uconj1 corr u b) = (uev τ b)⁻¹ * uval τ u * uev τ b ∧
    (∀ x ∈ uconj1 corr u b, x ∈ u ∨ (ok x.1 x.2.1 ∧ t < x.1)) ∧
    ∀ ℓ, ucnt ℓ (uconj1 corr u b) ≤ ucnt ℓ u + N * ucntLt ℓ u := by
  induction u with
  | nil => simp [uconj1, uval]
  | cons a u ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih (fun x hx => hu x (List.mem_cons_of_mem a hx))
      have ha := hu a List.mem_cons_self
      obtain ⟨hce, hcN, hcL⟩ := hc a b ha.1 hb.1 (le_trans hb.2 ha.2)
      have hsplit : uconj1 corr (a :: u) b = a :: (corr a b ++ uconj1 corr u b) := by
        simp [uconj1]
      refine ⟨?_, ?_, ?_⟩
      · rw [hsplit, uval_cons, uval_append, ih1, hce, uval_cons]
        group
      · intro x hx
        rw [hsplit] at hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inl List.mem_cons_self
        rcases List.mem_append.1 hx with hx | hx
        · have := hcL x hx
          exact Or.inr ⟨this.1, lt_of_le_of_lt ha.2 this.2⟩
        · rcases ih2 x hx with h | h
          · exact Or.inl (List.mem_cons_of_mem a h)
          · exact Or.inr h
      · intro ℓ
        have hcorr : ucnt ℓ (corr a b) ≤ N * (if a.1 < ℓ then 1 else 0) := by
          split_ifs with h
          · simpa using le_trans (ucnt_le_length ℓ _) hcN
          · rw [ucnt_eq_zero]
            · simp
            intro x hx
            have := (hcL x hx).2
            omega
        rw [hsplit, ucnt_cons, ucnt_append, ucnt_cons, ucntLt_cons]
        have := ih3 ℓ
        rw [Nat.mul_add]
        omega

theorem uconjAll_spec {τ : ℕ → ℕ → G} {ok : ℕ → ℕ → Prop} {N : ℕ}
    {corr : ULetter → ULetter → List ULetter} (hc : UCorrOK τ ok N corr) (t : ℕ)
    (bs : List ULetter) (hbs : ∀ b ∈ bs, ok b.1 b.2.1 ∧ b.1 ≤ t) :
    ∀ u : List ULetter, (∀ a ∈ u, ok a.1 a.2.1 ∧ t ≤ a.1) →
    uval τ (uconjAll corr u bs) = (uval τ bs)⁻¹ * uval τ u * uval τ bs ∧
    u.Sublist (uconjAll corr u bs) ∧
    (∀ x ∈ uconjAll corr u bs, x ∈ u ∨ (ok x.1 x.2.1 ∧ t < x.1)) ∧
    ∀ ℓ, ucnt ℓ (uconjAll corr u bs) ≤
      ucnt ℓ u + bs.length * N * ucntLt ℓ (uconjAll corr u bs) := by
  induction bs with
  | nil =>
      intro u _
      refine ⟨by simp [uconjAll, uval], by simp [uconjAll], fun x hx => Or.inl (by simpa [uconjAll] using hx), by simp [uconjAll]⟩
  | cons b bs ih =>
      intro u hu
      have hb := hbs b List.mem_cons_self
      obtain ⟨h1, h2, h3⟩ := uconj1_spec hc t b hb u hu
      have hu1 : ∀ a ∈ uconj1 corr u b, ok a.1 a.2.1 ∧ t ≤ a.1 := by
        intro a ha
        rcases h2 a ha with h | h
        · exact hu a h
        · exact ⟨h.1, h.2.le⟩
      obtain ⟨i1, i2, i3, i4⟩ :=
        ih (fun x hx => hbs x (List.mem_cons_of_mem b hx)) (uconj1 corr u b) hu1
      have hfold : uconjAll corr u (b :: bs) = uconjAll corr (uconj1 corr u b) bs := rfl
      rw [hfold]
      refine ⟨?_, (sublist_uconj1 corr u b).trans i2, ?_, ?_⟩
      · rw [i1, h1, uval_cons]
        group
      · intro x hx
        rcases i3 x hx with h | h
        · rcases h2 x h with h' | h'
          · exact Or.inl h'
          · exact Or.inr h'
        · exact Or.inr h
      · intro ℓ
        have hsub := (sublist_uconj1 corr u b).trans i2
        have hlt := ucntLt_le_of_sublist hsub ℓ
        have e1 := i4 ℓ
        have e2 := h3 ℓ
        have e3 : N * ucntLt ℓ u ≤ N * ucntLt ℓ (uconjAll corr (uconj1 corr u b) bs) :=
          Nat.mul_le_mul_left N hlt
        simp only [List.length_cons]
        rw [Nat.add_mul, Nat.add_mul, one_mul]
        omega

/-- A word all of whose letters are `τ t i` or its inverse is a power of `τ t i`, with exponent
at most its length. -/
theorem exists_zpow_of_class (τ : ℕ → ℕ → G) (t i : ℕ) :
    ∀ bs : List ULetter, (∀ x ∈ bs, x.1 = t ∧ x.2.1 = i) →
      ∃ e : ℤ, |e| ≤ bs.length ∧ uval τ bs = τ t i ^ e := by
  intro bs
  induction bs with
  | nil => intro _; exact ⟨0, by simp, by simp [uval]⟩
  | cons x bs ih =>
      intro h
      obtain ⟨e, he, hv⟩ := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      obtain ⟨hx1, hx2⟩ := h x List.mem_cons_self
      obtain ⟨k, j, c⟩ := x
      simp only at hx1 hx2
      subst hx1 hx2
      rw [uval_cons, hv]
      cases c
      · refine ⟨1 + e, ?_, ?_⟩
        · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          have := abs_add_le (1 : ℤ) e
          simp at this
          linarith
        · simp [uev, zpow_add]
      · refine ⟨-1 + e, ?_, ?_⟩
        · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          have := abs_add_le (-1 : ℤ) e
          simp at this
          linarith
        · simp [uev, zpow_add]

/-- The formal inverse of a word. -/
def uinv (w : List ULetter) : List ULetter :=
  (w.map fun x => (x.1, x.2.1, !x.2.2)).reverse

theorem uval_uinv (τ : ℕ → ℕ → G) (w : List ULetter) : uval τ (uinv w) = (uval τ w)⁻¹ := by
  unfold uval uinv
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  congr 2
  refine List.map_congr_left (fun x _ => ?_)
  obtain ⟨k, j, c⟩ := x
  cases c <;> simp [uev]

theorem mem_uinv {w : List ULetter} {x : ULetter} (hx : x ∈ uinv w) :
    ∃ y ∈ w, x.1 = y.1 ∧ x.2.1 = y.2.1 := by
  unfold uinv at hx
  rw [List.mem_reverse, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, rfl, rfl⟩

theorem length_uinv (w : List ULetter) : (uinv w).length = w.length := by
  simp [uinv]

/-- `k` copies of a word. -/
def urep (u : List ULetter) (k : ℕ) : List ULetter := (List.replicate k u).flatten

theorem uval_urep (τ : ℕ → ℕ → G) (u : List ULetter) (k : ℕ) :
    uval τ (urep u k) = uval τ u ^ k := by
  induction k with
  | zero => simp [urep, uval]
  | succ k ih =>
      rw [urep, List.replicate_succ, List.flatten_cons, uval_append, ← urep, ih, pow_succ']

theorem length_urep (u : List ULetter) (k : ℕ) : (urep u k).length = k * u.length := by
  simp [urep, List.length_flatten, List.sum_replicate]

theorem mem_urep {u : List ULetter} {k : ℕ} {x : ULetter} (hx : x ∈ urep u k) : x ∈ u := by
  unfold urep at hx
  rw [List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  rw [(List.eq_of_mem_replicate hl)] at hxl
  exact hxl

/-- **Pulling one class to the front.**  Every letter `τ_{t,i}^{±1}` of a word on levels `≥ t`
is moved to the left.  The rest of the word is conjugated by the letters moved past it; the
count of level-`ℓ` letters grows by at most `(#pulled) · N` per letter of lower level. -/
theorem upull {τ : ℕ → ℕ → G} {ok : ℕ → ℕ → Prop} {N : ℕ}
    {corr : ULetter → ULetter → List ULetter} (hc : UCorrOK τ ok N corr) (t i : ℕ) :
    ∀ w : List ULetter, (∀ x ∈ w, ok x.1 x.2.1 ∧ t ≤ x.1) →
    ∃ bs w' : List ULetter, (∀ x ∈ bs, x.1 = t ∧ x.2.1 = i ∧ ok x.1 x.2.1) ∧
      bs.length ≤ ucnt t w ∧ uval τ w = uval τ bs * uval τ w' ∧
      (∀ x ∈ w', ok x.1 x.2.1 ∧ t ≤ x.1 ∧ ¬ (x.1 = t ∧ x.2.1 = i) ∧ (x.1 = t → x ∈ w)) ∧
      ∀ ℓ, ucnt ℓ w' ≤ ucnt ℓ w + bs.length * N * ucntLt ℓ w' := by
  intro w
  induction w with
  | nil =>
      intro _
      exact ⟨[], [], by simp, by simp, by simp [uval], by simp, by simp [ucnt]⟩
  | cons x w ih =>
      intro hw
      have hx := hw x List.mem_cons_self
      obtain ⟨bs, w', hbs, hlen, hval, hw', hcnt⟩ :=
        ih (fun y hy => hw y (List.mem_cons_of_mem x hy))
      by_cases hB : x.1 = t ∧ x.2.1 = i
      · refine ⟨x :: bs, w', ?_, ?_, ?_, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact ⟨hB.1, hB.2, hx.1⟩
          · exact hbs y hy
        · rw [ucnt_cons, if_pos hB.1, List.length_cons]
          omega
        · rw [uval_cons, uval_cons, hval, mul_assoc]
        · intro y hy
          obtain ⟨a1, a2, a3, a4⟩ := hw' y hy
          exact ⟨a1, a2, a3, fun h => List.mem_cons_of_mem x (a4 h)⟩
        · intro ℓ
          have := hcnt ℓ
          rw [ucnt_cons, List.length_cons, Nat.add_mul, Nat.add_mul]
          omega
      · have hbsok : ∀ b ∈ bs, ok b.1 b.2.1 ∧ b.1 ≤ t := by
          intro b hb
          obtain ⟨h1, -, h3⟩ := hbs b hb
          exact ⟨h3, h1.le⟩
        obtain ⟨c1, -, c3, c4⟩ := uconjAll_spec hc t bs hbsok [x] (by simpa using hx)
        refine ⟨bs, uconjAll corr [x] bs ++ w', hbs, ?_, ?_, ?_, ?_⟩
        · rw [ucnt_cons]
          omega
        · rw [uval_cons, hval, uval_append, c1, uval_cons, uval_nil]
          group
        · intro y hy
          rcases List.mem_append.1 hy with hy | hy
          · rcases c3 y hy with h | h
            · rw [List.mem_singleton] at h
              subst h
              exact ⟨hx.1, hx.2, hB, fun _ => List.mem_cons_self⟩
            · exact ⟨h.1, h.2.le, fun h' => by omega, fun h' => by omega⟩
          · obtain ⟨a1, a2, a3, a4⟩ := hw' y hy
            exact ⟨a1, a2, a3, fun h => List.mem_cons_of_mem x (a4 h)⟩
        · intro ℓ
          have e1 := c4 ℓ
          have e2 := hcnt ℓ
          rw [ucnt_append, ucntLt_append, ucnt_cons, Nat.mul_add]
          have e3 : ucnt ℓ [x] = if x.1 = ℓ then 1 else 0 := by
            rw [ucnt_cons]; simp [ucnt]
          omega

end UpperWords

end Lib
end Wolf

/-!
# One level of Wolf's collection, with the constants (for the upper bound (3.10))

Continues `W_upper_words`.  A class of level-`t` letters is pulled to the front and its power
reduced modulo a relation `τ_{t,i}^d = (word)` (`upull_red`); the per-level counts of what is
left are then bounded by solving the triangular recursion they satisfy (`ufix`).  That solution
is where Wolf's exponents `2^ℓ` come from: pulling `n ≤ K m^{2^t}` letters past a word whose
level-`j` count is `O(m^{2^j})` creates `O(m^{2^t} m^{2^j}) ⊆ O(m^{2^ℓ})` letters at each level
`ℓ > j, t`.

Doing this for every class of level `t` (`uphase`, `ustage`) collects the level-`t` part of the
word into an ordered product `∏_i τ_{t,i}^{e_i}` drawn from a set `ulevelSet` whose size is at
most `∏_i (2L+1 or d_i)`, and pushes the rest of the word to levels `≥ t + 1`.
-/

namespace Wolf
namespace Lib

section UpperStage

variable {G : Type*} [Group G]

/-- **Pulling one class to the front, then reducing it.**  After `upull`, the pulled power
`τ_{t,i}^e` is reduced modulo `d` using a relation `τ_{t,i}^d = (red)`: the quotient part
`(τ_{t,i}^d)^q` is written out as `|q|` copies of `red` (or its inverse) and put back in front
of the remaining word.  With `d = 0` (and `red = []`) nothing is reduced. -/
theorem upull_red {τ : ℕ → ℕ → G} {ok : ℕ → ℕ → Prop} {N : ℕ}
    {corr : ULetter → ULetter → List ULetter} (hc : UCorrOK τ ok N corr) (t i d : ℕ)
    (Z : ℕ → Prop) (red : List ULetter) (hred : uval τ red = τ t i ^ d)
    (hredN : red.length ≤ N)
    (hredL : ∀ x ∈ red, ok x.1 x.2.1 ∧ t ≤ x.1 ∧ ¬ (x.1 = t ∧ x.2.1 = i) ∧ (x.1 = t → Z x.2.1))
    (w : List ULetter) (hw : ∀ x ∈ w, ok x.1 x.2.1 ∧ t ≤ x.1) :
    ∃ (e : ℤ) (n : ℕ) (w' : List ULetter), n ≤ ucnt t w ∧ (d = 0 → |e| ≤ n) ∧
      (d ≠ 0 → 0 ≤ e ∧ e < d) ∧ uval τ w = τ t i ^ e * uval τ w' ∧
      (∀ x ∈ w', ok x.1 x.2.1 ∧ t ≤ x.1 ∧ ¬ (x.1 = t ∧ x.2.1 = i) ∧
        (x.1 = t → x ∈ w ∨ Z x.2.1)) ∧
      ∀ ℓ, ucnt ℓ w' ≤ ucnt ℓ w + n * N + n * N * ucntLt ℓ w' := by
  obtain ⟨bs, w1, hbs, hlen, hval, hw1, hcnt⟩ := upull hc t i w hw
  obtain ⟨e0, he0, hv0⟩ :=
    exists_zpow_of_class τ t i bs (fun x hx => ⟨(hbs x hx).1, (hbs x hx).2.1⟩)
  by_cases hd : d = 0
  · refine ⟨e0, bs.length, w1, hlen, fun _ => he0, fun h => absurd hd h, ?_, ?_, ?_⟩
    · rw [hval, hv0]
    · intro x hx
      obtain ⟨a1, a2, a3, a4⟩ := hw1 x hx
      exact ⟨a1, a2, a3, fun h => Or.inl (a4 h)⟩
    · intro ℓ
      have := hcnt ℓ
      omega
  · set n := bs.length with hn
    set q : ℤ := e0 / (d : ℤ) with hq
    set r : List ULetter := if 0 ≤ q then red else uinv red with hr
    set v : List ULetter := urep r q.natAbs with hv
    have hvval : uval τ v = τ t i ^ ((d : ℤ) * q) := by
      rw [hv, uval_urep, hr]
      split_ifs with hq0
      · rw [hred, ← zpow_natCast, ← zpow_natCast, ← zpow_mul]
        congr 1
        have : ((q.natAbs : ℕ) : ℤ) = q := by omega
        rw [this]
      · rw [uval_uinv, hred, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_mul]
        congr 1
        have : ((q.natAbs : ℕ) : ℤ) = -q := by omega
        rw [this]
        ring
    have hrlen : r.length ≤ N := by
      rw [hr]
      split_ifs
      · exact hredN
      · rw [length_uinv]; exact hredN
    have hqn : q.natAbs ≤ n := by
      have h1 := Int.natAbs_ediv_le_natAbs e0 (d : ℤ)
      have h2 : e0.natAbs ≤ n := by
        rw [abs_le] at he0
        omega
      rw [hq]
      omega
    have hvlen : v.length ≤ n * N := by
      rw [hv, length_urep]
      exact Nat.mul_le_mul hqn hrlen
    have hvL : ∀ x ∈ v, ok x.1 x.2.1 ∧ t ≤ x.1 ∧ ¬ (x.1 = t ∧ x.2.1 = i) ∧
        (x.1 = t → Z x.2.1) := by
      intro x hx
      have hx' := mem_urep hx
      rw [hr] at hx'
      split_ifs at hx'
      · exact hredL x hx'
      · obtain ⟨y, hy, h1, h2⟩ := mem_uinv hx'
        rw [h1, h2]
        exact hredL y hy
    refine ⟨e0 % (d : ℤ), n, v ++ w1, hlen, fun h => absurd h hd, fun _ => ?_, ?_, ?_, ?_⟩
    · have hd' : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
      exact ⟨Int.emod_nonneg _ hd'.ne', Int.emod_lt_of_pos _ hd'⟩
    · rw [uval_append, hvval, ← mul_assoc, ← zpow_add, hq, Int.emod_add_mul_ediv, hval, hv0]
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨a1, a2, a3, a4⟩ := hvL x hx
        exact ⟨a1, a2, a3, fun h => Or.inr (a4 h)⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hw1 x hx
        exact ⟨a1, a2, a3, fun h => Or.inl (a4 h)⟩
    · intro ℓ
      have e1 := hcnt ℓ
      have e2 := ucnt_le_length ℓ v
      rw [ucnt_append, ucntLt_append]
      have e3 : n * N * ucntLt ℓ w1 ≤ n * N * (ucntLt ℓ v + ucntLt ℓ w1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega

/-! ### Solving the triangular recursion -/

theorem upow_two_mul_le {m : ℕ} (hm : 1 ≤ m) {t j ℓ : ℕ} (ht : t < ℓ) (hj : j < ℓ) :
    m ^ 2 ^ t * m ^ 2 ^ j ≤ m ^ 2 ^ ℓ := by
  rw [← pow_add]
  apply Nat.pow_le_pow_right hm
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have h1 : 2 ^ t ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

theorem upow_two_mono {m : ℕ} (hm : 1 ≤ m) {a b : ℕ} (h : a ≤ b) : m ^ 2 ^ a ≤ m ^ 2 ^ b :=
  Nat.pow_le_pow_right hm (Nat.pow_le_pow_right (by norm_num) h)

theorem ugeom (a : ℕ) : ∀ ℓ, (∑ j ∈ Finset.range ℓ, a * (1 + a) ^ j) + 1 = (1 + a) ^ ℓ := by
  intro ℓ
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [ih]

/-- **The doubling.**  A sequence with `c_ℓ = 0` below `t` and
`c_ℓ ≤ K m^{2^ℓ} + n N ∑_{j<ℓ} c_j`, where `n ≤ K m^{2^t}`, satisfies
`c_ℓ ≤ K (1+KN)^ℓ m^{2^ℓ}`: the product `m^{2^t} · m^{2^j}` of the number of pulled letters and
a lower level's count never exceeds `m^{2^ℓ}`. -/
theorem ufix {m t K N n : ℕ} (hm : 1 ≤ m) (c : ℕ → ℕ) (hn : n ≤ K * m ^ 2 ^ t)
    (hc0 : ∀ ℓ < t, c ℓ = 0)
    (hc : ∀ ℓ, c ℓ ≤ K * m ^ 2 ^ ℓ + n * N * ∑ j ∈ Finset.range ℓ, c j) :
    ∀ ℓ, c ℓ ≤ K * (1 + K * N) ^ ℓ * m ^ 2 ^ ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    by_cases hℓ : ℓ ≤ t
    · have hs : ∑ j ∈ Finset.range ℓ, c j = 0 :=
        Finset.sum_eq_zero (fun j hj => hc0 j (by simp at hj; omega))
      have h1 := hc ℓ
      rw [hs, mul_zero, add_zero] at h1
      have h2 : 1 ≤ (1 + K * N) ^ ℓ := Nat.one_le_pow _ _ (by omega)
      calc c ℓ ≤ K * m ^ 2 ^ ℓ := h1
        _ = K * 1 * m ^ 2 ^ ℓ := by ring
        _ ≤ K * (1 + K * N) ^ ℓ * m ^ 2 ^ ℓ := by gcongr
    · push Not at hℓ
      have hsum : n * N * ∑ j ∈ Finset.range ℓ, c j ≤
          ∑ j ∈ Finset.range ℓ, K * (K * N * (1 + K * N) ^ j) * m ^ 2 ^ ℓ := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j hj
        have hjℓ : j < ℓ := Finset.mem_range.1 hj
        have h1 := ih j hjℓ
        have h2 := upow_two_mul_le hm hℓ hjℓ
        calc n * N * c j ≤ (K * m ^ 2 ^ t) * N * (K * (1 + K * N) ^ j * m ^ 2 ^ j) := by
              gcongr
          _ = K * (K * N * (1 + K * N) ^ j) * (m ^ 2 ^ t * m ^ 2 ^ j) := by ring
          _ ≤ K * (K * N * (1 + K * N) ^ j) * m ^ 2 ^ ℓ := by gcongr
      have hg := ugeom (K * N) ℓ
      have hre : ∑ j ∈ Finset.range ℓ, K * (K * N * (1 + K * N) ^ j) * m ^ 2 ^ ℓ =
          K * m ^ 2 ^ ℓ * ∑ j ∈ Finset.range ℓ, K * N * (1 + K * N) ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      calc c ℓ ≤ K * m ^ 2 ^ ℓ + n * N * ∑ j ∈ Finset.range ℓ, c j := hc ℓ
        _ ≤ K * m ^ 2 ^ ℓ +
            ∑ j ∈ Finset.range ℓ, K * (K * N * (1 + K * N) ^ j) * m ^ 2 ^ ℓ := by omega
        _ = K * m ^ 2 ^ ℓ * ((∑ j ∈ Finset.range ℓ, K * N * (1 + K * N) ^ j) + 1) := by
            rw [hre]; ring
        _ = K * (1 + K * N) ^ ℓ * m ^ 2 ^ ℓ := by rw [hg]; ring

/-! ### One class, one level, with the constants -/

/-- One pulled-and-reduced class, with the per-level counts kept at `O(m^{2^ℓ})`.  The letters
of level `t` left behind are those of the word other than the pulled class, or those the
reduction introduced (`Z`). -/
theorem ustep {τ : ℕ → ℕ → G} {ok : ℕ → ℕ → Prop} {N : ℕ}
    {corr : ULetter → ULetter → List ULetter} (hc : UCorrOK τ ok N corr) {s : ℕ}
    (hok : ∀ k i, ok k i → k ≤ s) (t i d : ℕ) (Z P : ℕ → Prop) (red : List ULetter)
    (hred : uval τ red = τ t i ^ d) (hredN : red.length ≤ N)
    (hredL : ∀ x ∈ red, ok x.1 x.2.1 ∧ t ≤ x.1 ∧ ¬ (x.1 = t ∧ x.2.1 = i) ∧ (x.1 = t → Z x.2.1))
    (K : ℕ) :
    ∃ K', K ≤ K' ∧ ∀ m, 1 ≤ m → ∀ w : List ULetter,
      (∀ x ∈ w, ok x.1 x.2.1 ∧ t ≤ x.1 ∧ (x.1 = t → P x.2.1)) →
      (∀ ℓ, ucnt ℓ w ≤ K * m ^ 2 ^ ℓ) →
      ∃ (e : ℤ) (w' : List ULetter), (d = 0 → |e| ≤ K' * m ^ 2 ^ t) ∧
        (d ≠ 0 → 0 ≤ e ∧ e < d) ∧ uval τ w = τ t i ^ e * uval τ w' ∧
        (∀ x ∈ w', ok x.1 x.2.1 ∧ t ≤ x.1 ∧ (x.1 = t → (P x.2.1 ∧ x.2.1 ≠ i) ∨ Z x.2.1)) ∧
        ∀ ℓ, ucnt ℓ w' ≤ K' * m ^ 2 ^ ℓ := by
  set K1 := K * (1 + N) with hK1
  have hKK1 : K ≤ K1 := by rw [hK1]; nlinarith
  have hpow : 1 ≤ (1 + K1 * N) ^ s := Nat.one_le_pow _ _ (by omega)
  have hK1K' : K1 ≤ K1 * (1 + K1 * N) ^ s := by nlinarith
  refine ⟨K1 * (1 + K1 * N) ^ s, le_trans hKK1 hK1K', ?_⟩
  intro m hm w hw hcw
  obtain ⟨e, n, w', hn, he0, he1, hval, hw', hcnt⟩ :=
    upull_red hc t i d Z red hred hredN hredL w (fun x hx => ⟨(hw x hx).1, (hw x hx).2.1⟩)
  have hnK : n ≤ K * m ^ 2 ^ t := le_trans hn (hcw t)
  have hnK1 : n ≤ K1 * m ^ 2 ^ t := le_trans hnK (Nat.mul_le_mul_right _ hKK1)
  have hlow : ∀ ℓ < t, ucnt ℓ w' = 0 := by
    intro ℓ hℓ
    apply ucnt_eq_zero
    intro x hx
    have := (hw' x hx).2.1
    omega
  have hfix := ufix (N := N) hm (fun ℓ => ucnt ℓ w') hnK1 hlow (by
    intro ℓ
    by_cases hℓ : ℓ < t
    · simp only [hlow ℓ hℓ]
      exact Nat.zero_le _
    · push Not at hℓ
      have h1 := hcnt ℓ
      have h2 := hcw ℓ
      have h3 : n * N ≤ K * N * m ^ 2 ^ ℓ := by
        calc n * N ≤ K * m ^ 2 ^ t * N := Nat.mul_le_mul_right _ hnK
          _ = K * N * m ^ 2 ^ t := by ring
          _ ≤ K * N * m ^ 2 ^ ℓ := Nat.mul_le_mul_left _ (upow_two_mono hm hℓ)
      have h4 : K1 * m ^ 2 ^ ℓ = K * m ^ 2 ^ ℓ + K * N * m ^ 2 ^ ℓ := by rw [hK1]; ring
      rw [← ucntLt_eq_sum]
      omega)
  refine ⟨e, w', fun h => ?_, he1, hval, ?_, ?_⟩
  · have h1 := he0 h
    have h4 : K1 * m ^ 2 ^ t ≤ K1 * (1 + K1 * N) ^ s * m ^ 2 ^ t :=
      Nat.mul_le_mul_right _ hK1K'
    have h2 : (n : ℤ) ≤ ((K1 * (1 + K1 * N) ^ s * m ^ 2 ^ t : ℕ) : ℤ) := by
      exact_mod_cast le_trans hnK1 h4
    push_cast at h2 ⊢
    linarith
  · intro x hx
    obtain ⟨a1, a2, a3, a4⟩ := hw' x hx
    refine ⟨a1, a2, fun h => ?_⟩
    rcases a4 h with h' | h'
    · exact Or.inl ⟨(hw x h').2.2 h, fun hi => a3 ⟨h, hi⟩⟩
    · exact Or.inr h'
  · intro ℓ
    by_cases hℓ : ℓ ≤ s
    · refine le_trans (hfix ℓ) ?_
      have : (1 + K1 * N) ^ ℓ ≤ (1 + K1 * N) ^ s := Nat.pow_le_pow_right (by omega) hℓ
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
    · rw [ucnt_eq_zero]
      · exact Nat.zero_le _
      intro x hx
      have := hok _ _ (hw' x hx).1
      omega

/-! ### The level sets -/

/-- The admissible exponents of class `i`: at most `L` in absolute value when `d i = 0`, a
residue modulo `d i` otherwise. -/
def uexps (d : ℕ → ℕ) (L : ℕ) (i : ℕ) : Set ℤ :=
  {e | (d i = 0 → |e| ≤ L) ∧ (d i ≠ 0 → 0 ≤ e ∧ e < d i)}

/-- The ordered products `∏_{i ∈ cs} τ_{t,i}^{e_i}` with admissible exponents. -/
def ulevelSet (τ : ℕ → ℕ → G) (t : ℕ) (d : ℕ → ℕ) (L : ℕ) : List ℕ → Set G
  | [] => {1}
  | i :: cs => (fun p : G × G => p.1 * p.2) ''
      (((fun e : ℤ => τ t i ^ e) '' uexps d L i) ×ˢ ulevelSet τ t d L cs)

theorem mem_ulevelSet_cons {τ : ℕ → ℕ → G} {t : ℕ} {d : ℕ → ℕ} {L i : ℕ} {cs : List ℕ} {e : ℤ}
    {g : G} (he : e ∈ uexps d L i) (hg : g ∈ ulevelSet τ t d L cs) :
    τ t i ^ e * g ∈ ulevelSet τ t d L (i :: cs) :=
  ⟨(τ t i ^ e, g), ⟨⟨e, he, rfl⟩, hg⟩, rfl⟩

theorem uexps_mono {d : ℕ → ℕ} {L L' : ℕ} (h : L ≤ L') (i : ℕ) :
    uexps d L i ⊆ uexps d L' i := by
  intro e he
  exact ⟨fun hd => le_trans (he.1 hd) (by exact_mod_cast h), he.2⟩

theorem ulevelSet_mono (τ : ℕ → ℕ → G) (t : ℕ) (d : ℕ → ℕ) {L L' : ℕ} (h : L ≤ L') :
    ∀ cs, ulevelSet τ t d L cs ⊆ ulevelSet τ t d L' cs := by
  intro cs
  induction cs with
  | nil => exact le_rfl
  | cons i cs ih =>
      rintro _ ⟨⟨_, g⟩, ⟨⟨e, he, rfl⟩, hg⟩, rfl⟩
      exact mem_ulevelSet_cons (uexps_mono h i he) (ih hg)

theorem mul_mem_ulevelSet_append (τ : ℕ → ℕ → G) (t : ℕ) (d : ℕ → ℕ) (L : ℕ) :
    ∀ (cs cs' : List ℕ) (g g' : G), g ∈ ulevelSet τ t d L cs → g' ∈ ulevelSet τ t d L cs' →
      g * g' ∈ ulevelSet τ t d L (cs ++ cs') := by
  intro cs
  induction cs with
  | nil =>
      intro cs' g g' hg hg'
      simp only [ulevelSet, Set.mem_singleton_iff] at hg
      subst hg
      simpa using hg'
  | cons i cs ih =>
      rintro cs' _ g' ⟨⟨_, g⟩, ⟨⟨e, he, rfl⟩, hg⟩, rfl⟩ hg'
      simp only [List.cons_append]
      rw [mul_assoc]
      exact mem_ulevelSet_cons he (ih cs' g g' hg hg')

theorem uexps_finite (d : ℕ → ℕ) (L i : ℕ) : (uexps d L i).Finite := by
  refine (Set.finite_Icc (-(L : ℤ)) (max L (d i))).subset ?_
  intro e he
  by_cases hd : d i = 0
  · have := he.1 hd
    rw [abs_le] at this
    constructor <;> omega
  · have := he.2 hd
    constructor <;> omega

theorem uexps_ncard_le (d : ℕ → ℕ) (L i : ℕ) :
    (uexps d L i).ncard ≤ if d i = 0 then 2 * L + 1 else d i := by
  split_ifs with hd
  · have hsub : uexps d L i ⊆ ((Finset.Icc (-(L : ℤ)) L : Finset ℤ) : Set ℤ) := by
      intro e he
      have := he.1 hd
      rw [abs_le] at this
      simp only [Finset.coe_Icc, Set.mem_Icc]
      exact this
    refine le_trans (Set.ncard_le_ncard hsub (Finset.finite_toSet _)) ?_
    rw [Set.ncard_coe_finset, Int.card_Icc]
    omega
  · have hsub : uexps d L i ⊆ ((Finset.Ico (0 : ℤ) (d i)) : Set ℤ) := by
      intro e he
      have := he.2 hd
      simp only [Finset.coe_Ico, Set.mem_Ico]
      exact this
    refine le_trans (Set.ncard_le_ncard hsub (Finset.finite_toSet _)) ?_
    rw [Set.ncard_coe_finset, Int.card_Ico]
    omega

theorem ulevelSet_finite_ncard (τ : ℕ → ℕ → G) (t : ℕ) (d : ℕ → ℕ) (L : ℕ) :
    ∀ cs, (ulevelSet τ t d L cs).Finite ∧
      (ulevelSet τ t d L cs).ncard ≤
        (cs.map fun i => if d i = 0 then 2 * L + 1 else d i).prod := by
  intro cs
  induction cs with
  | nil => simp [ulevelSet]
  | cons i cs ih =>
      have hA : ((fun e : ℤ => τ t i ^ e) '' uexps d L i).Finite :=
        (uexps_finite d L i).image _
      have hAc : ((fun e : ℤ => τ t i ^ e) '' uexps d L i).ncard ≤
          if d i = 0 then 2 * L + 1 else d i :=
        le_trans (Set.ncard_image_le (uexps_finite d L i)) (uexps_ncard_le d L i)
      refine ⟨(hA.prod ih.1).image _, ?_⟩
      refine le_trans (Set.ncard_image_le (hA.prod ih.1)) ?_
      rw [Set.ncard_prod, List.map_cons, List.prod_cons]
      exact Nat.mul_le_mul hAc ih.2

/-! ### A phase and a stage -/

/-- **A phase**: the classes in `cs` are pulled one after another; the reductions may only
introduce level-`t` letters of the classes `Z`, which are not pulled in this phase. -/
theorem uphase {τ : ℕ → ℕ → G} {ok : ℕ → ℕ → Prop} {N : ℕ}
    {corr : ULetter → ULetter → List ULetter} (hc : UCorrOK τ ok N corr) {s : ℕ}
    (hok : ∀ k i, ok k i → k ≤ s) (t : ℕ) (Z : ℕ → Prop) (d : ℕ → ℕ)
    (red : ℕ → List ULetter) :
    ∀ cs : List ℕ, (∀ i ∈ cs, ¬ Z i ∧ uval τ (red i) = τ t i ^ d i ∧ (red i).length ≤ N ∧
      ∀ x ∈ red i, ok x.1 x.2.1 ∧ t ≤ x.1 ∧ (x.1 = t → Z x.2.1)) →
    ∀ K, ∃ K', K ≤ K' ∧ ∀ m, 1 ≤ m → ∀ w : List ULetter,
      (∀ x ∈ w, ok x.1 x.2.1 ∧ t ≤ x.1 ∧ (x.1 = t → x.2.1 ∈ cs ∨ Z x.2.1)) →
      (∀ ℓ, ucnt ℓ w ≤ K * m ^ 2 ^ ℓ) →
      ∃ g ∈ ulevelSet τ t d (K' * m ^ 2 ^ t) cs, ∃ w' : List ULetter,
        uval τ w = g * uval τ w' ∧ (∀ x ∈ w', ok x.1 x.2.1 ∧ t ≤ x.1 ∧ (x.1 = t → Z x.2.1)) ∧
        ∀ ℓ, ucnt ℓ w' ≤ K' * m ^ 2 ^ ℓ := by
  intro cs
  induction cs with
  | nil =>
      intro _ K
      refine ⟨K, le_rfl, fun m _ w hw hcw => ⟨1, rfl, w, by simp, ?_, hcw⟩⟩
      intro x hx
      obtain ⟨a1, a2, a3⟩ := hw x hx
      refine ⟨a1, a2, fun h => ?_⟩
      rcases a3 h with h' | h'
      · simp at h'
      · exact h'
  | cons i cs ih =>
      intro hcs K
      obtain ⟨hZi, hred, hredN, hredL⟩ := hcs i List.mem_cons_self
      obtain ⟨K1, hK1, hstep⟩ := ustep hc hok t i (d i) Z (fun j => j ∈ i :: cs ∨ Z j) (red i)
        hred hredN (fun x hx => by
          obtain ⟨a1, a2, a3⟩ := hredL x hx
          refine ⟨a1, a2, fun h => ?_, a3⟩
          have hz := a3 h.1
          rw [h.2] at hz
          exact hZi hz) K
      obtain ⟨K2, hK2, hrest⟩ := ih (fun j hj => hcs j (List.mem_cons_of_mem i hj)) K1
      refine ⟨K1 + K2, by omega, ?_⟩
      intro m hm w hw hcw
      obtain ⟨e, w1, he0, he1, hval, hw1, hcw1⟩ := hstep m hm w hw hcw
      have hw1' : ∀ x ∈ w1, ok x.1 x.2.1 ∧ t ≤ x.1 ∧ (x.1 = t → x.2.1 ∈ cs ∨ Z x.2.1) := by
        intro x hx
        obtain ⟨a1, a2, a3⟩ := hw1 x hx
        refine ⟨a1, a2, fun h => ?_⟩
        rcases a3 h with ⟨h1, h2⟩ | h'
        · rcases h1 with h1 | h1
          · rcases List.mem_cons.1 h1 with h1 | h1
            · exact absurd h1 h2
            · exact Or.inl h1
          · exact Or.inr h1
        · exact Or.inr h'
      obtain ⟨g, hg, w', hval', hw', hcw'⟩ := hrest m hm w1 hw1' hcw1
      refine ⟨τ t i ^ e * g, mem_ulevelSet_cons ?_ ?_, w', ?_, hw', ?_⟩
      · refine ⟨fun h => le_trans (he0 h) ?_, he1⟩
        exact_mod_cast Nat.mul_le_mul_right _ (by omega : K1 ≤ K1 + K2)
      · exact ulevelSet_mono τ t d (Nat.mul_le_mul_right _ (by omega : K2 ≤ K1 + K2)) cs hg
      · rw [hval, hval', mul_assoc]
      · intro ℓ
        exact le_trans (hcw' ℓ) (Nat.mul_le_mul_right _ (by omega))

/-- **A stage**: all the letters of level `t` are collected, first the classes `A` (each
reduced modulo `d`, the reduction introducing only letters of the classes `B`), then the
classes `B` (not reduced, `d = 0`).  What remains lies on levels `≥ t + 1`. -/
theorem ustage {τ : ℕ → ℕ → G} {ok : ℕ → ℕ → Prop} {N : ℕ}
    {corr : ULetter → ULetter → List ULetter} (hc : UCorrOK τ ok N corr) {s : ℕ}
    (hok : ∀ k i, ok k i → k ≤ s) (t : ℕ) (d : ℕ → ℕ) (red : ℕ → List ULetter)
    (A B : List ℕ) (hAB : ∀ i, ok t i → i ∈ A ∨ i ∈ B)
    (hA : ∀ i ∈ A, i ∉ B ∧ uval τ (red i) = τ t i ^ d i ∧ (red i).length ≤ N ∧
      ∀ x ∈ red i, ok x.1 x.2.1 ∧ t ≤ x.1 ∧ (x.1 = t → x.2.1 ∈ B))
    (hB : ∀ i ∈ B, d i = 0) (K : ℕ) :
    ∃ K', K ≤ K' ∧ ∀ m, 1 ≤ m → ∀ w : List ULetter, (∀ x ∈ w, ok x.1 x.2.1 ∧ t ≤ x.1) →
      (∀ ℓ, ucnt ℓ w ≤ K * m ^ 2 ^ ℓ) →
      ∃ g ∈ ulevelSet τ t d (K' * m ^ 2 ^ t) (A ++ B), ∃ w' : List ULetter,
        uval τ w = g * uval τ w' ∧ (∀ x ∈ w', ok x.1 x.2.1 ∧ t + 1 ≤ x.1) ∧
        ∀ ℓ, ucnt ℓ w' ≤ K' * m ^ 2 ^ ℓ := by
  obtain ⟨K1, hK1, h1⟩ := uphase hc hok t (fun j => j ∈ B) d red A hA K
  obtain ⟨K2, hK2, h2⟩ := uphase hc hok t (fun _ => False) d (fun _ => []) B
    (fun i hi => ⟨not_false, by simp [uval, hB i hi], by simp, by simp⟩) K1
  refine ⟨K1 + K2, by omega, ?_⟩
  intro m hm w hw hcw
  obtain ⟨g1, hg1, w1, hv1, hw1, hc1⟩ := h1 m hm w (fun x hx => by
    refine ⟨(hw x hx).1, (hw x hx).2, fun h => ?_⟩
    have hx1 := (hw x hx).1
    rw [h] at hx1
    exact hAB x.2.1 hx1) hcw
  obtain ⟨g2, hg2, w2, hv2, hw2, hc2⟩ := h2 m hm w1 (fun x hx => by
    obtain ⟨a1, a2, a3⟩ := hw1 x hx
    exact ⟨a1, a2, fun h => Or.inl (a3 h)⟩) hc1
  refine ⟨g1 * g2, mul_mem_ulevelSet_append τ t d _ A B g1 g2
    (ulevelSet_mono τ t d (Nat.mul_le_mul_right _ (by omega)) A hg1)
    (ulevelSet_mono τ t d (Nat.mul_le_mul_right _ (by omega)) B hg2), w2, ?_, ?_, ?_⟩
  · rw [hv1, hv2, mul_assoc]
  · intro x hx
    obtain ⟨a1, a2, a3⟩ := hw2 x hx
    refine ⟨a1, ?_⟩
    by_contra hlt
    exact a3 (by omega)
  · intro ℓ
    exact le_trans (hc2 ℓ) (Nat.mul_le_mul_right _ (by omega))

end UpperStage

end Lib
end Wolf

/-!
# Theorem 3.2, upper bound: Wolf's (3.9)–(3.10)

For a finitely generated nilpotent group `Γ` and any finite generating set `S`,
`g_S(m) ≤ c m^{E₂}` with `E₂ = ∑_k 2^k n_k`.

The route is Wolf's.  The corrected Lemma 3.7 supplies, at each level `k`, a finite family
`τ_{k,i} ∈ Γ_k` whose images generate `Γ_k/Γ_{k+1}`, with a subfamily `J_k` that is independent,
of infinite order, and spans a subgroup of finite index `D_k`.  Writing an element of the
`S`-ball of radius `m` as a word on these letters (at most `N₀ m` of them), the collection
process of `W_upper_words`/`W_upper_stage` is run level by level (`uiter`): at level `t` the
members outside `J_t` are pulled first and their exponents reduced modulo `D_t`, the reduction
`τ_{t,i}^{D_t} ∈ ⟨J_t⟩ Γ_{t+1}` being a fixed word; then the members of `J_t` are pulled, with
exponents `O(m^{2^t})`.  So every element of the ball lies in a product `C_0 C_1 ⋯ C_s` of level
sets with `|C_t| ≤ D_t^{r_t} (2K_t m^{2^t} + 1)^{#J_t}`, and `#J_t ≤ n_t` because `J_t` is
independent of infinite order in `Γ_t/Γ_{t+1}` (`card_le_lcsRank`).

Wolf's letters are the `τ_{k,i}` themselves; the corrections `a⁻¹ b⁻¹ a b` for two letters are
fixed words on the higher levels (`UCorrOK`), which is all the collection process uses — Lemma
3.7's commutator form (ii) is not needed here.
-/

namespace Wolf
namespace Lib

open Chou Chou.Lib
open scoped commutatorElement

/-! ### Iterating the stages -/

/-- The stages at levels `t, t+1, …, t+n-1`, run one after the other, put the value of a word
into the product of the level sets. -/
theorem uiter {G : Type*} [Group G] {τ : ℕ → ℕ → G} {ok : ℕ → ℕ → Prop} (Kseq : ℕ → ℕ)
    (C : ℕ → Set G) (m : ℕ)
    (hstage : ∀ t (w : List ULetter), (∀ x ∈ w, ok x.1 x.2.1 ∧ t ≤ x.1) →
      (∀ ℓ, ucnt ℓ w ≤ Kseq t * m ^ 2 ^ ℓ) →
      ∃ g ∈ C t, ∃ w' : List ULetter, uval τ w = g * uval τ w' ∧
        (∀ x ∈ w', ok x.1 x.2.1 ∧ t + 1 ≤ x.1) ∧ ∀ ℓ, ucnt ℓ w' ≤ Kseq (t + 1) * m ^ 2 ^ ℓ) :
    ∀ n t (w : List ULetter), (∀ x ∈ w, ok x.1 x.2.1 ∧ t ≤ x.1) →
      (∀ ℓ, ucnt ℓ w ≤ Kseq t * m ^ 2 ^ ℓ) →
      ∃ g ∈ prodSet C t n, ∃ w' : List ULetter, uval τ w = g * uval τ w' ∧
        ∀ x ∈ w', ok x.1 x.2.1 ∧ t + n ≤ x.1 := by
  intro n
  induction n with
  | zero =>
      intro t w hw _
      exact ⟨1, by simp [prodSet], w, by simp, fun x hx => by simpa using hw x hx⟩
  | succ n ih =>
      intro t w hw hcw
      obtain ⟨c, hc, w1, hv1, hw1, hcw1⟩ := hstage t w hw hcw
      obtain ⟨g, hg, w', hv', hw'⟩ := ih (t + 1) w1 hw1 hcw1
      refine ⟨c * g, ⟨(c, g), ⟨hc, hg⟩, rfl⟩, w', ?_, fun x hx => ?_⟩
      · rw [hv1, hv', mul_assoc]
      · have := hw' x hx
        exact ⟨this.1, by omega⟩

/-! ### Lifting from the factor -/

/-- An element of the subgroup generated by the images of a family is the image of a word on
the family. -/
theorem exists_list_of_mem_iSup_zpowers {H Q : Type*} [Group H] [Group Q] (π : H →* Q)
    {ι : Type*} (x : ι → H) {q : Q} (hq : q ∈ ⨆ i, Subgroup.zpowers (π (x i))) :
    ∃ l : List (ι × Bool), π ((l.map fun p => if p.2 then (x p.1)⁻¹ else x p.1).prod) = q := by
  refine Subgroup.iSup_induction (fun i => Subgroup.zpowers (π (x i)))
    (C := fun q => ∃ l : List (ι × Bool),
      π ((l.map fun p => if p.2 then (x p.1)⁻¹ else x p.1).prod) = q) hq ?_ ?_ ?_
  · rintro i _ ⟨n, rfl⟩
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · refine ⟨List.replicate k (i, false), ?_⟩
      simp [List.map_replicate, List.prod_replicate, map_pow]
    · refine ⟨List.replicate k (i, true), ?_⟩
      simp [List.map_replicate, List.prod_replicate, map_pow, zpow_neg]
  · exact ⟨[], by simp⟩
  · rintro _ _ ⟨la, rfl⟩ ⟨lb, rfl⟩
    exact ⟨la ++ lb, by simp [List.map_append, List.prod_append, map_mul]⟩

variable {Γ : Type*} [Group Γ]

/-- An element of `Γ_k` whose class lies in the span of a family of classes is a word on the
family times an element of `Γ_{k+1}`. -/
theorem exists_mul_mem_lcs_succ (k : ℕ) {ι : Type*} (x : ι → ↥(MilnorWolf.lcs Γ k))
    (g : ↥(MilnorWolf.lcs Γ k))
    (hg : QuotientGroup.mk' ((MilnorWolf.lcs Γ (k + 1)).subgroupOf (MilnorWolf.lcs Γ k)) g ∈
      ⨆ i, Subgroup.zpowers (QuotientGroup.mk'
        ((MilnorWolf.lcs Γ (k + 1)).subgroupOf (MilnorWolf.lcs Γ k)) (x i))) :
    ∃ (l : List (ι × Bool)) (g' : Γ), g' ∈ MilnorWolf.lcs Γ (k + 1) ∧
      (g : Γ) = (l.map fun p => if p.2 then ((x p.1 : Γ))⁻¹ else (x p.1 : Γ)).prod * g' := by
  obtain ⟨l, hl⟩ := exists_list_of_mem_iSup_zpowers _ x hg
  obtain ⟨z, hz, hze⟩ := (QuotientGroup.mk'_eq_mk' _).1 hl
  refine ⟨l, (z : Γ), Subgroup.mem_subgroupOf.1 hz, ?_⟩
  rw [← hze, Subgroup.coe_mul]
  congr 1
  clear hl hze
  induction l with
  | nil => simp
  | cons p l ih =>
      rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, ih, List.map_cons, List.prod_cons]
      split_ifs <;> simp

/-! ### The letters -/

/-- The family of Lemma 3.7, indexed by natural numbers (`1` beyond the family). -/
noncomputable def upperTau {r : ℕ → ℕ} (τ : ∀ k, Fin (r k) → ↥(MilnorWolf.lcs Γ k))
    (k i : ℕ) : Γ :=
  if h : i < r k then (τ k ⟨i, h⟩ : Γ) else 1

theorem upperTau_fin {r : ℕ → ℕ} (τ : ∀ k, Fin (r k) → ↥(MilnorWolf.lcs Γ k)) (k : ℕ)
    (i : Fin (r k)) : upperTau τ k i.val = (τ k i : Γ) := by
  simp [upperTau]

theorem upperTau_mem {r : ℕ → ℕ} (τ : ∀ k, Fin (r k) → ↥(MilnorWolf.lcs Γ k)) (k i : ℕ) :
    upperTau τ k i ∈ MilnorWolf.lcs Γ k := by
  unfold upperTau
  split_ifs
  · exact (τ k _).2
  · exact one_mem _

theorem uev_upperTau_mem {r : ℕ → ℕ} (τ : ∀ k, Fin (r k) → ↥(MilnorWolf.lcs Γ k))
    (x : ULetter) : uev (upperTau τ) x ∈ MilnorWolf.lcs Γ x.1 := by
  unfold uev
  split_ifs
  · exact inv_mem (upperTau_mem τ _ _)
  · exact upperTau_mem τ _ _

theorem uval_map_letters {r : ℕ → ℕ} (τ : ∀ k, Fin (r k) → ↥(MilnorWolf.lcs Γ k)) (k : ℕ)
    {ι : Type*} (f : ι → Fin (r k)) (l : List (ι × Bool)) :
    uval (upperTau τ) (l.map fun p => (k, (f p.1).val, p.2)) =
      (l.map fun p => if p.2 then ((τ k (f p.1) : Γ))⁻¹ else (τ k (f p.1) : Γ)).prod := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      rw [List.map_cons, uval_cons, ih, List.map_cons, List.prod_cons]
      congr 1
      unfold uev
      simp only [upperTau_fin]

/-! ### The rank -/

/-- **`#J_k ≤ n_k`.**  The members of `J_k` are independent and of infinite order in
`Γ_k/Γ_{k+1}`, hence `ℤ`-linearly independent there, and the factor is isomorphic to the
definition bundle's `lcsFactor Γ k`, a finitely generated abelian group of rank `n_k`. -/
theorem card_le_lcsRank [Group.FG Γ] [Group.IsNilpotent Γ] (k : ℕ) {rk : ℕ}
    (τ : Fin rk → ↥(MilnorWolf.lcs Γ k)) (hcomm : ∀ x y : lcsQuot Γ k, x * y = y * x)
    (J : Finset (Fin rk))
    (hind : iSupIndep fun j : J => Subgroup.zpowers (QuotientGroup.mk (τ j) : lcsQuot Γ k))
    (hinf : ∀ j ∈ J, ¬ IsOfFinOrder (QuotientGroup.mk (τ j) : lcsQuot Γ k)) :
    J.card ≤ MilnorWolf.lcsRank Γ k := by
  let _ : CommGroup (lcsQuot Γ k) := ⟨hcomm⟩
  have hli := linearIndependent_of_iSupIndep (fun j : J => (QuotientGroup.mk (τ j) : lcsQuot Γ k))
    hind (fun j n hn => zpow_eq_one_imp_eq_zero (hinf j j.2) n hn)
  set f : Additive (lcsQuot Γ k) →+ Additive (MilnorWolf.lcsFactor Γ k) :=
    MonoidHom.toAdditive (lcsQuotToFactor (Γ := Γ) k) with hf
  have hfinj : Function.Injective f := lcsQuotToFactor_injective (Γ := Γ) k
  have hli' := hli.map' f.toIntLinearMap (LinearMap.ker_eq_bot.2 hfinj)
  have : Group.FG (MilnorWolf.lcsFactor Γ k) := forall_fg_lcsFactor k
  have : Module.Finite ℤ (Additive (MilnorWolf.lcsFactor Γ k)) :=
    Module.Finite.iff_addGroup_fg.2 inferInstance
  have := hli'.fintype_card_le_finrank
  rw [Fintype.card_coe] at this
  exact this

/-! ### The bound -/

/-- **Wolf's (3.9)–(3.10), counted.**  For a finitely generated nilpotent group and any finite
subset `S`, the `S`-ball of radius `m` has at most `P m^{E₂}` elements. -/
theorem exists_card_wordBall_le_mul_pow_growthExponentTwo [Group.FG Γ] [Group.IsNilpotent Γ]
    (S : Finset Γ) :
    ∃ P : ℕ, ∀ m : ℕ, 1 ≤ m →
      Nat.card (wordBall (S : Set Γ) m) ≤ P * m ^ (MilnorWolf.growthExponentTwo Γ) := by
  classical
  set s : ℕ := Group.nilpotencyClass Γ with hsdef
  have hs : MilnorWolf.lcs Γ (s + 1) = ⊥ := by
    have h := lcs_nilpotencyClass_eq_bot (Γ := Γ)
    have hle : MilnorWolf.lcs Γ (Group.nilpotencyClass Γ + 1) ≤
        MilnorWolf.lcs Γ (Group.nilpotencyClass Γ) :=
      (⊤ : Subgroup Γ).lowerCentralSeries_antitone (Nat.le_succ _)
    rw [h] at hle
    exact le_bot_iff.1 hle
  have hbot : ∀ k, s ≤ k → ∀ g ∈ MilnorWolf.lcs Γ k, g = 1 := by
    intro k hk g hg
    have hle : MilnorWolf.lcs Γ k ≤ MilnorWolf.lcs Γ s :=
      (⊤ : Subgroup Γ).lowerCentralSeries_antitone hk
    rw [hsdef, lcs_nilpotencyClass_eq_bot] at hle
    exact (Subgroup.mem_bot).1 (hle hg)
  obtain ⟨r, τ, hi, -, -⟩ :=
    _root_.Wolf.exists_commutator_generating_sets_with_free_finiteIndex_subfamily_lowerCentralSeries
      (Γ := Γ) s hs fg_lcsQuot_zero
  set ok : ℕ → ℕ → Prop := fun k i => k < s ∧ i < r k with hokdef
  have hokS : ∀ k i, ok k i → k ≤ s := fun k i h => h.1.le
  -- every element of `Γ_k` is a word on the letters of levels `≥ k`
  have hword : ∀ k, ∀ g ∈ MilnorWolf.lcs Γ k, ∃ w : List ULetter,
      (∀ x ∈ w, ok x.1 x.2.1 ∧ k ≤ x.1) ∧ uval (upperTau τ) w = g := by
    suffices h : ∀ n k, s ≤ k + n → ∀ g ∈ MilnorWolf.lcs Γ k, ∃ w : List ULetter,
        (∀ x ∈ w, ok x.1 x.2.1 ∧ k ≤ x.1) ∧ uval (upperTau τ) w = g from
      fun k g hg => h s k (by omega) g hg
    intro n
    induction n with
    | zero =>
        intro k hk g hg
        exact ⟨[], by simp, by rw [hbot k (by omega) g hg]; rfl⟩
    | succ n ih =>
        intro k hk g hg
        by_cases hks : s ≤ k
        · exact ⟨[], by simp, by rw [hbot k hks g hg]; rfl⟩
        · obtain ⟨l, g', hg', heq⟩ := exists_mul_mem_lcs_succ k (τ k) ⟨g, hg⟩
            (by rw [(hi k).2.2.1]; exact Subgroup.mem_top _)
          obtain ⟨w', hw', hv'⟩ := ih (k + 1) (by omega) g' hg'
          refine ⟨l.map (fun p => (k, (id p.1 : Fin (r k)).val, p.2)) ++ w', ?_, ?_⟩
          · intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
              exact ⟨⟨by omega, p.1.2⟩, le_rfl⟩
            · exact ⟨(hw' x hx).1, by have := (hw' x hx).2; omega⟩
          · rw [uval_append, uval_map_letters τ k id l, hv']
            exact heq.symm
  -- the corrections `a⁻¹ b⁻¹ a b`, one level up
  have hcorrex : ∀ a b : ULetter, ∃ u : List ULetter, ok a.1 a.2.1 → ok b.1 b.2.1 → b.1 ≤ a.1 →
      uval (upperTau τ) u = (uev (upperTau τ) a)⁻¹ * (uev (upperTau τ) b)⁻¹ *
        uev (upperTau τ) a * uev (upperTau τ) b ∧ ∀ x ∈ u, ok x.1 x.2.1 ∧ a.1 < x.1 := by
    intro a b
    have hmem : (uev (upperTau τ) a)⁻¹ * (uev (upperTau τ) b)⁻¹ * uev (upperTau τ) a *
        uev (upperTau τ) b ∈ MilnorWolf.lcs Γ (a.1 + 1) := by
      have h := Subgroup.commutator_mem_commutator (inv_mem (uev_upperTau_mem τ a))
        (Subgroup.mem_top (uev (upperTau τ) b)⁻¹)
      rw [commutatorElement_def, inv_inv, inv_inv] at h
      exact h
    obtain ⟨w, hw, hv⟩ := hword (a.1 + 1) _ hmem
    exact ⟨w, fun _ _ _ => ⟨hv, fun x hx => ⟨(hw x hx).1, by have := (hw x hx).2; omega⟩⟩⟩
  choose corr hcorr using hcorrex
  -- the valid letters form a finite set
  set R : ℕ := ∑ k ∈ Finset.range s, r k with hR
  have hrR : ∀ k, k < s → r k ≤ R := fun k hk =>
    Finset.single_le_sum (f := r) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
  set F : Finset ULetter := Finset.range s ×ˢ (Finset.range R ×ˢ Finset.univ) with hF
  have hmemF : ∀ x : ULetter, ok x.1 x.2.1 → x ∈ F := by
    intro x hx
    simp only [hF, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
    exact ⟨by have := hx.1; omega, lt_of_lt_of_le hx.2 (hrR _ hx.1)⟩
  set Nc : ℕ := (F ×ˢ F).sup fun p => (corr p.1 p.2).length with hNc
  -- the free parts `J_t` and their indices `D_t`
  choose J hJind hJinf hJfin using fun t => (hi t).2.2.2
  set J' : ℕ → Finset ℕ := fun t => (J t).map Fin.valEmbedding with hJ'
  have hJ'lt : ∀ t i, i ∈ J' t → i < r t := by
    intro t i hi
    simp only [hJ', Finset.mem_map, Fin.valEmbedding_apply] at hi
    obtain ⟨j, -, rfl⟩ := hi
    exact j.2
  set D : ℕ → ℕ := fun t => (⨆ j : J t, Subgroup.zpowers (QuotientGroup.mk'
    ((MilnorWolf.lcs Γ (t + 1)).subgroupOf (MilnorWolf.lcs Γ t)) (τ t j))).index with hD
  have hD0 : ∀ t, D t ≠ 0 := fun t => (hJfin t).index_ne_zero
  -- the reductions `τ_{t,i}^{D_t} ∈ ⟨J_t⟩ Γ_{t+1}`, as words
  have hredex : ∀ t i, ∃ u : List ULetter, i < r t → i ∉ J' t →
      uval (upperTau τ) u = upperTau τ t i ^ D t ∧
        ∀ x ∈ u, ok x.1 x.2.1 ∧ t ≤ x.1 ∧ (x.1 = t → x.2.1 ∈ J' t) := by
    intro t i
    by_cases hts : t < s
    · by_cases hir : i < r t
      · have hnorm : (⨆ j : J t, Subgroup.zpowers (QuotientGroup.mk'
            ((MilnorWolf.lcs Γ (t + 1)).subgroupOf (MilnorWolf.lcs Γ t)) ((fun j : J t => τ t j) j))).Normal :=
          ⟨fun n _ g => by rwa [(hi t).2.1 g n, mul_inv_cancel_right]⟩
        have hpow : QuotientGroup.mk' ((MilnorWolf.lcs Γ (t + 1)).subgroupOf
            (MilnorWolf.lcs Γ t)) (τ t ⟨i, hir⟩ ^ D t) ∈
            ⨆ j : J t, Subgroup.zpowers (QuotientGroup.mk' ((MilnorWolf.lcs Γ (t + 1)).subgroupOf
              (MilnorWolf.lcs Γ t)) ((fun j : J t => τ t j) j)) := by
          rw [map_pow]
          exact Subgroup.pow_index_mem _ _
        obtain ⟨l, g', hg', heq⟩ :=
          exists_mul_mem_lcs_succ t (fun j : J t => τ t j) (τ t ⟨i, hir⟩ ^ D t) hpow
        obtain ⟨w', hw', hv'⟩ := hword (t + 1) g' hg'
        refine ⟨l.map (fun p => (t, ((fun j : J t => (j : Fin (r t))) p.1).val, p.2)) ++ w',
          fun _ _ => ⟨?_, ?_⟩⟩
        · rw [uval_append, uval_map_letters τ t (fun j : J t => (j : Fin (r t))) l, hv',
            upperTau, dif_pos hir]
          have h1 : ((τ t ⟨i, hir⟩ : Γ)) ^ D t =
              ((τ t ⟨i, hir⟩ ^ D t : ↥(MilnorWolf.lcs Γ t)) : Γ) := by simp
          rw [h1, heq]
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
            refine ⟨⟨by omega, (p.1 : Fin (r t)).2⟩, le_rfl, fun _ => ?_⟩
            simp only [hJ', Finset.mem_map, Fin.valEmbedding_apply]
            exact ⟨p.1, p.1.2, rfl⟩
          · obtain ⟨a1, a2⟩ := hw' x hx
            exact ⟨a1, by omega, fun h => by omega⟩
      · exact ⟨[], fun h => absurd h hir⟩
    · refine ⟨[], fun _ _ => ⟨?_, by simp⟩⟩
      have : upperTau τ t i = 1 := hbot t (by omega) _ (upperTau_mem τ t i)
      rw [this, one_pow]
      rfl
  choose red hred using hredex
  set Nr : ℕ := ((Finset.range s) ×ˢ (Finset.range R)).sup
    (fun p => (red p.1 p.2).length) with hNr
  set N : ℕ := Nc + Nr with hN
  have hc : UCorrOK (upperTau τ) ok N corr := by
    intro a b ha hb hab
    obtain ⟨h1, h2⟩ := hcorr a b ha hb hab
    refine ⟨h1, ?_, h2⟩
    have : (corr a b).length ≤ Nc := by
      rw [hNc]
      exact Finset.le_sup (f := fun p : ULetter × ULetter => (corr p.1 p.2).length) (b := (a, b))
        (Finset.mem_product.2 ⟨hmemF a ha, hmemF b hb⟩)
    omega
  -- the stages
  set dd : ℕ → ℕ → ℕ := fun t i => if i ∈ J' t then 0 else D t with hdd
  set A : ℕ → List ℕ := fun t => if t < s then
    ((Finset.range (r t)).filter (fun i => i ∉ J' t)).toList else [] with hA
  set B : ℕ → List ℕ := fun t => (J' t).toList with hB
  have hmemA : ∀ t i, i ∈ A t ↔ t < s ∧ i < r t ∧ i ∉ J' t := by
    intro t i
    simp only [hA]
    split_ifs with h
    · simp [Finset.mem_toList, Finset.mem_filter, h]
    · simp [h]
  have hmemB : ∀ t i, i ∈ B t ↔ i ∈ J' t := by
    intro t i
    simp [hB]
  have hddA : ∀ t i, i ∈ A t → dd t i = D t := by
    intro t i hi
    simp only [hdd, if_neg ((hmemA t i).1 hi).2.2]
  have hddB : ∀ t i, i ∈ B t → dd t i = 0 := by
    intro t i hi
    simp only [hdd, if_pos ((hmemB t i).1 hi)]
  have hstage : ∀ t K, ∃ K', K ≤ K' ∧ ∀ m, 1 ≤ m → ∀ w : List ULetter,
      (∀ x ∈ w, ok x.1 x.2.1 ∧ t ≤ x.1) → (∀ ℓ, ucnt ℓ w ≤ K * m ^ 2 ^ ℓ) →
      ∃ g ∈ ulevelSet (upperTau τ) t (dd t) (K' * m ^ 2 ^ t) (A t ++ B t),
        ∃ w' : List ULetter, uval (upperTau τ) w = g * uval (upperTau τ) w' ∧
          (∀ x ∈ w', ok x.1 x.2.1 ∧ t + 1 ≤ x.1) ∧ ∀ ℓ, ucnt ℓ w' ≤ K' * m ^ 2 ^ ℓ := by
    intro t K
    refine ustage hc hokS t (dd t) (red t) (A t) (B t) ?_ ?_ ?_ K
    · intro i hi
      by_cases hJ : i ∈ J' t
      · exact Or.inr ((hmemB t i).2 hJ)
      · exact Or.inl ((hmemA t i).2 ⟨hi.1, hi.2, hJ⟩)
    · intro i hi
      obtain ⟨hts, hir, hJ⟩ := (hmemA t i).1 hi
      obtain ⟨h1, h2⟩ := hred t i hir hJ
      refine ⟨fun h => hJ ((hmemB t i).1 h), ?_, ?_, ?_⟩
      · rw [h1, hddA t i hi]
      · have : (red t i).length ≤ Nr := by
          rw [hNr]
          exact Finset.le_sup (f := fun p : ℕ × ℕ => (red p.1 p.2).length) (b := (t, i))
            (Finset.mem_product.2 ⟨Finset.mem_range.2 hts,
              Finset.mem_range.2 (lt_of_lt_of_le hir (hrR t hts))⟩)
        omega
      · intro x hx
        obtain ⟨a1, a2, a3⟩ := h2 x hx
        exact ⟨a1, a2, fun h => (hmemB t _).2 (a3 h)⟩
    · intro i hi
      exact hddB t i hi
  choose Fk hFk hFst using hstage
  -- the generators and their inverses, as words
  have hSex : ∀ x : Γ, ∃ u : List ULetter, (∀ y ∈ u, ok y.1 y.2.1 ∧ 0 ≤ y.1) ∧
      uval (upperTau τ) u = x := fun x => hword 0 x (Subgroup.mem_top x)
  choose wd hwd using hSex
  set T0 : Finset Γ := S ∪ S.image (fun x => x⁻¹) with hT0
  set N0 : ℕ := T0.sup fun x => (wd x).length with hN0
  have hball : ∀ l : List Γ, (∀ x ∈ l, x ∈ (S : Set Γ) ∨ x⁻¹ ∈ (S : Set Γ)) →
      ∃ w : List ULetter, (∀ y ∈ w, ok y.1 y.2.1 ∧ 0 ≤ y.1) ∧
        uval (upperTau τ) w = l.prod ∧ w.length ≤ N0 * l.length := by
    intro l
    induction l with
    | nil => intro _; exact ⟨[], by simp, rfl, by simp⟩
    | cons x l ih =>
        intro hl
        obtain ⟨w, hw, hv, hlen⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
        have hxT : x ∈ T0 := by
          rcases hl x List.mem_cons_self with h | h
          · exact Finset.mem_union_left _ (by exact_mod_cast h)
          · exact Finset.mem_union_right _
              (Finset.mem_image.2 ⟨x⁻¹, by exact_mod_cast h, inv_inv x⟩)
        have hxl : (wd x).length ≤ N0 := by
          rw [hN0]
          exact Finset.le_sup (f := fun x => (wd x).length) hxT
        refine ⟨wd x ++ w, ?_, ?_, ?_⟩
        · intro y hy
          rcases List.mem_append.1 hy with hy | hy
          · exact (hwd x).1 y hy
          · exact hw y hy
        · rw [uval_append, (hwd x).2, hv, List.prod_cons]
        · rw [List.length_append, List.length_cons, Nat.mul_succ]
          omega
  -- the constants of the successive stages, and the level sets
  let Kseq : ℕ → ℕ := fun t => Nat.rec N0 (fun t K => Fk t K) t
  let C : ℕ → ℕ → Set Γ := fun m t =>
    ulevelSet (upperTau τ) t (dd t) (Kseq (t + 1) * m ^ 2 ^ t) (A t ++ B t)
  have hsub : ∀ m, 1 ≤ m → wordBall (S : Set Γ) m ⊆ prodSet (C m) 0 s := by
    intro m hm γ hγ
    obtain ⟨l, hlm, hlS, rfl⟩ := hγ
    obtain ⟨w, hw, hv, hlen⟩ := hball l hlS
    have hcw : ∀ ℓ, ucnt ℓ w ≤ Kseq 0 * m ^ 2 ^ ℓ := by
      intro ℓ
      have h1 := ucnt_le_length ℓ w
      have h2 : m ≤ m ^ 2 ^ ℓ := Nat.le_self_pow (by positivity) m
      have h3 : N0 * l.length ≤ N0 * m := Nat.mul_le_mul_left _ hlm
      have h4 : N0 * m ≤ N0 * m ^ 2 ^ ℓ := Nat.mul_le_mul_left _ h2
      show ucnt ℓ w ≤ N0 * m ^ 2 ^ ℓ
      omega
    obtain ⟨g, hg, w', hv', hw'⟩ := uiter Kseq (C m) m
      (fun t w hw hcw => hFst t (Kseq t) m hm w hw hcw) s 0 w hw hcw
    have hnil : w' = [] := by
      rcases w' with _ | ⟨x, w'⟩
      · rfl
      · have h1 := hw' x List.mem_cons_self
        have h2 := h1.1.1
        omega
    rw [← hv, hv', hnil, uval_nil, mul_one]
    exact hg
  have hCfin : ∀ m t, (C m t).Finite := fun m t => (ulevelSet_finite_ncard _ _ _ _ _).1
  have hlevel : ∀ m, 1 ≤ m → ∀ t, (C m t).ncard ≤
      D t ^ (A t).length * ((2 * Kseq (t + 1) + 1) ^ (J t).card * (m ^ 2 ^ t) ^ (J t).card) := by
    intro m hm t
    refine le_trans (ulevelSet_finite_ncard (upperTau τ) t (dd t) (Kseq (t + 1) * m ^ 2 ^ t)
      (A t ++ B t)).2 ?_
    rw [List.map_append, List.prod_append]
    apply Nat.mul_le_mul
    · refine (List.prod_le_pow_card _ (D t) ?_).trans (le_of_eq (by rw [List.length_map]))
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      rw [hddA t i hi, if_neg (hD0 t)]
    · refine (List.prod_le_pow_card _ (2 * (Kseq (t + 1) * m ^ 2 ^ t) + 1) ?_).trans ?_
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        rw [hddB t i hi, if_pos rfl]
      · have hlenB : (List.map (fun i => if dd t i = 0 then 2 * (Kseq (t + 1) * m ^ 2 ^ t) + 1
            else dd t i) (B t)).length = (J t).card := by
          rw [List.length_map, hB, Finset.length_toList, hJ', Finset.card_map]
        rw [hlenB, ← mul_pow]
        apply Nat.pow_le_pow_left
        have : 1 ≤ m ^ 2 ^ t := Nat.one_le_pow _ _ (by omega)
        nlinarith
  have hJrank : ∀ t, t < s → (J t).card ≤ MilnorWolf.lcsRank Γ t := fun t _ =>
    card_le_lcsRank t (τ t) (hi t).2.1 (J t) (hJind t) (hJinf t)
  refine ⟨∏ t ∈ Finset.range s, D t ^ (A t).length * (2 * Kseq (t + 1) + 1) ^ (J t).card, ?_⟩
  intro m hm
  calc Nat.card (wordBall (S : Set Γ) m) ≤ (prodSet (C m) 0 s).ncard := by
        rw [Nat.card_coe_set_eq]
        exact Set.ncard_le_ncard (hsub m hm) (prodSet_finite (C m) (hCfin m) s 0)
    _ ≤ ∏ t ∈ Finset.range s, (C m t).ncard := by
        simpa using ncard_prodSet_le (C m) (hCfin m) s 0
    _ ≤ ∏ t ∈ Finset.range s, (D t ^ (A t).length * (2 * Kseq (t + 1) + 1) ^ (J t).card) *
          m ^ (2 ^ t * MilnorWolf.lcsRank Γ t) := by
        apply Finset.prod_le_prod'
        intro t ht
        refine le_trans (hlevel m hm t) ?_
        rw [← mul_assoc]
        apply Nat.mul_le_mul_left
        rw [← pow_mul]
        exact Nat.pow_le_pow_right (by omega)
          (Nat.mul_le_mul_left _ (hJrank t (Finset.mem_range.1 ht)))
    _ = (∏ t ∈ Finset.range s, D t ^ (A t).length * (2 * Kseq (t + 1) + 1) ^ (J t).card) *
          m ^ (MilnorWolf.growthExponentTwo Γ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, MilnorWolf.growthExponentTwo]

/-- **Wolf's Theorem 3.2, upper bound.** -/
theorem exists_growthFunction_le_const_mul_pow_growthExponentTwo_of_isNilpotent' {Γ : Type*}
    [Group Γ] [Group.FG Γ] [Group.IsNilpotent Γ] (S : Finset Γ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      (MilnorWolf.growthFunction S m : ℝ) ≤ c * (m : ℝ) ^ (MilnorWolf.growthExponentTwo Γ) := by
  obtain ⟨P, hP⟩ := exists_card_wordBall_le_mul_pow_growthExponentTwo S
  refine ⟨(P : ℝ) + 1, by positivity, fun m hm => ?_⟩
  have h := hP m hm
  have h' : (MilnorWolf.growthFunction S m : ℝ) ≤ (P : ℝ) * (m : ℝ) ^
      (MilnorWolf.growthExponentTwo Γ) := by
    unfold MilnorWolf.growthFunction
    exact_mod_cast h
  have hpos : (0 : ℝ) ≤ (m : ℝ) ^ (MilnorWolf.growthExponentTwo Γ) := by positivity
  nlinarith

end Lib
end Wolf

open Wolf

theorem solution {Γ : Type*}
    [Group Γ] [Group.FG Γ] [Group.IsNilpotent Γ] (S : Finset Γ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      (MilnorWolf.growthFunction S m : ℝ) ≤ c * (m : ℝ) ^ (MilnorWolf.growthExponentTwo Γ) :=
  Wolf.Lib.exists_growthFunction_le_const_mul_pow_growthExponentTwo_of_isNilpotent' S hS

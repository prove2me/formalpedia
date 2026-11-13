-- Prove2me | solution 1 for OddOrder.Peterfalvi.S11.caseA_blockScalarFacts
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T12:32:33.098202+00:00
-- url     : https://prove2.me/submissions/05d7e516-571c-4dee-a02a-21f5b09d3bac

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Mathlib/Subgroup.lean
--   OddOrder/GroupTheory/RepresentationTheory/LineScalarCharacter.lean
--   OddOrder/GroupTheory/RepresentationTheory/SemilinearImprimitiveBound.lean
--   OddOrder/Mathlib/CyclicSubgroupUnique.lean
--   OddOrder/GroupTheory/RepresentationTheory/TypePGaloisUBound.lean
--   OddOrder/GroupTheory/RepresentationTheory/AInvariantSubrep.lean
--   OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.Group
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finite.Prod
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Theorems.Thm_OddOrder_Peterfalvi_S11_uActionHom_range_comm

-- ===== OddOrder/Mathlib/Subgroup.lean =====
namespace Subgroup

variable {G : Type*} [Group G]

open scoped Pointwise

open scoped Pointwise in
/-- **Translating a subgroup by an automorphism conjugates its pointwise stabiliser.**  If `σ` is
an automorphism of the acting group `A` implementing conjugation by `g` (`φ (σ a) = g φ(a) g⁻¹`),
then `ptStab φ (g • J) = σ (ptStab φ J)`.

This is Peterfalvi (9.7)(a)'s "`U/C_U(H_i)` has the same order for every `i`": the blocks are the
`W₁`-translates `H_i = g_i • H₁`, and conjugation by `g_i` is an automorphism of `U` (`U` being
normal in `U W₁`), so the centralisers are conjugate and their indices agree (issue 0152). -/
theorem ptStabOfMulAut_smul {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (J : Subgroup G) (g : MulAut G) (σ : A ≃* A)
    (hσ : ∀ a : A, φ (σ a) = g * φ a * g⁻¹) :
    ptStabOfMulAut φ (g • J) = (ptStabOfMulAut φ J).map σ.toMonoidHom := by
  ext a
  constructor
  · intro ha
    refine ⟨σ.symm a, fun x hx => ?_, by simp⟩
    have hgx : (g : MulAut G) x ∈ g • J := ⟨x, hx, rfl⟩
    have h := ha _ hgx
    have hφ : φ (σ (σ.symm a)) = g * φ (σ.symm a) * g⁻¹ := hσ _
    rw [σ.apply_symm_apply] at hφ
    rw [hφ] at h
    change (g : MulAut G) ((φ (σ.symm a)) ((g⁻¹ : MulAut G) ((g : MulAut G) x))) = _ at h
    rw [show (g⁻¹ : MulAut G) ((g : MulAut G) x) = x from by simp] at h
    exact g.injective h
  · rintro ⟨b, hb, rfl⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hφ : φ (σ.toMonoidHom b) = g * φ b * g⁻¹ := hσ b
    rw [hφ]
    change (g : MulAut G) ((φ b) ((g⁻¹ : MulAut G) ((g : MulAut G) x))) = _
    rw [show (g⁻¹ : MulAut G) ((g : MulAut G) x) = x from by simp, hb x hx]
    rfl

/-- The pointwise stabilisers of translated subgroups have the same index. -/
theorem index_ptStabOfMulAut_smul {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (J : Subgroup G) (g : MulAut G) (σ : A ≃* A)
    (hσ : ∀ a : A, φ (σ a) = g * φ a * g⁻¹) :
    (ptStabOfMulAut φ (g • J)).index = (ptStabOfMulAut φ J).index := by
  rw [ptStabOfMulAut_smul φ J g σ hσ]
  exact Subgroup.index_map_equiv _ σ

open scoped Pointwise in
/-- **消費者向けの形**: 作用する群が `MulAut G` の部分群 `Ū` そのもので (`φ = Ū.subtype`)、
`g` が `Ū` を正規化するとき、`J` と `g • J` の各点固定化群は `Ū` の中で同じ指数を持つ。

`σ` (= `g` による共役) をここで内部的に構成するので、呼び出し側は「`g` が `Ū` を正規化する」
という群論の事実だけ供給すればよい。Pf (9.7)(a) では `Ū = U` の作用像、`g` = ブロックを移す
`W₁`-元の作用、正規性は Frobenius `U ⋊ W₁` の `U ⊴ U W₁` から来る (issue 0152)。 -/
theorem index_ptStabOfMulAut_subtype_smul {G : Type*} [Group G]
    (Ubar : Subgroup (MulAut G)) (J : Subgroup G) (g : MulAut G)
    (hg : ∀ u ∈ Ubar, g * u * g⁻¹ ∈ Ubar) (hg' : ∀ u ∈ Ubar, g⁻¹ * u * g ∈ Ubar) :
    (ptStabOfMulAut Ubar.subtype (g • J)).index
      = (ptStabOfMulAut Ubar.subtype J).index := by
  refine index_ptStabOfMulAut_smul Ubar.subtype J g
    { toFun := fun u => ⟨g * (u : MulAut G) * g⁻¹, hg u u.2⟩
      invFun := fun u => ⟨g⁻¹ * (u : MulAut G) * g, hg' u u.2⟩
      left_inv := fun u => Subtype.ext (by group)
      right_inv := fun u => Subtype.ext (by group)
      map_mul' := fun u v => Subtype.ext (by push_cast; group) }
    (fun a => rfl)

end Subgroup

-- ===== OddOrder/GroupTheory/RepresentationTheory/LineScalarCharacter.lean =====
namespace OddOrder.RepresentationTheory

variable {p : ℕ} [Fact p.Prime] {U V : Type*} [Group U] [AddCommGroup V] [Module (ZMod p) V]

/-- **Kernel of the scalar character = pointwise stabilizer of the line**: `φ u = 1` iff `u` fixes
`V` pointwise.  For an order-`p` block this is exactly "`u` fixes a nontrivial character of the
block iff `u` centralizes the block" — the free action of `𝔽_p^×` on the line — so it discharges the
order-`p` stabilizer/centralizer identifications of Peterfalvi (9.5)/(9.8) (Coq `inertia_irr_prime`,
`PFsection9.v:948`). -/
theorem lineScalarChar_eq_one_iff (ρ : Representation (ZMod p) U V)
    (hdim : Module.finrank (ZMod p) V = 1) (u : U) :
    lineScalarChar ρ hdim u = 1 ↔ ∀ x : V, ρ u x = x := by
  constructor
  · intro h x
    rw [lineScalarChar_smul ρ hdim u x, h, Units.val_one, one_smul]
  · intro h
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hdim
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hsx : ((lineScalarChar ρ hdim u : ZMod p) - 1) • x = 0 := by
      rw [sub_smul, one_smul, ← lineScalarChar_smul ρ hdim u x, h x, sub_self]
    rcases smul_eq_zero.mp hsx with hc | hx0
    · have hval : (lineScalarChar ρ hdim u : ZMod p) = 1 := sub_eq_zero.mp hc
      exact Units.ext (by rw [hval, Units.val_one])
    · exact absurd hx0 hx

end OddOrder.RepresentationTheory

-- ===== OddOrder/GroupTheory/RepresentationTheory/SemilinearImprimitiveBound.lean =====
namespace OddOrder.RepresentationTheory

/-- **Injectivity of the block-scalar ratio homomorphism.**  If an element whose scalar values are
constant on all `n + 1` blocks is necessarily trivial, then the normalized ratio homomorphism is
injective.  This is the qualitative form of the (9.7.a) product embedding; unlike its cardinality
corollaries below, it can be restricted to Sylow subgroups by downstream consumers. -/
theorem blockScalarRatioHom_injective {Ubar A : Type*} [Group Ubar] [CommGroup A] {n : ℕ}
    (φ : Fin (n + 1) → (Ubar →* A))
    (hconst : ∀ x : Ubar, (∀ i : Fin (n + 1), φ i x = φ 0 x) → x = 1) :
    Function.Injective (blockScalarRatioHom φ) := by
  intro x y hxy
  have hxy' : ∀ i : Fin n, φ i.succ x / φ 0 x = φ i.succ y / φ 0 y :=
    fun i => congrFun hxy i
  have hz : x * y⁻¹ = 1 := by
    apply hconst
    refine Fin.cases rfl (fun j => ?_)
    have h : φ j.succ x * φ 0 y = φ j.succ y * φ 0 x :=
      (div_eq_div_iff_mul_eq_mul).mp (hxy' j)
    change φ j.succ (x * y⁻¹) = φ 0 (x * y⁻¹)
    rw [map_mul, map_mul, map_inv, map_inv, ← div_eq_mul_inv, ← div_eq_mul_inv,
      div_eq_div_iff_mul_eq_mul, mul_comm (φ 0 x)]
    exact h
  exact mul_inv_eq_one.mp hz

/-- **Ratio-embedding order divisibility**: under the block-scalar hypotheses of
`card_le_pow_of_block_scalars`, the order of `Ubar` divides `|A|^n`.

The ratio map is a group homomorphism
`x ↦ (φ_{i+1}(x) / φ_0(x))_i : Ubar →* (Fin n → A)`.  The `hconst` hypothesis makes it
injective, so Lagrange gives the divisibility of finite group orders.  Unlike the cardinality-only
bound below, this form retains prime-factor information; Peterfalvi (13.13) uses it to remove the
2-primary part of `(p - 1)^(q - 1)` for an odd-order source group. -/
theorem card_dvd_pow_of_block_scalars {Ubar A : Type*} [CommGroup Ubar] [Finite Ubar]
    [CommGroup A] [Finite A]
    {n : ℕ} (φ : Fin (n + 1) → (Ubar →* A))
    (hconst : ∀ x : Ubar, (∀ i : Fin (n + 1), φ i x = φ 0 x) → x = 1) :
    Nat.card Ubar ∣ Nat.card A ^ n := by
  simpa [Nat.card_pi] using
    Subgroup.card_dvd_of_injective (blockScalarRatioHom φ)
      (blockScalarRatioHom_injective φ hconst)

/-- **Ratio-embedding divisibility, sharpened to a common target subgroup** (Peterfalvi (9.7)(a),
the book's `a`-form).  If all `n + 1` block scalars take values in one subgroup `B ≤ A`, the ratio
embedding lands in `B^n`, so `|Ū|` divides `|B|^n` rather than merely `|A|^n`.

This is what turns the repo's `|Ū| ∣ (p−1)^{q−1}` into the book's statement that `Ū` embeds in a
direct product of `q − 1` cyclic groups of order `a = |U : C_U(H₁)|`: for the `W₁`-permuted blocks
`H_i = H_1^{w_i}` the scalar characters `φ_i` all have the *same* image (conjugation by `w_i` is an
automorphism of `U`), and that common image `B = im φ_1` is cyclic of order `a`, with `a ∣ p − 1`
by Lagrange in `A = 𝔽_p^×`.

Together with `card_dvd_pow_of_block_scalars` (the `B = ⊤` case) this covers both readings; the
sharper one keeps the prime-factor information of `a` instead of that of `p − 1` (issue 0152). -/
theorem card_dvd_pow_card_of_block_scalars_mem {Ubar A : Type*} [CommGroup Ubar] [Finite Ubar]
    [CommGroup A] [Finite A]
    {n : ℕ} (φ : Fin (n + 1) → (Ubar →* A)) (B : Subgroup A)
    (hmem : ∀ (i : Fin (n + 1)) (x : Ubar), φ i x ∈ B)
    (hconst : ∀ x : Ubar, (∀ i : Fin (n + 1), φ i x = φ 0 x) → x = 1) :
    Nat.card Ubar ∣ Nat.card B ^ n := by
  refine card_dvd_pow_of_block_scalars
    (fun i => (φ i).codRestrict B (hmem i)) (fun x hx => hconst x fun i => ?_)
  exact congrArg Subtype.val (hx i)

/-- The common block-scalar order `a = |B|` divides `|A|`, by Lagrange.  With `A = 𝔽_p^×` this is
the book's "`a` divides `p − 1`" in Peterfalvi (9.7)(a). -/
theorem card_subgroup_dvd_card {A : Type*} [CommGroup A] [Finite A] (B : Subgroup A) :
    Nat.card B ∣ Nat.card A :=
  Subgroup.card_subgroup_dvd_card B

end OddOrder.RepresentationTheory

-- ===== OddOrder/Mathlib/CyclicSubgroupUnique.lean =====
namespace OddOrder.GroupTheory

open Finset

variable {A : Type*} [CommGroup A]

/-- Membership in the `n`-torsion subgroup, realised as the kernel of `x ↦ x ^ n`. -/
theorem mem_powMonoidHom_ker {n : ℕ} {x : A} :
    x ∈ (powMonoidHom n : A →* A).ker ↔ x ^ n = 1 := Iff.rfl

/-- A subgroup is contained in the torsion of its own order (Lagrange). -/
theorem le_powMonoidHom_ker_card (B : Subgroup A) :
    B ≤ (powMonoidHom (Nat.card B) : A →* A).ker := by
  intro x hx
  rw [mem_powMonoidHom_ker]
  have hord : orderOf (⟨x, hx⟩ : B) ∣ Nat.card B := orderOf_dvd_natCard _
  have hx' : ((⟨x, hx⟩ : B) : A) ^ Nat.card B = 1 := by
    rw [← Subgroup.coe_pow, orderOf_dvd_iff_pow_eq_one.mp hord, Subgroup.coe_one]
  simpa using hx'

/-- **In a finite cyclic group, a subgroup is its own torsion.**  Lagrange gives the inclusion, and
`IsCyclic.card_pow_eq_one_le` bounds the torsion by `|B|`, forcing equality. -/
theorem eq_powMonoidHom_ker_card [Finite A] [IsCyclic A] (B : Subgroup A) :
    B = (powMonoidHom (Nat.card B) : A →* A).ker := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have hpos : 0 < Nat.card B := Nat.card_pos
  refine Subgroup.eq_of_le_of_card_ge (le_powMonoidHom_ker_card B) ?_
  have hle : #{a : A | a ^ Nat.card B = 1} ≤ Nat.card B :=
    IsCyclic.card_pow_eq_one_le hpos
  have hcard : Nat.card ((powMonoidHom (Nat.card B) : A →* A).ker) =
      #{a : A | a ^ Nat.card B = 1} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    exact Finset.filter_congr fun x _ => by simp
  omega

/-- **Subgroups of a finite cyclic group are determined by their order.**  Two subgroups of the
same order coincide, since each is the torsion of that order. -/
theorem Subgroup.eq_of_card_eq_of_isCyclic [Finite A] [IsCyclic A] {B C : Subgroup A}
    (h : Nat.card B = Nat.card C) : B = C := by
  rw [eq_powMonoidHom_ker_card B, eq_powMonoidHom_ker_card C, h]

end OddOrder.GroupTheory

-- ===== OddOrder/GroupTheory/RepresentationTheory/TypePGaloisUBound.lean =====
namespace OddOrder.RepresentationTheory

universe u

/-- **The qualitative block-scalar product embedding.**  Under the imprimitive block hypotheses,
the normalized scalar-ratio homomorphism embeds `U` into `n` copies of `(ZMod p)ˣ`.

This is the group-structural form of the block engine.  The cardinality and divisibility theorems
below forget this map; Peterfalvi (14.6) instead restricts it to a Sylow subgroup. -/
theorem exists_blockScalarRatioEmbedding_of_blocks {p : ℕ} [Fact p.Prime]
    {U M : Type u} [CommGroup U] [Finite U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    {n : ℕ} (ρ : Representation (ZMod p) U M) (B : Fin (n + 1) → Subrepresentation ρ)
    (hBcard : ∀ i, Nat.card (B i).toSubmodule = p)
    (hconst : ∀ u : U,
        (∀ i : Fin (n + 1),
          lineScalarChar (B i).toRepresentation
              (finrank_eq_one_of_card_eq_prime (hBcard i)) u
            = lineScalarChar (B 0).toRepresentation
                (finrank_eq_one_of_card_eq_prime (hBcard 0)) u)
        → u = 1) :
    ∃ ψ : U →* (Fin n → (ZMod p)ˣ), Function.Injective ψ :=
  ⟨blockScalarRatioHom (fun i => lineScalarChar (B i).toRepresentation
      (finrank_eq_one_of_card_eq_prime (hBcard i))),
    blockScalarRatioHom_injective _ hconst⟩

/-- The scalar-character identity on an order-`p` subrepresentation, viewed in the ambient
representation.  This avoids exposing the subtype module's implementation instances to callers
that assemble the block identities into an equality on the whole representation. -/
theorem lineScalarChar_smul_coe_of_card_eq_prime {p : ℕ} [Fact p.Prime]
    {U M : Type u} [Group U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    (ρ : Representation (ZMod p) U M) (B : Subrepresentation ρ)
    (hBcard : Nat.card B.toSubmodule = p) (u : U) (x : B) :
    ρ u x.1 =
      (lineScalarChar B.toRepresentation
        (finrank_eq_one_of_card_eq_prime hBcard) u : ZMod p) • x.1 := by
  change (↑(B.toRepresentation u x) : M) = _
  simpa using congrArg Subtype.val
    (lineScalarChar_smul B.toRepresentation
      (finrank_eq_one_of_card_eq_prime hBcard) u x)

/-- **Peterfalvi (9.7)(a), the book's `a`-form**: if all block scalars take values in one subgroup
`A ≤ 𝔽_p^×`, then `|U|` divides `|A|^n` and `|A|` divides `p − 1`.

The book puts `a = |U : C_U(H₁)|` and concludes that `U` embeds in a direct product of `q − 1`
cyclic groups of order `a`, with `a ∣ p − 1`.  Here `A` is that common image: for the `W₁`-permuted
blocks `H_i = H₁^{w_i}` the scalar characters all have the same image (conjugation by `w_i` is an
automorphism of `U`), so this hypothesis is exactly what the book's `{H_i} = {H₁^w | w ∈ W₁}`
supplies.  Taking `A = ⊤` recovers `card_dvd_pred_pow_of_blocks` (issue 0152). -/
theorem card_dvd_blockScalarOrder_pow_of_blocks {p : ℕ} [Fact p.Prime]
    {U M : Type u} [CommGroup U] [Finite U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    {n : ℕ} (ρ : Representation (ZMod p) U M) (B : Fin (n + 1) → Subrepresentation ρ)
    (hBcard : ∀ i, Nat.card (B i).toSubmodule = p)
    (A : Subgroup (ZMod p)ˣ)
    (hmem : ∀ (i : Fin (n + 1)) (u : U),
      lineScalarChar (B i).toRepresentation (finrank_eq_one_of_card_eq_prime (hBcard i)) u ∈ A)
    (hconst : ∀ u : U,
        (∀ i : Fin (n + 1),
          lineScalarChar (B i).toRepresentation (finrank_eq_one_of_card_eq_prime (hBcard i)) u
            = lineScalarChar (B 0).toRepresentation
                (finrank_eq_one_of_card_eq_prime (hBcard 0)) u)
        → u = 1) :
    Nat.card U ∣ Nat.card A ^ n ∧ Nat.card A ∣ p - 1 := by
  refine ⟨card_dvd_pow_card_of_block_scalars_mem
    (fun i => lineScalarChar (B i).toRepresentation
      (finrank_eq_one_of_card_eq_prime (hBcard i))) A hmem hconst, ?_⟩
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  exact hunits ▸ card_subgroup_dvd_card A

/-- **Peterfalvi (9.7)(a), the book's statement, from block equivalence.**  If every block scalar
character has the same range as block `0`'s — which is what the `W₁`-conjugacy `H_i = H₁^{w_i}`
gives, via `lineScalarChar_range_eq_of_equivariant` — then with
`a := |im φ_0| = |U : C_U(H₁)|`:

* `|U|` divides `a ^ n` (`n = q − 1`), i.e. `U` embeds in a product of `q − 1` cyclic groups of
  order `a`, since `im φ_0 ≤ 𝔽_p^×` is cyclic;
* `a` divides `p − 1`.

This is the sharpening of `card_dvd_pred_pow_of_blocks`, which only sees `p − 1` (issue 0152). -/
theorem card_dvd_blockScalarRange_pow_of_blocks {p : ℕ} [Fact p.Prime]
    {U M : Type u} [CommGroup U] [Finite U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    {n : ℕ} (ρ : Representation (ZMod p) U M) (B : Fin (n + 1) → Subrepresentation ρ)
    (hBcard : ∀ i, Nat.card (B i).toSubmodule = p)
    (hrange : ∀ i : Fin (n + 1),
      (lineScalarChar (B i).toRepresentation
        (finrank_eq_one_of_card_eq_prime (hBcard i))).range =
      (lineScalarChar (B 0).toRepresentation
        (finrank_eq_one_of_card_eq_prime (hBcard 0))).range)
    (hconst : ∀ u : U,
        (∀ i : Fin (n + 1),
          lineScalarChar (B i).toRepresentation (finrank_eq_one_of_card_eq_prime (hBcard i)) u
            = lineScalarChar (B 0).toRepresentation
                (finrank_eq_one_of_card_eq_prime (hBcard 0)) u)
        → u = 1) :
    Nat.card U ∣ Nat.card (lineScalarChar (B 0).toRepresentation
        (finrank_eq_one_of_card_eq_prime (hBcard 0))).range ^ n
      ∧ Nat.card (lineScalarChar (B 0).toRepresentation
        (finrank_eq_one_of_card_eq_prime (hBcard 0))).range ∣ p - 1 :=
  card_dvd_blockScalarOrder_pow_of_blocks ρ B hBcard _
    (fun i u => hrange i ▸ MonoidHom.mem_range.mpr ⟨u, rfl⟩) hconst

/-- **Peterfalvi (9.7)(a) from equal block-scalar *orders* alone.**  `𝔽_p^×` is cyclic, so two
subgroups of the same order coincide (`Subgroup.eq_of_card_eq_of_isCyclic`).  Hence it is enough to
know that every block scalar character has the *same image order* as block `0`'s — which is what
the `W₁`-conjugacy `H_i = H₁^{w_i}` gives directly, since conjugation by `w_i` is an automorphism
of `U` carrying `C_U(H₁)` onto `C_U(H_i)`, so the two indices agree.

This is the form the Section 11 case-(a) carrier can discharge without building an equivariant
isomorphism of the blocks as representations (issue 0152). -/
theorem card_dvd_blockScalarRange_pow_of_blocks_card_eq {p : ℕ} [Fact p.Prime]
    {U M : Type u} [CommGroup U] [Finite U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    {n : ℕ} (ρ : Representation (ZMod p) U M) (B : Fin (n + 1) → Subrepresentation ρ)
    (hBcard : ∀ i, Nat.card (B i).toSubmodule = p)
    (hcard : ∀ i : Fin (n + 1),
      Nat.card (lineScalarChar (B i).toRepresentation
        (finrank_eq_one_of_card_eq_prime (hBcard i))).range =
      Nat.card (lineScalarChar (B 0).toRepresentation
        (finrank_eq_one_of_card_eq_prime (hBcard 0))).range)
    (hconst : ∀ u : U,
        (∀ i : Fin (n + 1),
          lineScalarChar (B i).toRepresentation (finrank_eq_one_of_card_eq_prime (hBcard i)) u
            = lineScalarChar (B 0).toRepresentation
                (finrank_eq_one_of_card_eq_prime (hBcard 0)) u)
        → u = 1) :
    Nat.card U ∣ Nat.card (lineScalarChar (B 0).toRepresentation
        (finrank_eq_one_of_card_eq_prime (hBcard 0))).range ^ n
      ∧ Nat.card (lineScalarChar (B 0).toRepresentation
        (finrank_eq_one_of_card_eq_prime (hBcard 0))).range ∣ p - 1 :=
  card_dvd_blockScalarRange_pow_of_blocks ρ B hBcard
    (fun i => OddOrder.GroupTheory.Subgroup.eq_of_card_eq_of_isCyclic (hcard i)) hconst

/-- **Peterfalvi (9.7)(a), the two block-scalar conclusions in one call.**  Bundling the ratio
embedding with the book's `a`-form divisibility lets a caller discharge the (genuinely hard)
"no global scalar" hypothesis `hconst` **once**, in a `refine ... ?_ ?_` whose goals are elaborated
from this signature.

That matters in practice: hoisting `hconst` into a `have` on the caller's side makes Lean pick a
different route to `Semiring (ZMod p)` (via `CommRing` rather than `Field`) and the
`Representation` types stop matching.  Taking both conclusions here keeps every goal's elaboration
anchored to one signature (issue 0152). -/
theorem blockScalarFacts_of_blocks {p : ℕ} [Fact p.Prime]
    {U M : Type u} [CommGroup U] [Finite U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    {n : ℕ} (ρ : Representation (ZMod p) U M) (B : Fin (n + 1) → Subrepresentation ρ)
    (hBcard : ∀ i, Nat.card (B i).toSubmodule = p)
    (hcard : ∀ i : Fin (n + 1),
      Nat.card (lineScalarChar (B i).toRepresentation
        (finrank_eq_one_of_card_eq_prime (hBcard i))).range =
      Nat.card (lineScalarChar (B 0).toRepresentation
        (finrank_eq_one_of_card_eq_prime (hBcard 0))).range)
    (hconst : ∀ u : U,
        (∀ i : Fin (n + 1),
          lineScalarChar (B i).toRepresentation (finrank_eq_one_of_card_eq_prime (hBcard i)) u
            = lineScalarChar (B 0).toRepresentation
                (finrank_eq_one_of_card_eq_prime (hBcard 0)) u)
        → u = 1) :
    (∃ ψ : U →* (Fin n → (ZMod p)ˣ), Function.Injective ψ)
      ∧ Nat.card U ∣ Nat.card (lineScalarChar (B 0).toRepresentation
          (finrank_eq_one_of_card_eq_prime (hBcard 0))).range ^ n
      ∧ Nat.card (lineScalarChar (B 0).toRepresentation
          (finrank_eq_one_of_card_eq_prime (hBcard 0))).range ∣ p - 1 :=
  ⟨exists_blockScalarRatioEmbedding_of_blocks ρ B hBcard hconst,
    (card_dvd_blockScalarRange_pow_of_blocks_card_eq ρ B hBcard hcard hconst).1,
    (card_dvd_blockScalarRange_pow_of_blocks_card_eq ρ B hBcard hcard hconst).2⟩

/-- **The block-scalar order is the book's index `a = |U : C_U(H₁)|`.**  The kernel of a block
scalar character is the pointwise stabilizer of that block (`lineScalarChar_eq_one_iff`), so the
first isomorphism theorem identifies `|im φ_i|` with the index of the centralizer of the block --
exactly Peterfalvi's `a`. -/
theorem card_lineScalarChar_range_eq_index {p : ℕ} [Fact p.Prime]
    {U M : Type u} [CommGroup U] [Finite U] [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    (ρ : Representation (ZMod p) U M) (B : Subrepresentation ρ)
    (hBcard : Nat.card B.toSubmodule = p) :
    Nat.card (lineScalarChar B.toRepresentation
        (finrank_eq_one_of_card_eq_prime hBcard)).range
      = ((lineScalarChar B.toRepresentation
        (finrank_eq_one_of_card_eq_prime hBcard)).ker).index := by
  rw [← Subgroup.index_ker]

end OddOrder.RepresentationTheory

-- ===== OddOrder/GroupTheory/RepresentationTheory/AInvariantSubrep.lean =====
namespace OddOrder.GroupTheory

open OddOrder.Isaacs.Ch03

variable {A K : Type*} [Group A] [CommGroup K] {p : ℕ} [Module (ZMod p) (Additive K)]
  {φ : A →* MulAut K}

/-- The subrepresentation attached to a `φ`-invariant subgroup `J` has the same cardinality as `J`
(the carrier is `Additive.ofMul '' J`, in bijection with `J`).  Supplies the `hBcard` (each block
has order `p`) input of `card_le_cyclotomicQuotient_of_blocks`. -/
theorem card_aInvariantSubrep {J : Subgroup K} (hJ : IsAInvariant φ J) :
    Nat.card (aInvariantSubrep (p := p) hJ).toSubmodule = Nat.card J := by
  rw [aInvariantSubrep_toSubmodule]
  exact Nat.card_congr
    (Equiv.subtypeEquiv (Additive.toMul (α := K))
      (fun v => mem_symm_elabSubmoduleSubgroupEquiv J v))

/-- **The kernel of a block's scalar character is the pointwise stabiliser of that block.**

For an order-`p` (hence `𝔽_p`-line) `φ`-invariant subgroup `J`, an element of the acting group `A`
acts on `J` by the scalar `1` exactly when it fixes `J` elementwise, i.e. when it lies in
`Subgroup.ptStabOfMulAut φ J`.

This is the bridge that turns Peterfalvi (9.7)(a)'s block-scalar order `|im φ_J| = |A : ker φ_J|`
into the book's index `a = |U : C_U(H₁)|`, and lets the `W₁`-conjugacy of the blocks be applied
through `Subgroup.index_ptStabOfMulAut_smul` (issue 0152). -/
theorem ker_lineScalarChar_aInvariantSubrep [Fact p.Prime] [Finite K] {J : Subgroup K}
    (hJ : IsAInvariant φ J)
    (hcard : Nat.card (aInvariantSubrep (p := p) hJ).toSubmodule = p) :
    (OddOrder.RepresentationTheory.lineScalarChar
        (aInvariantSubrep (p := p) hJ).toRepresentation
        (OddOrder.RepresentationTheory.finrank_eq_one_of_card_eq_prime hcard)).ker
      = Subgroup.ptStabOfMulAut φ J := by
  ext a
  rw [MonoidHom.mem_ker, OddOrder.RepresentationTheory.lineScalarChar_eq_one_iff,
    Subgroup.mem_ptStabOfMulAut]
  constructor
  · intro h x hx
    have hmem : Additive.ofMul x ∈ (aInvariantSubrep (p := p) hJ).toSubmodule :=
      (mem_symm_elabSubmoduleSubgroupEquiv (p := p) J (Additive.ofMul x)).mpr (by simpa using hx)
    have := congrArg Subtype.val (h ⟨Additive.ofMul x, hmem⟩)
    change elabRepresentation p φ a (Additive.ofMul x) = Additive.ofMul x at this
    rw [elabRepresentation_apply] at this
    exact Additive.ofMul.injective this
  · intro h x
    refine Subtype.ext ?_
    have hx : Additive.toMul (x : Additive K) ∈ J :=
      (mem_symm_elabSubmoduleSubgroupEquiv (p := p) J (x : Additive K)).mp x.2
    change elabRepresentation p φ a (x : Additive K) = (x : Additive K)
    have := h _ hx
    change (φ a) (Additive.toMul (x : Additive K)) = Additive.toMul (x : Additive K) at this
    exact congrArg Additive.ofMul this

end OddOrder.GroupTheory

-- ===== OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean =====
namespace OddOrder.Peterfalvi.S11

open OddOrder.RepresentationTheory OddOrder.GroupTheory OddOrder.Isaacs.Ch03

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk')

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **A pointwise global `ZMod p`-scalar is central in `MulAut`.**  If `l` acts on every element as
the scalar `μ`, then `φ l` commutes with every automorphism of `V`: automorphisms are additive maps,
and additive maps commute with `ZMod p`-scalar multiplication (`ZMod.map_smul`). -/
theorem commute_mulAut_of_elabRepresentation_apply_eq_smul {p : ℕ} {L V : Type*} [Group L]
    [CommGroup V] [Module (ZMod p) (Additive V)] (φ : L →* MulAut V) (l : L) (μ : ZMod p)
    (happly : ∀ x : V, Additive.ofMul ((φ l) x) = μ • Additive.ofMul x) (σ : MulAut V) :
    Commute σ (φ l) := by
  have : σ * (φ l) = (φ l) * σ := by
    refine MulEquiv.ext fun x => ?_
    change σ ((φ l) x) = (φ l) (σ x)
    calc σ ((φ l) x)
        = Additive.toMul ((MulEquiv.toAdditive σ) (Additive.ofMul ((φ l) x))) := rfl
      _ = Additive.toMul ((MulEquiv.toAdditive σ) (μ • Additive.ofMul x)) := by rw [happly]
      _ = Additive.toMul (μ • (MulEquiv.toAdditive σ) (Additive.ofMul x)) := by
          rw [ZMod.map_smul]
      _ = Additive.toMul (μ • Additive.ofMul (σ x)) := rfl
      _ = Additive.toMul (Additive.ofMul ((φ l) (σ x))) := by rw [← happly]
      _ = (φ l) (σ x) := rfl
  exact this

/-- Unfolding `uActionHom` along the conjugation action of `L = U ⊔ W₁` on its normal subgroup
`U`: the action of a conjugate is the conjugate of the actions. -/
theorem uActionHom_conjNormal [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    (chief : ChiefFactorData data)
    [(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal]
    (l : ↥(data.typeP.U ⊔ data.typeP.W1))
    (x : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) :
    haveI : chief.N.Normal := chief.N_normal
    uActionHom data chief (MulAut.conjNormal l x)
      = quotientMulAutHom (N := chief.N) chief.N_aInvariant l
        * uActionHom data chief x
        * (quotientMulAutHom (N := chief.N) chief.N_aInvariant l)⁻¹ := by
  have : chief.N.Normal := chief.N_normal
  have hval : ((MulAut.conjNormal l x :
        ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) :
        ↥(data.typeP.U ⊔ data.typeP.W1))
      = l * (x : ↥(data.typeP.U ⊔ data.typeP.W1)) * l⁻¹ := MulAut.conjNormal_apply l x
  calc uActionHom data chief (MulAut.conjNormal l x)
      = quotientMulAutHom (N := chief.N) chief.N_aInvariant
          ((MulAut.conjNormal l x :
            ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) :
            ↥(data.typeP.U ⊔ data.typeP.W1)) := rfl
    _ = quotientMulAutHom (N := chief.N) chief.N_aInvariant
          (l * (x : ↥(data.typeP.U ⊔ data.typeP.W1)) * l⁻¹) := by rw [hval]
    _ = _ := by rw [map_mul, map_mul, map_inv]; rfl

/-- **The Frobenius fixed-point-freeness eliminates global scalars** (the multiplicative half of
the Coq `psi` injectivity, `PFsection9.v:442-484`).  If `g ∈ U` acts on the chief factor `H̄` by an
automorphism *central in `Aut(H̄)`* — e.g. a scalar power map — then it acts trivially.

Centrality makes the action of `g` invariant under `W̄₁`-conjugation, so the image `ḡ ∈ Ū = U/C`
lies in `C_Ū(W̄₁)`; the coprime fixed-point descent (Isaacs Cor 3.28,
`map_fixedSubgroup_eq_fixedSubgroup_quotient`) identifies `C_Ū(W̄₁)` with the image of `C_U(W₁)`,
which is trivial by the Frobenius fixed-point-freeness of `(U ⊔ W₁, U, W₁)`
(`typeP_uW1_frobenius`).  Hence `ḡ = 1`, i.e. `uActionHom g = 1`. -/
theorem uActionHom_eq_one_of_commute_mulAut [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (g : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
    (hcentral : ∀ σ : MulAut (↥data.H ⧸ chief.N), Commute (uActionHom data chief g) σ) :
    uActionHom data chief g = 1 := by
  have : chief.N.Normal := chief.N_normal
  have frob := typeP_uW1_frobenius data.typeP data.nontrivial.1
  have hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal := frob.isNormal
  -- The kernel `C = C_U(H̄)` of the `U`-action is invariant under `L`-conjugation.
  have hNinv : IsAInvariant
      (MulAut.conjNormal :
        ↥(data.typeP.U ⊔ data.typeP.W1)
          →* MulAut ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (uActionHom data chief).ker := by
    rw [isAInvariant_iff_smul_mem]
    intro l x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [uActionHom_conjNormal chief l x, hx, mul_one, mul_inv_cancel]
  -- Coprimality `|W₁| ⟂ |U|` and solvability of the cyclic `W₁`.
  have hCop : Nat.Coprime
      (Nat.card ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (Nat.card ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) :=
    frob.coprime_card_kernel_complement.symm
  have hXcyc : IsCyclic ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) := by
    have := data.typeP.W1_cyclic
    exact isCyclic_of_surjective _
      (Subgroup.subgroupOfEquivOfLe le_sup_right).symm.surjective
  have hSolv : Group.IsSolvable ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
      ∨ Group.IsSolvable ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) := by
    left
    let := hXcyc.commGroup
    infer_instance
  -- `C_U(W₁) = 1`: the Frobenius fixed-point-freeness.
  have hfixbot : fixedSubgroup
      (MulAut.conjNormal :
        ↥(data.typeP.U ⊔ data.typeP.W1)
          →* MulAut ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_fixedSubgroup] at hx
    rw [Subgroup.mem_bot]
    by_contra hxne
    obtain ⟨w, hwW1, hwne⟩ :=
      data.typeP.W1.bot_or_exists_ne_one.resolve_left data.typeP.W1_nontrivial
    have hŵX : (⟨w, Subgroup.mem_sup_right hwW1⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))
        ∈ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) :=
      Subgroup.mem_subgroupOf.mpr hwW1
    have hvaleq : (⟨w, Subgroup.mem_sup_right hwW1⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))
          * (x : ↥(data.typeP.U ⊔ data.typeP.W1))
          * (⟨w, Subgroup.mem_sup_right hwW1⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))⁻¹
        = (x : ↥(data.typeP.U ⊔ data.typeP.W1)) := by
      have h := congrArg Subtype.val (hx _ hŵX)
      rwa [MulAut.conjNormal_apply] at h
    exact frob.conj_frobenius _ hŵX (fun h => hwne (congrArg Subtype.val h))
      (x : ↥(data.typeP.U ⊔ data.typeP.W1)) x.2
      (fun h => hxne (OneMemClass.coe_eq_one.mp h)) hvaleq
  -- Descend: `C_Ū(W̄₁)` is the image of `C_U(W₁) = 1`.
  have hmap := map_fixedSubgroup_eq_fixedSubgroup_quotient hNinv hCop hSolv
  rw [hfixbot, Subgroup.map_bot] at hmap
  -- `ḡ` is `W̄₁`-fixed: centrality makes each `W₁`-conjugate of `g` agree with `g` mod `C`.
  have hgfix : QuotientGroup.mk' (uActionHom data chief).ker g
      ∈ fixedSubgroup (quotientMulAutHom hNinv)
        (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) := by
    rw [mem_fixedSubgroup]
    intro l hl
    rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_eq_mk']
    refine ⟨(MulAut.conjNormal l g)⁻¹ * g, ?_, mul_inv_cancel_left _ _⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, uActionHom_conjNormal chief l g,
      ← (hcentral (quotientMulAutHom (N := chief.N) chief.N_aInvariant l)).eq,
      mul_inv_cancel_right, inv_mul_cancel]
  rw [← hmap, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hgfix
  exact hgfix

/-- Invariance under a hom `φ` transfers to invariance under the range inclusion `φ.range.subtype`:
`Ū = φ.range` acts by the same automorphisms as the image of `φ`, so a `φ`-invariant subgroup is
`Ū`-invariant. -/
theorem isAInvariant_range_subtype {A K : Type*} [Group A] [Group K] {φ : A →* MulAut K}
    {J : Subgroup K} (hJ : IsAInvariant φ J) :
    IsAInvariant (MonoidHom.range φ).subtype J := by
  rw [isAInvariant_iff_smul_mem]
  rintro ⟨_, a, rfl⟩ g hg
  exact hJ.smul_mem a hg

/-- **The `U W₁`-action normalises the image `Ū` of the `U`-action** on the chief factor.

`uActionHom` is `quotientMulAutHom` restricted to `U ≤ U W₁`, and `U ⊴ U W₁` (the Frobenius
structure `typeP_uW1_frobenius`), so conjugating an element of `Ū` by the automorphism induced by
any `w ∈ U W₁` stays in `Ū`.

This is the input that makes Peterfalvi (9.7)(a)'s constant `a` independent of the block: the
blocks are the `W₁`-translates of `S₀`, and translation by `w` conjugates the pointwise stabiliser
`C_Ū(S₀)` onto `C_Ū(w • S₀)` inside `Ū`, so the two indices -- hence the two block-scalar orders --
agree (issue 0152). -/
theorem range_uActionHom_conj_mem [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) (w : ↥(data.typeP.U ⊔ data.typeP.W1))
    {u : MulAut (↥data.H ⧸ chief.N)} (hu : u ∈ MonoidHom.range (uActionHom data chief)) :
    quotientMulAutHom chief.N_aInvariant w * u *
        (quotientMulAutHom chief.N_aInvariant w)⁻¹
      ∈ MonoidHom.range (uActionHom data chief) := by
  have : chief.N.Normal := chief.N_normal
  have hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (typeP_uW1_frobenius data.typeP data.nontrivial.1).isNormal
  obtain ⟨v, rfl⟩ := hu
  refine ⟨⟨w * (v : ↥(data.typeP.U ⊔ data.typeP.W1)) * w⁻¹, ?_⟩, ?_⟩
  · exact hUnorm.conj_mem _ v.2 w
  · change quotientMulAutHom chief.N_aInvariant
        (w * (v : ↥(data.typeP.U ⊔ data.typeP.W1)) * w⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    rfl

/-- The inverse form of `range_uActionHom_conj_mem`, as required by
`Subgroup.index_ptStabOfMulAut_subtype_smul`. -/
theorem range_uActionHom_conj_inv_mem [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) (w : ↥(data.typeP.U ⊔ data.typeP.W1))
    {u : MulAut (↥data.H ⧸ chief.N)} (hu : u ∈ MonoidHom.range (uActionHom data chief)) :
    (quotientMulAutHom chief.N_aInvariant w)⁻¹ * u *
        quotientMulAutHom chief.N_aInvariant w
      ∈ MonoidHom.range (uActionHom data chief) := by
  have h := range_uActionHom_conj_mem data chief w⁻¹ hu
  rwa [map_inv, inv_inv] at h

open scoped Classical in
/-- **Peterfalvi (9.7.a), both block-scalar conclusions.**

1. The faithful image `Ū = U/C_U(H̄)` embeds into the product of `q - 1` copies of `(𝔽_p)ˣ`, via
   the normalized scalar ratio `ū ↦ (φ_{i+1}(ū) / φ_0(ū))_i` on the `q` order-`p` Clifford
   summands.  (Peterfalvi (14.6) restricts a Sylow subgroup along this map, which cardinality
   divisibility alone would not retain.)
2. **The book's `a`-form** (p. 51): there is an `a` dividing `p − 1` with `u ∣ a^{q−1}` -- i.e.
   `Ū` is a subgroup of a direct product of `q − 1` cyclic groups of order `a`, where
   `a = |U : C_U(H₁)|` is the common block-scalar order.

Conclusion 2 is what the earlier `caseA_u_dvd_pred_pow` only saw through the coarser `p − 1`.  It
holds because the blocks are the `W₁`-translates `Hpart j = w_j • S₀`: `w_j` normalises `Ū`
(`range_uActionHom_conj_mem`), so the pointwise stabilisers `C_Ū(Hpart j)` are `Ū`-conjugate and
have equal index (`Subgroup.index_ptStabOfMulAut_subtype_smul`), hence all block-scalar characters
have images of the same order -- and in the cyclic `(𝔽_p)ˣ` equal order forces equal image
(issue 0152).

Both are produced by one call to `blockScalarFacts_of_blocks`, so the genuinely hard §9 crux
(no nonidentity `ū` acts by one common scalar on every block) is discharged once. -/
theorem _root_.solution [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    (∃ ψ : ↥(MonoidHom.range (uActionHom data chief)) →*
        (Fin (data.q - 1) → (ZMod chief.p)ˣ),
      Function.Injective ψ) ∧ ∃ a : ℕ, a ∣ chief.p - 1 ∧ chars.u ∣ a ^ (data.q - 1) := by
  have : Fact chief.p.Prime := ⟨chief.p_prime⟩
  have : chief.N.Normal := chief.N_normal
  -- Build the vector-space structure over the canonical quotient-group instance, so the
  -- `MulAut H̄` used by `uActionHom` and by `elabRepresentation` agrees definitionally.
  let : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.comm }
  let : Module (ZMod chief.p) (Additive (↥data.H ⧸ chief.N)) :=
    chief.quotient_elementaryAbelian.zmodModule
  have : Finite ↥(MonoidHom.range (uActionHom data chief)) := inferInstance
  let : CommGroup ↥(MonoidHom.range (uActionHom data chief)) :=
    { (inferInstance : Group ↥(MonoidHom.range (uActionHom data chief))) with
      mul_comm := uActionHom_range_comm chief }
  have hq1 : (data.q - 1) + 1 = data.q := Nat.sub_add_cancel data.nontrivial.2.1.pos
  have key := blockScalarFacts_of_blocks (p := chief.p) (n := data.q - 1)
    (elabRepresentation chief.p (MonoidHom.range (uActionHom data chief)).subtype)
    (fun i => aInvariantSubrep
      (isAInvariant_range_subtype (caseA.Hpart_aInvariant (finCongr hq1 i))))
    (fun i => (card_aInvariantSubrep _).trans
      (caseA.Hpart_order (finCongr hq1 i)))
    (by
    -- **Block-scalar orders agree** (Peterfalvi (9.7)(a)'s `a` is independent of the block): the
    -- blocks are the `W₁`-translates `Hpart j = w_j • S₀`, and `w_j` normalises `Ū`, so the
    -- pointwise stabilisers `C_Ū(Hpart j)` are `Ū`-conjugate and have equal index.
      intro i
      rw [card_lineScalarChar_range_eq_index, card_lineScalarChar_range_eq_index,
        ker_lineScalarChar_aInvariantSubrep, ker_lineScalarChar_aInvariantSubrep,
        caseA.Hpart_orbit, caseA.Hpart_orbit,
        Subgroup.index_ptStabOfMulAut_subtype_smul _ _ _
          (fun _ hu => range_uActionHom_conj_mem data chief _ hu)
          (fun _ hu => range_uActionHom_conj_inv_mem data chief _ hu),
        Subgroup.index_ptStabOfMulAut_subtype_smul _ _ _
          (fun _ hu => range_uActionHom_conj_mem data chief _ hu)
          (fun _ hu => range_uActionHom_conj_inv_mem data chief _ hu)]
      all_goals exact (card_aInvariantSubrep _).trans (caseA.Hpart_order _)
    -- **The genuine §9 crux** (Coq `psi`, `PFsection9.v:442-484`): no nonidentity
    -- `ū ∈ Ū` acts by one common scalar on every block.
      )
    (by
      intro u hscal
      let B := fun i : Fin ((data.q - 1) + 1) =>
        aInvariantSubrep (p := chief.p)
          (φ := (MonoidHom.range (uActionHom data chief)).subtype)
          (isAInvariant_range_subtype (caseA.Hpart_aInvariant (finCongr hq1 i)))
      let μ : (ZMod chief.p)ˣ := lineScalarChar (B 0).toRepresentation
        (finrank_eq_one_of_card_eq_prime
          ((card_aInvariantSubrep _).trans
            (caseA.Hpart_order (finCongr hq1 0)))) u
      have hscalB : ∀ i, lineScalarChar (B i).toRepresentation
          (finrank_eq_one_of_card_eq_prime
            ((card_aInvariantSubrep _).trans
              (caseA.Hpart_order (finCongr hq1 i)))) u = μ := by
        intro i
        simpa only [B, μ] using hscal i
      -- On each Clifford summand, the action is the common scalar `μ`.
      have hblock (i : Fin ((data.q - 1) + 1)) (x : ↥data.H ⧸ chief.N)
          (hx : x ∈ caseA.Hpart (finCongr hq1 i)) :
          (elabRepresentation chief.p
              (MonoidHom.range (uActionHom data chief)).subtype u).toFun
              (Additive.ofMul x) = (μ : ZMod chief.p) • Additive.ofMul x := by
        have hxB : Additive.ofMul x ∈
            (B i).toSubmodule.carrier := by
          have hm := (mem_symm_elabSubmoduleSubgroupEquiv (p := chief.p)
            (caseA.Hpart (finCongr hq1 i)) (Additive.ofMul x)).mpr (by simpa using hx)
          exact hm
        have hs := lineScalarChar_smul_coe_of_card_eq_prime
          (elabRepresentation chief.p
            (MonoidHom.range (uActionHom data chief)).subtype) (B i)
          ((card_aInvariantSubrep _).trans
            (caseA.Hpart_order (finCongr hq1 i))) u
          ⟨Additive.ofMul x, hxB⟩
        rw [hscalB i] at hs
        exact hs
      -- The summands span `H̄`; subgroup induction extends the scalar identity to every vector.
      have hpoint : ∀ x : ↥data.H ⧸ chief.N,
          (elabRepresentation chief.p
              (MonoidHom.range (uActionHom data chief)).subtype u).toFun
              (Additive.ofMul x) = (μ : ZMod chief.p) • Additive.ofMul x := by
        intro x
        have hre : ⨆ i : Fin ((data.q - 1) + 1), caseA.Hpart (finCongr hq1 i) = ⊤ := by
          rw [Equiv.iSup_comp (finCongr hq1) (g := caseA.Hpart)]
          exact caseA.Hpart_iSup
        have hx : x ∈ ⨆ i : Fin ((data.q - 1) + 1),
            caseA.Hpart (finCongr hq1 i) := hre ▸ Subgroup.mem_top x
        refine Subgroup.iSup_induction
          (C := fun z =>
            (elabRepresentation chief.p
                (MonoidHom.range (uActionHom data chief)).subtype u).toFun
                (Additive.ofMul z) = (μ : ZMod chief.p) • Additive.ofMul z)
          (fun i => caseA.Hpart (finCongr hq1 i)) hx hblock ?_ ?_
        · simp
        · intro a b ha hb
          change
            (elabRepresentation chief.p
                (MonoidHom.range (uActionHom data chief)).subtype u).toFun
                (Additive.ofMul a + Additive.ofMul b)
              = (μ : ZMod chief.p) • (Additive.ofMul a + Additive.ofMul b)
          calc
            _ = (elabRepresentation chief.p
                  (MonoidHom.range (uActionHom data chief)).subtype u).toFun (Additive.ofMul a)
                + (elabRepresentation chief.p
                  (MonoidHom.range (uActionHom data chief)).subtype u).toFun
                    (Additive.ofMul b) :=
                (elabRepresentation chief.p
                  (MonoidHom.range (uActionHom data chief)).subtype u).map_add _ _
            _ = (μ : ZMod chief.p) • Additive.ofMul a
                + (μ : ZMod chief.p) • Additive.ofMul b := by rw [ha, hb]
            _ = (μ : ZMod chief.p) • (Additive.ofMul a + Additive.ofMul b) :=
                (smul_add _ _ _).symm
      -- A global scalar is central in `MulAut(H̄)`; Frobenius fpf forces `u = 1`.
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp u.2
      have hone : uActionHom data chief g = 1 :=
        uActionHom_eq_one_of_commute_mulAut chief g (fun σ => by
          rw [hg]
          exact (commute_mulAut_of_elabRepresentation_apply_eq_smul
            (MonoidHom.range (uActionHom data chief)).subtype u (μ : ZMod chief.p)
            (fun x => by simpa [elabRepresentation_apply] using hpoint x) σ).symm)
      exact Subtype.ext (hg ▸ hone)
      )
  exact ⟨key.1, _, key.2.2, by rw [chars.u_eq_card_quotient]; exact key.2.1⟩

end OddOrder.Peterfalvi.S11

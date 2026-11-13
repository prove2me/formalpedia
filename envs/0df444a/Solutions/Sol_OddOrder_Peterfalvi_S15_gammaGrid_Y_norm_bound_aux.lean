-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.gammaGrid_Y_norm_bound_aux
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:22:30.688001+00:00
-- url     : https://prove2.me/submissions/9ba2fbd5-a8f4-4e27-a447-c00cd9e19553

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/IsReal.lean
--   OddOrder/GroupTheory/RepresentationTheory/InflationInduction.lean
--   OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean
--   OddOrder/Peterfalvi/S15_BridgeCharacter.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Theorems.Thm_OddOrder_Peterfalvi_S15_gammaGrid_real_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_betaGrid_support_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_indPW1_inner_self_aux

-- ===== OddOrder/GroupTheory/RepresentationTheory/IsReal.lean =====
namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {G : Type*} [Group G] {k : Type*} [CommRing k] [StarRing k]

section InnerConj

variable [Fintype G]

/-- Conjugating both arguments of the class-function inner product swaps them:
`⟨φ̄, ψ̄⟩ = ⟨ψ, φ⟩` (equivalently `⟨φ̄, ψ̄⟩ = star ⟨φ, ψ⟩` via `inner_star_comm`). -/
theorem inner_conj_conj [Invertible (Nat.card G : k)] (φ ψ : ClassFunction G k) :
    ClassFunction.inner φ.conj ψ.conj = ClassFunction.inner ψ φ := by
  rw [ClassFunction.inner, ClassFunction.inner, ClassFunction.innerSum,
    ClassFunction.innerSum]
  congr 1
  exact Finset.sum_congr rfl fun g _ => by
    rw [conj_apply, conj_apply, star_star, mul_comm]

/-- Over `ℂ`, the self inner product `⟨φ, φ⟩` is the manifestly real (and nonnegative) value
`|G|⁻¹ · ∑ |φ(g)|²`. -/
theorem inner_self_eq_ofReal [Invertible (Nat.card G : ℂ)] (φ : ClassFunction G ℂ) :
    ClassFunction.inner φ φ
      = (((Nat.card G : ℝ)⁻¹ * ∑ g : G, Complex.normSq (φ g) : ℝ) : ℂ) := by
  rw [ClassFunction.inner, ClassFunction.innerSum, invOf_eq_inv]
  have hterm : ∀ g : G, φ g * star (φ g) = ((Complex.normSq (φ g) : ℝ) : ℂ) := fun g => by
    rw [show star (φ g) = starRingEnd ℂ (φ g) from rfl, Complex.mul_conj]
  simp only [hterm]
  push_cast
  ring

/-- The self inner product has nonnegative real part. -/
theorem inner_self_re_nonneg [Invertible (Nat.card G : ℂ)] (φ : ClassFunction G ℂ) :
    0 ≤ (ClassFunction.inner φ φ).re := by
  rw [inner_self_eq_ofReal, Complex.ofReal_re]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun g _ => Complex.normSq_nonneg _)

/-- The self inner product is real: it equals the `ℂ`-cast of its own real part. -/
theorem inner_self_eq_re [Invertible (Nat.card G : ℂ)] (φ : ClassFunction G ℂ) :
    ClassFunction.inner φ φ = ((ClassFunction.inner φ φ).re : ℂ) := by
  rw [inner_self_eq_ofReal]
  simp

end InnerConj

end ClassFunction

end OddOrder.RepresentationTheory

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

open scoped Classical in
/-- **P3 — inflated class functions are orthogonal to irreducibles not killing `N`.**  For `N ⊴ G`,
any class function `φ` of `G ⧸ N` inflates to something orthogonal to every irreducible character
`ψ` of `G` whose kernel does **not** contain `N`: `⟨φ ∘ mk', ψ⟩_G = 0`.

Peterfalvi's "(13.18.b) `Ind_{PW₁}^S 1 ⊥ μ_{0j}` because `P ⊄ ker μ_{0j}`": expand `φ` in the
`Irr(G ⧸ N)` basis (`sum_inner_irreducibleCharacter_smul`); each `compHom (mk' N) χ̄` is the
irreducible `inflate N χ̄` with `N ⊆ ker` (`subset_characterKernel_inflate`), so it differs from `ψ`
(which has `N ⊄ ker`) and is orthogonal to it (`irreducibleCharacter_inner_eq_ite`). -/
theorem inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker {N : Subgroup G} [N.Normal]
    [Fintype G] [Finite (G ⧸ N)] [Finite (IrreducibleCharacter (G ⧸ N))]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card (G ⧸ N) : ℂ)]
    (φ : ClassFunction (G ⧸ N) ℂ) (ψ : IrreducibleCharacter G)
    (hψ : ¬ ((N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction G ℂ))) :
    ClassFunction.inner (ClassFunction.compHom (QuotientGroup.mk' N) φ)
        (ψ : ClassFunction G ℂ) = 0 := by
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have : Fintype (IrreducibleCharacter (G ⧸ N)) := Fintype.ofFinite _
  have compHom_sum : ∀ (s : Finset (IrreducibleCharacter (G ⧸ N)))
      (a : IrreducibleCharacter (G ⧸ N) → ℂ),
      ClassFunction.compHom (QuotientGroup.mk' N)
          (∑ χ ∈ s, a χ • (χ : ClassFunction (G ⧸ N) ℂ))
        = ∑ χ ∈ s, a χ •
            ClassFunction.compHom (QuotientGroup.mk' N) (χ : ClassFunction (G ⧸ N) ℂ) := by
    intro s a
    induction s using Finset.induction with
    | empty => simp [ClassFunction.compHom_zero]
    | @insert χ s hχ ih =>
        rw [Finset.sum_insert hχ, ClassFunction.compHom_add, ClassFunction.compHom_smul, ih,
          Finset.sum_insert hχ]
  conv_lhs => rw [← sum_inner_irreducibleCharacter_smul φ, compHom_sum]
  rw [inner_sum_left]
  refine Finset.sum_eq_zero (fun χ _ => ?_)
  have hne : inflate N χ ≠ ψ := fun heq =>
    hψ (heq ▸ subset_characterKernel_inflate N χ)
  rw [ClassFunction.inner_smul_left, ← inflate_coe N χ, irreducibleCharacter_inner_eq_ite,
    if_neg hne, mul_zero]

end OddOrder.RepresentationTheory

-- ===== OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **(13.18.b), Frobenius half**: `‖Ind_{PW₁}^S 1‖²_S = (u−1)/q + 1`.

By the inflation `Ind_{PW₁}^S 1 = Ind_{W̄₁}^{S̄} 1` inflated through `P` (P2
`induce_one_eq_compHom_induce_one_of_le` + P1 `inner_compHom_mk'_eq`), its `S`-norm equals
`‖Ind_{W̄₁}^{S̄} 1‖²` in the Frobenius quotient `S̄ = S/P ≅ U⋊W₁` (`uW1_isComplement_P` transported
by `isFrobeniusGroup_map_equiv`), which `norm_induce_one_frobenius` evaluates to
`(|U|−1)/|W₁| + 1 = (u−1)/q + 1` (using `c = 1`, Pf (13.12), so `|U| = u`).  The
`FiniteInduce`-instance content is `indPW1_inner_self_aux`; here we bridge to the caller's
`Fintype`/`Invertible` instances (both `Subsingleton`). -/
theorem indPW1_inner_self_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) := by
  intro _ _
  convert indPW1_inner_self_aux _hG hyp hc1 using 2
  exact Subsingleton.elim _ _

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_BridgeCharacter.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`P ⊄ ker μ_{0j}`** (Pf (13.18.b) kernel step, `S`-side).  For `j ≠ 0`, the base-row grid
irreducible `μ_{0j}` does not have the Fitting kernel `P` in its character kernel.

Contrapositive of Peterfalvi's argument (mirroring `PrimeTIResidue.constituent_P_not_subset_ker`):
if `P ⊆ ker μ_{0j}` then `W₂ ⊆ P ⊆ ker μ_{0j}`, so `Res_{S'} μ_{0j}` is trivial on the `W₂`-part
(`characterKernel_restrict_subgroupOf`); its constituent `ψ` — the (4.5.a) source of
`μ_j = ∑_i μ_{ij} = Ind_{S'} ψ`, with `⟨Res_{S'} μ_{0j}, ψ⟩ = 1` by Frobenius reciprocity — inherits
that kernel containment (`characterKernel_subset_of_isCharacter_of_inner_ne_zero`), contradicting
the
`mu_colSum_eq_induce` clause `W₂ ⊄ ker ψ`. -/
theorem P_not_subset_characterKernel_mu [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)) := by
  classical
  set μ0 := hyp.mu ⟨0, hyp.q_prime.pos⟩ j with hμ0
  have hW2_le_P : hyp.W2 ≤ hyp.P := by
    have h := hyp.Sdata.W2_le
    rw [hyp.Sdata_W2_eq, hyp.Sdata.H_eq, ← hyp.P_eq_SF] at h
    exact h.trans inf_le_left
  intro hPker
  obtain ⟨psiS, hpsiIrr, hpsiInd, hpsiW2⟩ := hyp.mu_colSum_eq_induce j
  have hj' : j ≠ ⟨0, hyp.p_prime.pos⟩ := fun h => hj (by rw [h])
  have hW2notpsi := hpsiW2 hj'
  have hW2Sker : (hyp.W2.subgroupOf hyp.S : Set ↥hyp.S) ⊆
      OddOrder.Peterfalvi.S03.characterKernel μ0 :=
    fun x hx => hPker (Subgroup.comap_mono hW2_le_P hx)
  have hRker := OddOrder.Peterfalvi.S08.characterKernel_restrict_subgroupOf
    ((derivedInG hyp.S).subgroupOf hyp.S) hW2Sker
  have hResChar := OddOrder.Peterfalvi.S08.isCharacter_restrict
    (hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j).isCharacter
    ((derivedInG hyp.S).subgroupOf hyp.S)
  -- `⟨∑_i μ_{ij}, μ_{0j}⟩ = 1` (orthonormality: only the `i = 0` term survives).
  have hmul : ClassFunction.inner (∑ i, hyp.mu i j) μ0 = 1 := by
    rw [inner_sum_left]
    refine (Finset.sum_eq_single ⟨0, hyp.q_prime.pos⟩ (fun i _ hi => ?_)
      (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨hyp.mu i j, hyp.mu_irreducible i j⟩ : IrreducibleCharacter ↥hyp.S)
        ⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
      rw [if_neg (fun heq => hi (hyp.mu_col_injective j
        (congrArg (fun χ : IrreducibleCharacter ↥hyp.S => (χ : ClassFunction ↥hyp.S ℂ)) heq)))] at h
      exact h
    · have h := irreducibleCharacter_inner_eq_ite
        (⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩ : IrreducibleCharacter ↥hyp.S)
        ⟨μ0, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
      simpa using h
  have hfrob := ClassFunction.inner_induce_eq_inner_restrict
    ((derivedInG hyp.S).subgroupOf hyp.S) psiS μ0
  rw [← hpsiInd, hmul] at hfrob
  have hinner : ClassFunction.inner
      (ClassFunction.restrict ((derivedInG hyp.S).subgroupOf hyp.S) μ0) psiS ≠ 0 := by
    rw [RepresentationTheory.inner_conj_symm, ← hfrob]; simp
  exact hW2notpsi (fun x hx =>
    OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
      hResChar hpsiIrr hinner (hRker hx))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.b) orthogonality half** (`FiniteInduce`-instance form). -/
private theorem indPW1_inner_mu_aux [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
      ClassFunction.inner (indPW1 hyp) (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
  classical
  have hP_le_S : hyp.P ≤ hyp.S :=
    (by rw [hyp.S_deriv_eq_PU]; exact le_sup_left : hyp.P ≤ derivedInG hyp.S).trans
      (Subgroup.map_subtype_le _)
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  have hNA : hyp.P.subgroupOf hyp.S ≤ (hyp.P ⊔ hyp.W1).subgroupOf hyp.S :=
    Subgroup.comap_mono le_sup_left
  rw [show indPW1 hyp = ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
        (trivialClassFunction _) from rfl,
    OddOrder.RepresentationTheory.induce_one_eq_compHom_induce_one_of_le hNA]
  exact OddOrder.RepresentationTheory.inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker _
    ⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ j, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩
    (P_not_subset_characterKernel_mu _hG hyp j hj)

/-- **(13.18.b), orthogonality half**: `⟨Ind_{PW₁}^S 1, μ_{0j}⟩ = 0` for `j ≠ 0`.

`Ind_{PW₁}^S 1 = (Ind_{Ā}^{S̄} 1) ∘ mk'` (P2) is inflated from `S̄ = S/P`, so all its irreducible
constituents kill `P`; `μ_{0j}` does not (`P_not_subset_characterKernel_mu`), so they are orthogonal
(`inner_compHom_mk'_irreducible_eq_zero_of_not_subset_ker`).  `_aux` carries the `FiniteInduce`
instances; the wrapper bridges to the caller's (`Subsingleton`). -/
theorem indPW1_inner_mu [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (indPW1 hyp) (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
  intro _ _
  convert indPW1_inner_mu_aux _hG hyp j _hj using 2
  exact Subsingleton.elim _ _

/-- **(13.18.b) norm**: `‖β_j‖²_S = (u−1)/q + 2`.

Genuine reduction: `β_j = Ind_{PW₁}^S 1 − μ_{0j}`, so by bilinearity
`‖β_j‖² = ‖Ind‖² − ⟨Ind,μ_{0j}⟩ − ⟨μ_{0j},Ind⟩ + ‖μ_{0j}‖²`.  Here `‖μ_{0j}‖² = 1` is **proven**
from `hyp.mu_irreducible` (via `irreducibleCharacter_inner_eq_ite`), `⟨μ_{0j},Ind⟩ = 0` follows
from `⟨Ind,μ_{0j}⟩ = 0` by conjugate symmetry, and the remaining `‖Ind‖² = (u−1)/q + 1`
(`indPW1_inner_self`) and `⟨Ind,μ_{0j}⟩ = 0` (`indPW1_inner_mu`) are the isolated §13 obligations.
`(u−1)/q + 1 + 1 = (u−1)/q + 2`. -/
theorem betaGrid_norm_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    ∀ [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)],
      ClassFunction.inner (betaGrid hyp j) (betaGrid hyp j)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ) := by
  intro _ _
  set μ := hyp.mu ⟨0, hyp.q_prime.pos⟩ j with hμdef
  have hμμ : ClassFunction.inner μ μ = 1 := by
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨μ, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      (⟨μ, hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ j⟩)
    simpa using hite
  have hIμ : ClassFunction.inner (indPW1 hyp) μ = 0 := indPW1_inner_mu hG hyp j hj
  have hμI : ClassFunction.inner μ (indPW1 hyp) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hIμ, star_zero]
  have hII : ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
      = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) :=
    indPW1_inner_self_of_c_eq_one hG hyp hc1
  have hbeta : betaGrid hyp j = indPW1 hyp - μ := rfl
  rw [hbeta, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hII, hIμ, hμI, hμμ]
  push_cast
  ring

/-- **The Coq `A0beta` inclusion `P^# ∪ V_S ⊆ 'A0(S)`** (the final step of (13.18.a)): the sharp
Fitting kernel `P^#` and the `S`-class-closure of the cyclic-TI set `V = W − (W₁ ∪ W₂)` both land
in the honest `A₀(S) = A(S) ∪ V^S`.  The `V^S` part is the definitional right component (after the
`Sdata.W1/W2` synchronization); `P^#` lands in `A(S) = centralizerSupport (S_σ^#) S'` because
`P = S_F ≤ S_σ` (`maxNilpotentNormalHall_le_Msigma`, every maximal — general type `P`),
`P ≤ S' = P ⊔ U`, and every element self-centralizes. -/
theorem sharpP_union_V_subset_A0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    sharpSubgroup hyp.P ∪
        conjClassSetIn hyp.S (typePV hyp.S hyp.Sdata)
      ⊆ S10.typePACore0 hyp.S hyp.Sdata := by
  have hPle_Ms : hyp.P ≤ OddOrder.BG.Ch3.S10.Msigma hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.S_maximal
  intro z hz
  rcases hz with hzP | hzV
  · -- `P^# ⊆ A(S) ⊆ A₀(S)`.
    refine S10.typePACore_subset_A0Set hyp.Sdata ?_
    obtain ⟨hzP_mem, hz1⟩ := hzP
    rw [Set.mem_singleton_iff] at hz1
    refine S10.mem_typePACore.mpr ⟨?_, hz1, z, ⟨hPle_Ms hzP_mem, ?_⟩, ?_⟩
    · have hPle : hyp.P ≤ derivedInG hyp.S := by
        rw [hyp.S_deriv_eq_PU]; exact le_sup_left
      exact hPle hzP_mem
    · rwa [Set.mem_singleton_iff]
    · exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
        rw [Set.mem_singleton_iff] at hw; subst hw; rfl
  · exact Set.mem_union_right _ hzV

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.a), `'A0(S)`-support form**: `supp(β_j) ⊆ 'A0(S)` for `j ≠ 0`.

The Coq `A0beta` (`PFsection13.v:1870`), obtained from `PVSbeta` (`β_j ∈ 'CF(S, P^# ∪ V_S)`,
`PFsection13.v:1833`) via `P^# ∪ V_S ⊆ 'A0(S)`.  `PVSbeta` cancels the induced permutation character
`Ind_{PW₁}^S 1` against `μ_{0j}` off `P^# ∪ V_S`, using the `W₁`-class `normedTI` structure in
`S̄ = S/P = Ū ⋊ W̄₁` (Coq `gammaW1`) together with the prime-`TI` residue value `prTIirr_id`; both
bottom out at the shared prime-`TI` residue content (issue 9014) that connects the free `μ`-grid to
the σ-residue theory.  **This single `'A0`-support obligation is what both
`gammaGrid_orthogonal_one`
and `gammaGrid_Y_norm_bound` reduce to** (the honest `'A0`-Dade=Ind bridge
`sInstance_dade0_eq_induce`, issue 9076, then discharges the remaining Dade content). -/
theorem betaGrid_A0_support_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    (betaGrid hyp j).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S hyp.Sdata) hyp.S := by
  intro z hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  exact sharpP_union_V_subset_A0 hG hyp (betaGrid_support_of_c_eq_one hG hyp hc1 j hj hz)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c)** `⟨Γ, 1_G⟩ = 0`.

**De-scaffolded** (issue 9076): the `'A0(S)` `normedTI` content the old docstring flagged as
"missing" is now supplied by the honest `'A0`-Dade=Ind bridge `sInstance_dade0_eq_induce`.
Reduction
(Coq `oGamma1`): `⟨Γ,1⟩ = ⟨τ_S β_{#1},1⟩ − ⟨1,1⟩ + ⟨η_{01},1⟩`, and
* `⟨1,1⟩ = 1` (`constOne_inner_self_eq_one`);
* `⟨η_{01},1⟩ = 0` — grid orthogonality: `1_G = η_{00}` (`eta_principal_eq_trivial`) and `η_{01} ⊥
  η_{00}` (`eta_orthonormal`);
* `⟨τ_S β_{#1},1_G⟩ = 1` — the bridge gives `τ_S β_{#1} = Ind_S^G β_{#1}` (needs `β_{#1}` supported
in
  `'A0(S)`, `betaGrid_A0_support`), so by Frobenius reciprocity (`inner_induce_eq_inner_restrict`)
  `⟨Ind_S^G β_{#1}, 1_G⟩ = ⟨β_{#1}, 1_S⟩ = ⟨Ind_{PW₁}^S 1, 1_S⟩ − ⟨μ_{01}, 1_S⟩ = 1 − 0`, where
  `⟨Ind 1, 1_S⟩ = 1` (`inner_induce_trivialChar_constOne_eq_one`) and `⟨μ_{01}, 1_S⟩ = 0` (`μ_{01}`
  irreducible and `≠ 1_S`, since `⟨Ind 1, μ_{01}⟩ = 0 ≠ 1`, `indPW1_inner_mu`).

The **single** remaining gate is `betaGrid_A0_support` (the (13.18.a) `'A0`-support). -/
private theorem gammaGrid_orthogonal_one_aux [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    ClassFunction.inner (GammaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
  classical
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Fintype ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `⟨Ind_{PW₁}^S 1, 1_S⟩ = 1`.
  have hind : ClassFunction.inner (indPW1 hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S)) = 1 := by
    rw [indPW1, ←
        OddOrder.RepresentationTheory.IrreducibleCharacter.coe_trivialIrreducibleCharacter]
    exact OddOrder.Peterfalvi.S09.Cert.inner_induce_trivialChar_constOne_eq_one
      ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
  -- `⟨μ_{01}, 1_S⟩ = 0`: `μ_{01}` is irreducible and `≠ 1_S` (else `⟨Ind 1, μ_{01}⟩ = 1 ≠ 0`).
  have hmu : ClassFunction.inner
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S)) = 0 := by
    have hIμ : ClassFunction.inner (indPW1 hyp)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 :=
      indPW1_inner_mu hG hyp ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)
    have hne : (⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩,
          hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩⟩ :
          OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
        ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥hyp.S := by
      intro heq
      apply one_ne_zero (α := ℂ)
      have hcf : hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
          = OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S) :=
        congrArg (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S =>
          (χ : ClassFunction ↥hyp.S ℂ)) heq
      rw [hcf, hind] at hIμ
      exact hIμ
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩,
        hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥hyp.S)
    rw [if_neg hne] at hite
    exact hite
  -- `⟨τ_S(β_{#1}), 1_G⟩ = 1` via the `'A0`-Dade=Ind bridge + Frobenius reciprocity.
  have htau : ClassFunction.inner (tauSbetaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 1 := by
    have hbridge : tauSbetaGrid hG hyp
        = ClassFunction.induce hyp.S (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩) := by
      rw [tauSbetaGrid]
      exact hyp.sInstance_dade0_eq_induce hG hnoV
        (betaGrid_A0_support_of_c_eq_one hG hyp hc1
          ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num))
    rw [hbridge, ClassFunction.inner_induce_eq_inner_restrict]
    have hres : ClassFunction.restrict hyp.S
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
        = OddOrder.Peterfalvi.S09.Hypothesis71.constOne (↥hyp.S) := by
      ext x; rw [ClassFunction.restrict_apply]; rfl
    rw [hres]
    simp only [betaGrid]
    rw [ClassFunction.inner_sub_left, hind, hmu, sub_zero]
  -- `⟨η_{01}, 1_G⟩ = 0`.
  have heta : ClassFunction.inner
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
    have h00 : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ := by
      rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]; rfl
    rw [h00]
    have horth := OddOrder.Peterfalvi.S16.eta_orthonormal hyp
      ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.q_prime.pos⟩
      ⟨1, by have := hyp.three_le_p; omega⟩ ⟨0, hyp.p_prime.pos⟩
    rw [if_neg (by rintro ⟨-, h2⟩; exact absurd (congrArg Fin.val h2) (by norm_num))] at horth
    exact horth
  rw [GammaGrid, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one, htau, heta]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c)** `⟨Γ, 1_G⟩ = 0` (public form).  Thin wrapper over `gammaGrid_orthogonal_one_aux`
that reconciles the caller's `Fintype G`/`Invertible (Nat.card G : ℂ)` instances with the
`FiniteInduce`-scoped ones the core proof uses (both are `Subsingleton`). -/
theorem gammaGrid_orthogonal_one_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ClassFunction.inner (GammaGrid hG hyp)
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
  intro _ _
  convert gammaGrid_orthogonal_one_aux hG hnoV hyp hc1 using 2; exact Subsingleton.elim _ _

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (13.18) residual `Γ` is a virtual character**: each constituent of
`Γ = τ_S(β_{#1}) − 1_G + η_{01}` lies in `ℤ[Irr G]` — the Dade image via the `'A0` Dade=Ind
bridge (`sInstance_dade0_eq_induce` + `induce_mem_ZIrr`, with `β_{#1} ∈ ℤ[Irr S]` from
`induce_mem_ZIrr` on the trivial character and irreducibility of `μ_{01}`), the trivial
character, and `η_{01} = τ₃(ω_{01})` (`tau3_mem_ZIrr` + `omega_mem_ZIrr`).  Feeds the
integrality of `⟨Γ, η_{01}⟩` in the (13.18.d) bound. -/
theorem gammaGrid_mem_ZIrr_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    GammaGrid hG hyp ∈ OddOrder.RepresentationTheory.ZIrr G := by
  classical
  have hp3 := hyp.three_le_p
  set j1 : Fin hyp.p := ⟨1, by omega⟩ with hj1def
  have hj1ne : (j1 : ℕ) ≠ 0 := by simp [hj1def]
  have hβZ : betaGrid hyp j1 ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S := by
    refine Submodule.sub_mem _ ?_
      (OddOrder.RepresentationTheory.IsIrreducibleCharacter.mem_ZIrr
        (hyp.mu_irreducible _ j1))
    have htriv := (OddOrder.RepresentationTheory.trivialIrreducibleCharacter
      ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)).isIrreducible
    rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_trivialIrreducibleCharacter]
      at htriv
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr _
      (OddOrder.RepresentationTheory.IsIrreducibleCharacter.mem_ZIrr htriv)
  have hTZ : tauSbetaGrid hG hyp ∈ OddOrder.RepresentationTheory.ZIrr G := by
    rw [tauSbetaGrid,
      hyp.sInstance_dade0_eq_induce hG hnoV
        (betaGrid_A0_support_of_c_eq_one hG hyp hc1 j1 hj1ne)]
    exact OddOrder.RepresentationTheory.ClassFunction.induce_mem_ZIrr _ hβZ
  rw [show GammaGrid hG hyp = tauSbetaGrid hG hyp
      - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
      + hyp.eta ⟨0, hyp.q_prime.pos⟩ j1 from rfl]
  refine Submodule.add_mem _ (Submodule.sub_mem _ hTZ ?_) ?_
  · have htriv := (OddOrder.RepresentationTheory.trivialIrreducibleCharacter G).isIrreducible
    rw [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_trivialIrreducibleCharacter]
      at htriv
    exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.mem_ZIrr htriv
  · rw [hyp.eta_eq_tau_omega]
    exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ j1)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- Core of the **(13.18.d) residual-norm bound**, with the `FiniteInduce`-scoped instances
(Coq `PFsection13.v:1915-1934`).  The chain: `‖τ_S β₁‖² = ‖β₁‖² = (u−1)/q + 2` (Dade isometry
on `A₀(S)`-support + `betaGrid_norm`); peel `1_G` (`⟨Γ,1⟩ = 0`, `⟨η_{01},1⟩ = 0`), peel `Y`
(`X ⊥ Y`, `Y ⊥ η`-grid); then split `X − η_{01} = X₁ + a·η_{0,−1} + (a−1)·η_{01}` where
`a = ⟨Γ, η_{01}⟩ ∈ ℤ` (`gammaGrid_mem_ZIrr`), using `Γ` real ((13.18.c)) and
`η̄_{01} = η_{0,−1} ⊥ η_{01}`; drop `‖X₁‖² ≥ 0` and close with the integer inequality
`a² + (a−1)² ≥ 1`. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    (X Y : ClassFunction G ℂ) (defXY : GammaGrid hG hyp = X + Y)
    (oXY : ClassFunction.inner X Y = 0)
    (oYeta : ∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) :
    (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ) := by
  classical
  have hp3 := hyp.three_le_p
  set j1 : Fin hyp.p := ⟨1, by omega⟩ with hj1def
  set i0 : Fin hyp.q := ⟨0, hyp.q_prime.pos⟩ with hi0def
  set j' : Fin hyp.p := OddOrder.Peterfalvi.S15.finNeg hyp.p_prime.pos j1 with hj'def
  have hj1ne : (j1 : ℕ) ≠ 0 := by simp [hj1def]
  set η01 : ClassFunction G ℂ := hyp.eta i0 j1 with hη01def
  set η01' : ClassFunction G ℂ := hyp.eta i0 j' with hη01'def
  -- index bookkeeping: `j' ≠ j1`, `j1 ≠ 0`, `finNeg 0 = 0`
  have hj'ne : j' ≠ j1 := by
    intro h
    have hval := congrArg Fin.val h
    simp only [hj'def, OddOrder.Peterfalvi.S15.finNeg, hj1def] at hval
    rw [Nat.mod_eq_of_lt (by omega)] at hval
    omega
  have hneg0 : OddOrder.Peterfalvi.S15.finNeg hyp.q_prime.pos i0 = i0 := by
    apply Fin.ext
    simp [OddOrder.Peterfalvi.S15.finNeg, hi0def]
  -- `η̄_{01} = η_{0,−1}` (the (3.9.a) conj-pair field at `finNeg 0 = 0`)
  have hconj : η01.conj = η01' := by
    rw [hη01def, hyp.eta_conj i0 j1, hneg0, hη01'def, hj'def]
  -- grid orthonormality instances
  have h_11 : ClassFunction.inner η01 η01 = 1 := by
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j1 j1
    rw [if_pos ⟨rfl, rfl⟩] at h
    exact h
  have h_1'1 : ClassFunction.inner η01' η01 = 0 := by
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j' j1
    rw [if_neg (by rintro ⟨-, h2⟩; exact hj'ne h2)] at h
    exact h
  have h_11' : ClassFunction.inner η01 η01' = 0 := by
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j1 j'
    rw [if_neg (by rintro ⟨-, h2⟩; exact hj'ne h2.symm)] at h
    exact h
  have h_1'1' : ClassFunction.inner η01' η01' = 1 := by
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j' j'
    rw [if_pos ⟨rfl, rfl⟩] at h
    exact h
  -- `1_G = η_{00}` and its orthogonalities
  have hone : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
      = hyp.eta i0 ⟨0, hyp.p_prime.pos⟩ := by
    rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]
    rfl
  have hη01_one : ClassFunction.inner η01
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
    rw [hone]
    have h := OddOrder.Peterfalvi.S16.eta_orthonormal hyp i0 i0 j1 ⟨0, hyp.p_prime.pos⟩
    rw [if_neg (by
      rintro ⟨-, h2⟩
      exact hj1ne (by simpa using congrArg Fin.val h2))] at h
    exact h
  have hΓone : ClassFunction.inner (GammaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 :=
    gammaGrid_orthogonal_one_of_c_eq_one hG hnoV hyp hc1
  -- Pythagoras helper
  have pyth : ∀ A B : ClassFunction G ℂ, ClassFunction.inner A B = 0 →
      ClassFunction.inner (A + B) (A + B)
        = ClassFunction.inner A A + ClassFunction.inner B B := by
    intro A B hAB
    have hBA : ClassFunction.inner B A = 0 := by
      rw [ClassFunction.inner_star_comm, hAB, star_zero]
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, hAB, hBA]
    ring
  -- the isometry: `‖τ_S β₁‖² = ‖β₁‖² = (u−1)/q + 2`
  have hTT : ClassFunction.inner (tauSbetaGrid hG hyp) (tauSbetaGrid hG hyp)
      = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ) := by
    rw [tauSbetaGrid,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS0 hG)
        (betaGrid_A0_support_of_c_eq_one hG hyp hc1 j1 hj1ne)
        (betaGrid_A0_support_of_c_eq_one hG hyp hc1 j1 hj1ne)]
    exact betaGrid_norm_of_c_eq_one hG hyp hc1 j1 hj1ne
  -- Pythagoras 1: `τ_S β₁ = (Γ − η_{01}) + 1_G`
  have hTdecomp : tauSbetaGrid hG hyp
      = (GammaGrid hG hyp - η01) + OddOrder.Peterfalvi.S09.Hypothesis71.constOne G := by
    rw [show GammaGrid hG hyp = tauSbetaGrid hG hyp
        - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + η01 from rfl]
    abel
  have hP1 : ClassFunction.inner (tauSbetaGrid hG hyp) (tauSbetaGrid hG hyp)
      = ClassFunction.inner (GammaGrid hG hyp - η01) (GammaGrid hG hyp - η01) + 1 := by
    rw [hTdecomp, pyth _ _ (by
      rw [ClassFunction.inner_sub_left, hΓone, hη01_one, sub_zero]),
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one]
  -- Pythagoras 2: `Γ − η_{01} = (X − η_{01}) + Y`
  have hP2 : ClassFunction.inner (GammaGrid hG hyp - η01) (GammaGrid hG hyp - η01)
      = ClassFunction.inner (X - η01) (X - η01) + ClassFunction.inner Y Y := by
    have hd : GammaGrid hG hyp - η01 = (X - η01) + Y := by rw [defXY]; abel
    have oY01 : ClassFunction.inner Y η01 = 0 := oYeta i0 j1
    rw [hd, pyth _ _ (by
      rw [ClassFunction.inner_sub_left, oXY]
      rw [show ClassFunction.inner η01 Y = 0 by
        rw [ClassFunction.inner_star_comm, oY01, star_zero]]
      ring)]
  -- the grid coefficient `a = ⟨Γ, η_{01}⟩` is an integer `m`
  have hηZ : η01 ∈ OddOrder.RepresentationTheory.ZIrr G := by
    rw [hη01def, hyp.eta_eq_tau_omega]
    exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr i0 j1)
  obtain ⟨m, hm⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int
    (gammaGrid_mem_ZIrr_of_c_eq_one hG hnoV hyp hc1) hηZ
  -- `⟨X, η_{01}⟩ = m` and `⟨X, η_{0,−1}⟩ = m` (the latter via `Γ` real + conj-pair)
  have hXη : ClassFunction.inner X η01 = (m : ℂ) := by
    have h := congrArg (fun φ : ClassFunction G ℂ => ClassFunction.inner φ η01) defXY
    simp only [ClassFunction.inner_add_left] at h
    have oY01 : ClassFunction.inner Y η01 = 0 := oYeta i0 j1
    rw [oY01, add_zero] at h
    rw [← h, hm]
  have hΓη' : ClassFunction.inner (GammaGrid hG hyp) η01' = (m : ℂ) := by
    rw [← hconj, ← gammaGrid_real_of_c_eq_one hG hnoV hyp hc1,
      OddOrder.RepresentationTheory.ClassFunction.inner_conj_conj,
      ClassFunction.inner_star_comm, hm, star_intCast]
  have hXη' : ClassFunction.inner X η01' = (m : ℂ) := by
    have h := congrArg (fun φ : ClassFunction G ℂ => ClassFunction.inner φ η01') defXY
    simp only [ClassFunction.inner_add_left] at h
    have oY01' : ClassFunction.inner Y η01' = 0 := oYeta i0 j'
    rw [oY01', add_zero] at h
    rw [← h, hΓη']
  -- Pythagoras 3+4: `X − η_{01} = (X₁ + m·η_{0,−1}) + (m−1)·η_{01}`
  set X1 : ClassFunction G ℂ := X - (m : ℂ) • η01 - (m : ℂ) • η01' with hX1def
  have hX1η : ClassFunction.inner X1 η01 = 0 := by
    rw [hX1def, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
      hXη, h_11, h_1'1]
    ring
  have hX1η' : ClassFunction.inner X1 η01' = 0 := by
    rw [hX1def, ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
      hXη', h_11', h_1'1']
    ring
  have hXdecomp : X - η01 = (X1 + (m : ℂ) • η01') + ((m : ℂ) - 1) • η01 := by
    rw [hX1def, sub_smul, one_smul]
    abel
  have hstar_m : star ((m : ℂ)) = (m : ℂ) := star_intCast m
  have hstar_m1 : star ((m : ℂ) - 1) = (m : ℂ) - 1 := by
    rw [star_sub, star_one, hstar_m]
  have hP3 : ClassFunction.inner (X - η01) (X - η01)
      = ClassFunction.inner (X1 + (m : ℂ) • η01') (X1 + (m : ℂ) • η01')
        + ((m : ℂ) - 1) * ((m : ℂ) - 1) := by
    rw [hXdecomp, pyth _ _ (by
      rw [ClassFunction.inner_smul_right, ClassFunction.inner_add_left,
        ClassFunction.inner_smul_left, hX1η, h_1'1]
      ring)]
    rw [ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, hstar_m1, h_11]
    ring
  have hP4 : ClassFunction.inner (X1 + (m : ℂ) • η01') (X1 + (m : ℂ) • η01')
      = ClassFunction.inner X1 X1 + (m : ℂ) * (m : ℂ) := by
    rw [pyth _ _ (by rw [ClassFunction.inner_smul_right, hX1η', hstar_m]; ring),
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_right, hstar_m, h_1'1']
    ring
  -- assemble the ℂ-level identity and take real parts
  have hX1re := OddOrder.RepresentationTheory.ClassFunction.inner_self_eq_re X1
  have hchain : ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℂ)
      = (((ClassFunction.inner X1 X1).re : ℝ) : ℂ)
        + ((m * m + (m - 1) * (m - 1) : ℤ) : ℂ)
        + ClassFunction.inner Y Y + 1 := by
    rw [← hTT, hP1, hP2, hP3, hP4, ← hX1re]
    push_cast
    ring
  have hre := congrArg Complex.re hchain
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.intCast_re,
    Complex.ratCast_re] at hre
  -- final integer inequality `m² + (m−1)² ≥ 1` and the nonnegativity of `‖X₁‖²`
  have hmm1 : (1 : ℤ) ≤ m * m + (m - 1) * (m - 1) := by
    by_cases h : 1 ≤ m
    · nlinarith
    · have h' : m ≤ 0 := by omega
      nlinarith
  have hX1nonneg : 0 ≤ (ClassFunction.inner X1 X1).re :=
    OddOrder.RepresentationTheory.ClassFunction.inner_self_re_nonneg X1
  have hmm1' : (1 : ℝ) ≤ ((m * m + (m - 1) * (m - 1) : ℤ) : ℝ) := by exact_mod_cast hmm1
  have hgoal : (ClassFunction.inner Y Y).re
      = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 2 : ℚ) : ℝ)
        - (ClassFunction.inner X1 X1).re
        - ((m * m + (m - 1) * (m - 1) : ℤ) : ℝ) - 1 := by linarith [hre]
  rw [hgoal]
  push_cast at hmm1' ⊢
  linarith

end OddOrder.Peterfalvi.S15

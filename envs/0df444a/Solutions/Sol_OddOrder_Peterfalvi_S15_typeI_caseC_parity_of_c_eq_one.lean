-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.typeI_caseC_parity_of_c_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:24:58.938187+00:00
-- url     : https://prove2.me/submissions/c65e798f-bcfa-48df-a2d6-2dcf5f3dae34

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean
--   OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean
--   OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean
--   OddOrder/GroupTheory/RepresentationTheory/InflationInduction.lean
--   OddOrder/Peterfalvi/S15_BridgeCharacter.lean
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
--   OddOrder/Peterfalvi/S15_SAndTGrid.lean
--   OddOrder/Peterfalvi/S15_SAndT.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
import Theorems.Thm_OddOrder_RepresentationTheory_cfdot_real_vchar_even
import Theorems.Thm_OddOrder_Peterfalvi_S15_gammaGrid_real_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_betaGrid_support_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_tauS_mu_row0_vanish_on_V
import Theorems.Thm_OddOrder_Peterfalvi_S15_dadeSupport_betaGrid_disjoint_support_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_coherent_extension_orthogonal_eta_of_mem_Sset

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- The source difference `Ind 1_H - ζ` is virtual when the `Ind 1_H`
source term is virtual and the distinguished `ζ` is irreducible. -/
theorem sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.hyp76.zeta H78.ind1H - H78.hyp76.zeta H78.zetaDistinct ∈ ZIrr L :=
  Submodule.sub_mem _ hindZ hzeta_irr.mem_ZIrr

/-- Virtuality of `Ind 1_H` and irreducibility of `ζ` supply the
virtual-character input needed by the Dade bridge for `β`. -/
theorem beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.beta ∈ ZIrr G :=
  H78.beta_mem_ZIrr_of_sourceDiff_mem_ZIrr
    (H78.sourceDiff_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible hindZ hzeta_irr)

/-- If `β` is a virtual character and `ν` is a concrete coherent extension on
`S = T \ {Ind 1_H}`, then the residual `Δ = β - 1_G + νζ` is virtual. -/
theorem delta_mem_ZIrr_of_beta_mem_ZIrr_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hbeta : H78.beta ∈ ZIrr G) :
    H78.delta ∈ ZIrr G := by
  have hconst : Hypothesis71.constOne G ∈ ZIrr G := by
    have htriv : OddOrder.RepresentationTheory.trivialClassFunction G ∈ ZIrr G :=
      OddOrder.RepresentationTheory.trivialClassFunction_isIrreducible.mem_ZIrr
    simpa [Hypothesis71.constOne, OddOrder.RepresentationTheory.trivialClassFunction]
      using htriv
  have hzeta : H78.nu (H78.hyp76.zeta H78.zetaDistinct) ∈ ZIrr G :=
    H78.nu_zetaDistinct_mem_ZIrr_of_isCoherent hcoh hnu
  simpa [delta] using Submodule.add_mem (ZIrr G)
    (Submodule.sub_mem (ZIrr G) hbeta hconst) hzeta

/-- If the `Ind 1_H` source term is virtual and the distinguished `ζ` is
irreducible, then coherence supplies the residual virtual character `Δ`. -/
theorem delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    (H78 : Hypothesis78 G A L)
    {A_prime : Set L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent τ H78.sourceSet A_prime)
    (hnu : H78.nu = hcoh.extension)
    (hindZ : H78.hyp76.zeta H78.ind1H ∈ ZIrr L)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.delta ∈ ZIrr G :=
  H78.delta_mem_ZIrr_of_beta_mem_ZIrr_of_isCoherent hcoh hnu
    (H78.beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible hindZ hzeta_irr)

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/CoherenceFormula.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- `BetaDecomp` identifies the (7.9) residual `Δ` with the weighted part plus
`Γ`. -/
theorem delta_eq_weightedNuSum_add_gamma
    (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    H78.delta = (hBD.a : ℂ) • H78.weightedNuSum + hBD.Gamma := by
  rw [delta, hBD.beta_eq]
  abel

/-- The residual `Δ` is orthogonal to `1_G`. -/
theorem delta_orth_one (H78 : Hypothesis78 G A L) (hBD : H78.BetaDecomp) :
    ClassFunction.inner H78.delta (Hypothesis71.constOne G) = 0 := by
  rw [H78.delta_eq_weightedNuSum_add_gamma hBD, ClassFunction.inner_add_left,
    ClassFunction.inner_smul_left, H78.weightedNuSum_orth_one hBD,
    hBD.Gamma_orth_one, mul_zero, add_zero]

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

/-- **The residual `Δ = β − 1_G + νζ` is real** (Peterfalvi (7.9), delta-reality — pure algebra).
Given `β̄ − β = νζ − νζ̄` (`hbeta_conj_sub`, itself (A) `dadeMap_conj` + agreement + Dade linearity)
and `(νζ)‾ = ν(ζ̄)` (`hnu_conj`, (B) `coherence_extension_conj`), the two conjugate-difference terms
cancel: `Δ̄ − Δ = (β̄−β) + ((νζ)‾−νζ) = (νζ−νζ̄) + (νζ̄−νζ) = 0`.  `1_G` is real, so it drops out.
Feeds `cfdot_real_vchar_even` for the (7.9) `hdelta_even`. -/
theorem delta_isReal {G : Type*} [Group G] [Fintype G] {A : Set G} {L : Subgroup G}
    [Fintype L] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (H78 : Hypothesis78 G A L)
    (hnu_conj : (H78.nu (H78.hyp76.zeta H78.zetaDistinct)).conj
        = H78.nu (H78.hyp76.zeta H78.zetaDistinct).conj)
    (hbeta_conj_sub : H78.beta.conj - H78.beta
        = H78.nu (H78.hyp76.zeta H78.zetaDistinct)
          - H78.nu (H78.hyp76.zeta H78.zetaDistinct).conj) :
    ClassFunction.IsReal H78.delta := by
  have hd : H78.delta = H78.beta - Hypothesis71.constOne G
      + H78.nu (H78.hyp76.zeta H78.zetaDistinct) := rfl
  have hconstOne : (Hypothesis71.constOne G).conj = Hypothesis71.constOne G := by
    ext g; simp [ClassFunction.conj_apply, Hypothesis71.constOne_apply]
  have hbeta : H78.beta.conj = (H78.nu (H78.hyp76.zeta H78.zetaDistinct)
      - H78.nu (H78.hyp76.zeta H78.zetaDistinct).conj) + H78.beta := by
    rw [← hbeta_conj_sub]; abel
  rw [ClassFunction.IsReal, hd, ClassFunction.conj_add, ClassFunction.conj_sub, hconstOne,
    hnu_conj, hbeta]
  abel

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **Prime-`TI` row-`0` cross-column distinctness** (issue 9076 piece 4c-4): distinct columns of
row `0` carry distinct `μ`-entries, `μ_{0j} ≠ μ_{0,#1}` for `j ≠ #1`.  This is the cross-column
injectivity of the prime-`TI` residue grid: the `μ_{ij}` are pairwise-distinct irreducibles across
the *whole* grid (Coq: the residues `prTIres i j` are distinct for distinct `(i, j)`).  The
`Hypothesis` structure records only the *within-column* distinctness `mu_col_injective`; this
row-direction distinctness is the missing prime-`TI` fact.  Prime-`TI` theory, cf. issue 9014. -/
theorem Hypothesis.mu_row0_ne [Finite G] (hyp : Hypothesis (G := G)) {j : Fin hyp.p}
    (hj : j ≠ ⟨1, by have := hyp.three_le_p; omega⟩) :
    hyp.mu ⟨0, hyp.q_prime.pos⟩ j
      ≠ hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := by
  classical
  intro heq
  -- The diagonal value `⟨μ_{0,#1}, μ_{0,#1}⟩ = 1` (irreducibility, `mu_irreducible`).
  have hdiag : OddOrder.RepresentationTheory.ClassFunction.inner
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 1 :=
    (hyp.mu_irreducible ⟨0, hyp.q_prime.pos⟩
      ⟨1, by have := hyp.three_le_p; omega⟩).inner_self_eq_one
  -- The off-diagonal (row-`0` cross-column) value `⟨μ_{0j}, μ_{0,#1}⟩ = 0` (`j ≠ #1`) is the
  -- prime-`TI` grounding: the full-grid orthonormality field `mu_orthonormal` (b-side, issues
  -- 9076/3002/9014), discharged in the spine by `Section16CharacterData.muS_orthonormal`
  -- (`muS = columnFamily.mu = residueS.mu2`, cf. `S13_PrimeTIResidueBridge`).
  have hoff : OddOrder.RepresentationTheory.ClassFunction.inner (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)
      (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 := by
    rw [hyp.mu_orthonormal]
    exact if_neg (fun hc => hj hc.2)
  rw [heq, hdiag] at hoff
  exact one_ne_zero hoff

/-- **Prime-`TI` support pin, proven** (Coq `prDade_sub_TIirr_on`, `PFsection4.v`): the `μ`-column
difference `μ_{0j} − μ_{0,#1}` is supported inside `A₀(S) = A(S) ∪ V^S` — its support meets `S`
only in `P^# ∪ V_S`, because the two prime-`TI` residues share the same `1_S`-part off `A₀(S)` and
it cancels in the difference.  This is the `S`-side instance of Coq `prDade_sub_TIirr_on`
(`μ2_{ij} − μ2_{ik} ∈ 'CF(S, 'A0)`).

**Honest signature (issue 9076, 2026-07-11)**: carries `(hj0 : (j:ℕ) ≠ 0)` — the unrestricted
`∀ j` form is *false* at the trivial column `j = 0` (`μ_{00}(1) = 1 ≠ μ_{0,#1}(1)`, and `1 ∉ A₀`).
The sole consumer `tauS_mu_row0_cross` (S15_SAndT) passes its `_hj`.

**Fully discharged (2026-07-11)**: the support claim is the `(13.18)` grounding field
`mu_diff_support` (issue 9081: producer-supplied by the proven
`Section16CharacterData.muS_diff_support`, Dade-free via `hyp46SmpCore`), and the degree
hypothesis is the proven per-entry degree `mu_apply_one_eq_u` (Pf (13.3)(a): `μ_{ij}(1) = u` for
`j ≠ 0`, via `mu_j_isIndPC` + `H_index_eq_uq`) — the same two steps Coq's `defGamma` uses
(`prDade_sub_TIirr` + the `FTprTIred1` `mulfI`-cancellation, `PFsection13.v:1909`). -/
theorem Hypothesis.tauS_mu_row0_diff_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj0 : (j : ℕ) ≠ 0) :
    (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
        - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S hyp.Sdata) hyp.S :=
  hyp.mu_diff_support ⟨0, hyp.q_prime.pos⟩
    (fun h => hj0 (congrArg Fin.val h))
    (fun h => one_ne_zero (congrArg Fin.val h))
    ((hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩ j
        (fun h => hj0 (congrArg Fin.val h))).trans
      (hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩
        ⟨1, by have := hyp.three_le_p; omega⟩
        (fun h => one_ne_zero (congrArg Fin.val h))).symm)

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

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(4.8)/(5.3) prime-`TI` Dade cross-relation, `S`-side row-`0` form**:
`τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}` for `j ≠ 0`.

This is Coq `prDade_sub_TIirr` (`PFsection4.v:870`) `τ(μ2_{ij} − μ2_{ik}) = δ_j·(η_{ij} − η_{ik})`
specialized to row `i = 0`, columns `j` and `#1`, with the `FT`-context sign `δ_j = 1`.  It is the
single deep input behind (13.18.c)'s `j`-independence `gammaGrid_defGamma`.

✅ **Now on the correct Dade map** (issue 9076, 2026-07-08): `τ_S` is `dadeIntegralCharacterMap`
of the honest **`'A0(S)`-Dade** `dadeHypS0` (support `A₀(S) = A(S) ∪ V^S`), **not** the smaller
`'A(S)`-Dade `dadeHypS`.  The `μ`-column difference `μ_{0j} − μ_{01}` is supported on `P^# ∪ V_S`
(Coq `prDade_sub_TIirr_on`), and `V_S ⊄ S' ⊇ A(S)`, so with the old `dadeHypS` map the `V_S`-part
fell in the arbitrary linear-extension region and the statement was **unprovable as stated**; the
`'A0`-Dade correction fixes that (`dadeHypS0` inherits one deep FT-support pin,
`S10.not_isConj_typePACore_typePV`).

The route: `X := τ_S(μ-diff)` has `‖X‖² = 2` (Dade isometry) and `X ∈ ZIrr`; it agrees with
`η_{0j} − η_{01}` on the regular set via `τ_S = Ind_S^G` on `A₀`-supported (`normedTI 'A0`,
`H = ⊥`) + the prime-`TI` `μ`-value `μ_{0j}|_V = ω`-value (Coq `prTIirr_id`, prime-`TI` theory,
cf. 9014); then `X = η_{0j} − η_{01}` by `S16.eta_diff_rigidity` (Peterfalvi (3.8), issue 9076
piece 4b). -/
theorem tauS_mu_row0_cross [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (_hj : (j : ℕ) ≠ 0) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      = hyp.eta ⟨0, hyp.q_prime.pos⟩ j
          - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := by
  classical
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData) with hD
  by_cases hj1 : j = ⟨1, by have := hyp.three_le_p; omega⟩
  · -- Trivial column `j = #1`: both `μ`- and `η`-differences vanish, and `τ_S 0 = 0`.
    simp only [hj1, sub_self, map_zero]
  · -- `j ≠ #1`: `X := τ_S(μ_{0j} − μ_{0,#1})` is a norm-`2` `ZIrr` character agreeing with
    -- `η_{0j} − η_{0,#1}` on the regular set `V`, so `S16.eta_diff_rigidity` (3.8) pins it.
    have hμaIrr : IsIrreducibleCharacter (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) :=
      hyp.mu_irreducible _ _
    have hμbIrr : IsIrreducibleCharacter
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) :=
      hyp.mu_irreducible _ _
    have hμne : hyp.mu ⟨0, hyp.q_prime.pos⟩ j
        ≠ hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ :=
      hyp.mu_row0_ne hj1
    have hsupp := hyp.tauS_mu_row0_diff_support hG j _hj
    have hZIrrS : (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        ∈ ZIrr (↥hyp.S) :=
      (ZIrr (↥hyp.S)).sub_mem hμaIrr.mem_ZIrr hμbIrr.mem_ZIrr
    -- (a) `X ∈ ZIrr G` (Dade sends supported virtual characters to virtual characters, `(2.6.b)`).
    have hXZ : D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) ∈ ZIrr G :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.dadeHypS0 hG) hsupp hZIrrS
    -- (b) `‖μ_{0j} − μ_{0,#1}‖² = 2` (two distinct irreducibles).
    have hinner : ∀ φ ψ : ClassFunction ↥hyp.S ℂ, IsIrreducibleCharacter φ →
        IsIrreducibleCharacter ψ → ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
      intro φ ψ hφ hψ
      have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥hyp.S)
        (⟨ψ, hψ⟩ : IrreducibleCharacter ↥hyp.S)
      simp only [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hpq : φ = ψ
      · rw [if_pos (Subtype.ext hpq), if_pos hpq]
      · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
    have h_ab : ClassFunction.inner (hyp.mu ⟨0, hyp.q_prime.pos⟩ j)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 0 := by
      rw [hinner _ _ hμaIrr hμbIrr, if_neg hμne]
    have h_ba : ClassFunction.inner
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j) = 0 := by
      rw [hinner _ _ hμbIrr hμaIrr, if_neg (Ne.symm hμne)]
    have hnorm2 : ClassFunction.inner
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = 2 := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h_ab, h_ba,
        hμaIrr.inner_self_eq_one, hμbIrr.inner_self_eq_one]
      ring
    have hX2 : ClassFunction.inner
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩))
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) = 2 := by
      rw [hD, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS0 hG) hsupp hsupp]
      exact hnorm2
    -- (c) `X − (η_{0j} − η_{0,#1})` vanishes on the regular set `V` (prime-`TI` `V`-value pin).
    have hvanish : ∀ x ∈ conjClassSet
          ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
        (D (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
              - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
          - ((1 : ℤ) : ℂ) • (hyp.eta ⟨0, hyp.q_prime.pos⟩ j
              - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) x = 0 := by
      intro x hx
      have hv := hyp.tauS_mu_row0_vanish_on_V hG hnoV j _hj x hx
      simpa [hD] using hv
    -- (3.8) rigidity: a norm-`2` `ZIrr` character agreeing with `η_{0j} − η_{0,#1}` on `V` is it.
    have hrig := OddOrder.Peterfalvi.S16.eta_diff_rigidity hyp hXZ hX2
      ⟨0, hyp.q_prime.pos⟩ hj1 (s := (1 : ℤ)) (Or.inl rfl) hvanish
    rw [Int.cast_one, one_smul] at hrig
    exact hrig

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.c), `j`-independence** (`defGamma`): for every column `j ≠ 0`, the bridge residual
`τ_S(β_j) − 1_G + η_{0j}` equals the fixed gap `Γ = GammaGrid` (defined at column `#1`).

This is exactly Peterfalvi (13.18.c)'s "`Γ` is independent of `j`" (Coq `defGamma`,
`PFsection13.v:1905`), **NOT** grid-orthogonality: the previous scaffold field
`Gamma_independent : ⟨Γ, η_{ik}⟩ = 0` was an **overstatement** (issue 3003), refuted by the genuine
(13.18.d) `X + Y` decomposition where `Γ`'s grid-component `X` is nonzero.

Proof (sorry-free glue, one isolated obligation): `τ_S(β_j) − τ_S(β_{#1}) = τ_S(β_j − β_{#1})` by
`ℤ`-linearity of the Dade map (`map_sub`), and `β_j − β_{#1} = μ_{01} − μ_{0j} = −(μ_{0j} − μ_{01})`
(both share the `Ind_{PW₁}^S 1` positive part), so `τ_S(β_j − β_{#1}) = −(η_{0j} − η_{01}) =
η_{01} −
η_{0j}` by the (4.8)/(5.3) cross-relation `tauS_mu_row0_cross`.  Cancelling the `−1_G`'s and
`abel` closes the goal. -/
theorem gammaGrid_defGamma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData) (betaGrid hyp j)
        - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + hyp.eta ⟨0, hyp.q_prime.pos⟩ j
      = GammaGrid hG hyp := by
  have hcross := tauS_mu_row0_cross hG hnoV hyp j hj
  have hbeta : betaGrid hyp j - betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩
      = -(hyp.mu ⟨0, hyp.q_prime.pos⟩ j
          - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) := by
    simp only [betaGrid]; abel
  have key : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData) (betaGrid hyp j)
      - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData)
          (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)
      = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
        - hyp.eta ⟨0, hyp.q_prime.pos⟩ j := by
    rw [← map_sub, hbeta, map_neg, hcross]; abel
  simp only [GammaGrid, tauSbetaGrid]
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
    ((hyp.dadeHypS0 hG).fullDadeIsometryData) with hD
  rw [← sub_eq_zero, show
      (D (betaGrid hyp j) - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          + hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
        - (D (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩)
          - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
          + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      = (D (betaGrid hyp j) - D (betaGrid hyp ⟨1, by have := hyp.three_le_p; omega⟩))
        - (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩
          - hyp.eta ⟨0, hyp.q_prime.pos⟩ j) by abel, key, sub_self]

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

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S16_PairingCoherence.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- The zeta family of `h78` is the placed induced family (definitional). -/
theorem h78_zeta_eq (i : Fin (data.n + 1)) :
    (data.h78 hG).hyp76.zeta i = data.zeta i := rfl

/-- The distinguished index of `h78` is `0` (definitional). -/
theorem h78_zetaDistinct_eq : (data.h78 hG).zetaDistinct = 0 := rfl

/-- The principal index of `h78` is `ind1H` (definitional). -/
theorem h78_ind1H_eq : (data.h78 hG).ind1H = data.ind1H := rfl

/-- The coherent extension of `h78` is the bundle's coherence extension
(definitional). -/
theorem h78_nu_eq : (data.h78 hG).nu = data.coh.extension := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The distinguished `ζ_0` is irreducible** (Frobenius kernel induction,
[Is] Thm 6.34). -/
theorem h78_zeta_irreducible :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct) := by
  have := data.kernelIn_normal
  rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ 0)
    data.theta_zero_ne_trivial

/-- **The induced principal `ζ_{ind1H} = Ind 1_H` is a virtual character.** -/
theorem h78_ind_mem_ZIrr :
    (data.h78 hG).hyp76.zeta (data.h78 hG).ind1H ∈ ZIrr ↥L := by
  have := data.kernelIn_normal
  rw [data.h78_ind1H_eq, data.h78_zeta_eq]
  exact ClassFunction.induce_mem_ZIrr _ (data.θ data.ind1H).property.mem_ZIrr

/-- **The `(7.8)` coherent source set equals the (12.1) family `S`.** -/
theorem h78_sourceSet_eq : (data.h78 hG).sourceSet = data.typeIHyp.Sset := by
  have := data.kernelIn_normal
  ext φ
  constructor
  · rintro ⟨idx, hidx, rfl⟩
    exact data.zeta_mem_Sset hidx
  · rintro ⟨θ', hθ'_ne, rfl⟩
    obtain ⟨j, hj⟩ := data.cover θ'
    have hj' : data.zeta j = ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ) := hj
    refine ⟨j, ?_, hj'⟩
    intro hjind
    apply induce_ne_trivialChar_induce data.kernelIn θ' hθ'_ne
    rw [← hj', show j = data.ind1H from hjind]
    change ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
      = ClassFunction.induce data.kernelIn
        ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
          ClassFunction _ ℂ)
    rw [data.triv]

/-- **The bundle coherence as an `IsCoherent` over the `(7.8)` `sourceSet`** (transport along
`h78_sourceSet_eq`, keeping the same extension `ν`). -/
noncomputable def isCoherentSourceSet :
    OddOrder.Peterfalvi.S07.IsCoherent data.typeIHyp.tau (data.h78 hG).sourceSet
      data.typeIHyp.A where
  nonzero := (data.h78_sourceSet_eq hG).symm ▸ data.coh.nonzero
  extension := data.coh.extension
  extension_inner_eq := fun φ ψ hφ hψ => data.coh.extension_inner_eq φ ψ
    (data.h78_sourceSet_eq hG ▸ hφ) (data.h78_sourceSet_eq hG ▸ hψ)
  extends_on_supported := fun φ hφ => data.coh.extends_on_supported φ
    (data.h78_sourceSet_eq hG ▸ hφ)
  extension_mem_ZIrr := fun φ hφ => data.coh.extension_mem_ZIrr φ
    (data.h78_sourceSet_eq hG ▸ hφ)

set_option backward.isDefEq.respectTransparency false in
/-- **The conjugate `ζ̄_0` is a family member**: there is `j₁ ≠ ind1H` with
`ζ_{j₁} = ζ̄_0` (`conjPerm` of the distinguished source is covered). -/
theorem exists_conjIndex :
    ∃ j₁, j₁ ≠ (data.h78 hG).ind1H ∧
      (data.h78 hG).hyp76.zeta j₁
        = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
  have := data.kernelIn_normal
  have hconj_eq : ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj
      = ClassFunction.induce data.kernelIn
          ((IrreducibleCharacter.conjPerm _ (data.θ 0)) : ClassFunction _ ℂ) := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq, conj_induce]
    exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe (data.θ 0)).symm
  obtain ⟨j₁, hj₁_range⟩ := data.cover (IrreducibleCharacter.conjPerm _ (data.θ 0))
  have hj₁_conj : (data.h78 hG).hyp76.zeta j₁
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
    rw [data.h78_zeta_eq, hconj_eq]; exact hj₁_range
  refine ⟨j₁, ?_, hj₁_conj⟩
  intro hj1
  apply data.ind1H_ne_zero
  have hzeta_inj : Function.Injective (data.h78 hG).hyp76.zeta := data.inj
  refine (hzeta_inj ?_).symm
  -- `ζ_{ind1H}` is real (`Ind 1_H`), and `ζ_{ind1H} = ζ_{j₁} = ζ̄_0`.
  have e1 : (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
    rw [← show j₁ = (data.h78 hG).ind1H from hj1]; exact hj₁_conj
  have e2 : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    change (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)).conj
      = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
    rw [data.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  calc (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)
      = ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj := by
        rw [e1, ClassFunction.conj_conj]
    _ = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := e2

set_option backward.isDefEq.respectTransparency false in
/-- **The distinguished `ζ_0` is not real** (odd order): it is a nontrivial irreducible
(degree `[L:H] > 1`) of the odd-order group `L`. -/
theorem h78_zeta_ne_conj (hodd : Odd (Nat.card G)) :
    (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
      ≠ ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
  have := data.kernelIn_normal
  have hirr := data.h78_zeta_irreducible hG
  have hodd_L : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  -- The kernel is proper (complement nontrivial), so `[L:H] > 1`.
  have hK_ne_top : data.kernelIn ≠ ⊤ := by
    intro hKtop
    refine data.hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := data.hFrob.isComplement.disjoint
    rw [show (data.typeIHyp.typeI.typeF.H).subgroupOf L = data.kernelIn from rfl, hKtop]
      at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < (data.kernelIn).index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  have hdeg : (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct) (1 : ↥L)
      = ((data.kernelIn).index : ℂ) := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
    exact data.deg0
  have hne_triv : (⟨(data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct), hirr⟩ :
      IrreducibleCharacter ↥L) ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)
        = trivialClassFunction ↥L := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : (((data.kernelIn).index : ℂ)) = 1 := by
      rw [← hdeg, hcf, trivialClassFunction_apply]
    exact absurd (by exact_mod_cast hone : (data.kernelIn).index = 1) (by omega)
  intro h
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv h.symm

set_option backward.isDefEq.respectTransparency false in
/-- **`ζ_0 − ζ̄_0` is supported on `A(L)`** (equal degree; both vanish off `H`). -/
theorem zeta_sub_conj_support (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {j₁ : Fin (data.n + 1)}
    (hj₁ : (data.h78 hG).hyp76.zeta j₁
      = ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj) :
    ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
        - (data.h78 hG).hyp76.zeta j₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
  have := data.kernelIn_normal
  have hdeg : (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct) (1 : ↥L)
      = ((data.kernelIn).index : ℂ) := by
    rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
    exact data.deg0
  intro x hx
  rw [ClassFunction.mem_support, ClassFunction.sub_apply, hj₁, ClassFunction.conj_apply] at hx
  refine (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) x).mpr ⟨?_, ?_⟩
  · -- `x ∈ kernelIn`: else `ζ_0 x = 0`, so the difference vanishes.
    by_contra hxH
    apply hx
    rw [(data.h78 hG).hyp76.zeta_eq_zero_of_not_mem_H _ x hxH, star_zero, sub_zero]
  · -- `x ≠ 1`: at `1`, `ζ_0(1) = [L:H]` is real.
    intro hx1
    apply hx
    rw [hx1, hdeg]
    simp

/-- **Members of `ℤ[S]` vanishing at `1` are `A(L)`-supported** (the `hspan` input of
`extension_mapRingEquiv_comm`): each `Ind θ ∈ S` vanishes off the normal kernel
(`Sset_vanishes_off_H`), so `ℤ[S] ⊆ {ψ | supp ψ ⊆ H}` by span induction; vanishing at `1`
then lands the support in `H^# = A(L)`. -/
theorem zSpan_Sset_support_subset (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan data.typeIHyp.Sset) (h1 : φ 1 = 0) :
    φ.support ⊆ data.typeIHyp.A := by
  have := data.kernelIn_normal
  -- `ℤ[S] ⊆ {ψ | ψ.support ⊆ kernelIn}` by span induction.
  have hsuppH : ∀ ψ ∈ OddOrder.Peterfalvi.S07.zSpan data.typeIHyp.Sset,
      ψ.support ⊆ (data.kernelIn : Set ↥L) := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
        intro g hg
        rw [ClassFunction.mem_support] at hg
        by_contra hgK
        exact hg (OddOrder.Peterfalvi.S14.Sset_vanishes_off_H data.typeIHyp hx
          (fun hmem => hgK (Subgroup.mem_subgroupOf.mpr hmem)))
    | zero => intro g hg; rw [ClassFunction.mem_support] at hg; exact absurd rfl hg
    | add x y _ _ hx hy =>
        intro g hg
        rcases ClassFunction.support_add_subset x y hg with h | h
        · exact hx h
        · exact hy h
    | smul c x _ hx =>
        intro g hg
        refine hx ?_
        rw [ClassFunction.mem_support] at hg ⊢
        intro hxg
        apply hg
        rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hxg, mul_zero]
  intro g hg
  have hgH : g ∈ data.kernelIn := hsuppH φ hφ hg
  have hg1 : g ≠ 1 := by
    rintro rfl; exact (ClassFunction.mem_support.mp hg) h1
  change g ∈ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) g).mpr ⟨hgH, hg1⟩

/-- **The family `S` consists of irreducibles** (Frobenius kernel induction). -/
theorem Sset_subset_irreducible :
    data.typeIHyp.Sset ⊆ irreducibleCharacters ↥L := by
  have := data.kernelIn_normal
  rintro φ ⟨θ', hθ'_ne, rfl⟩
  exact mem_irreducibleCharacters.mpr
    (isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob θ' hθ'_ne)

/-- **The family `S` is closed under complex conjugation** (`Ind θ̄ = (Ind θ)‾`, and
`θ̄ ≠ 1` for `θ ≠ 1`). -/
theorem Sset_closedUnderConjugate {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ data.typeIHyp.Sset) :
    ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv φ ∈ data.typeIHyp.Sset := by
  have := data.kernelIn_normal
  obtain ⟨θ', hθ'_ne, rfl⟩ := hφ
  have hbridge : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
      (ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ))
      = (ClassFunction.induce data.kernelIn (θ' : ClassFunction _ ℂ)).conj := by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  rw [hbridge, conj_induce]
  refine ⟨IrreducibleCharacter.conjPerm _ θ', ?_, ?_⟩
  · -- `θ̄' ≠ 1`: conjugating `θ̄' = 1` gives `θ' = 1̄ = 1`.
    intro hconj_triv
    refine hθ'_ne (IrreducibleCharacter.ext ?_)
    have hcoe := congrArg IrreducibleCharacter.toClassFunction hconj_triv
    rw [show (IrreducibleCharacter.conjPerm _ θ').toClassFunction
        = (θ' : ClassFunction ↥data.kernelIn ℂ).conj
      from IrreducibleCharacter.conjPerm_apply_coe θ'] at hcoe
    calc (θ' : ClassFunction ↥data.kernelIn ℂ)
        = ((θ' : ClassFunction ↥data.kernelIn ℂ).conj).conj := (ClassFunction.conj_conj _).symm
      _ = ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
            ClassFunction _ ℂ).conj := by rw [hcoe]
      _ = ((trivialIrreducibleCharacter ↥data.kernelIn : IrreducibleCharacter _) :
            ClassFunction _ ℂ) := trivialClassFunction_isReal
  · exact congrArg _ (IrreducibleCharacter.conjPerm_apply_coe θ').symm

/-- **The coherent extension commutes with complex conjugation on `S`**
(Peterfalvi (5.9)(a) via `extension_mapRingEquiv_comm`). -/
theorem coherence_extension_conj (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ data.typeIHyp.Sset)
    (h2 : ∃ ψ ∈ data.typeIHyp.Sset, ψ ≠ χ) :
    (data.coh.extension χ).conj = data.coh.extension χ.conj := by
  have hbridgeG : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hbridgeL : ∀ X : ClassFunction ↥L ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  rw [hbridgeG (data.coh.extension χ), hbridgeL χ]
  exact data.coh.extension_mapRingEquiv_comm subset_rfl data.Sset_subset_irreducible
    (fun φ hφ h1 => data.zSpan_Sset_support_subset hG hφ h1)
    Complex.conjAe.toRingEquiv (fun φ hφ => data.Sset_closedUnderConjugate hφ)
    (fun φ hφ => data.coh.extension_mem_ZIrr φ (Submodule.subset_span hφ)) hχS h2

/-- **`β̄ − β = ζ_0^ν − ζ̄_0^ν`** (the `hbeta_conj_sub` input of `delta_isReal`). -/
theorem beta_conj_sub (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).beta.conj - (data.h78 hG).beta
      = (data.h78 hG).nu ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct)
        - (data.h78 hG).nu
            ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
  classical
  have := data.kernelIn_normal
  set hyp := data.typeIHyp.dadeData.dade with hhyp
  set dade := hyp.fullDadeIsometryData with hdade
  obtain ⟨j₁, hj₁ne, hj₁⟩ := data.exists_conjIndex hG
  -- `ζ_ind = Ind 1_H` is real.
  have hind_real : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)).conj
      = (data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H) := by
    change (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)).conj
      = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ)
    rw [data.triv, conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  -- `S`-memberships of `ζ_0` and `ζ̄_0 = ζ_{j₁}`.
  have hzd_mem : (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
      ∈ data.typeIHyp.Sset := data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero)
  have hj₁_mem : (data.h78 hG).hyp76.zeta j₁ ∈ data.typeIHyp.Sset :=
    data.zeta_mem_Sset (by rw [← data.h78_ind1H_eq hG]; exact hj₁ne)
  have hsupp' : ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
        - (1 : ℂ) • (data.h78 hG).hyp76.zeta j₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
    rw [one_smul]; exact data.zeta_sub_conj_support hG hj₁
  have hagree := coherence_hagree_dadeMap hyp data.coh hzd_mem hj₁_mem
    (m0 := 1) (mi := 1) (by norm_num) (by norm_num) hsupp'
  -- `dade.toDadeMap` on supported functions is the ℤ-linear `dadeIntegralCharacterMap`.
  have hbridge : ∀ (φ : ClassFunction ↥L ℂ)
      (hφ : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (typeIA L data.typeIHyp.typeI) L),
      dade.toDadeMap ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩
        = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade φ := by
    intro φ hφ
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp dade hφ]
    rfl
  have hiz_supp : ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)
        - (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L :=
    (data.h78 hG).diff_support
  have hbeta_eq : (data.h78 hG).beta
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade
          ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H)
            - (data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)) := by
    rw [← hbridge _ hiz_supp]; rfl
  have hconjbridgeL : ∀ X : ClassFunction ↥L ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hconjbridgeG : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hLHS : (data.h78 hG).beta.conj - (data.h78 hG).beta
      = dade.toDadeMap ⟨(data.h78 hG).hyp76.zeta ((data.h78 hG).zetaDistinct)
          - (1 : ℂ) • (data.h78 hG).hyp76.zeta j₁,
          (ClassFunction.mem_supportedSubmodule).mpr hsupp'⟩ := by
    rw [hbridge _ hsupp', hbeta_eq,
      hconjbridgeG (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp dade _),
      ← OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm hyp dade
        Complex.conjAe.toRingEquiv hiz_supp, ← hconjbridgeL, ← map_sub]
    congr 1
    rw [one_smul, ClassFunction.conj_sub, hind_real, ← hj₁]
    abel
  rw [hLHS, hagree, ← hj₁, data.h78_nu_eq, one_smul]

/-- **The (7.9) residual `Δ = β − 1_G + ζ_0^ν` is real** (odd order). -/
theorem delta_isReal (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ClassFunction.IsReal (data.h78 hG).delta := by
  obtain ⟨j₁, hj₁ne, hj₁⟩ := data.exists_conjIndex hG
  have hzd_mem : (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct
      ∈ data.typeIHyp.Sset := data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero)
  have hj₁_mem : (data.h78 hG).hyp76.zeta j₁ ∈ data.typeIHyp.Sset :=
    data.zeta_mem_Sset (by rw [← data.h78_ind1H_eq hG]; exact hj₁ne)
  have h2 : ∃ ψ ∈ data.typeIHyp.Sset,
      ψ ≠ (data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct :=
    ⟨_, hj₁_mem, by rw [hj₁]; exact (data.h78_zeta_ne_conj hG hG.odd).symm⟩
  have hnu_conj : ((data.h78 hG).nu
        ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct)).conj
      = (data.h78 hG).nu
        ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct).conj := by
    rw [data.h78_nu_eq]
    exact data.coherence_extension_conj hG hzd_mem h2
  exact _root_.OddOrder.Peterfalvi.S09.delta_isReal (data.h78 hG) hnu_conj
    (data.beta_conj_sub hG)

/-- **The residual `Δ` is a virtual character** (coherence + irreducible sources). -/
theorem delta_mem_ZIrr (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).delta ∈ ZIrr G :=
  (data.h78 hG).delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent
    (data.isCoherentSourceSet hG) rfl (data.h78_ind_mem_ZIrr hG)
    (data.h78_zeta_irreducible hG)

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S15_SAndTGrid.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`β_L^τ` is supported in `Ã(A(L))`**: the input `Ind_H^L 1 − φ` is `A(L)`-supported — at
`1` the value is `e − e = 0` (`induce_apply_one` + the degree hypothesis), and off `1` its
support lies in nontrivial kernel-conjugates (`support`s of both `Ind` terms), which land in
`A(L)` by `H^# ⊆ A(L)` (`sharpSubgroup_H_subset_typeIA`) and the `L`-conjugation invariance of
`A(L)` (`L_normalizes_A`).  Hence the Dade lift agrees with the (2.5) Dade map there
(`dadeIntegralCharacterMap_apply_of_support`), which vanishes off `Ã(A(L)) = dadeSupport`
(`IsDadeMap.map_eq_zero_of_not_mem_dadeSupport`). -/
theorem typeIBetaL_support_subset_dadeSupport [Finite G] {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) (φ : ClassFunction ↥L ℂ)
    (hφ : φ ∈ typeISetup.Sset)
    (hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    (typeIBetaL typeISetup φ).support ⊆ typeISetup.dadeData.dade.dadeSupport := by
  classical
  set H' : Subgroup ↥L := (typeISetup.H).subgroupOf L with hH'def
  set ι : ClassFunction ↥L ℂ :=
    ClassFunction.induce H' (trivialClassFunction ↥H') with hιdef
  have hsupp : (ι - φ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.GroupTheory.typeIA L typeISetup.typeI) L := by
    intro z hz
    have hzne : (ι - φ) z ≠ 0 := hz
    have hz1 : z ≠ 1 := by
      rintro rfl
      apply hzne
      rw [ClassFunction.sub_apply, hιdef, ClassFunction.induce_apply_one,
        trivialClassFunction_apply, mul_one, hdeg]
      have hHeq : H' = (maxNilpotentNormalHall L).subgroupOf L := by
        rw [hH'def]
        change (typeISetup.typeI.typeF.H).subgroupOf L = _
        rw [typeISetup.typeI.typeF.H_eq]
      rw [hHeq, sub_self]
    have hzc : z ∈ OddOrder.RepresentationTheory.ClassFunction.conjugatesInto H' := by
      by_contra hnotc
      apply hzne
      rw [ClassFunction.sub_apply]
      obtain ⟨θ, -, hφeq⟩ := hφ
      have hφz : ClassFunction.induce ((typeISetup.typeI.typeF.H).subgroupOf L)
          (θ : ClassFunction ↥((typeISetup.typeI.typeF.H).subgroupOf L) ℂ) z = 0 :=
        ClassFunction.induce_eq_zero_of_not_conjugatesInto _ hnotc
      rw [hιdef, ClassFunction.induce_eq_zero_of_not_conjugatesInto _ hnotc, hφeq, hφz,
        sub_zero]
    obtain ⟨c, hc⟩ := hzc
    have hcne : c⁻¹ * z * c ≠ 1 := by
      intro h1
      apply hz1
      have h2 := congrArg (fun w => c * w * c⁻¹) h1
      simpa [mul_assoc] using h2
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    have hmem : ((c⁻¹ * z * c : ↥L) : G) ∈ sharpSubgroup typeISetup.typeI.typeF.H :=
      ⟨Subgroup.mem_subgroupOf.mp hc, fun h1 => hcne (Subtype.ext h1)⟩
    have hA := sharpSubgroup_H_subset_typeIA typeISetup.typeI hmem
    have hconjA := typeISetup.dadeData.dade.L_normalizes_A c hA
    simpa [mul_assoc] using hconjA
  intro x hx
  by_contra hnot
  apply hx
  change typeIBetaL typeISetup φ x = 0
  rw [typeIBetaL,
    show typeISetup.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        typeISetup.dadeData.dade
        (typeISetup.dadeData.dade.fullDadeIsometryData) from rfl,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support _ _ hsupp]
  exact (typeISetup.dadeData.dade.isDadeMap_dadeMap).map_eq_zero_of_not_mem_dadeSupport _ _ hnot

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.a), `β_L^τ`-column instance**: the (13.19.a) support disjointness for the specific
`Ã(L)`-supported `β_L^τ = typeIBetaL φ` (`typeIBetaL_support_subset_dadeSupport`), a thin instance
of the general `dadeSupport_betaGrid_disjoint_support`. -/
theorem typeIBetaL_dadeS_betaGrid_disjoint_support_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ))
    (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    Disjoint (typeIBetaL typeISetup φ).support
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
        ((hyp.dadeHypS0 _hG).fullDadeIsometryData)
        (betaGrid hyp j)).support :=
  dadeSupport_betaGrid_disjoint_support_of_c_eq_one _hG hnoV hyp hc1 typeISetup
    (typeIBetaL typeISetup φ)
    (typeIBetaL_support_subset_dadeSupport typeISetup φ _hφ _hdeg) j hj

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.a) support disjointness**: `Ã(L) ∩ (P^G ∪ W^G) = ∅` — the order of an `Ã(L)`-element
is divisible by a prime divisor of `|H|`, and `|H|` is coprime to `p q` ((8.17.a)); `β_L^τ` is
supported in `Ã(L)`-classes while `β_S^τ` is supported in `P^# ∪ (W∖(W₁∪W₂))^G` ((13.18.a)).
The column-`#1` instance of `typeIBetaL_dadeS_betaGrid_disjoint_support`. -/
theorem typeIBetaL_betaS_disjoint_support_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ typeISetup.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    Disjoint (typeIBetaL typeISetup φ).support (tauSbetaGrid _hG hyp).support := by
  rw [tauSbetaGrid]
  exact typeIBetaL_dadeS_betaGrid_disjoint_support_of_c_eq_one _hG hnoV hyp hc1
    typeISetup φ _hφ _hdeg ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Bridge**: `β_L^τ = τ₁(Ind_H^L 1_H − ζ_0)` at the distinguished member `ζ_0 = dataL.zeta 0` is
literally the §7.8 `beta` of the bundle (`(dataL.h78 hG).beta = τ(Ind_H^L 1_H − ζ_0)`).  Both are
the Dade image of `Ind_H^L 1_H − ζ_0`; the §9 `Hypothesis71.τ` and the §7 `tau` agree on supported
inputs (`toHypothesis71_tau_apply`), and `ζ_{ind1H} = Ind_H^L 1_H` (`dataL.triv`). -/
theorem typeIBetaL_zeta0_eq_h78_beta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) :
    typeIBetaL dataL.typeIHyp (dataL.zeta 0) = (dataL.h78 hG).beta := by
  have := dataL.kernelIn_normal
  rw [OddOrder.Peterfalvi.S09.Hypothesis78.beta_def]
  change dataL.typeIHyp.tau _ = dataL.typeIHyp.toHypothesis71.τ _
  rw [dataL.typeIHyp.toHypothesis71_tau_apply]
  apply congrArg dataL.typeIHyp.tau
  change ClassFunction.induce ((dataL.typeIHyp.H).subgroupOf L)
      (trivialClassFunction ↥((dataL.typeIHyp.H).subgroupOf L)) - dataL.zeta 0
    = (dataL.h78 hG).hyp76.zeta (dataL.h78 hG).ind1H
      - (dataL.h78 hG).hyp76.zeta (dataL.h78 hG).zetaDistinct
  rw [dataL.h78_ind1H_eq, dataL.h78_zeta_eq, dataL.h78_zetaDistinct_eq, dataL.h78_zeta_eq]
  congr 1
  -- `Ind_H^L 1_H = ζ_{ind1H}` (`θ ind1H = 1_H`, `dataL.triv`)
  change ClassFunction.induce ((dataL.typeIHyp.H).subgroupOf L)
      (trivialClassFunction ↥((dataL.typeIHyp.H).subgroupOf L))
    = ClassFunction.induce dataL.kernelIn (dataL.θ dataL.ind1H : ClassFunction _ ℂ)
  rw [dataL.triv, IrreducibleCharacter.coe_trivialIrreducibleCharacter]
  rfl

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) parity core** (Coq `odd_bSphi_bLeta`): at the distinguished member `ζ_0`,
the S-pairing `bSphi = ⟨β_S^τ, ζ_0^{τ₁}⟩` and the `η`-pairing `bLeta = ⟨β_L^τ, η_{01}⟩` are
integers whose **sum is odd**.  From `0 = ⟨β_L^τ, β_S^τ⟩` (disjoint support (13.19.a)),
`β_L^τ = 1 − ζ_0^{τ₁} + Δ_L` (the §7.8 residual `delta`), `β_S^τ = 1 − η_{01} + Γ_S`
((13.18.c) `gammaGrid_defGamma`), and `⟨Δ_L, Γ_S⟩` even (`cfdot_real_vchar_even`: both real
virtual characters orthogonal to `1_G`). -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) :
    ∃ nS nL : ℤ,
      ClassFunction.inner (tauSbetaGrid hG hyp)
          (dataL.coh.extension (dataL.zeta 0)) = (nS : ℂ) ∧
        ClassFunction.inner (typeIBetaL dataL.typeIHyp (dataL.zeta 0))
            (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
          = (nL : ℂ) ∧
        Odd (nS + nL) := by
  classical
  -- Abbreviations (kept as explicit terms to avoid `set`-fold clashes with lemma outputs).
  have hj1lt : (1 : ℕ) < hyp.p := by have := hyp.three_le_p; omega
  -- `ζ_0^{τ₁} = ν(ζ_0)` (definitional bridge).
  have hνζ : (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta (dataL.h78 hG).zetaDistinct)
      = dataL.coh.extension (dataL.zeta 0) := rfl
  -- ZIrr memberships.
  have hζextZ : dataL.coh.extension (dataL.zeta 0) ∈ OddOrder.RepresentationTheory.ZIrr G :=
    dataL.coh.extension_mem_ZIrr _
      (Submodule.subset_span (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)))
  have hΓSZ : GammaGrid hG hyp ∈ OddOrder.RepresentationTheory.ZIrr G :=
    gammaGrid_mem_ZIrr_of_c_eq_one hG hnoV hyp hc1
  have hβLZ : (dataL.h78 hG).beta ∈ OddOrder.RepresentationTheory.ZIrr G :=
    (dataL.h78 hG).beta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible
      (dataL.h78_ind_mem_ZIrr hG) (dataL.h78_zeta_irreducible hG)
  have hη01Z : hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩ ∈ OddOrder.RepresentationTheory.ZIrr G :=
    OddOrder.Peterfalvi.S16.eta_mem_ZIrr hyp _ _
  -- `β_S^τ = Γ_S + 1 − η_{01}`  ((13.18.c) `gammaGrid_defGamma`).
  have hβSdecomp : tauSbetaGrid hG hyp
      = GammaGrid hG hyp + OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩ := by
    have h := gammaGrid_defGamma hG hnoV hyp ⟨1, hj1lt⟩ (by simp)
    rw [tauSbetaGrid, ← h]; abel
  -- `Δ_L = β_L^τ − 1 + ζ_0^{τ₁}`, hence `β_L^τ = 1 − ζ_0^{τ₁} + Δ_L`.
  have hΔ : (dataL.h78 hG).delta
      = (dataL.h78 hG).beta - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        + dataL.coh.extension (dataL.zeta 0) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis78.delta, hνζ]
  have hβLdecomp : (dataL.h78 hG).beta
      = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G - dataL.coh.extension (dataL.zeta 0)
        + (dataL.h78 hG).delta := by rw [hΔ]; abel
  -- The two output integers.
  obtain ⟨nS, hnS⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hΓSZ hζextZ
  obtain ⟨nL, hnL⟩ := OddOrder.RepresentationTheory.ClassFunction.inner_mem_ZIrr_int hβLZ hη01Z
  -- `⟨Δ_L, Γ_S⟩` is an even integer  (`cfdot_real_vchar_even`, both real virtual `⊥ 1`).
  obtain ⟨z, a, b, hz, ha, hb, heven⟩ := cfdot_real_vchar_even hG.odd
    (dataL.delta_mem_ZIrr hG) (dataL.delta_isReal hG) hΓSZ
      (gammaGrid_real_of_c_eq_one hG hnoV hyp hc1)
  have hΔ_one : ClassFunction.inner (dataL.h78 hG).delta
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 :=
    (dataL.h78 hG).delta_orth_one (dataL.betaDecomp hG)
  have hΓS_one : ClassFunction.inner (GammaGrid hG hyp)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 :=
    gammaGrid_orthogonal_one_of_c_eq_one hG hnoV hyp hc1
  have ha0 : a = 0 := by
    rw [show (trivialIrreducibleCharacter G : ClassFunction G ℂ)
        = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G from rfl, hΔ_one] at ha
    exact_mod_cast ha
  have hb0 : b = 0 := by
    rw [show (trivialIrreducibleCharacter G : ClassFunction G ℂ)
        = OddOrder.Peterfalvi.S09.Hypothesis71.constOne G from rfl, hΓS_one] at hb
    exact_mod_cast hb
  have hzeven : Even z := by rw [ha0, hb0] at heven; simpa using heven
  -- vanishing inner products.
  have hζ_one : ClassFunction.inner (dataL.coh.extension (dataL.zeta 0))
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 0 := by
    rw [← hνζ]; exact (dataL.h78 hG).zetaImage_orth_one (dataL.betaDecomp hG)
  have hζ_eta : ClassFunction.inner (dataL.coh.extension (dataL.zeta 0))
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩) = 0 :=
    coherent_extension_orthogonal_eta_of_mem_Sset hG hnoV hyp dataL _
      (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) _ _
  have h_one_ext : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (dataL.coh.extension (dataL.zeta 0)) = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, hζ_one, star_zero]
  have h_eta_ext : ClassFunction.inner (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩)
      (dataL.coh.extension (dataL.zeta 0)) = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, hζ_eta, star_zero]
  have hone_eta : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩) = 0 := by
    have h00 : OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
        = hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ := by
      rw [OddOrder.Peterfalvi.S16.eta_principal_eq_trivial hyp]; rfl
    rw [h00, OddOrder.Peterfalvi.S16.eta_orthonormal hyp,
      if_neg (by rintro ⟨-, h2⟩; exact absurd (congrArg Fin.val h2) (by simp))]
  have hone_one : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G) = 1 :=
    OddOrder.Peterfalvi.S09.Hypothesis71.constOne_inner_self_eq_one
  -- reversed-direction pieces.
  have h_one_ΓS : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (GammaGrid hG hyp) = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, hΓS_one, star_zero]
  have h_ζext_ΓS : ClassFunction.inner (dataL.coh.extension (dataL.zeta 0))
      (GammaGrid hG hyp) = (nS : ℂ) := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm, hnS,
      star_intCast]
  -- `⟨Δ_L, η_{01}⟩ = ⟨β_L^τ, η_{01}⟩ = nL`.
  have hΔ_eta : ClassFunction.inner (dataL.h78 hG).delta
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, hj1lt⟩) = (nL : ℂ) := by
    rw [hΔ, ClassFunction.inner_add_left, ClassFunction.inner_sub_left, hone_eta, hζ_eta,
      sub_zero, add_zero, hnL]
  -- `⟨β_S^τ, ζ_0^{τ₁}⟩ = ⟨Γ_S, ζ_0^{τ₁}⟩ = nS`.
  have hbS : ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0))
      = (nS : ℂ) := by
    rw [hβSdecomp, ClassFunction.inner_sub_left, ClassFunction.inner_add_left,
      hnS, h_one_ext, h_eta_ext, add_zero, sub_zero]
  refine ⟨nS, nL, hbS, by rw [typeIBetaL_zeta0_eq_h78_beta hG dataL]; exact hnL, ?_⟩
  -- degree of the distinguished member.
  have hdeg0 : dataL.zeta 0 (1 : ↥L)
      = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
    rw [show dataL.zeta 0 (1 : ↥L)
        = ClassFunction.induce dataL.kernelIn (dataL.θ 0 : ClassFunction _ ℂ) (1 : ↥L) from rfl,
      dataL.deg0]
    congr 2
    show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  -- Parity: `0 = ⟨β_L^τ, β_S^τ⟩ = 1 − nS − nL + z`, hence `nS + nL = 1 + z` is odd.
  have hdisj : ClassFunction.inner ((dataL.h78 hG).beta) (tauSbetaGrid hG hyp) = 0 := by
    rw [← typeIBetaL_zeta0_eq_h78_beta hG dataL]
    exact OddOrder.RepresentationTheory.ClassFunction.inner_eq_zero_of_disjoint_support
      (typeIBetaL_betaS_disjoint_support_of_c_eq_one hG hnoV hyp hc1 dataL.typeIHyp _
        (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero)) hdeg0)
  have hkey : (0 : ℂ) = 1 - (nS : ℂ) - (nL : ℂ) + (z : ℂ) := by
    have e := hdisj
    rw [hβLdecomp, hβSdecomp] at e
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
      ClassFunction.inner_add_right, ClassFunction.inner_sub_right] at e
    rw [hone_one, hone_eta, h_one_ΓS, hζ_one, hζ_eta, h_ζext_ΓS, hΔ_one, hΔ_eta, ← hz] at e
    linear_combination -e
  have hInt : nS + nL = 1 + z := by
    have h2 : ((nS + nL : ℤ) : ℂ) = ((1 + z : ℤ) : ℂ) := by push_cast; linear_combination hkey
    exact_mod_cast h2
  rw [hInt]
  obtain ⟨k, hk⟩ := hzeven
  exact ⟨k, by omega⟩

end OddOrder.Peterfalvi.S15

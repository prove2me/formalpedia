-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.typeI_caseC_bound_c1_of_c_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:24:58.1622+00:00
-- url     : https://prove2.me/submissions/d4d56984-696f-46e5-8ce7-1efa0672ba14

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean
--   OddOrder/Peterfalvi/S15_BridgeCharacter.lean
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
--   OddOrder/Peterfalvi/S16_PairingBessel.lean
--   OddOrder/Peterfalvi/S15_SAndT.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
import Theorems.Thm_OddOrder_RepresentationTheory_card_index_mul_sum_induced_family_degree_sq
import Theorems.Thm_OddOrder_Peterfalvi_S15_gammaGrid_Y_norm_bound_aux
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_tauS_mu_row0_vanish_on_V
import Theorems.Thm_OddOrder_Peterfalvi_S15_dadeSupport_betaGrid_disjoint_support_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_coherent_extension_orthogonal_eta_of_mem_Sset

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

-- ===== OddOrder/Peterfalvi/S15_BridgeCharacter.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

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

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.d) residual-norm bound**: for any split `Γ = X + Y` with `X ⊥ Y` and `Y` orthogonal
to the whole `η`-grid `{η_{ik}}`, `‖Y‖² ≤ (u−1)/q` — fully proven (Coq `PFsection13.v:1915-1934`;
the earlier `Re⟨Γ,Γ⟩ ≤ (u−1)/q + 1` overstatement was corrected in issue 3003: `‖Γ‖²` itself is
**not** bounded, only the grid-orthogonal residual `Y`).  Public form of
`gammaGrid_Y_norm_bound_aux`, reconciling the caller's `Fintype G`/`Invertible` instances with
the `FiniteInduce`-scoped ones (both are `Subsingleton`). -/
theorem gammaGrid_Y_norm_bound_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (X Y : ClassFunction G ℂ), GammaGrid hG hyp = X + Y →
        ClassFunction.inner X Y = 0 →
        (∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) →
        (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ) := by
  intro _ _ X Y defXY oXY oYeta
  have h := gammaGrid_Y_norm_bound_aux hG hnoV hyp hc1 X Y defXY
    (by convert oXY using 2; exact Subsingleton.elim _ _)
    (fun i k => by convert oYeta i k using 2; exact Subsingleton.elim _ _)
  convert h using 3
  exact Subsingleton.elim _ _

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

/-- The principal index of `h78` is `ind1H` (definitional). -/
theorem h78_ind1H_eq : (data.h78 hG).ind1H = data.ind1H := rfl

/-- **Each nontrivial family member induces irreducibly** (general-index form of
`h78_zeta_irreducible`). -/
theorem zeta_irreducible_at {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta i) := by
  have := data.kernelIn_normal
  rw [data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ i)
    (data.theta_ne_trivial hi)

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_PairingBessel.lean =====
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

/-- `d_0 = 1` (the distinguished source is linear: `ζ_0(1) = e = [L:H]·θ_0(1)`). -/
theorem d_zero_eq_one : data.d 0 = 1 := by
  have := data.kernelIn_normal
  have h := data.zeta_deg 0
  have hz0 : data.zeta 0 (1 : ↥L) ≠ 0 := induce_apply_one_ne_zero _ (data.θ 0)
  have h2 : data.d 0 * data.zeta 0 (1 : ↥L) = 1 * data.zeta 0 (1 : ↥L) := by
    rw [one_mul, ← h]
  exact mul_right_cancel₀ hz0 h2

/-- `d_i` is a positive natural (the source degree). -/
theorem exists_d_natCast (i : Fin (data.n + 1)) :
    ∃ m : ℕ, 0 < m ∧ data.d i = (m : ℂ) := by
  obtain ⟨m, hm, hcast⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (data.θ i)
  exact ⟨m, hm, hcast⟩

/-- `star (d_i) = d_i`. -/
theorem d_star (i : Fin (data.n + 1)) : star (data.d i) = data.d i := by
  obtain ⟨m, -, hm⟩ := data.exists_d_natCast i
  rw [hm, star_natCast]

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S15_SAndT.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`(β_S^τ, ζ_i^{τ₁}) = d_i·bSphi`** (`i ≠ ind1H`): the `β_S^τ`-pairing is constant along the
`L`-family up to degree.  For `i ≠ 0` the difference `ζ_i^{τ₁} − d_i ζ_0^{τ₁} = τ(ζ_i − d_i ζ_0)`
(`hagree`) is an `Ã(L)`-supported Dade image, disjoint from `supp β_S^τ` ((13.19.a)); for `i = 0`
it is `bSphi` (`d_0 = 1`). -/
theorem inner_tauSbetaGrid_coh_ext_zeta_eq_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nS : ℤ)
    (hnS : ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0))
        = (nS : ℂ))
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H) :
    ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta i))
      = dataL.d i * (nS : ℂ) := by
  classical
  have := dataL.kernelIn_normal
  by_cases hi0 : i = 0
  · subst hi0
    rw [dataL.d_zero_eq_one, one_mul]; exact hnS
  · have hsupp : (dataL.coh.extension (dataL.zeta i)
        - dataL.d i • dataL.coh.extension (dataL.zeta 0)).support
        ⊆ dataL.typeIHyp.dadeData.dade.dadeSupport := by
      have hagree := dataL.hagree hG i hi0 hi
      rw [← hagree]
      intro g hg
      rw [ClassFunction.mem_support] at hg
      by_contra hgnot
      have hdade := (dataL.typeIHyp.dadeData.dade.fullDadeIsometryData
).toDadeIsometryData.isDadeMap
      exact hg (hdade.map_eq_zero_of_not_mem_dadeSupport _ g hgnot)
    have hzero : ClassFunction.inner (tauSbetaGrid hG hyp)
        (dataL.coh.extension (dataL.zeta i)
          - dataL.d i • dataL.coh.extension (dataL.zeta 0)) = 0 := by
      apply ClassFunction.inner_eq_zero_of_disjoint_support
      rw [tauSbetaGrid]
      exact (dadeSupport_betaGrid_disjoint_support_of_c_eq_one hG hnoV hyp hc1
        dataL.typeIHyp _ hsupp ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)).symm
    rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
      dataL.d_star, hnS, sub_eq_zero] at hzero
    exact hzero

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`(Γ_S, ζ_i^{τ₁}) = bSphi·d_i`** (`i ≠ ind1H`): the `η`-orthogonal residual `Γ_S = GammaGrid`
pairs with the `L`-family exactly as `β_S^τ` does — `Γ_S = β_S^τ − 1 + η_{01}`
(`gammaGrid_defGamma`),
and the `1_G`/`η_{01}` parts are orthogonal to the coherent image (`(betaDecomp).orth_one`,
(13.19.b)). -/
theorem inner_gammaGrid_coh_ext_zeta_eq_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nS : ℤ)
    (hnS : ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0))
        = (nS : ℂ))
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H) :
    ClassFunction.inner (GammaGrid hG hyp) (dataL.coh.extension (dataL.zeta i))
      = (nS : ℂ) * dataL.d i := by
  classical
  have hGdecomp : GammaGrid hG hyp = tauSbetaGrid hG hyp
      - OddOrder.Peterfalvi.S09.Hypothesis71.constOne G
      + hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩ := by
    have h := gammaGrid_defGamma hG hnoV hyp ⟨1, by have := hyp.three_le_p; omega⟩ (by norm_num)
    rw [tauSbetaGrid, ← h]
  have hi_h78 : i ≠ (dataL.h78 hG).ind1H := by rw [dataL.h78_ind1H_eq]; exact hi
  have h1 : ClassFunction.inner (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G)
      (dataL.coh.extension (dataL.zeta i)) = 0 := by
    rw [show dataL.coh.extension (dataL.zeta i)
        = (dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i) from rfl,
      OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm,
      (dataL.betaDecomp hG).orth_one i hi_h78, star_zero]
  have hη : ClassFunction.inner
      (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
      (dataL.coh.extension (dataL.zeta i)) = 0 := by
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.ClassFunction.inner_symm,
      coherent_extension_orthogonal_eta_of_mem_Sset hG hnoV hyp dataL _
        (dataL.zeta_mem_Sset hi) _ _,
      star_zero]
  rw [hGdecomp, ClassFunction.inner_add_left, ClassFunction.inner_sub_left, h1, hη,
    inner_tauSbetaGrid_coh_ext_zeta_eq_of_c_eq_one hG hnoV hyp hc1 dataL nS hnS hi,
    sub_zero, add_zero, mul_comm]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.c) case (c1) bound**: if `bSphi = (β_S^τ, ζ_0^{τ₁}) ≠ 0` (the S-parity is odd),
then `(|H| − 1)/e ≤ (u − 1)/q`.  The `η`-orthogonal projection `Y = bSphi·Σ d_i ζ_i^{τ₁}` of
`Γ_S = GammaGrid` (coefficients `(Γ_S, ζ_i^{τ₁}) = bSphi·d_i`,
`inner_gammaGrid_coh_ext_zeta_eq`) satisfies the (13.18.d) bound `‖Y‖² ≤ (u−1)/q`
(`gammaGrid_Y_norm_bound`); with `‖Y‖² = bSphi²·Σ d_i²`, `Σ d_i² = (|H|−1)/e`
(`card_index_mul_sum_induced_family_degree_sq`), and `bSphi² ≥ 1`, this gives the bound.
Mirror of the M-side `bessel_bound_of_inner_beta_zeta_ne_zero` (S16_PairingBessel). -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nS : ℤ)
    (hnS : ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0))
        = (nS : ℂ))
    (hnS0 : nS ≠ 0) :
    (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
        / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ) ≤
      ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ)) := by
  classical
  have := dataL.kernelIn_normal
  -- index/card bridges to `kernelIn`.
  have he_eq : (dataL.kernelIn).index = ((maxNilpotentNormalHall L).subgroupOf L).index := by
    change ((dataL.typeIHyp.typeI.typeF.H).subgroupOf L).index = _
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  have hcard_eq : Nat.card ↥dataL.kernelIn = Nat.card ↥dataL.typeIHyp.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe dataL.kernel_le).toEquiv
  -- the weighted `L`-family vector `v = Σ d_i ζ_i^{τ₁}`.
  set v : ClassFunction G ℂ := ∑ i ∈ Finset.univ.erase dataL.ind1H,
    dataL.d i • dataL.coh.extension (dataL.zeta i) with hvdef
  -- orthonormality of the `ζ_i^{τ₁}`.
  have hON : ∀ i ∈ Finset.univ.erase dataL.ind1H, ∀ j ∈ Finset.univ.erase dataL.ind1H,
      ClassFunction.inner (dataL.coh.extension (dataL.zeta i))
        (dataL.coh.extension (dataL.zeta j)) = if i = j then 1 else 0 := by
    intro i hi j hj
    rw [dataL.nu_isometry i j (Finset.mem_erase.mp hi).1 (Finset.mem_erase.mp hj).1]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact IsIrreducibleCharacter.inner_self_eq_one
        (dataL.zeta_irreducible_at hG (Finset.mem_erase.mp hi).1)
    · rw [if_neg hij]
      exact OddOrder.Peterfalvi.S09.Cert.induce_family_orthogonal_of_injective dataL.kernelIn
          dataL.θ dataL.inj i j hij
  -- `⟨v, v⟩ = Σ d_i²`.
  have hvv : ClassFunction.inner v v
      = ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hvdef, inner_sum_left]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ClassFunction.inner_smul_left, inner_sum_right,
      Finset.sum_eq_single_of_mem i hi (fun j hj hji => by
        rw [OddOrder.RepresentationTheory.inner_smul_right, hON i hi j hj,
          if_neg (Ne.symm hji), mul_zero]),
      OddOrder.RepresentationTheory.inner_smul_right, hON i hi i hi, if_pos rfl,
      dataL.d_star, mul_one, sq]
  -- `Σ d_i² = (|kernelIn| − 1)/e`  (degree-square sum).
  have hidx_ne : ((dataL.kernelIn).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have hdeg_sum := card_index_mul_sum_induced_family_degree_sq dataL.hFrob dataL.θ
    dataL.ind1H dataL.triv dataL.inj dataL.cover
  have hSval : ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2
      = ((Nat.card ↥dataL.kernelIn : ℂ) - 1) / ((dataL.kernelIn).index : ℂ) := by
    rw [eq_div_iff hidx_ne, mul_comm]
    exact hdeg_sum
  -- `⟨GammaGrid, v⟩ = nS·Σ d_i²`.
  have hGv : ClassFunction.inner (GammaGrid hG hyp) v
      = (nS : ℂ) * ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hvdef, inner_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [OddOrder.RepresentationTheory.inner_smul_right, dataL.d_star,
      inner_gammaGrid_coh_ext_zeta_eq_of_c_eq_one hG hnoV hyp hc1
        dataL nS hnS (Finset.mem_erase.mp hi).1, sq]
    ring
  -- the projection `Y = nS • v` and the complement `X = GammaGrid − Y`.
  set Y : ClassFunction G ℂ := (nS : ℂ) • v with hYdef
  -- `Y ⊥ η`.
  have hYeta : ∀ (a : Fin hyp.q) (b : Fin hyp.p), ClassFunction.inner Y (hyp.eta a b) = 0 := by
    intro a b
    rw [hYdef, hvdef, ClassFunction.inner_smul_left, inner_sum_left]
    rw [Finset.sum_eq_zero fun i hi => by
      rw [ClassFunction.inner_smul_left,
        coherent_extension_orthogonal_eta_of_mem_Sset hG hnoV hyp dataL _
          (dataL.zeta_mem_Sset (Finset.mem_erase.mp hi).1) a b, mul_zero], mul_zero]
  -- `⟨Y, Y⟩ = nS²·Σ d_i²`.
  have hYY : ClassFunction.inner Y Y
      = (nS : ℂ) ^ 2 * ∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2 := by
    rw [hYdef, ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hvv, show star ((nS : ℂ)) = (nS : ℂ) by simp]
    ring
  -- `⟨GammaGrid − Y, Y⟩ = 0`.
  have hXY : ClassFunction.inner (GammaGrid hG hyp - Y) Y = 0 := by
    rw [ClassFunction.inner_sub_left, hYY, hYdef,
      OddOrder.RepresentationTheory.inner_smul_right, hGv,
      show star ((nS : ℂ)) = (nS : ℂ) by simp]
    ring
  -- the (13.18.d) bound.
  have hbound := gammaGrid_Y_norm_bound_of_c_eq_one hG hnoV hyp hc1
    (GammaGrid hG hyp - Y) Y (by abel) hXY hYeta
  -- the real value `Sr = (|kernelIn| − 1)/e` of `Σ d_i²`.
  set Sr : ℝ := ((Nat.card ↥dataL.kernelIn : ℝ) - 1) / ((dataL.kernelIn).index : ℝ) with hSrdef
  have hSc : (∑ i ∈ Finset.univ.erase dataL.ind1H, dataL.d i ^ 2) = (Sr : ℂ) := by
    rw [hSval, hSrdef]; push_cast; ring
  have hYYre : (ClassFunction.inner Y Y).re = (nS : ℝ) ^ 2 * Sr := by
    rw [hYY, hSc,
      show (nS : ℂ) ^ 2 * (Sr : ℂ) = (((nS : ℝ) ^ 2 * Sr : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [hYYre] at hbound
  -- positivity facts.
  have hidx_pos : (0 : ℝ) < ((dataL.kernelIn).index : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hcard1 : (1 : ℝ) ≤ (Nat.card ↥dataL.kernelIn : ℝ) := by exact_mod_cast Nat.card_pos
  have hSr_nonneg : (0 : ℝ) ≤ Sr := by
    rw [hSrdef]; exact div_nonneg (by linarith) hidx_pos.le
  have hnS_sq : (1 : ℝ) ≤ (nS : ℝ) ^ 2 := by
    have hint : (1 : ℤ) ≤ nS ^ 2 := by
      nlinarith [Int.one_le_abs hnS0, sq_abs nS]
    exact_mod_cast hint
  -- `Sr ≤ nS²·Sr = ‖Y‖² ≤ (u−1)/q`.
  have hfinal_R : Sr ≤ (((hyp.u : ℚ) - 1) / (hyp.q : ℚ) : ℝ) :=
    le_trans (le_mul_of_one_le_left hSr_nonneg hnS_sq) hbound
  -- `1 ≤ u` (from `|U| = u·c`).
  have hu_pos : 1 ≤ hyp.u := by
    have hcard : 0 < Nat.card ↥hyp.U := Nat.card_pos
    rw [hyp.card_U_eq_uc] at hcard
    rcases Nat.eq_zero_or_pos hyp.u with h0 | h0
    · rw [h0, zero_mul] at hcard; exact absurd hcard (lt_irrefl 0)
    · exact h0
  -- cast the ℝ inequality back to the ℚ goal (through `kernelIn`).
  rw [← hcard_eq, ← he_eq]
  have hcard_ne : 1 ≤ Nat.card ↥dataL.kernelIn := Nat.card_pos
  have goal_R : ((((Nat.card ↥dataL.kernelIn - 1 : ℕ) : ℚ)
        / ((dataL.kernelIn).index : ℚ)) : ℝ)
      ≤ ((((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ)) : ℝ) := by
    have e1 : ((((Nat.card ↥dataL.kernelIn - 1 : ℕ) : ℚ)
        / ((dataL.kernelIn).index : ℚ)) : ℝ) = Sr := by
      rw [hSrdef, Nat.cast_sub hcard_ne]; push_cast; ring
    have e2 : ((((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ)) : ℝ)
        = (((hyp.u : ℚ) - 1) / (hyp.q : ℚ) : ℝ) := by
      rw [Nat.cast_sub hu_pos]; push_cast; ring
    rw [e1, e2]; exact hfinal_R
  exact_mod_cast goal_R

end OddOrder.Peterfalvi.S15

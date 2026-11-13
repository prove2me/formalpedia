-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.dadeSupport_betaGrid_disjoint_support_of_c_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:24:38.125183+00:00
-- url     : https://prove2.me/submissions/5e43d01b-6f5a-43ae-ba41-149f90107a4f

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean
--   OddOrder/Peterfalvi/S15_Gate3.lean
--   OddOrder/Peterfalvi/S15_BridgeCharacter.lean
--   OddOrder/Peterfalvi/S15_SAndTGrid.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTGrid
import Theorems.Thm_OddOrder_Peterfalvi_S04_Hypothesis_exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport
import Theorems.Thm_OddOrder_Peterfalvi_S15_betaGrid_support_of_c_eq_one
import Theorems.Thm_OddOrder_Peterfalvi_S15_card_LF_coprime_pq

-- ===== OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean =====
namespace OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

variable [Finite G]

/-- **Conjugate subgroups have the same type I status**: if `L` is type I and `conj g • L = M`,
then `M` is type I.  The Peterfalvi (13.17.b) input ruling out conjugacy of a type-`I` subgroup to
the type-II subgroups `S`, `T`. -/
theorem isTypeI_of_conj {L M : Subgroup G} (h : IsTypeI L) {g : G}
    (hconj : MulAut.conj g • L = M) : IsTypeI M :=
  hconj ▸ isTypeI_pointwise_smul (MulAut.conj g) h

end OddOrder.GroupTheory

-- ===== OddOrder/Peterfalvi/S15_Gate3.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Type is conjugacy-invariant** (the (13.17.a/b) `L ~ S`/`L ~ T` rule-out): a type-`I` maximal
subgroup `L` is not conjugate to any non-type-`I` maximal subgroup `M`.  If `conj g • L = M` then
`M` would be type `I` (`isTypeI_of_conj`, the automorphism-equivariance of the Peterfalvi taxonomy
— `OddOrder.GroupTheory.MaximalSubgroupTypeConj`), contradicting
`not_isTypeI_of_isTypeNonI`.  This is **gate-4 piece 1**, now discharged (sorry-free, axiom-clean);
reusable across the §16 conjugacy arguments. -/
theorem not_conj_of_isTypeI_of_isTypeNonI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L M : Subgroup G} (hLI : IsTypeI L) (hMmax : M ∈ maximalSubgroups G)
    (hMnonI : IsTypeNonI M) : ¬ ∃ g : G, MulAut.conj g • L = M :=
  fun ⟨_g, hg⟩ =>
    OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG hMmax hMnonI
      (OddOrder.GroupTheory.isTypeI_of_conj hLI hg)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_BridgeCharacter.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

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

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndTGrid.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`A(M) ⊆ H^#` for a Frobenius type-I maximal** (with `sharpSubgroup_H_subset_typeIA`,
equality — Coq `FTsupp_Frobenius`): an element of the type-I support `A(M)` centralizes some
`y ∈ H^#`, and in a Frobenius group the centralizer of a nontrivial kernel element lies in the
kernel (`IsFrobeniusGroup.centralizer_kernel_le`, Isaacs Thm 6.4). -/
theorem typeIA_subset_sharpSubgroup_of_frobenius [Finite G] {M : Subgroup G}
    (data : TypeIData M) {E : Subgroup ↥M}
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.typeF.H.subgroupOf M) E) :
    typeIA M data ⊆ sharpSubgroup data.typeF.H := by
  rintro x ⟨hxM, hx1, y, hy, hxc⟩
  have hyM : y ∈ M := data.typeF.H_le hy.1
  have hyH' : (⟨y, hyM⟩ : ↥M) ∈ data.typeF.H.subgroupOf M := by
    rw [Subgroup.mem_subgroupOf]
    exact hy.1
  have hy1' : (⟨y, hyM⟩ : ↥M) ≠ 1 := fun h => hy.2 (by
    simpa using congrArg Subtype.val h)
  have hxc' : (⟨x, hxM⟩ : ↥M) ∈ Subgroup.centralizer ({⟨y, hyM⟩} : Set ↥M) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hxc
    exact Subtype.ext (by push_cast; exact hcomm)
  have hxH' := hF.centralizer_kernel_le _ hyH' hy1' hxc'
  rw [Subgroup.mem_subgroupOf] at hxH'
  exact ⟨hxH', hx1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19.a) support disjointness, arbitrary-column form** (Coq `o_tauL_S`): for every
`j ≠ 0`, `β_L^τ` (supported in `Ã(L)`-classes) has support disjoint from the `S`-side Dade
image `τ_S(β_j)` (supported in `P^# ∪ (W∖(W₁∪W₂))^S`-classes, (13.18.a)) — the order of an
`Ã(L)`-element is divisible by a prime divisor of `|H|`, and `|H|` is coprime to `p q`
((8.17.a)).  The column-`#1` instance is `typeIBetaL_betaS_disjoint_support`; the general
column feeds the (13.19.c) zero-axis constancy through `gammaGrid_defGamma`. -/
theorem _root_.solution [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (χ : ClassFunction G ℂ)
    (hχ : χ.support ⊆ typeISetup.dadeData.dade.dadeSupport)
    (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    Disjoint χ.support
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
        ((hyp.dadeHypS0 _hG).fullDadeIsometryData)
        (betaGrid hyp j)).support := by
  classical
  rw [Set.disjoint_left]
  intro x hxL hxS
  -- L-side: a prime `r ∣ orderOf a` (`a ∈ A(L)`) divides `orderOf x`
  have hxD := hχ hxL
  obtain ⟨a, haA, r, hr, hra, hrx⟩ :=
    typeISetup.dadeData.dade.exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport hxD
  obtain ⟨frob₀, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius _hG hnoV typeISetup.maximal
    ⟨typeISetup.typeI⟩
  have hHeq : frob₀.typeI.typeF.H = typeISetup.typeI.typeF.H :=
    frob₀.typeI.typeF.H_eq.trans typeISetup.typeI.typeF.H_eq.symm
  have hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
      ((typeISetup.typeI.typeF.H).subgroupOf L) frob₀.complement := by
    have h := frob₀.frobenius
    rwa [hHeq] at h
  have haH := typeIA_subset_sharpSubgroup_of_frobenius typeISetup.typeI hfrob haA
  have hrLF : r ∣ Nat.card ↥(maxNilpotentNormalHall L) := by
    refine hra.trans ?_
    have hdvd := Subgroup.orderOf_dvd_natCard typeISetup.typeI.typeF.H haH.1
    rwa [typeISetup.typeI.typeF.H_eq] at hdvd
  -- S-side: `orderOf x ∣ p^q · (q·p)`
  have hbridge : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
        ((hyp.dadeHypS0 _hG).fullDadeIsometryData)
        (betaGrid hyp j)
      = ClassFunction.induce hyp.S (betaGrid hyp j) :=
    hyp.sInstance_dade0_eq_induce _hG hnoV
      (betaGrid_A0_support_of_c_eq_one _hG hyp hc1 j hj)
  rw [hbridge] at hxS
  have hxc :=
    OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_conjugatesIntoSet
      (betaGrid_support_of_c_eq_one _hG hyp hc1 j hj) hxS
  obtain ⟨c, hcS, hmem⟩ := hxc
  have hordx : orderOf (c⁻¹ * x * c) = orderOf x := by
    have hinj : orderOf ((MulAut.conj c⁻¹).toMonoidHom x) = orderOf x :=
      orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulEquiv.injective _) _
    rw [← hinj]
    congr 1
    simp [mul_assoc]
  have hxdvd : orderOf x ∣ hyp.p ^ hyp.q * (hyp.q * hyp.p) := by
    rcases hmem with hP | hV
    · -- `c⁻¹xc ∈ P^#`
      have hdvd : orderOf (c⁻¹ * x * c) ∣ Nat.card ↥hyp.P :=
        Subgroup.orderOf_dvd_natCard hyp.P hP.1
      rw [hordx, hyp.card_P_eq _hG hyp.Sdata_W2_eq] at hdvd
      exact hdvd.trans (dvd_mul_right _ _)
    · -- `c⁻¹xc` is `S`-conjugate to `w ∈ typePV ⊆ W`
      obtain ⟨w, hw, t, htS, hconjw⟩ := hV
      have hconjw' : t * w * t⁻¹ = c⁻¹ * x * c := hconjw
      have hordw : orderOf (c⁻¹ * x * c) = orderOf w := by
        rw [← hconjw']
        have hinj : orderOf ((MulAut.conj t).toMonoidHom w) = orderOf w :=
          orderOf_injective (MulAut.conj t).toMonoidHom (MulEquiv.injective _) _
        rw [← hinj]
        congr 1
      have hwW : w ∈ hyp.W := by
        have h1 : w ∈ hyp.Sdata.W := hw.1
        rw [hyp.Sdata.W_eq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq] at h1
        rwa [hyp.W_eq_join]
      have hdvdW : orderOf w ∣ Nat.card ↥hyp.W :=
        Subgroup.orderOf_dvd_natCard hyp.W hwW
      have hWnorm : hyp.W1 ≤ Subgroup.normalizer (hyp.W2 : Set G) := by
        intro v hv
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hcomm := hyp.W1_commutes_W2 v hv y hy
          rwa [show v * y * v⁻¹ = y by
            rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]]
        · intro hy
          have hz := hyp.W1_commutes_W2 v hv (v * y * v⁻¹) hy
          have h5 : v * (v * y * v⁻¹) = v * y := by
            rw [hz.eq]
            group
          have h6 : v * y * v⁻¹ = y := mul_left_cancel h5
          rwa [h6] at hy
      have hWcard : Nat.card ↥hyp.W = hyp.q * hyp.p := by
        rw [hyp.W_eq_join,
          OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint hWnorm
            hyp.W1_inf_W2_eq_bot, ← hyp.q_eq_card_W1, ← hyp.p_eq_card_W2]
      have hxw : orderOf x = orderOf w := by rw [← hordx, hordw]
      have hxqp : orderOf x ∣ hyp.q * hyp.p := by
        rw [hxw, ← hWcard]
        exact hdvdW
      exact hxqp.trans (dvd_mul_left _ _)
  -- a prime dividing both `|L_F|` and `p·q` contradicts (8.17.a)
  have hrpq : r ∣ hyp.p * hyp.q := by
    have h2 := hrx.trans hxdvd
    rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
    · exact dvd_mul_of_dvd_left (hr.dvd_of_dvd_pow h3) _
    · rcases (Nat.Prime.dvd_mul hr).mp h3 with h4 | h4
      · exact dvd_mul_of_dvd_right h4 _
      · exact dvd_mul_of_dvd_left h4 _
  have hnconjS := not_conj_of_isTypeI_of_isTypeNonI _hG ⟨typeISetup.typeI⟩
    hyp.S_maximal hyp.S_nonI
  have hnconjT := not_conj_of_isTypeI_of_isTypeNonI _hG ⟨typeISetup.typeI⟩
    hyp.T_maximal hyp.T_nonI
  have hcop := card_LF_coprime_pq _hG hyp typeISetup.maximal ⟨typeISetup.typeI⟩
    hnconjS hnconjT
  have hone : r ∣ 1 := hcop ▸ Nat.dvd_gcd hrLF hrpq
  exact hr.one_lt.ne' (Nat.dvd_one.mp hone)

end OddOrder.Peterfalvi.S15

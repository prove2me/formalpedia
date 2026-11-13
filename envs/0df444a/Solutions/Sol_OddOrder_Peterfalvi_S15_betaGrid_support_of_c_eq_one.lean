-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.betaGrid_support_of_c_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:17:09.986258+00:00
-- url     : https://prove2.me/submissions/781a93c2-3957-4924-a261-99d8be60ba49

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
--   OddOrder/Peterfalvi/S13_PrimeTIResidueBridge.lean
--   OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Theorems.Thm_OddOrder_Peterfalvi_S15_indPW1_apply_eq_one_of_mem_W1_sharp
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_mu_row0_apply_eq_zero_of_mem_derived_not_mem_P_of_c_eq_one

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

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section CountingLayer

open OddOrder.GroupTheory

/-- **Peterfalvi (4.3.c)+(13.3.c), the `W₁#` `μ`-value**: `μ_{0j}(x) = 1` for `x ∈ W₁`,
`x ≠ 1`.  The (4.3.c) value identity `mu_apply_of_not_mem_W2` applies (`x ∉ W₂` since
`W₁ ⊓ W₂ = ⊥` and `x ≠ 1`), giving `μ_{0j}(x) = δ_j·ω_{0j}(x)`; then `δ_j = 1`
(`delta_eq_one_S`, Pf (13.3.c)) and the row-`0` `ω`-value `ω_{0j}|_{W₁} = 1`
(`omega_row_zero_apply_of_mem_W1`).  This is the `hmuW1` input of the (13.18.a) exact
`β`-support `betaGrid_support_sharpP_union_typePV_of_values` (`S16_NonExistenceG/TGapCross`)
and of the original support argument (Pf p.83 "`μ_{0j}(x) = ω_{0j}(x) = 1`"). -/
theorem Hypothesis.mu_row0_apply_eq_one_of_mem_W1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (x : ↥hyp.S) (hxW1 : (x : G) ∈ hyp.W1) (hx1 : x ≠ 1) :
    hyp.mu ⟨0, hyp.q_prime.pos⟩ j x = 1 := by
  have hxW : (x : G) ∈ hyp.W := by
    rw [hyp.W_eq_join]; exact Subgroup.mem_sup_left hxW1
  have hxW2 : (x : G) ∉ (hyp.W2 : Set G) := by
    intro hmem
    apply hx1
    have hinf : (x : G) ∈ hyp.W1 ⊓ hyp.W2 := ⟨hxW1, hmem⟩
    rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hinf
    exact Subtype.ext hinf
  have hval := hyp.mu_apply_of_not_mem_W2 ⟨0, hyp.q_prime.pos⟩ j (x : G) hxW x.2 hxW2
  rw [show (⟨(x : G), x.2⟩ : ↥hyp.S) = x from rfl] at hval
  rw [hval, hyp.delta_eq_one_S hG j,
    hyp.omega_row_zero_apply_of_mem_W1 j ⟨(x : G), hxW⟩ hxW1]
  norm_num

end CountingLayer

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S13_PrimeTIResidueBridge.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **The certain-type `S06.Hypothesis` of the `S`-side (type-uniform).**  From the type-`P` datum
`hyp.Sdata : TypePData S` and `S`'s maximality + type-`P` status (`IsTypeP S`, obtained from the
carried `S_nonI` alternative — no `IsTypeP1` needed), `typePData_toS06Hypothesis` supplies the §6
certain-type Hypothesis on `↥S`.  This is the common source of the `μ`-grid (`columnFamily.mu`)
that §12 uses for type-`P1` maximals, here made available for the type-`P2` group `S`. -/
noncomputable def Hypothesis.s06S [Finite G] (hyp : Hypothesis (G := G))
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) : OddOrder.Peterfalvi.S06.Hypothesis ↥hyp.S :=
  OddOrder.Peterfalvi.S12.typePData_toS06Hypothesis hyp.Sdata hG.odd
    (OddOrder.Peterfalvi.S12.typePData_W1_hall_coprime hG hyp.S_maximal
      (OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI) hyp.Sdata)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.18.a), `[S : PW₁] = u`** (`S15` home; a copy temporarily also lives in
`S16_NonExistenceG/TGapCross` — redirect tracked cross-lane).  The index is read from
`|S| = p^q·u·q` and `|P W₁| = |P|·|W₁| = p^q·q`.  This is the degree of the permutation
character `Ind_{PW₁}^S 1`. -/
theorem PW1_index_eq_u_of_c_eq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
    ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).index = hyp.u := by
  have hD_le_S : OddOrder.GroupTheory.derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_D : hyp.P ≤ OddOrder.GroupTheory.derivedInG hyp.S := by
    rw [hyp.S_deriv_eq_PU]
    exact le_sup_left
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_D.trans hD_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hW1norm : hyp.W1 ≤ Subgroup.normalizer (hyp.P : Set G) := hW1_le_S.trans hS_norm_P
  have hDW1 : OddOrder.GroupTheory.derivedInG hyp.S ⊓ hyp.W1 = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.M_complement.disjoint
    rw [eq_bot_iff]
    rintro x ⟨hxD, hxW1⟩
    have hxS : x ∈ hyp.S := hD_le_S hxD
    have hmem : (⟨x, hxS⟩ : ↥hyp.S) ∈
        ((OddOrder.GroupTheory.derivedInG hyp.S).subgroupOf hyp.S) ⊓
          (hyp.Sdata.W1.subgroupOf hyp.S) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxD,
        Subgroup.mem_subgroupOf.mpr (hyp.Sdata_W1_eq ▸ hxW1)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    simpa using Subtype.ext_iff.mp hmem
  have hPW1disj : Disjoint hyp.P hyp.W1 :=
    (disjoint_iff.mpr hDW1).mono hP_le_D (le_refl hyp.W1)
  have hcardPW1 : Nat.card ↥(hyp.P ⊔ hyp.W1) = hyp.p ^ hyp.q * hyp.q := by
    rw [sup_comm, OddOrder.BG.Ch3.S12.card_sup_eq_mul_of_le_normalizer_of_disjoint
      hW1norm (disjoint_iff.mp hPW1disj.symm),
      hyp.card_P_eq hG hyp.Sdata_W2_eq, ← hyp.q_eq_card_W1]
    exact Nat.mul_comm hyp.q (hyp.p ^ hyp.q)
  have hcardPW1S : Nat.card ↥((hyp.P ⊔ hyp.W1).subgroupOf hyp.S) =
      hyp.p ^ hyp.q * hyp.q := by
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (sup_le hP_le_S hW1_le_S)).toEquiv, hcardPW1]
  have hm := Subgroup.card_mul_index ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
  rw [hcardPW1S, hyp.card_S_val hG, hc1, mul_one] at hm
  have hpos : 0 < hyp.p ^ hyp.q * hyp.q :=
    mul_pos (pow_pos hyp.p_prime.pos hyp.q) hyp.q_prime.pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    (hyp.p ^ hyp.q * hyp.q) * ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S).index
        = hyp.p ^ hyp.q * (hyp.u * hyp.q) := by simpa [mul_assoc] using hm
    _ = (hyp.p ^ hyp.q * hyp.q) * hyp.u := by ring

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.18.a), the bridge character vanishes at `1`**: `β_j(1) = 0` — the two
degrees agree, `Ind_{PW₁}^S 1 (1) = [S:PW₁] = u = μ_{0j}(1)` (`PW1_index_eq_u`,
`mu_apply_one_eq_u`). -/
theorem betaGrid_apply_one_eq_zero_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    betaGrid hyp j 1 = 0 := by
  have hj0 : j ≠ ⟨0, hyp.p_prime.pos⟩ := fun h => hj (by simp [h])
  rw [betaGrid, OddOrder.RepresentationTheory.ClassFunction.sub_apply, indPW1,
    ClassFunction.induce_apply_one, PW1_index_eq_u_of_c_eq_one hG hyp hc1,
    trivialClassFunction_apply,
    mul_one, hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩ j hj0, sub_self]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.18.a), vanishing of the induced trivial character on `S′ − P`** (the `PU`-case of the
Coq `PVSbeta`): `Ind_{P⋊W₁}^S 1 (z) = 0` for `z ∈ S′ ∖ P`.  The conjugator set is empty: a
conjugate `g⁻¹zg ∈ PW₁` also lies in the normal `S′`, and `(P ⊔ W₁) ⊓ S′ = P` by the Dedekind
modular law (`P ≤ S′`, `W₁ ⊓ S′ = ⊥` from the `M_complement` disjointness), so `z` would lie in
the normal `P` — contradiction. -/
theorem indPW1_apply_eq_zero_of_mem_derived_not_mem_P [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {z : ↥hyp.S} (hzS' : (z : G) ∈ derivedInG hyp.S) (hzP : (z : G) ∉ hyp.P) :
    indPW1 hyp z = 0 := by
  classical
  have hM'_le_S : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have hP_le_M' : hyp.P ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_left
  have hP_le_S : hyp.P ≤ hyp.S := hP_le_M'.trans hM'_le_S
  have hW1_le_S : hyp.W1 ≤ hyp.S := hyp.Sdata_W1_eq ▸ hyp.Sdata.W1_le
  have hS_norm_P : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hPnorm : (hyp.P.subgroupOf hyp.S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_S).mpr hS_norm_P
  -- `W₁ ⊓ S′ = ⊥` (the `M_complement` disjointness, `uW1_isComplement_P` pattern).
  have hM'W1 : derivedInG hyp.S ⊓ hyp.W1 = ⊥ := by
    have hd := disjoint_iff.mp hyp.Sdata.M_complement.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxM', hxW1⟩
    have hxS : x ∈ hyp.S := hM'_le_S hxM'
    have hmem : (⟨x, hxS⟩ : ↥hyp.S) ∈
        ((derivedInG hyp.S).subgroupOf hyp.S) ⊓ (hyp.Sdata.W1.subgroupOf hyp.S) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxM', Subgroup.mem_subgroupOf.mpr (hyp.Sdata_W1_eq ▸ hxW1)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  -- Dedekind-style: an element of `(P ⊔ W₁) ⊓ S′` lies in `P` (factor `w = p·w₁` through the
  -- coset decomposition `PW₁ = P * W₁`, then `w₁ ∈ W₁ ⊓ S′ = ⊥`).
  have hPW1S' : ∀ {w : G}, w ∈ hyp.P ⊔ hyp.W1 → w ∈ derivedInG hyp.S → w ∈ hyp.P := by
    intro w hwPW1 hwS'
    have hwmem : w ∈ (↑(hyp.P ⊔ hyp.W1) : Set G) := hwPW1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left hyp.P hyp.W1
      (hW1_le_S.trans hS_norm_P)] at hwmem
    obtain ⟨p, hp, w1, hw1, hpw⟩ := Set.mem_mul.mp hwmem
    have hw1S' : w1 ∈ derivedInG hyp.S := by
      have hw1eq : w1 = p⁻¹ * w := by rw [← hpw]; group
      rw [hw1eq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hP_le_M' (SetLike.mem_coe.mp hp))) hwS'
    have hw1bot : w1 ∈ derivedInG hyp.S ⊓ hyp.W1 :=
      Subgroup.mem_inf.mpr ⟨hw1S', SetLike.mem_coe.mp hw1⟩
    rw [hM'W1, Subgroup.mem_bot] at hw1bot
    have hweq : w = p := by rw [← hpw, hw1bot, mul_one]
    rw [hweq]
    exact SetLike.mem_coe.mp hp
  rw [show indPW1 hyp = ClassFunction.induce ((hyp.P ⊔ hyp.W1).subgroupOf hyp.S)
        (trivialClassFunction _) from rfl, induce_one_apply]
  have hempty : (Finset.univ.filter
      (fun g : ↥hyp.S => g⁻¹ * z * g ∈ (hyp.P ⊔ hyp.W1).subgroupOf hyp.S)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro g _ hmem
    have hwPW1 : ((g⁻¹ * z * g : ↥hyp.S) : G) ∈ hyp.P ⊔ hyp.W1 :=
      Subgroup.mem_subgroupOf.mp hmem
    -- The conjugate stays in the normal `S′`.
    have hwS' : ((g⁻¹ * z * g : ↥hyp.S) : G) ∈ derivedInG hyp.S := by
      have hz' : z ∈ (derivedInG hyp.S).subgroupOf hyp.S := Subgroup.mem_subgroupOf.mpr hzS'
      have hconj := (inferInstance :
        ((derivedInG hyp.S).subgroupOf hyp.S).Normal).conj_mem z hz' g⁻¹
      rw [inv_inv] at hconj
      have : g⁻¹ * z * g ∈ (derivedInG hyp.S).subgroupOf hyp.S := hconj
      exact Subgroup.mem_subgroupOf.mp this
    -- Dedekind puts it in `P`, so `z` lies in the normal `P` — contradiction.
    have hwP : g⁻¹ * z * g ∈ hyp.P.subgroupOf hyp.S :=
      Subgroup.mem_subgroupOf.mpr (hPW1S' hwPW1 hwS')
    have hzback := hPnorm.conj_mem _ hwP g
    have hzz : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rw [hzz] at hzback
    exact hzP (Subgroup.mem_subgroupOf.mp hzback)
  rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.18.a), exact `β`-support** (Coq `PVSbeta`, `PFsection13.v:1833`):
`supp(β_j) ⊆ P^# ∪ V_S^S` — the honest carrier `β_j ∈ CF(S, P^# ∪ V_S)`.

Fully proven: the group-theoretic skeleton conjugates every point outside `S′` to `x·y` with
`x ∈ W₁^#`, `y ∈ W₂` (Peterfalvi (2.1), `mem_compl_conj_into_W`); at `y = 1` the two proven
`W₁^#`-values cancel (`indPW1_apply_eq_one_of_mem_W1_sharp`, `mu_row0_apply_eq_one_of_mem_W1` —
the `(4.3.c)+(13.3.c)` value), otherwise `x·y ∈ V_S`; inside `S′` the two proven `S′−P`-values
cancel (`indPW1_apply_eq_zero_of_mem_derived_not_mem_P`,
`mu_row0_apply_eq_zero_of_mem_derived_not_mem_P` — the `(13.3.a)+(13.12)` vanishing), and at
`1` the degrees agree (`betaGrid_apply_one_eq_zero`).

⚠ The previous statement here (grid form `supp(β_j) ⊆ ⋃ᵢ supp(μ_{ij})`) was an unfaithful
restate (it would additionally require every point of `P^#` to carry a nonzero `μ`-value) —
replaced by the Coq-faithful carrier, issue-3003 pattern.  A hypothesis-parametrized copy of
this skeleton lives in `S16_NonExistenceG/TGapCross`
(`betaGrid_support_sharpP_union_typePV_of_values`) — cross-lane redirect tracked. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1) (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    (betaGrid hyp j).support ⊆
      {z : ↥hyp.S |
        (z : G) ∈ OddOrder.GroupTheory.sharpSubgroup hyp.P ∪
          OddOrder.GroupTheory.conjClassSetIn hyp.S
            (OddOrder.GroupTheory.typePV hyp.S hyp.Sdata)} := by
  classical
  have hj0 : j ≠ ⟨0, hyp.p_prime.pos⟩ := fun h => hj (by simp [h])
  intro z hz
  rw [OddOrder.RepresentationTheory.ClassFunction.mem_support] at hz
  by_cases hzD : (z : G) ∈ OddOrder.GroupTheory.derivedInG hyp.S
  · by_cases hzP : (z : G) ∈ hyp.P
    · by_cases hz1 : z = 1
      · exact absurd (hz1 ▸ betaGrid_apply_one_eq_zero_of_c_eq_one hG hyp hc1 j hj) hz
      · exact Or.inl ⟨hzP, fun h => hz1 (Subtype.ext h)⟩
    · exfalso
      apply hz
      rw [betaGrid, OddOrder.RepresentationTheory.ClassFunction.sub_apply,
        indPW1_apply_eq_zero_of_mem_derived_not_mem_P hG hyp hzD hzP,
        hyp.mu_row0_apply_eq_zero_of_mem_derived_not_mem_P_of_c_eq_one
          hG hc1 j hj0 z hzD hzP, sub_self]
  · set h := hyp.s06S hG with hs06
    have hzK : z ∉ h.K := fun hzK => hzD (Subgroup.mem_subgroupOf.mp hzK)
    obtain ⟨c, x, hxW1, hx1, y, hyW2, hconj⟩ := h.mem_compl_conj_into_W hzK
    have hxW1G : (x : G) ∈ hyp.W1 := by
      have hx := Subgroup.mem_subgroupOf.mp hxW1
      rwa [hyp.Sdata_W1_eq] at hx
    have hyW2G : (y : G) ∈ hyp.W2 := by
      have hy := Subgroup.mem_subgroupOf.mp hyW2
      rwa [hyp.Sdata_W2_eq] at hy
    have hconjβ : betaGrid hyp j z = betaGrid hyp j (x * y) := by
      rw [← hconj]
      have hc := (betaGrid hyp j).conj_eq z c⁻¹
      rw [inv_inv] at hc
      exact hc.symm
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hz
      rw [hconjβ, mul_one, betaGrid, OddOrder.RepresentationTheory.ClassFunction.sub_apply,
        indPW1_apply_eq_one_of_mem_W1_sharp hG hyp hxW1G hx1,
        hyp.mu_row0_apply_eq_one_of_mem_W1 hG j x hxW1G hx1, sub_self]
    right
    rw [OddOrder.GroupTheory.mem_conjClassSetIn]
    refine ⟨(x : G) * (y : G), ?_, (c : G), c.2, ?_⟩
    · have hxW1data : (x : G) ∈ hyp.Sdata.W1 := Subgroup.mem_subgroupOf.mp hxW1
      have hyW2data : (y : G) ∈ hyp.Sdata.W2 := Subgroup.mem_subgroupOf.mp hyW2
      have hxyW : (x : G) * (y : G) ∈ hyp.Sdata.W := by
        rw [hyp.Sdata.W_eq]
        exact mul_mem (Subgroup.mem_sup_left hxW1data) (Subgroup.mem_sup_right hyW2data)
      simp only [OddOrder.GroupTheory.typePV, Set.mem_sdiff, Set.mem_union,
        SetLike.mem_coe, not_or]
      refine ⟨hxyW, ?_, ?_⟩
      · intro hxyW1
        apply hy1
        have hyW1 : (y : G) ∈ hyp.Sdata.W1 := by
          have heq : (y : G) = (x : G)⁻¹ * ((x : G) * (y : G)) := by group
          rw [heq]
          exact mul_mem (inv_mem hxW1data) hxyW1
        have hbot := (OddOrder.Peterfalvi.S12.typePData_disjoint_W1_W2 hyp.Sdata).le_bot
          (Subgroup.mem_inf.mpr ⟨hyW1, hyW2data⟩)
        rw [Subgroup.mem_bot] at hbot
        exact Subtype.ext hbot
      · intro hxyW2
        apply hx1
        have hxW2 : (x : G) ∈ hyp.Sdata.W2 := by
          have heq : (x : G) = ((x : G) * (y : G)) * (y : G)⁻¹ := by group
          rw [heq]
          exact mul_mem hxyW2 (inv_mem hyW2data)
        have hbot := (OddOrder.Peterfalvi.S12.typePData_disjoint_W1_W2 hyp.Sdata).le_bot
          (Subgroup.mem_inf.mpr ⟨hxW1data, hxW2⟩)
        rw [Subgroup.mem_bot] at hbot
        exact Subtype.ext hbot
    · have hconjG : (c : G)⁻¹ * (z : G) * (c : G) = (x : G) * (y : G) := by
        have hc := congrArg hyp.S.subtype hconj
        rwa [map_mul, map_mul, map_inv] at hc
      rw [← hconjG]
      group

end OddOrder.Peterfalvi.S15

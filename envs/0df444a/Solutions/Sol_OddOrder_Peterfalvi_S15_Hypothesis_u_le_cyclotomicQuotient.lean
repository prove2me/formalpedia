-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.u_le_cyclotomicQuotient
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:38:53.520476+00:00
-- url     : https://prove2.me/submissions/b57c1dfc-aa7b-4a18-b0dd-fa368d8e127d

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/SemilinearImprimitiveBound.lean
--   OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finite.Prod
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Theorems.Thm_OddOrder_Peterfalvi_S11_caseA_blockScalarFacts

-- ===== OddOrder/GroupTheory/RepresentationTheory/SemilinearImprimitiveBound.lean =====
namespace OddOrder.RepresentationTheory

/-- **Non-Galois → cyclotomic-quotient bridge**: `(p − 1)^{q−1} ≤ (p^q − 1)/(p − 1)`.

`(p−1)^{q−1}·(p−1) = (p−1)^q < p^q`, so `(p−1)^q ≤ p^q − 1`; division by `p − 1`
gives the claim.
Pure `ℕ` arithmetic, `sorry`-free.  Lifts the non-Galois bound `u ≤ (p−1)^{q−1}` to the uniform
`u ≤ (p^q − 1)/(p − 1)` matching the Galois branch (`SingerLineBound`). -/
theorem pow_sub_one_le_cyclotomicQuotient {p q : ℕ} (hp : 2 ≤ p) (hq : 1 ≤ q) :
    (p - 1) ^ (q - 1) ≤ (p ^ q - 1) / (p - 1) := by
  have hp1 : 0 < p - 1 := by omega
  rw [Nat.le_div_iff_mul_le hp1]
  have hpow : (p - 1) ^ (q - 1) * (p - 1) = (p - 1) ^ q := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow]
  have hlt : (p - 1) ^ q < p ^ q := Nat.pow_lt_pow_left (by omega) (by omega)
  have hpq1 : 1 ≤ p ^ q := Nat.one_le_pow _ _ (by omega)
  omega

end OddOrder.RepresentationTheory

-- ===== OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean =====
namespace OddOrder.Peterfalvi.S11

open OddOrder.RepresentationTheory OddOrder.GroupTheory OddOrder.Isaacs.Ch03

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk')

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **Peterfalvi (9.7.a): the qualitative block-scalar product embedding.**  Projection of
`caseA_blockScalarFacts`; see there for the accompanying `a`-form divisibility. -/
theorem caseA_exists_blockScalarRatioEmbedding [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    ∃ ψ : ↥(MonoidHom.range (uActionHom data chief)) →*
        (Fin (data.q - 1) → (ZMod chief.p)ˣ),
      Function.Injective ψ :=
  (caseA_blockScalarFacts chars caseA).1

open scoped Classical in
/-- **Peterfalvi (9.7.a): imprimitive block-scalar order divisibility.**  From the case-(a) Clifford
data, the image `Ū = U/C_U(H̄)` embeds as a subgroup of `((𝔽_p)ˣ)^{q-1}`; hence its order
`u = |Ū|` divides `(p - 1)^{q-1}`.  This strengthened form retains the odd-part information used
in Peterfalvi (13.13). -/
theorem caseA_u_dvd_pred_pow [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    chars.u ∣ (chief.p - 1) ^ (data.q - 1) := by
  have : Fact chief.p.Prime := ⟨chief.p_prime⟩
  obtain ⟨ψ, hψ⟩ := caseA_exists_blockScalarRatioEmbedding chars caseA
  have hunits : Nat.card (ZMod chief.p)ˣ = chief.p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime chief.p_prime]
  have hdiv := Subgroup.card_dvd_of_injective ψ hψ
  rw [Nat.card_pi, hunits] at hdiv
  have hu : chars.u = Nat.card ↥(uActionHom data chief).range :=
    chars.u_eq_card_quotient
  rw [hu]
  simpa using hdiv

/-- **Peterfalvi (9.7.a): the imprimitive `u`-bound** `u ≤ (p^q − 1)/(p − 1)`.  This is the
cardinality consequence of `caseA_u_dvd_pred_pow`, followed by the elementary cyclotomic bound
`(p - 1)^{q-1} ≤ (p^q - 1)/(p - 1)`. -/
theorem caseA_u_le_cyclotomicQuotient [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    chars.u ≤ (chief.p ^ data.q - 1) / (chief.p - 1) := by
  have hpow : 0 < (chief.p - 1) ^ (data.q - 1) :=
    pow_pos (Nat.sub_pos_of_lt chief.p_prime.one_lt) _
  have hle : chars.u ≤ (chief.p - 1) ^ (data.q - 1) :=
    Nat.le_of_dvd hpow (caseA_u_dvd_pred_pow chars caseA)
  exact hle.trans (pow_sub_one_le_cyclotomicQuotient (p := chief.p) (q := data.q)
    chief.p_prime.two_le data.nontrivial.2.1.one_le)

/-- **Peterfalvi (9.7): the `u`-bound `u ≤ (p^q − 1)/(p − 1)`, unconditionally.**  The Clifford
dichotomy (`chiefFactor_clifford_U_dichotomy`) splits the `U`-action on the chief factor `H̄`:

* **irreducible** (Galois, case (b)): the Singer-field cyclic bound gives the divisibility
  `u ∣ (p^q − 1)/(p − 1)` (`chiefFactor_caseB_image_dvd_norm`);
* **imprimitive** (case (a)): the block-scalar ratio embedding `Ū ↪ ℤ_{p-1}^{q-1}` gives
  `u ≤ (p−1)^{q−1} ≤ (p^q − 1)/(p − 1)` (`caseA_u_le_cyclotomicQuotient`, via the case-(a)
  carrier `clifford_caseA_data`).

This is the upstream fact behind Peterfalvi (13.2.c) `basic_structure.u_bound` (issue 9000):
the §13/§15 consumer instantiates `chars` for the type-P₂ member `S` and cites this bound. -/
theorem u_le_cyclotomicQuotient [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief) :
    chars.u ≤ (chief.p ^ data.q - 1) / (chief.p - 1) := by
  rcases chiefFactor_clifford_U_dichotomy chief with hcaseB | ⟨S₀, hS₀ne, hS₀inv, hS₀card, hirr₀⟩
  · -- Galois / irreducible (case (b)): the Singer divisibility bound, weakened to `≤`.
    have hdvd := chiefFactor_caseB_image_dvd_norm chief hcaseB
    have hpos : 0 < (chief.p ^ data.q - 1) / (chief.p - 1) := by
      have hp2 := chief.p_prime.two_le
      have hq1 : 1 ≤ data.q := data.nontrivial.2.1.pos
      have hle : chief.p ≤ chief.p ^ data.q := Nat.le_self_pow (by omega) _
      exact Nat.div_pos (by omega) (by omega)
    rw [chars.u_eq_card_quotient]
    exact Nat.le_of_dvd hpos hdvd
  · -- imprimitive (case (a)): the block-scalar bound through the case-(a) carrier.
    exact caseA_u_le_cyclotomicQuotient chars
      (clifford_caseA_data chars hS₀ne hS₀inv hS₀card hirr₀)

end OddOrder.Peterfalvi.S11

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.2.c)/(9.7): the `u`-bound `u ≤ (p^q − 1)/(p − 1)` for the type-`P₂`
member `S`**, unconditionally.  This is the honest discharge of `basic_structure_gated.u_bound`
(Pf (13.2.c), issue 9000 lane-b cite / 2038 HUB ruling): lane a proved the unconditional §9/§11
bound `S11.u_le_cyclotomicQuotient` (`chars.u ≤ (chief.p^data.q − 1)/(chief.p − 1)` for *any*
`Section11CharacterData` on a `TypesIIIIIIVSetup`), and we cite it on the `S`-instance
`toTypesIIIIIIVSetupS` after discharging the three identifications:
* `data.q = q` (`|W₁| = q`, `q_eq_card_W1`);
* `chief.p = p` (the chief prime, forced by `|P| = p^q = chief.p^q · |N|`);
* `chars.u = u` (the `U`-action image `|Ū| = [U : C_U(P)] = |U|/|C| = uc/c = u`, via the proven
  `relIndex_cSub_U_eq_u` `[U : C] = chars.u` and `cSub = C`, `card_U_eq_uc`).
**Ungated** — depends only on `S11.u_le_cyclotomicQuotient` (proven, Clifford dichotomy) and the
`S`-instance identities, not on the (11.9) `typeP_Galois` character body. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1) := by
  classical
  have := hyp.finiteG
  obtain ⟨chief, _⟩ :=
    OddOrder.Peterfalvi.S11.exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetupS hG)
  have := chief.N_normal
  -- (i) the `S`-instance chief factor `q` equals `q = |W₁|`.
  have hq : (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q := by
    change Nat.card ↥hyp.Sdata.W1 = hyp.q
    rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
  -- (ii) the chief prime `chief.p = p`, from `|P| = p^q = chief.p^q · |N|`.
  have hpp : chief.p = hyp.p := by
    have hHeq : ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G) = hyp.P := by
      change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
    have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H = hyp.p ^ hyp.q := by
      rw [hHeq]; exact hyp.card_P_eq hG hyp.Sdata_W2_eq
    have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
    rw [hq] at hquot
    have hsplitP := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
    rw [hquot, hcardH] at hsplitP
    have hdvd : chief.p ∣ hyp.p ^ hyp.q :=
      dvd_trans (dvd_pow_self chief.p hyp.q_prime.pos.ne') (hsplitP ▸ Dvd.intro _ rfl)
    exact (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.p_prime).mp
      (chief.p_prime.dvd_of_dvd_pow hdvd)
  -- (iii) the `U`-action image order `chars.u = |Ū| = [U : C] = u`.
  have hu_eq : (hyp.mkSection11CharacterDataS hG chief).u = hyp.u := by
    have hc0 : 0 < hyp.c := hyp.c_eq_card_C ▸ Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hc0 ?_
    have key : (hyp.mkSection11CharacterDataS hG chief).u
        * Nat.card ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief)
        = Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).U := by
      rw [← OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u (hyp.mkSection11CharacterDataS hG chief)]
      have h := Subgroup.index_mul_card
        ((OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief).subgroupOf
          (hyp.toTypesIIIIIIVSetupS hG).U)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (OddOrder.Peterfalvi.S11.cSub_le_U (hyp.toTypesIIIIIIVSetupS hG) chief)).toEquiv] at h
    rw [hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief, ← hyp.c_eq_card_C,
      show (hyp.toTypesIIIIIIVSetupS hG).U = hyp.U from hyp.Sdata_U_eq, hyp.card_U_eq_uc] at key
    exact key
  -- cite lane a's unconditional bound and rewrite through the three identifications.
  have hbound :=
    OddOrder.Peterfalvi.S11.u_le_cyclotomicQuotient (hyp.mkSection11CharacterDataS hG chief)
  rw [hu_eq, hpp, hq] at hbound
  exact hbound

end OddOrder.Peterfalvi.S15

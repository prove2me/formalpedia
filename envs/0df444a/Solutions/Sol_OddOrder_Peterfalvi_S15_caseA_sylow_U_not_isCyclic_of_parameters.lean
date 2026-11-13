-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.caseA_sylow_U_not_isCyclic_of_parameters
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:56:20.948848+00:00
-- url     : https://prove2.me/submissions/139c0f92-a089-4ea8-82d9-bccb9a64b2d1

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean
--   OddOrder/GroupTheory/RepresentationTheory/BlockScalarSylow.lean
--   OddOrder/Peterfalvi/S11_CaseAOddPartBound.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Theorems.Thm_OddOrder_Peterfalvi_S11_caseA_blockScalarFacts

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

end OddOrder.Peterfalvi.S11

-- ===== OddOrder/GroupTheory/RepresentationTheory/BlockScalarSylow.lean =====
namespace OddOrder.RepresentationTheory

/-- A faithful two-coordinate representation of sharp square order cannot have a cyclic Sylow
subgroup at a prime dividing the coordinate exponent.

Indeed, injectivity makes every source element have `n`-th power one.  If a Sylow `r`-subgroup
`R` were cyclic, a generator would show `|R| ∣ n`.  Writing `n = |R| k` and
`|U| = n² = |R| [U:R]` would then force `r ∣ [U:R]`, contradicting the Sylow index theorem. -/
theorem sylow_not_isCyclic_of_card_eq_sq_of_injective_pi
    {U A : Type*} [Group U] [Finite U] [Group A] {n r : ℕ}
    (ψ : U →* (Fin 2 → A)) (hψ : Function.Injective ψ)
    (hcoord : ∀ (u : U) (i : Fin 2), (ψ u i) ^ n = 1)
    (hcard : Nat.card U = n ^ 2) (hr : r.Prime) (hrn : r ∣ n)
    (R : Sylow r U) :
    ¬ IsCyclic ↥(R : Subgroup U) := by
  let : Fact r.Prime := ⟨hr⟩
  intro hRcyclic
  let : IsCyclic ↥(R : Subgroup U) := hRcyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(R : Subgroup U))
  have hgpowU : ((g : U) ^ n) = 1 := by
    apply hψ
    rw [map_pow, map_one]
    ext i
    exact hcoord (g : U) i
  have hgpowR : g ^ n = 1 := Subtype.ext hgpowU
  have hRdvdn : Nat.card ↥(R : Subgroup U) ∣ n := by
    rw [← hg]
    exact orderOf_dvd_of_pow_eq_one hgpowR
  obtain ⟨k, hk⟩ := hRdvdn
  have hlagrange :
      Nat.card ↥(R : Subgroup U) * (R : Subgroup U).index = Nat.card U :=
    (R : Subgroup U).card_mul_index
  have hindex :
      (R : Subgroup U).index = Nat.card ↥(R : Subgroup U) * k ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left
      (show 0 < Nat.card ↥(R : Subgroup U) from Nat.card_pos)
    rw [hlagrange, hcard, hk]
    ring
  have hrU : r ∣ Nat.card U := by
    rw [hcard, pow_two]
    exact dvd_mul_of_dvd_left hrn n
  have hrR : r ∣ Nat.card ↥(R : Subgroup U) := by
    have hrprod :
        r ∣ Nat.card ↥(R : Subgroup U) * (R : Subgroup U).index := by
      rwa [hlagrange]
    exact (hr.dvd_mul.mp hrprod).resolve_right R.not_dvd_index
  apply R.not_dvd_index
  rw [hindex]
  exact dvd_mul_of_dvd_left hrR (k ^ 2)

/-- **Peterfalvi (14.6), sharp block-scalar Sylow bridge.**  Let the odd-order group `U`
embed faithfully in two copies of `(ZMod p)ˣ`, where `p` is odd prime, and suppose
`|U| = ((p - 1) / 2)²`.  Then every Sylow `r`-subgroup with
`r ∣ (p - 1) / 2` is noncyclic.

Each scalar coordinate has order dividing both `p - 1` and the odd number `|U|`; hence its
order divides `(p - 1) / 2`.  The preceding sharp-square lemma then applies. -/
theorem sylow_not_isCyclic_of_odd_blockScalarEmbedding
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {U : Type*} [Group U] [Finite U]
    (hUodd : Odd (Nat.card U))
    (ψ : U →* (Fin 2 → (ZMod p)ˣ)) (hψ : Function.Injective ψ)
    (hcard : Nat.card U = ((p - 1) / 2) ^ 2)
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (p - 1) / 2)
    (R : Sylow r U) :
    ¬ IsCyclic ↥(R : Subgroup U) := by
  let : Fact p.Prime := ⟨hp⟩
  have heven : 2 ∣ p - 1 := even_iff_two_dvd.mp (hp.even_sub_one hp2)
  have hsplit : p - 1 = 2 * ((p - 1) / 2) :=
    (Nat.mul_div_cancel' heven).symm
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hp]
  apply sylow_not_isCyclic_of_card_eq_sq_of_injective_pi ψ hψ
    (n := (p - 1) / 2) (r := r) ?_ hcard hr hrhalf R
  intro u i
  let χ : U →* (ZMod p)ˣ :=
    (Pi.evalMonoidHom (fun _ : Fin 2 => (ZMod p)ˣ) i).comp ψ
  have hordU : orderOf (χ u) ∣ orderOf u := orderOf_map_dvd χ u
  have hordCard : orderOf (χ u) ∣ Nat.card U :=
    hordU.trans (orderOf_dvd_natCard u)
  have hordOdd : Odd (orderOf (χ u)) := hUodd.of_dvd_nat hordCard
  have hordPred : orderOf (χ u) ∣ p - 1 := by
    rw [← hunits]
    exact orderOf_dvd_natCard (χ u)
  rw [hsplit] at hordPred
  have hordHalf : orderOf (χ u) ∣ (p - 1) / 2 :=
    (Nat.coprime_two_right.mpr hordOdd).dvd_of_dvd_mul_left hordPred
  simpa only [χ, MonoidHom.comp_apply, Pi.evalMonoidHom_apply] using
    (orderOf_dvd_iff_pow_eq_one.mp hordHalf)

end OddOrder.RepresentationTheory

-- ===== OddOrder/Peterfalvi/S11_CaseAOddPartBound.lean =====
namespace OddOrder.Peterfalvi.S11

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.6), case-(9.7.a) Sylow noncyclicity.**  At the sharp (13.13) parameters
`q = 3` and `u = ((p - 1) / 2)²`, every Sylow `r`-subgroup of the faithful action image
`Ū = range(uActionHom)`, for `r ∣ (p - 1) / 2`, is noncyclic.

This is the direct §11 instantiation of the shared two-coordinate block-scalar theorem.  It
preserves the qualitative embedding from (9.7.a), rather than using only its cardinality
divisibility corollary. -/
theorem caseA_sylow_not_isCyclic_of_sharp_order [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseA : CliffordCaseAData chars)
    (hq : data.q = 3)
    (hu : chars.u = ((chief.p - 1) / 2) ^ 2)
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (chief.p - 1) / 2)
    (R : Sylow r ↥(MonoidHom.range (uActionHom data chief))) :
    ¬ IsCyclic ↥(R : Subgroup ↥(MonoidHom.range (uActionHom data chief))) := by
  obtain ⟨ψ, hψ⟩ := caseA_exists_blockScalarRatioEmbedding chars caseA
  have hqsub : data.q - 1 = 2 := by omega
  let e : Fin (data.q - 1) ≃ Fin 2 := finCongr hqsub
  let ψ2 : ↥(MonoidHom.range (uActionHom data chief)) →*
      (Fin 2 → (ZMod chief.p)ˣ) :=
    { toFun := fun u i => ψ u (e.symm i)
      map_one' := by ext i; simp
      map_mul' := fun x y => by ext i; simp }
  have hψ2 : Function.Injective ψ2 := by
    intro x y hxy
    apply hψ
    funext j
    have hij := congrFun hxy (e j)
    simpa only [ψ2, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.symm_apply_apply] using hij
  have hp2 : chief.p ≠ 2 := by
    intro hp2
    have heven := chiefFactor_p_sub_one_even (chief := chief) hG
    rw [hp2] at heven
    norm_num at heven
  have huCard :
      chars.u = Nat.card ↥(MonoidHom.range (uActionHom data chief)) :=
    chars.u_eq_card_quotient
  have hodd : Odd (Nat.card ↥(MonoidHom.range (uActionHom data chief))) := by
    rw [← huCard]
    exact u_odd hG chars
  have hcard :
      Nat.card ↥(MonoidHom.range (uActionHom data chief)) =
        ((chief.p - 1) / 2) ^ 2 := by
    rw [← huCard]
    exact hu
  exact OddOrder.RepresentationTheory.sylow_not_isCyclic_of_odd_blockScalarEmbedding
    chief.p_prime hp2 hodd ψ2 hψ2 hcard hr hrhalf R

/-- **Peterfalvi (14.6), case-(9.7.a) Sylow noncyclicity in `U`.**  Under the sharp
parameters, every Sylow `r`-subgroup of Peterfalvi's original `U`, for
`r ∣ (p - 1) / 2`, is noncyclic.

The action homomorphism is surjective onto its range.  Hence it sends a Sylow subgroup of `U`
to a Sylow subgroup of the faithful action image; a cyclic source would have cyclic image,
contradicting `caseA_sylow_not_isCyclic_of_sharp_order`.  Notice that no faithfulness assumption
on the original `U`-action is needed for this direction. -/
theorem caseA_sylow_U_not_isCyclic_of_sharp_order [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseA : CliffordCaseAData chars)
    (hq : data.q = 3)
    (hu : chars.u = ((chief.p - 1) / 2) ^ 2)
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (chief.p - 1) / 2)
    (R : Sylow r ↥data.U) :
    ¬ IsCyclic ↥(R : Subgroup ↥data.U) := by
  let e : ↥data.U ≃* ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    (Subgroup.subgroupOfEquivOfLe le_sup_left).symm
  let f : ↥data.U →* ↥(MonoidHom.range (uActionHom data chief)) :=
    (uActionHom data chief).rangeRestrict.comp e.toMonoidHom
  have hf : Function.Surjective f :=
    (uActionHom data chief).rangeRestrict_surjective.comp e.surjective
  let : Fact r.Prime := ⟨hr⟩
  let Rbar : Sylow r ↥(MonoidHom.range (uActionHom data chief)) := R.mapSurjective hf
  have hRbar := caseA_sylow_not_isCyclic_of_sharp_order hG chars caseA hq hu
    hr hrhalf Rbar
  intro hR
  let : IsCyclic ↥(R : Subgroup ↥data.U) := hR
  rw [show (Rbar : Subgroup ↥(MonoidHom.range (uActionHom data chief))) =
    (R : Subgroup ↥data.U).map f by rfl] at hRbar
  exact hRbar <|
    isCyclic_of_surjective _ (f.subgroupMap_surjective (R : Subgroup ↥data.U))

end OddOrder.Peterfalvi.S11

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`S`-instance chief-factor `q` identity**: the `(9.x)` chief-factor prime `data.q` of the
`S`-instance `toTypesIIIIIIVSetupS` is the type-`P` invariant `q = |W₁|`.  Extracted from
`u_le_cyclotomicQuotient` for reuse by the (13.3.b) dichotomy translations. -/
theorem Hypothesis.toTypesIIIIIIVSetupS_q_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q := by
  change Nat.card ↥hyp.Sdata.W1 = hyp.q
  rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]

/-- **`S`-instance chief-factor prime identity**: the chief prime `chief.p = p`, forced by
`|P| = p^q = chief.p^q · |N|`.  Extracted from `u_le_cyclotomicQuotient`. -/
theorem Hypothesis.chiefFactorS_p_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    chief.p = hyp.p := by
  have := chief.N_normal
  have hHeq : ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G) = hyp.P := by
    change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H = hyp.p ^ hyp.q := by
    rw [hHeq]; exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hyp.toTypesIIIIIIVSetupS_q_eq hG] at hquot
  have hsplitP := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplitP
  have hdvd : chief.p ∣ hyp.p ^ hyp.q :=
    dvd_trans (dvd_pow_self chief.p hyp.q_prime.pos.ne') (hsplitP ▸ Dvd.intro _ rfl)
  exact (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.p_prime).mp
    (chief.p_prime.dvd_of_dvd_pow hdvd)

/-- **`S`-instance `u` identity**: the `U`-action image order `chars.u = |Ū| = [U : C_U(P)] = u`.
Extracted from `u_le_cyclotomicQuotient`; the (13.3.b) dichotomy uses it to transport the
`caseB_of_no_irreducible_sOf_H0Cprime` conclusion `chars.u = (p^q−1)/(p−1)` to `hyp.u`. -/
theorem Hypothesis.mkSection11CharacterDataS_u_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    (hyp.mkSection11CharacterDataS hG chief).u = hyp.u := by
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

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.6), sharp-parameter Sylow noncyclicity for the `S`-side `U`.**
At the (13.13) parameters `q = 3` and `u = (p - 1)² / 4`, for every prime
`r ∣ (p - 1) / 2`, every Sylow `r`-subgroup of Peterfalvi's actual subgroup `U` is noncyclic.

The numeric equality is normalized to `u = ((p - 1) / 2)²`; the §11 block-scalar theorem gives
the result for the `S`-instance `U`, and `Sdata_U_eq` transports it to the named subgroup
`hyp.U`. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (hq : hyp.q = 3) (hu : hyp.u = (hyp.p - 1) ^ 2 / 4)
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (hyp.p - 1) / 2)
    (R : Sylow r ↥hyp.U) : ¬ IsCyclic ↥(R : Subgroup ↥hyp.U) := by
  have hpeven : 2 ∣ hyp.p - 1 := by
    have h := even_iff_two_dvd.mp
      (OddOrder.Peterfalvi.S11.chiefFactor_p_sub_one_even (chief := chief) hG)
    rwa [hyp.chiefFactorS_p_eq hG chief] at h
  have hhalfSq : (hyp.p - 1) ^ 2 / 4 = ((hyp.p - 1) / 2) ^ 2 := by
    have hsplit : hyp.p - 1 = 2 * ((hyp.p - 1) / 2) :=
      (Nat.mul_div_cancel' hpeven).symm
    rw [hsplit, mul_pow]
    norm_num
  have hqSharp : (hyp.toTypesIIIIIIVSetupS hG).q = 3 := by
    rw [hyp.toTypesIIIIIIVSetupS_q_eq hG]
    exact hq
  have huSharp : (hyp.mkSection11CharacterDataS hG chief).u =
      ((chief.p - 1) / 2) ^ 2 := by
    rw [hyp.mkSection11CharacterDataS_u_eq hG chief,
      hyp.chiefFactorS_p_eq hG chief, hu, hhalfSq]
  have hrhalf' : r ∣ (chief.p - 1) / 2 := by
    rwa [hyp.chiefFactorS_p_eq hG chief]
  let e : ↥hyp.U ≃* ↥(hyp.toTypesIIIIIIVSetupS hG).U :=
    MulEquiv.subgroupCongr hyp.Sdata_U_eq.symm
  let f : ↥hyp.U →* ↥(hyp.toTypesIIIIIIVSetupS hG).U := e.toMonoidHom
  have hf : Function.Surjective f := e.surjective
  let : Fact r.Prime := ⟨hr⟩
  let Rsetup : Sylow r ↥(hyp.toTypesIIIIIIVSetupS hG).U :=
    R.mapSurjective hf
  have hRsetup := OddOrder.Peterfalvi.S11.caseA_sylow_U_not_isCyclic_of_sharp_order
    hG (hyp.mkSection11CharacterDataS hG chief) caseA hqSharp huSharp hr hrhalf' Rsetup
  intro hR
  let : IsCyclic ↥(R : Subgroup ↥hyp.U) := hR
  rw [show (Rsetup : Subgroup ↥(hyp.toTypesIIIIIIVSetupS hG).U) =
    (R : Subgroup ↥hyp.U).map f by rfl] at hRsetup
  exact hRsetup <| isCyclic_of_surjective _
    (f.subgroupMap_surjective (R : Subgroup ↥hyp.U))

end OddOrder.Peterfalvi.S15

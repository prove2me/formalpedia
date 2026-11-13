-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.caseA_false_of_parameters_and_typeIOverNormalizerData
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:11:32.669197+00:00
-- url     : https://prove2.me/submissions/73d11eaa-0a86-4e6c-91d8-dcb222b590b3

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
--   OddOrder/Peterfalvi/S15_CaseASylowCenter.lean
--   OddOrder/Peterfalvi/S15_CaseAOmegaCenter.lean
--   OddOrder/Peterfalvi/S15_CaseAContradiction.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Theorems.Thm_OddOrder_Peterfalvi_S11_caseA_blockScalarFacts
import Theorems.Thm_OddOrder_Peterfalvi_S15_TypeIOverNormalizerData_prime_dvd_sq_sub_one_of_omega1Center
import Theorems.Thm_OddOrder_Peterfalvi_S15_sylow_center_le_U_sylow_of_centralizer_witness
import Theorems.Thm_OddOrder_Peterfalvi_S15_caseA_sylow_U_not_isCyclic_of_parameters

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

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.6), BG Prop. 1.16 witness.**  Let `R₀` be a noncyclic Sylow
`r`-subgroup of the `S`-side complement `U`, where `r ∣ (p - 1) / 2`.  Then some
nonidentity `x ∈ R₀` has `C_P(x) ≠ 1`.

The ambient image `B` of `R₀` is abelian because `U` is abelian, normalizes `P` because
`U ≤ S ≤ N_G(P)`, and has order coprime to `|P| = p^q` because `r < p`.  These are exactly
the hypotheses of BG Prop. 1.16(1). -/
theorem exists_sylow_mem_inf_centralizer_ne_bot_of_not_isCyclic [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (hyp.p - 1) / 2)
    (R : Sylow r ↥hyp.U) (hRnc : ¬ IsCyclic ↥(R : Subgroup ↥hyp.U)) :
    ∃ x ∈ (R : Subgroup ↥hyp.U).map hyp.U.subtype, x ≠ (1 : G) ∧
      hyp.P ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
  let B : Subgroup G := (R : Subgroup ↥hyp.U).map hyp.U.subtype
  have hBU : B ≤ hyp.U := by
    simpa only [B] using (Subgroup.map_subtype_le (R : Subgroup ↥hyp.U))
  have hBnc : ¬ IsCyclic ↥B := by
    intro hBcyc
    exact hRnc ((Subgroup.equivMapOfInjective (R : Subgroup ↥hyp.U) hyp.U.subtype
      hyp.U.subtype_injective).isCyclic.mpr (by simpa only [B] using hBcyc))
  let : IsMulCommutative ↥B := IsMulCommutative.of_comm fun a b => by
    apply Subtype.ext
    change (a : G) * (b : G) = (b : G) * (a : G)
    exact congrArg (fun z : ↥hyp.U => (z : G)) (hyp.S_U_commutative.is_comm.comm
      (⟨(a : G), hBU a.2⟩ : ↥hyp.U) (⟨(b : G), hBU b.2⟩ : ↥hyp.U))
  have hUS : hyp.U ≤ hyp.S := by
    rw [← hyp.Sdata_U_eq]
    exact hyp.Sdata.U_le.trans (Subgroup.map_subtype_le _)
  have hSP : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hBP : B ≤ Subgroup.normalizer (hyp.P : Set G) := hBU.trans (hUS.trans hSP)
  have hrltp : r < hyp.p := by
    have hhalfpos : 0 < (hyp.p - 1) / 2 := by have := hyp.three_le_p; omega
    have hrle : r ≤ (hyp.p - 1) / 2 := Nat.le_of_dvd hhalfpos hrhalf
    omega
  have hrne : r ≠ hyp.p := ne_of_lt hrltp
  let : Fact r.Prime := ⟨hr⟩
  let : Fact hyp.p.Prime := ⟨hyp.p_prime⟩
  have hBr : IsPGroup r B := by
    simpa only [B] using R.isPGroup'.map hyp.U.subtype
  have hPp : IsPGroup hyp.p hyp.P :=
    IsPGroup.of_card (hyp.card_P_eq hG hyp.Sdata_W2_eq)
  have hcop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥hyp.P) :=
    IsPGroup.coprime_card_of_ne r hyp.p hrne B hyp.P hBr hPp
  have hpdvd : hyp.p ∣ Nat.card ↥hyp.P := by
    rw [hyp.card_P_eq hG hyp.Sdata_W2_eq]
    exact dvd_pow_self hyp.p hyp.q_prime.pos.ne'
  have hPne : hyp.P ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot hyp.P).mp <| by
    exact hyp.p_prime.one_lt.trans_le (Nat.le_of_dvd Nat.card_pos hpdvd)
  simpa only [B] using
    (OddOrder.BG.Ch2.S07.exists_mem_inf_centralizer_ne_bot_of_not_isCyclic
      hBP hBnc hcop hPne)

/-- **Peterfalvi (14.6), ambient Sylow carrier.**  If `R₀ ∈ Syl_r(U)` is noncyclic and
`U ≤ K`, then there is `R ∈ Syl_r(K)` containing the image of `R₀`; simultaneously retain the
BG Prop. 1.16 witness `x ∈ R₀#` with `P ∩ C_G(x) ≠ 1`.  Taking `K = H = L_F` is the Sylow
selection used before the center argument in (14.6). -/
theorem exists_sylow_over_U_with_centralizer_witness_of_not_isCyclic [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (hyp.p - 1) / 2)
    (R₀ : Sylow r ↥hyp.U) (hR₀nc : ¬ IsCyclic ↥(R₀ : Subgroup ↥hyp.U))
    (K : Subgroup G) (hUK : hyp.U ≤ K) :
    ∃ R : Sylow r ↥K,
      (R₀ : Subgroup ↥hyp.U).map (Subgroup.inclusion hUK) ≤ R ∧
        ∃ x ∈ (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype, x ≠ (1 : G) ∧
          hyp.P ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
  obtain ⟨x, hxR₀, hx1, hxP⟩ :=
    exists_sylow_mem_inf_centralizer_ne_bot_of_not_isCyclic hG hyp hr hrhalf R₀ hR₀nc
  have hR₀K : IsPGroup r
      ((R₀ : Subgroup ↥hyp.U).map (Subgroup.inclusion hUK)) :=
    R₀.isPGroup'.map (Subgroup.inclusion hUK)
  obtain ⟨R, hR₀R⟩ := hR₀K.exists_le_sylow
  exact ⟨R, hR₀R, x, hxR₀, hx1, hxP⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseASylowCenter.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.6), ambient Sylow with trapped center.** The noncyclic `R₀` produces
an ambient Sylow `R`, a BG Proposition 1.16 witness `x`, and the conclusion `Z(R) ≤ R₀`
in one package. -/
theorem exists_sylow_over_U_with_trapped_center_of_not_isCyclic [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (hyp.p - 1) / 2)
    (R₀ : Sylow r ↥hyp.U) (hR₀nc : ¬ IsCyclic ↥(R₀ : Subgroup ↥hyp.U))
    (K : Subgroup G) (hUK : hyp.U ≤ K) :
    ∃ R : Sylow r ↥K,
      (R₀ : Subgroup ↥hyp.U).map (Subgroup.inclusion hUK) ≤ R ∧
        ∃ x ∈ (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype, x ≠ (1 : G) ∧
          hyp.P ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ ∧
            (Subgroup.center ↥((R : Subgroup ↥K).map K.subtype)).map
                ((R : Subgroup ↥K).map K.subtype).subtype ≤
              (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype := by
  obtain ⟨R, hR₀R, x, hxR₀, hx1, hxP⟩ :=
    exists_sylow_over_U_with_centralizer_witness_of_not_isCyclic
      hG hyp hr hrhalf R₀ hR₀nc K hUK
  exact ⟨R, hR₀R, x, hxR₀, hx1, hxP,
    sylow_center_le_U_sylow_of_centralizer_witness
      hG hyp hr R₀ hR₀nc K hUK R hR₀R hxR₀ hx1 hxP⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseAOmegaCenter.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- An elementary abelian subgroup of a product of two cyclic groups has logarithmic
prime order at most two.  Projecting to the first coordinate gives a cyclic image; its
kernel embeds in the second coordinate and is cyclic as well. -/
private theorem rank_pi_fin_two_le_two_of_isCyclic
    {C : Type*} [Group C] [Finite C] [IsCyclic C] :
    rank (Fin 2 → C) ≤ 2 := by
  rw [rank_le_iff]
  intro r hr
  rw [pRank_le_iff]
  intro A hA
  let π0 : ↥A →* C :=
    (Pi.evalMonoidHom (fun _ : Fin 2 => C) 0).comp A.subtype
  let π1 : ↥π0.ker →* C :=
    (Pi.evalMonoidHom (fun _ : Fin 2 => C) 1).comp
      (A.subtype.comp π0.ker.subtype)
  have hπ1 : Function.Injective π1 := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
    · have hx0 : π0 (x : ↥A) = 1 := x.2
      have hy0 : π0 (y : ↥A) = 1 := y.2
      simpa only [π0, MonoidHom.comp_apply, Pi.evalMonoidHom_apply,
        Subgroup.coe_subtype] using hx0.trans hy0.symm
    · simpa only [π1, MonoidHom.comp_apply, Pi.evalMonoidHom_apply,
        Subgroup.coe_subtype, Fin.succ_zero_eq_one] using hxy
  let : IsCyclic ↥π0.ker := isCyclic_of_injective π1 hπ1
  have hker_dvd : Nat.card ↥π0.ker ∣ r := by
    rw [← IsCyclic.exponent_eq_card (α := ↥π0.ker)]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    apply Subtype.ext
    exact hA.pow_eq_one (x : ↥A)
  have hker_le : Nat.card ↥π0.ker ≤ r := Nat.le_of_dvd hr.pos hker_dvd
  let : IsCyclic ↥π0.range := Subgroup.isCyclic π0.range
  have hrange_dvd : Nat.card ↥π0.range ∣ r := by
    rw [← IsCyclic.exponent_eq_card (α := ↥π0.range)]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    obtain ⟨a, ha⟩ := x.2
    apply Subtype.ext
    change (x : C) ^ r = 1
    rw [← ha, ← map_pow, hA.pow_eq_one, map_one]
  have hrange_le : Nat.card ↥π0.range ≤ r := Nat.le_of_dvd hr.pos hrange_dvd
  have hcard : Nat.card ↥π0.ker * Nat.card ↥π0.range = Nat.card ↥A := by
    rw [← Subgroup.index_ker π0]
    exact Subgroup.card_mul_index π0.ker
  have hcard_le : Nat.card ↥A ≤ r ^ 2 := by
    rw [← hcard, pow_two]
    exact Nat.mul_le_mul hker_le hrange_le
  calc
    Nat.log r (Nat.card ↥A) ≤ Nat.log r (r ^ 2) := Nat.log_mono_right hcard_le
    _ = 2 := Nat.log_pow hr.one_lt 2

/-- **Peterfalvi (14.6), two-coordinate rank bound.**  In case (9.7.a), after
`c = 1` and `q = 3`, the actual subgroup `U` embeds in two copies of `(ZMod p)ˣ`
and hence has BG rank at most two.

The qualitative §9 embedding is initially stated for the faithful action image.  Here
The two numerical conclusions are explicit inputs: their current unconditional producers
run through the (13.10) relayer tracked by issue 0116.  Together with `cSub = C`, `c = 1`
makes the original action faithful and therefore lifts the embedding to `U` itself. -/
theorem caseA_rank_U_le_two_of_c_eq_one_q_eq_three [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (hc : hyp.c = 1)
    (hq : hyp.q = 3) :
    rank ↥hyp.U ≤ 2 := by
  classical
  let data := hyp.toTypesIIIIIIVSetupS hG
  let action := OddOrder.Peterfalvi.S11.uActionHom data chief
  have : Fact chief.p.Prime := ⟨chief.p_prime⟩
  obtain ⟨ψ, hψ⟩ :=
    OddOrder.Peterfalvi.S11.caseA_exists_blockScalarRatioEmbedding
      (hyp.mkSection11CharacterDataS hG chief) caseA
  have hqsub : data.q - 1 = 2 := by
    rw [show data.q = hyp.q from hyp.toTypesIIIIIIVSetupS_q_eq hG, hq]
  let eFin : Fin (data.q - 1) ≃ Fin 2 := finCongr hqsub
  let ψ2 : ↥(MonoidHom.range action) →* (Fin 2 → (ZMod chief.p)ˣ) :=
    { toFun := fun u i => ψ u (eFin.symm i)
      map_one' := by ext i; simp
      map_mul' := fun x y => by ext i; simp }
  have hψ2 : Function.Injective ψ2 := by
    intro x y hxy
    apply hψ
    funext j
    have hij := congrFun hxy (eFin j)
    simpa only [ψ2, MonoidHom.coe_mk, OneHom.coe_mk,
      Equiv.symm_apply_apply] using hij
  have hker_card : Nat.card ↥action.ker = 1 := by
    rw [← OddOrder.Peterfalvi.S11.card_cSub_eq_card_ker data chief,
      hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief,
      ← hyp.c_eq_card_C, hc]
  have haction : Function.Injective action :=
    action.ker_eq_bot_iff.mp (Subgroup.card_eq_one.mp hker_card)
  let eU : ↥hyp.U ≃* ↥data.U := MulEquiv.subgroupCongr hyp.Sdata_U_eq.symm
  let eAction : ↥data.U ≃*
      ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    (Subgroup.subgroupOfEquivOfLe le_sup_left).symm
  let φ : ↥hyp.U →* ↥(MonoidHom.range action) :=
    action.rangeRestrict.comp (eAction.toMonoidHom.comp eU.toMonoidHom)
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply eU.injective
    apply eAction.injective
    apply haction
    exact congrArg Subtype.val hxy
  let ψU : ↥hyp.U →* (Fin 2 → (ZMod chief.p)ˣ) := ψ2.comp φ
  have hψU : Function.Injective ψU := hψ2.comp hφ
  exact (rank_le_of_injective hψU).trans rank_pi_fin_two_le_two_of_isCyclic

/-- **Peterfalvi (14.6), order of the Sylow center layer.**  Let `R₀ ∈ Syl_r(U)` be
noncyclic, let `R ∈ Syl_r(K)` contain its image, and suppose the ambient center of `R`
has been trapped in `R₀`.  If `rank U ≤ 2`, then the ambient subgroup
`Ω₁(Z(R))` has order `r` or `r²`.

Nontriviality is the standard fact that the center of a nontrivial finite `r`-group
contains an element of order `r`.  The order alternatives then follow from the generic
elementary-abelian rank squeeze. -/
theorem omega1Center_card_eq_prime_or_sq_of_rank_U_le_two [Finite G]
    {r : ℕ} (hr : r.Prime) (U K : Subgroup G) (hUK : U ≤ K)
    (hrankU : rank ↥U ≤ 2)
    (R₀ : Sylow r ↥U) (hR₀nc : ¬ IsCyclic ↥(R₀ : Subgroup ↥U))
    (R : Sylow r ↥K)
    (hR₀R : (R₀ : Subgroup ↥U).map (Subgroup.inclusion hUK) ≤ R)
    (hcenter :
      (Subgroup.center ↥((R : Subgroup ↥K).map K.subtype)).map
          ((R : Subgroup ↥K).map K.subtype).subtype ≤
        (R₀ : Subgroup ↥U).map U.subtype) :
    Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
        ((R : Subgroup ↥K).map K.subtype) r) = r ∨
      Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
        ((R : Subgroup ↥K).map K.subtype) r) = r ^ 2 := by
  classical
  let : Fact r.Prime := ⟨hr⟩
  let Rg : Subgroup G := (R : Subgroup ↥K).map K.subtype
  let R₀g : Subgroup G := (R₀ : Subgroup ↥U).map U.subtype
  let Z : Subgroup G := OddOrder.BG.Ch3.S10.omega1CenterInG Rg r
  have hR₀gRg : R₀g ≤ Rg := by
    rintro y ⟨u, hu, rfl⟩
    exact ⟨Subgroup.inclusion hUK u, hR₀R (Subgroup.mem_map_of_mem _ hu), rfl⟩
  have hR₀gU : R₀g ≤ U := Subgroup.map_subtype_le _
  have hrankR₀g : rank ↥R₀g ≤ 2 :=
    (rank_le_of_injective
      (f := Subgroup.inclusion hR₀gU) (Subgroup.inclusion_injective hR₀gU)).trans hrankU
  have hZelem : Z.IsElementaryAbelian r := by
    simpa only [Z, Rg, OddOrder.BG.Ch3.S10.omega1CenterInG,
      OddOrder.BG.Ch1.S05.omega1Center] using
      (Subgroup.IsElementaryAbelian.map Rg.subtype_injective
        (OddOrder.BG.Ch1.S05.omega1Center_isElementaryAbelian
          (R := ↥Rg) (p := r)))
  have hZcenter : Z ≤ (Subgroup.center ↥Rg).map Rg.subtype := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨x, hx.1, rfl⟩
  have hZR₀g : Z ≤ R₀g := hZcenter.trans hcenter
  have hR₀_ne : (R₀ : Subgroup ↥U) ≠ ⊥ := by
    intro hbot
    apply hR₀nc
    rw [hbot]
    exact isCyclic_of_subsingleton
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR₀_ne
  have hRg_ne : Rg ≠ ⊥ := by
    intro hbot
    have haRg : (a : G) ∈ Rg :=
      hR₀gRg (Subgroup.mem_map_of_mem U.subtype a.2)
    have haG : (a : G) = 1 := Subgroup.mem_bot.mp (hbot ▸ haRg)
    exact ha1 (Subtype.ext (Subtype.ext haG))
  have : Nontrivial ↥Rg := (Subgroup.nontrivial_iff_ne_bot Rg).mpr hRg_ne
  have hRgpg : IsPGroup r Rg := by
    simpa only [Rg] using R.isPGroup'.map K.subtype
  obtain ⟨z, -, hzcenter, hz1, hzpow⟩ :=
    OddOrder.GroupTheory.exists_mem_omega1_center_of_normal_ne_bot
      (P := ↥Rg) (p := r) hRgpg (N := ⊤) (by exact top_ne_bot)
  have hzZ : (z : G) ∈ Z := by
    simpa only [Z, OddOrder.BG.Ch3.S10.omega1CenterInG,
      OddOrder.BG.Ch1.S05.omega1Center] using
      (show (z : G) ∈
          (OddOrder.BG.Ch1.S05.omega1Center (↥Rg) r).map Rg.subtype from
        ⟨z, ⟨hzcenter, hzpow⟩, rfl⟩)
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have hzbot : (z : G) ∈ (⊥ : Subgroup G) := hbot ▸ hzZ
    exact hz1 (Subtype.ext (Subgroup.mem_bot.mp hzbot))
  simpa only [Z, Rg] using
    (card_eq_prime_or_sq_of_isElementaryAbelian_le hZelem hZR₀g hrankR₀g hZne)

/-- **Peterfalvi (14.6), case-(9.7.a) specialization.**  Given the conclusions
`c = 1` of (13.12) and `q = 3` of (13.13), the preceding faithful two-coordinate
argument proves the rank hypothesis and determines the order of `Ω₁(Z(R))`. -/
theorem caseA_omega1Center_card_eq_prime_or_sq_of_parameters [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (hc : hyp.c = 1) (hq : hyp.q = 3)
    {r : ℕ} (hr : r.Prime)
    (R₀ : Sylow r ↥hyp.U) (hR₀nc : ¬ IsCyclic ↥(R₀ : Subgroup ↥hyp.U))
    (K : Subgroup G) (hUK : hyp.U ≤ K) (R : Sylow r ↥K)
    (hR₀R : (R₀ : Subgroup ↥hyp.U).map (Subgroup.inclusion hUK) ≤ R)
    (hcenter :
      (Subgroup.center ↥((R : Subgroup ↥K).map K.subtype)).map
          ((R : Subgroup ↥K).map K.subtype).subtype ≤
        (R₀ : Subgroup ↥hyp.U).map hyp.U.subtype) :
    Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
        ((R : Subgroup ↥K).map K.subtype) r) = r ∨
      Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
        ((R : Subgroup ↥K).map K.subtype) r) = r ^ 2 := by
  exact omega1Center_card_eq_prime_or_sq_of_rank_U_le_two hr hyp.U K hUK
    (caseA_rank_U_le_two_of_c_eq_one_q_eq_three hG hyp caseA hc hq)
    R₀ hR₀nc R hR₀R hcenter

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseAContradiction.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.6), final arithmetic contradiction.**  If odd primes `p` and
`r` satisfy both `r ∣ (p - 1) / 2` and `p ∣ r² - 1`, then the latter gives
`p < r`, whereas the former gives `r ≤ (p - 1) / 2 < p`. -/
theorem false_of_odd_primes_dvd_half_and_sq_sub_one
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hp_odd : Odd p) (hr_odd : Odd r) (hp_three : 3 ≤ p)
    (hr_dvd : r ∣ (p - 1) / 2) (hp_dvd : p ∣ r ^ 2 - 1) : False := by
  have hpr : p < r :=
    OddOrder.Peterfalvi.S14.prime_lt_of_odd_dvd_sq_sub_one
      hr hp hr_odd hp_odd hp_dvd
  have hhalf_pos : 0 < (p - 1) / 2 := by omega
  have hr_le : r ≤ (p - 1) / 2 := Nat.le_of_dvd hhalf_pos hr_dvd
  have hhalf_le : (p - 1) / 2 ≤ p - 1 := Nat.div_le_self _ _
  omega

/-- **Peterfalvi (14.6), case (9.7.a) is impossible at the sharp parameters.**
Assume the explicit conclusions `c = 1`, `q = 3`, and
`u = (p - 1)² / 4` of (13.12)/(13.13), together with the type-I maximal subgroup
over `N_G(U)` constructed in (13.17)/(14.5).  A prime divisor
`r ∣ (p - 1) / 2` has a noncyclic Sylow subgroup `R₀` in `U`.  Extending it to
the Fitting kernel of the type-I subgroup traps the ambient Sylow center in
`R₀`; hence `|Ω₁(Z(R))|` is `r` or `r²`.  The conjugate `W₂^y` acts
fixed-point-freely on this layer and gives `p ∣ r² - 1`, contradicting the
preceding arithmetic theorem.

The three parameter equalities are deliberately explicit: no hidden analytic
producer is used by this theorem. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData
      (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (hc : hyp.c = 1) (hq : hyp.q = 3)
    (hu : hyp.u = (hyp.p - 1) ^ 2 / 4)
    (data : TypeIOverNormalizerData hyp) : False := by
  classical
  have hp_ne_three : hyp.p ≠ 3 := by
    intro hp_three
    exact hyp.p_ne_q (hp_three.trans hq.symm)
  have hp_three : 3 ≤ hyp.p := hyp.three_le_p
  obtain ⟨k, hk⟩ := hyp.p_odd
  have hp_five : 5 ≤ hyp.p := by
    clear hu
    omega
  have hhalf_ne_one : (hyp.p - 1) / 2 ≠ 1 := by
    clear hu
    omega
  obtain ⟨r, hr, hrhalf⟩ := Nat.exists_prime_and_dvd hhalf_ne_one
  let : Fact r.Prime := ⟨hr⟩
  let R₀ : Sylow r ↥hyp.U := default
  have hR₀nc : ¬ IsCyclic ↥(R₀ : Subgroup ↥hyp.U) :=
    caseA_sylow_U_not_isCyclic_of_parameters
      hG hyp caseA hq hu hr hrhalf R₀
  obtain ⟨R, hR₀R, _x, _hxR₀, _hx1, _hxP, hcenter⟩ :=
    exists_sylow_over_U_with_trapped_center_of_not_isCyclic
      hG hyp hr hrhalf R₀ hR₀nc data.H data.U_le_H
  have hcard :=
    caseA_omega1Center_card_eq_prime_or_sq_of_parameters
      hG hyp caseA hc hq hr R₀ hR₀nc data.H data.U_le_H R hR₀R hcenter
  have hp_dvd : hyp.p ∣ r ^ 2 - 1 :=
    data.prime_dvd_sq_sub_one_of_omega1Center hr R hcard
  have hR₀card : r ∣ Nat.card ↥(R₀ : Subgroup ↥hyp.U) :=
    R₀.isPGroup'.card_eq_or_dvd.resolve_left fun hcard_one => hR₀nc <| by
      let : Subsingleton ↥(R₀ : Subgroup ↥hyp.U) :=
        (Nat.card_eq_one_iff_unique.mp hcard_one).1
      exact isCyclic_of_subsingleton
  have hrU : r ∣ Nat.card ↥hyp.U :=
    hR₀card.trans (Subgroup.card_subgroup_dvd_card (R₀ : Subgroup ↥hyp.U))
  have hrG : r ∣ Nat.card G :=
    hrU.trans (Subgroup.card_subgroup_dvd_card hyp.U)
  have hr_odd : Odd r := hG.odd.of_dvd_nat hrG
  exact false_of_odd_primes_dvd_half_and_sq_sub_one
    hyp.p_prime hr hyp.p_odd hr_odd hyp.three_le_p hrhalf hp_dvd

end OddOrder.Peterfalvi.S15

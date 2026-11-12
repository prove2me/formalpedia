-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.centralizer_omega1ZCenterOpCore_isPGroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:50:33.039336+00:00
-- url     : https://prove2.me/submissions/d8e3ba74-fb3c-4d5d-9004-d40fb5a84f41

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The image of `Z(P)` in `G` centralizes `O_p(G)`.

Pure structural fact: since `O_p(G) ≤ P`, any element of `Z(P)` commutes with
every element of `O_p(G)`.  Hypothesis (iv) `O_{p'}(G) = 1` is **not** needed
here; it enters only at the next step (Hall-Higman 3.21). -/
private theorem center_sylow_le_centralizer_opCore
    {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) :
    (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
      Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) := by
  rintro _ ⟨⟨z, hzP⟩, hz_center, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh_P : h ∈ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P hh
  have hc : (⟨h, hh_P⟩ : (P : Subgroup G)) * ⟨z, hzP⟩
      = ⟨z, hzP⟩ * ⟨h, hh_P⟩ :=
    Subgroup.mem_center_iff.mp hz_center ⟨h, hh_P⟩
  exact congr_arg Subtype.val hc

/-- **Isaacs Thm 7.6 Step 1** (mmd L3837): Hall-Higman 3.21 with `π = {p}`.

If `G` is `{p}`-separable (equivalently `p`-solvable) and `O_{p'}(G) = ⊥`,
then `C_G(O_p(G)) ≤ O_p(G)`. -/
theorem centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) :
    Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) ≤
      OddOrder.Isaacs.Ch01.opCore p G := by
  have hπ' : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥ := by
    rw [show ({q | q ∉ ({p} : Set ℕ)} : Set ℕ) = {q | q ≠ p} by
      ext q; simp]
    exact hOp'
  have hHH :=
    OddOrder.Isaacs.Ch03.hall_higman_1_2_3 (G := G) ({p} : Set ℕ) hπ'
  rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p] at hHH
  exact hHH

/-- **Isaacs Thm 7.6 Step 1** (mmd L3837): `Z(P) ≤ O_p(G)` under `O_{p'}(G) = ⊥`.

Composition of `center_sylow_le_centralizer_opCore` (structural) and
`centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot` (Hall-Higman 3.21).
This is the core conclusion of Step 1 in the 8-step proof of Thm 7.6. -/
theorem center_sylow_le_opCore_of_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G) :
    (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
      OddOrder.Isaacs.Ch01.opCore p G :=
  (center_sylow_le_centralizer_opCore P).trans
    (centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot hOp')

private theorem zCenterOpCoreSubgroup_le_opCore
    {G : Type*} [Group G] {p : ℕ} :
    zCenterOpCoreSubgroup G p ≤ OddOrder.Isaacs.Ch01.opCore p G := by
  rintro _ ⟨⟨z, hz_L⟩, _, rfl⟩
  exact hz_L

/-- `Z(U) = Z(O_p(G))` is a `p`-group: it is a subgroup of `U = O_p(G)`,
which is a `p`-group. -/
theorem zCenterOpCoreSubgroup_isPGroup
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    IsPGroup p (zCenterOpCoreSubgroup G p) :=
  (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).to_le zCenterOpCoreSubgroup_le_opCore

/-- Centralizer-conjugation lemma: `q ∈ centralizer s` ⇒ `q * z * q⁻¹ = z`
for every `z ∈ s`.  Generic. -/
theorem conj_eq_self_of_mem_centralizer
    {G : Type*} [Group G] {s : Set G}
    {q : G} (hq : q ∈ Subgroup.centralizer s) {z : G} (hz : z ∈ s) :
    q * z * q⁻¹ = z := by
  have hcomm : z * q = q * z := Subgroup.mem_centralizer_iff.mp hq z hz
  calc q * z * q⁻¹ = z * q * q⁻¹ := by rw [hcomm]
    _ = z := by group

/-- **Isaacs Cor 4.35 specialized for Z(U) = Z(O_p(G))**.

Given a `p'`-group `A` acting on `Z(U)` and fixing every element of order
`p` (= elements of `V = Ω₁ Z(U)`), `actionCommutator φ = ⊥`. -/
theorem cor_4_35_for_zCenterOpCoreSubgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Type*} [Group A] [Finite A]
    (φ : A →* MulAut ↥(zCenterOpCoreSubgroup G p))
    (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ v : ↥(zCenterOpCoreSubgroup G p), v ^ p = 1 →
      ∀ a : A, (φ a) v = v) :
    OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
  let _ : CommGroup ↥(zCenterOpCoreSubgroup G p) :=
    zCenterOpCoreSubgroup_commGroup G p
  OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p
    (p := p) φ (zCenterOpCoreSubgroup_isPGroup p) hA_p' h_fix

/-- If `Q ⊆ K = C_G(V)`, conjugation by elements of `Q` fixes every element
of `V = Ω₁ Z(U)` pointwise in `G`. -/
theorem conj_fixes_omega1ZCenterOpCore_of_le_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G}
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G))
    (q : ↥Q) {v : G} (hv : v ∈ omega1ZCenterOpCore G p) :
    (q : G) * v * (q : G)⁻¹ = v :=
  conj_eq_self_of_mem_centralizer (hQ_le_K q.2) hv

/-- **Isaacs Thm 7.6 Step 6 prep** (mmd L3881): `Z(P) ⊆ Z(U)` (in the image
form): under hypothesis (iv), `Z(P)` lies inside `Z(O_p(G)) = Z(U)`.

`Z(P) ⊆ U` by Step 1(a) (`center_sylow_le_opCore_of_oPiCorePrime_eq_bot`),
and any `z ∈ Z(P)` commutes with every `u ∈ U ⊆ P`. -/
theorem center_sylow_le_zCenterOpCoreSubgroup_of_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G) :
    (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
      zCenterOpCoreSubgroup G p := by
  rintro _ ⟨⟨z', hz'_P⟩, hz'_center, rfl⟩
  -- z' ∈ U by Step 1(a).
  have hz_in_U : (z' : G) ∈ OddOrder.Isaacs.Ch01.opCore p G :=
    center_sylow_le_opCore_of_oPiCorePrime_eq_bot hOp' P
      ⟨⟨z', hz'_P⟩, hz'_center, rfl⟩
  -- ⟨z', hz_in_U⟩ ∈ Z(U) because z' commutes with each u ∈ U ⊆ P.
  refine ⟨⟨(z' : G), hz_in_U⟩, ?_, rfl⟩
  change (⟨(z' : G), hz_in_U⟩ : ↥(OddOrder.Isaacs.Ch01.opCore p G)) ∈
      Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G)
  rw [Subgroup.mem_center_iff]
  intro u
  apply Subtype.ext
  change ((u : G) * (z' : G)) = ((z' : G) * (u : G))
  have hu_P : (u : G) ∈ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P u.2
  have hcomm : (⟨(u : G), hu_P⟩ : (P : Subgroup G)) * ⟨z', hz'_P⟩
      = ⟨z', hz'_P⟩ * ⟨(u : G), hu_P⟩ :=
    Subgroup.mem_center_iff.mp hz'_center _
  exact congr_arg Subtype.val hcomm

end OddOrder.Isaacs.Ch07

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The conjugation action of `Q ≤ K = C_G(V)` on `V = Ω₁ Z(U)` is trivial:
every element of `V` is fixed by every element of `Q`.  Pure unpacking of
`conj_fixes_omega1ZCenterOpCore_of_le_centralizer` into the action form needed
to apply Cor 4.35. -/
private theorem conj_fixes_zCenterOpCoreSubgroup_v_of_le_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G}
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G))
    (z : ↥(zCenterOpCoreSubgroup G p)) (hz_p : z ^ p = 1) (q : ↥Q) :
    (conjActionOnZCenterOpCoreSubgroup Q q) z = z := by
  -- (z : G) ∈ V := Ω₁ Z(U) since z ∈ Z(U) and z^p = 1.
  have hz_V : (z : G) ∈ omega1ZCenterOpCore G p := by
    rw [mem_omega1ZCenterOpCore]
    refine ⟨z.2, ?_⟩
    -- z^p = 1 in subtype ↥(Z(U)) ⇒ (z : G)^p = 1.
    have hzp_coe := congr_arg (fun x : ↥(zCenterOpCoreSubgroup G p) => (x : G)) hz_p
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hzp_coe
    exact hzp_coe
  -- Q ⊆ C_G(V), so (q : G) * (z : G) * (q : G)⁻¹ = (z : G).
  have hconj : (q : G) * (z : G) * (q : G)⁻¹ = (z : G) :=
    conj_fixes_omega1ZCenterOpCore_of_le_centralizer hQ_le_K q hz_V
  apply Subtype.ext
  -- (conjActionOnZCenterOpCoreSubgroup Q q) z = MulAut.conjNormal (q : G) z
  unfold conjActionOnZCenterOpCoreSubgroup
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
  exact hconj

/-- A `q`-subgroup `Q` of `K = C_G(V)` (`q ≠ p` prime) is contained in
the centralizer of `Z(U)` in `G`.

Apply Cor 4.35 (`cor_4_35_for_zCenterOpCoreSubgroup`) with the conjugation action
of `Q` on `Z(U)`: `Q` is a `p'`-group, and `Q` fixes every order-`p` element of
`Z(U)` (these are the elements of `V = Ω₁ Z(U)`, and `Q ⊆ K = C_G(V)`).  This
yields `actionCommutator = ⊥`, i.e., `Q` acts trivially on `Z(U)`. -/
private theorem q_subgroup_in_K_le_centralizer_zCenter
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {q : ℕ} (hq_prime : q.Prime) (hqp : q ≠ p)
    {Q : Subgroup G} (hQ_q : IsPGroup q Q)
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) :
    Q ≤ Subgroup.centralizer (zCenterOpCoreSubgroup G p : Set G) := by
  have : Fact q.Prime := ⟨hq_prime⟩
  -- (1) Q is a p'-group: q ≠ p prime + |Q| = q^k ⇒ p ∤ |Q|.
  have hQp' : ¬ p ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ_q
    rw [hk]
    intro hpdvd
    have hp_prime : p.Prime := Fact.out
    have hq_dvd_p : p ∣ q := hp_prime.dvd_of_dvd_pow hpdvd
    -- p ∣ q with p, q prime ⇒ p = q
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hq_dvd_p
    exact hqp this.symm
  -- (2) Apply Cor 4.35: the conjugation action of Q on Z(U) has actionCommutator = ⊥.
  have h_ac_bot :
      OddOrder.Isaacs.Ch04.actionCommutator (conjActionOnZCenterOpCoreSubgroup Q)
        = ⊥ :=
    cor_4_35_for_zCenterOpCoreSubgroup (conjActionOnZCenterOpCoreSubgroup Q) hQp'
      (fun z hz_p s => conj_fixes_zCenterOpCoreSubgroup_v_of_le_centralizer hQ_le_K z hz_p s)
  -- (3) Translate "actionCommutator = ⊥" into "Q acts trivially":
  --     for all (qq : Q), (z : Z(U)), MulAut.conjNormal qq z = z.
  have h_trivial :
      ∀ qq : Q, ∀ z : ↥(zCenterOpCoreSubgroup G p),
        (conjActionOnZCenterOpCoreSubgroup Q qq) z = z :=
    (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially _).mp h_ac_bot
  -- (4) Convert to: Q ⊆ C_G(Z(U)) inside G.
  intro qq hqq_Q
  rw [Subgroup.mem_centralizer_iff]
  rintro z hz
  -- z ∈ Z(U) as Subgroup G ⇒ z is in zCenterOpCoreSubgroup, lifted from a z' in subtype.
  -- Apply h_trivial at (⟨qq, hqq_Q⟩ : ↥Q) and (⟨z, hz⟩ : ↥(Z(U))).
  have hcommute := h_trivial ⟨qq, hqq_Q⟩ ⟨z, hz⟩
  -- hcommute: (conjActionOnZCenterOpCoreSubgroup Q ⟨qq, hqq_Q⟩) ⟨z, hz⟩ = ⟨z, hz⟩
  -- Unfold: MulAut.conjNormal (qq) ⟨z, hz⟩ = ⟨z, hz⟩, i.e., qq * z * qq⁻¹ = z.
  have hcommute_coe : ((conjActionOnZCenterOpCoreSubgroup Q ⟨qq, hqq_Q⟩) ⟨z, hz⟩ : G)
      = (⟨z, hz⟩ : ↥(zCenterOpCoreSubgroup G p)) := by
    rw [hcommute]
  unfold conjActionOnZCenterOpCoreSubgroup at hcommute_coe
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply] at hcommute_coe
  -- hcommute_coe : qq * z * qq⁻¹ = z. Rearrange to z * qq = qq * z.
  calc z * qq = (qq * z * qq⁻¹) * qq := by rw [hcommute_coe]
    _ = qq * z := by group

/-- A `q`-subgroup `Q` of `K = C_G(V)` (`q ≠ p` prime) is contained in
`P`, under hypothesis (v) `P = C_G(Z(P))` and `O_{p'}(G) = ⊥`.

Combines `q_subgroup_in_K_le_centralizer_zCenter` (yielding `Q ⊆ C_G(Z(U))`) with
the chain `Z(P) ⊆ Z(U)` (`center_sylow_le_zCenterOpCoreSubgroup_of_oPiCorePrime_eq_bot`)
+ contravariant `centralizer_le` + hypothesis (v) `C_G(Z(P)) = P`. -/
private theorem q_subgroup_in_K_le_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {q : ℕ} (hq_prime : q.Prime) (hqp : q ≠ p)
    {Q : Subgroup G} (hQ_q : IsPGroup q Q)
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) :
    Q ≤ (P : Subgroup G) := by
  -- Q ⊆ C_G(Z(U)).
  have hQ_cZU : Q ≤ Subgroup.centralizer (zCenterOpCoreSubgroup G p : Set G) :=
    q_subgroup_in_K_le_centralizer_zCenter hq_prime hqp hQ_q hQ_le_K
  -- Z(P) ⊆ Z(U), so C_G(Z(U)) ⊆ C_G(Z(P)) = P.
  have hZP_le_ZU :
      ((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype : Subgroup G) ≤
        zCenterOpCoreSubgroup G p :=
    center_sylow_le_zCenterOpCoreSubgroup_of_oPiCorePrime_eq_bot hOp' P
  have hC_ZU_le_C_ZP :
      Subgroup.centralizer (zCenterOpCoreSubgroup G p : Set G) ≤
        Subgroup.centralizer
          (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G) :=
    Subgroup.centralizer_le hZP_le_ZU
  rw [h_centralizer_center] at hC_ZU_le_C_ZP
  exact hQ_cZU.trans hC_ZU_le_C_ZP

/-- A `q`-subgroup `Q` of `K = C_G(V)` (`q ≠ p` prime) is trivial,
under the Thm 7.6 hypotheses (iv) `O_{p'}(G) = ⊥` and (v) `P = C_G(Z(P))`.

From `q_subgroup_in_K_le_sylow` we get `Q ⊆ P`.  Then `Q` is a `q`-group inside a
`p`-group `P` with `q ≠ p`, forcing `Q = ⊥` by coprimality of cardinalities. -/
private theorem q_subgroup_in_K_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {q : ℕ} (hq_prime : q.Prime) (hqp : q ≠ p)
    {Q : Subgroup G} (hQ_q : IsPGroup q Q)
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) :
    Q = ⊥ := by
  have : Fact q.Prime := ⟨hq_prime⟩
  have hQ_le_P : Q ≤ (P : Subgroup G) :=
    q_subgroup_in_K_le_sylow hOp' P h_centralizer_center hq_prime hqp hQ_q hQ_le_K
  -- Q is a q-group and Q ≤ P which is a p-group; coprime ⇒ |Q| = 1.
  have hP_p : IsPGroup p (P : Subgroup G) := P.isPGroup'
  have hQ_p : IsPGroup p Q := hP_p.to_le hQ_le_P
  obtain ⟨a, hQa⟩ := IsPGroup.iff_card.mp hQ_q
  obtain ⟨b, hQb⟩ := IsPGroup.iff_card.mp hQ_p
  have hp_prime : p.Prime := Fact.out
  have hQ_card : Nat.card Q = 1 := by
    have h_eq : q ^ a = p ^ b := hQa.symm.trans hQb
    by_contra h_ne
    have ha_pos : 1 ≤ a := by
      rcases a with _ | a'
      · -- a = 0 ⇒ |Q| = q^0 = 1, contradicting h_ne.
        exfalso
        apply h_ne
        rw [hQa, pow_zero]
      · exact Nat.le_add_left 1 a'
    have hq_dvd_qa : q ∣ q ^ a := dvd_pow_self q (Nat.one_le_iff_ne_zero.mp ha_pos)
    rw [h_eq] at hq_dvd_qa
    have hq_dvd_p : q ∣ p := hq_prime.dvd_of_dvd_pow hq_dvd_qa
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp hq_dvd_p
    exact hqp this
  exact Subgroup.eq_bot_of_card_eq Q hQ_card

/-- **Isaacs Thm 7.6 Step 6 main** (mmd L3879-3884): under hypotheses
(iv) `O_{p'}(G) = ⊥` and (v) `P = C_G(Z(P))`, `K := C_G(V)` is a `p`-group.

Proof: for every `g ∈ K`, the order `orderOf g` has only `p` as a prime divisor.
Indeed, if some prime `q ≠ p` divided `orderOf g = n`, then `g^(n/q) ∈ K` would
generate a `q`-subgroup of order `q`, which is forced to be trivial by
`q_subgroup_in_K_eq_bot`, contradicting `orderOf (g^(n/q)) = q > 1`.

Hence `orderOf g` is a power of `p` for every `g ∈ K`, so `K` is a `p`-group. -/
theorem _root_.solution
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G)) :
    IsPGroup p (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) := by
  -- Use IsPGroup.iff_orderOf: K is a p-group iff every g ∈ K has order a power of p.
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg_K⟩
  set K : Subgroup G := Subgroup.centralizer (omega1ZCenterOpCore G p : Set G) with hK_def
  -- Step (1): orderOf ⟨g, hg_K⟩ in K = orderOf g in G.
  set n : ℕ := orderOf g with hn_def
  have h_ord_eq : orderOf (⟨g, hg_K⟩ : ↥K) = n := Subgroup.orderOf_mk g hg_K
  rw [h_ord_eq]
  -- Reduce to: n is a power of p. Argue by contradiction.
  by_contra hno_pk
  push Not at hno_pk
  have hn_pos : 0 < n := orderOf_pos g
  have hp_prime : p.Prime := Fact.out
  -- ∃ q prime, q ≠ p, q ∣ n.
  have h_exists_q : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ n := by
    by_contra h_all
    push Not at h_all
    suffices ∀ q ∈ n.primeFactorsList, q = p by
      have : ∃ k, n = p ^ k := by
        refine ⟨n.primeFactorsList.length, ?_⟩
        rw [← List.prod_replicate, ← List.eq_replicate_of_mem this,
          Nat.prod_primeFactorsList hn_pos.ne']
      obtain ⟨k, hk⟩ := this
      exact hno_pk _ hk
    intro q hq
    obtain ⟨hq_prime, hq_dvd⟩ := (Nat.mem_primeFactorsList hn_pos.ne').mp hq
    by_contra hqp
    exact h_all q hq_prime hqp hq_dvd
  obtain ⟨q, hq_prime, hqp, hq_dvd_n⟩ := h_exists_q
  -- Set h := g^(n/q). It has order q.
  set h_elem : G := g ^ (n / q) with h_elem_def
  have hh_K : h_elem ∈ K := K.pow_mem hg_K _
  have hgq_pow_q : h_elem ^ q = 1 := by
    rw [h_elem_def, ← pow_mul, Nat.div_mul_cancel hq_dvd_n, pow_orderOf_eq_one]
  -- h ≠ 1 because n/q < n and orderOf g = n.
  have hh_ne_one : h_elem ≠ 1 := by
    intro h_eq
    have h_div : n ∣ (n / q) := by
      rw [hn_def]; exact orderOf_dvd_of_pow_eq_one h_eq
    have hq_two : 2 ≤ q := hq_prime.two_le
    have hnq_lt : n / q < n := Nat.div_lt_self hn_pos hq_two
    have hnq_pos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn_pos hq_dvd_n) hq_prime.pos
    have : n ≤ n / q := Nat.le_of_dvd hnq_pos h_div
    omega
  -- orderOf h = q.
  have hh_ord : orderOf h_elem = q := by
    have h_ord_dvd : orderOf h_elem ∣ q := orderOf_dvd_of_pow_eq_one hgq_pow_q
    rcases (Nat.dvd_prime hq_prime).mp h_ord_dvd with h1 | hqeq
    · exact absurd (orderOf_eq_one_iff.mp h1) hh_ne_one
    · exact hqeq
  -- Q := Subgroup.zpowers h is a q-group of K.
  have hQ_q : IsPGroup q (Subgroup.zpowers h_elem) := by
    have : Fact q.Prime := ⟨hq_prime⟩
    rw [IsPGroup.iff_card]
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers, hh_ord, pow_one]
  have hQ_le_K : (Subgroup.zpowers h_elem) ≤ K := by
    rw [Subgroup.zpowers_le]; exact hh_K
  -- Apply q_subgroup_in_K_eq_bot: ⟨h⟩ = ⊥.
  have hQ_bot : Subgroup.zpowers h_elem = ⊥ :=
    q_subgroup_in_K_eq_bot hOp' P h_centralizer_center hq_prime hqp hQ_q hQ_le_K
  -- But h ∈ ⟨h⟩ = ⊥ ⇒ h = 1, contradicting hh_ne_one.
  have : h_elem ∈ Subgroup.zpowers h_elem := Subgroup.mem_zpowers _
  rw [hQ_bot, Subgroup.mem_bot] at this
  exact hh_ne_one this

end OddOrder.Isaacs.Ch07

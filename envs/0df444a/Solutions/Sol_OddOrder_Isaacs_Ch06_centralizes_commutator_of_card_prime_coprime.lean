-- Prove2me | solution 1 for OddOrder.Isaacs.Ch06.centralizes_commutator_of_card_prime_coprime
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:46:52.328186+00:00
-- url     : https://prove2.me/submissions/65e3f7f4-7914-481b-96ef-8a7067b8f3db

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean
--   OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionTI
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_OddComplement
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Theorems.Thm_OddOrder_Isaacs_Ch06_false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime_lt

-- ===== OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean =====
namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

section

/-- **Isaacs Thm 6.9** (`p = q` branch for subgroups of order `pq`): a Frobenius actor cannot
contain a noncyclic subgroup of order `p^2`; hence such a subgroup must be cyclic. -/
theorem false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_prime_sq
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {p : ℕ} (hp : p.Prime) (hCard : Nat.card B = p ^ 2)
    (hNotCyclic : ¬ IsCyclic B) :
    False := by
  exact
    false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_prime_sq_of_finite_target
      hFrob B hp
      (OddOrder.GroupTheory.IsElementaryAbelian.of_card_prime_sq_of_not_isCyclic
        hp hCard hNotCyclic)
      hCard

/-- **Isaacs Thm 6.9** (order `pq` branch): a Frobenius actor cannot contain a noncyclic
subgroup of order `p*q`, for primes `p` and `q` that may be equal. -/
theorem false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hCard : Nat.card B = p * q) (hNotCyclic : ¬ IsCyclic B) :
    False := by
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · have hCard' : Nat.card B = q * p := by rw [hCard, mul_comm]
    exact
      false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime_lt
        (p := q) (q := p) hFrob B hpq hCard' hNotCyclic
  · subst q
    exact
      false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_prime_sq
        hFrob B hp.out (by simpa [pow_two] using hCard) hNotCyclic
  · exact
      false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime_lt
        (p := p) (q := q) hFrob B hqp hCard hNotCyclic

end

end OddOrder.Isaacs.Ch06

-- ===== OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean =====
namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

open scoped commutatorElement

open OddOrder.Isaacs.Ch04

/-- Local copy (below `OddOrder.BG`): if `M` is normal and `T ⊓ M = ⊥`, then
`|T ⊔ M| = |T| · |M|`.  (Standard second-isomorphism counting.) -/
private theorem card_sup_eq_card_mul_card_of_disjoint_normal'
    {G : Type*} [Group G] [Finite G] {T M : Subgroup G} [M.Normal] (h_disj : T ⊓ M = ⊥) :
    Nat.card ↥(T ⊔ M) = Nat.card ↥T * Nat.card ↥M := by
  have hMT_bot : M.subgroupOf T = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot, Subgroup.disjoint_def]
    intro x hxM hxT
    have hx : x ∈ T ⊓ M := ⟨hxT, hxM⟩
    rwa [h_disj, Subgroup.mem_bot] at hx
  have hMT_card_one : Nat.card (M.subgroupOf T) = 1 := by rw [hMT_bot]; exact Subgroup.card_bot
  have hT_quot_card : Nat.card T = Nat.card (T ⧸ M.subgroupOf T) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf T)
    rw [hMT_card_one, mul_one] at this; exact this
  have h_iso := QuotientGroup.quotientInfEquivProdNormalQuotient T M
  have h_eq_TM : Nat.card ((T ⊔ M : Subgroup G) ⧸ (M.subgroupOf (T ⊔ M))) = Nat.card T := by
    rw [hT_quot_card]; exact (Nat.card_congr h_iso.toEquiv).symm
  have hM_sub_TM_card : Nat.card (M.subgroupOf (T ⊔ M : Subgroup G)) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : M ≤ T ⊔ M)).toEquiv
  have h_card := Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf (T ⊔ M))
  rw [h_eq_TM, hM_sub_TM_card] at h_card
  exact h_card

/-- Local copy (below `OddOrder.BG`): if `A` normalizes `B` and `A ⊓ B = ⊥`, then
`|A ⊔ B| = |A| · |B|`. -/
private theorem card_sup_eq_mul_of_le_normalizer_of_disjoint'
    {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hdisj : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hAle : A ≤ A ⊔ B := le_sup_left
  have hBle : B ≤ A ⊔ B := le_sup_right
  have hBn : (B.subgroupOf (A ⊔ B)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  have hdisj' : A.subgroupOf (A ⊔ B) ⊓ B.subgroupOf (A ⊔ B) = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf] at hxA hxB
    have hxAB : (x : G) ∈ A ⊓ B := ⟨hxA, hxB⟩
    rw [hdisj, Subgroup.mem_bot] at hxAB
    rw [Subgroup.mem_bot]; exact Subtype.ext hxAB
  have htop : A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAle hBle, Subgroup.subgroupOf_self]
  have h := card_sup_eq_card_mul_card_of_disjoint_normal'
    (T := A.subgroupOf (A ⊔ B)) (M := B.subgroupOf (A ⊔ B)) hdisj'
  rw [htop, Nat.card_congr (Subgroup.topEquiv).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv] at h
  exact h

variable {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
  [MulDistribMulAction A U]

/-- **Step 2.** In a finite Frobenius complement `A` of odd order, a subgroup `R` of prime
order `r` not dividing `|A'|` (`A' = commutator A`) centralizes `A'`.

`A` is a Z-group (Step 1), so `A'` is cyclic and normal.  `R` acts coprimely on the abelian
`A'`, giving `C_{A'}(R) ⊓ [A', R] = ⊥`.  If `R` did **not** centralize `A'`, then `[A', R] ≠ ⊥`
contains a subgroup `S` of some prime order `s` (unique in the cyclic `A'`, hence `R`-invariant)
with `C_S(R) = ⊥`; then `R ⊔ S` is a **non-cyclic** subgroup of `A` of order `r s`, contradicting
Isaacs Thm 6.9 (`false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime`). -/
theorem _root_.solution
    (hFrob : IsFrobeniusAction A U) (hodd : Odd (Nat.card A))
    {R : Subgroup A} {r : ℕ} (hr : r.Prime) (hRcard : Nat.card ↥R = r)
    (hrN : ¬ r ∣ Nat.card ↥(commutator A)) :
    R ≤ Subgroup.centralizer ((commutator A : Subgroup A) : Set A) := by
  have hZ : IsZGroup A := isZGroup_of_isFrobeniusAction_of_odd hFrob hodd
  have hNcyc : IsCyclic ↥(commutator A) := IsZGroup.isCyclic_commutator (G := A)
  have hNnorm : (commutator A).Normal := inferInstance
  let : CommGroup ↥(commutator A) := IsCyclic.commGroup
  -- conjugation action of `R` on the cyclic normal commutator subgroup
  set φ : ↥R →* MulAut ↥(commutator A) :=
    (MulAut.conjNormal (H := commutator A)).comp R.subtype with hφ
  have hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥(commutator A)) := by
    rw [hRcard]; exact (Nat.Prime.coprime_iff_not_dvd hr).mpr hrN
  -- it suffices to show `R` acts trivially on `commutator A`
  suffices hac : actionCommutator φ = ⊥ by
    rw [actionCommutator_eq_bot_iff_acts_trivially] at hac
    intro ρ hρ
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 := hac ⟨ρ, hρ⟩ ⟨n, hn⟩
    have h2 : ρ * n * ρ⁻¹ = n := by
      have := congrArg (Subgroup.subtype (commutator A)) h1
      simpa [hφ, MulAut.conjNormal_apply] using this
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  by_contra hbot
  have hinf : Subgroup.fixedPointsOfMulAut φ ⊓ actionCommutator φ = ⊥ :=
    fixedPoints_inf_actionCommutator_eq_bot_of_abelian φ hcop
  -- a prime `s ∣ |[A', R]|`
  have hcard_ne : Nat.card ↥(actionCommutator φ) ≠ 1 := fun h1 =>
    hbot (Subgroup.card_eq_one.mp h1)
  obtain ⟨s, hs, hsdvd⟩ := Nat.exists_prime_and_dvd hcard_ne
  have : Fact s.Prime := ⟨hs⟩
  have : Fintype ↥(actionCommutator φ) := Fintype.ofFinite _
  obtain ⟨y, hy_ord⟩ := exists_prime_orderOf_dvd_card (G := ↥(actionCommutator φ)) s
    (by rwa [Nat.card_eq_fintype_card] at hsdvd)
  -- the order-`s` subgroup `S ≤ commutator A` inside `[A', R]`
  set x : ↥(commutator A) := (actionCommutator φ).subtype y with hxdef
  have hx_ord : orderOf x = s := by
    rw [hxdef, orderOf_injective (actionCommutator φ).subtype Subtype.coe_injective y]; exact hy_ord
  have hx_mem : x ∈ actionCommutator φ := by rw [hxdef]; exact y.2
  set S : Subgroup ↥(commutator A) := Subgroup.zpowers x with hSdef
  have hScard : Nat.card ↥S = s := by rw [hSdef, Nat.card_zpowers, hx_ord]
  have hSle : S ≤ actionCommutator φ := (Subgroup.zpowers_le).mpr hx_mem
  -- `S` is `φ`-invariant (unique order-`s` subgroup of the cyclic `commutator A`)
  have hSinv : ∀ ρ : ↥R, S.map (φ ρ).toMonoidHom = S := by
    intro ρ
    have hmap : S.map (φ ρ).toMonoidHom = Subgroup.zpowers ((φ ρ) x) := by
      rw [hSdef, MonoidHom.map_zpowers]; rfl
    have hord : orderOf ((φ ρ) x) = s := by
      have h := orderOf_injective (φ ρ).toMonoidHom (φ ρ).injective x
      rw [hx_ord] at h; exact h
    rw [hmap]
    refine eq_of_card_eq_prime_of_isCyclic hs ?_ hScard
    rw [Nat.card_zpowers]; exact hord
  -- push `S` to the subgroup `S' ≤ commutator A ≤ A`
  set S' : Subgroup A := S.map (commutator A).subtype with hS'def
  have hS'card : Nat.card ↥S' = s := by
    rw [hS'def,
      Nat.card_congr (Subgroup.equivMapOfInjective S (commutator A).subtype
        Subtype.coe_injective).toEquiv.symm]
    exact hScard
  -- conjugation by `ρ ∈ R` keeps `S'` inside `S'`
  have hconj_mem : ∀ ρ ∈ R, ∀ a ∈ S', ρ * a * ρ⁻¹ ∈ S' := by
    intro ρ hρ a ha
    rw [hS'def, Subgroup.mem_map] at ha ⊢
    obtain ⟨n, hnS, rfl⟩ := ha
    refine ⟨φ ⟨ρ, hρ⟩ n, ?_, ?_⟩
    · have hinv := hSinv ⟨ρ, hρ⟩
      rw [← hinv]; exact Subgroup.mem_map_of_mem _ hnS
    · simp [hφ, MulAut.conjNormal_apply]
  have hRnorm : R ≤ Subgroup.normalizer (S' : Set A) := by
    intro ρ hρ
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hconj_mem ρ hρ a ha, fun ha => ?_⟩
    have hb := hconj_mem ρ⁻¹ (R.inv_mem hρ) (ρ * a * ρ⁻¹) ha
    simpa [mul_assoc] using hb
  -- `R ⊓ S' = ⊥` (distinct prime orders `r ≠ s`)
  have hsN : s ∣ Nat.card ↥(commutator A) :=
    hsdvd.trans (Subgroup.card_subgroup_dvd_card (actionCommutator φ))
  have hrs : r ≠ s := fun h => hrN (h ▸ hsN)
  have hdisj : R ⊓ S' = ⊥ := by
    have hcoprs : Nat.Coprime r s := (Nat.coprime_primes hr hs).mpr hrs
    have hdvdR : Nat.card ↥(R ⊓ S') ∣ r := hRcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hdvdS : Nat.card ↥(R ⊓ S') ∣ s := hS'card ▸ Subgroup.card_dvd_of_le inf_le_right
    have h1 : Nat.card ↥(R ⊓ S') = 1 := Nat.dvd_one.mp (hcoprs ▸ Nat.dvd_gcd hdvdR hdvdS)
    exact Subgroup.card_eq_one.mp h1
  -- `B := R ⊔ S'` is a subgroup of `A` of order `r s`
  set B : Subgroup A := R ⊔ S' with hBdef
  have hBcard : Nat.card ↥B = r * s := by
    rw [hBdef, card_sup_eq_mul_of_le_normalizer_of_disjoint' hRnorm hdisj, hRcard, hS'card]
  -- `B` is not cyclic: cyclicity forces `R` to centralize `S`, but `C_S(R) = ⊥`
  have hBnc : ¬ IsCyclic ↥B := by
    intro hcyc
    let : CommGroup ↥B := IsCyclic.commGroup
    have hSfix : S ≤ Subgroup.fixedPointsOfMulAut φ := by
      intro n hnS
      rw [Subgroup.mem_fixedPointsOfMulAut]
      intro ρ
      have hnS' : (↑n : A) ∈ S' := by rw [hS'def]; exact Subgroup.mem_map_of_mem _ hnS
      have hρB : (↑ρ : A) ∈ B := hBdef ▸ Subgroup.mem_sup_left ρ.2
      have hnB : (↑n : A) ∈ B := hBdef ▸ Subgroup.mem_sup_right hnS'
      have hcomm : (↑ρ : A) * ↑n = ↑n * ↑ρ := by
        have := mul_comm (⟨↑ρ, hρB⟩ : ↥B) (⟨↑n, hnB⟩ : ↥B)
        exact congrArg (Subgroup.subtype B) this
      apply Subtype.ext
      simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
      rw [hcomm]; group
    have hSbot : S ≤ ⊥ := hinf ▸ le_inf hSfix hSle
    rw [le_bot_iff] at hSbot
    rw [hSbot, Subgroup.card_bot] at hScard
    exact hs.one_lt.ne' hScard.symm
  have : Fact r.Prime := ⟨hr⟩
  exact false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime hFrob B hBcard hBnc

end OddOrder.Isaacs.Ch06

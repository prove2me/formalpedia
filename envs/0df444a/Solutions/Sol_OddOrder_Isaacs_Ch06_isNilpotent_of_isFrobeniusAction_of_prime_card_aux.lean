-- Prove2me | solution 1 for OddOrder.Isaacs.Ch06.isNilpotent_of_isFrobeniusAction_of_prime_card_aux
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T06:11:10.074717+00:00
-- url     : https://prove2.me/submissions/af9fdfbd-9799-4196-8f42-699bb78620ab

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch05_Transfer/NilpotentPComplement.lean
--   OddOrder/GroupTheory/ThompsonSubgroup.lean
--   OddOrder/Isaacs/Ch06_FrobeniusActions/KernelNilpotent.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionTI
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03c_Thm37
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Theorems.Thm_Subgroup_thompsonJ_ne_bot
import Theorems.Thm_OddOrder_Isaacs_Ch05_hasNormalPComplement_of_isNilpotent
import Theorems.Thm_OddOrder_Isaacs_Ch07_thompson_normal_p_complement_of_local_hypotheses

-- ===== OddOrder/Isaacs/Ch05_Transfer/NilpotentPComplement.lean =====
namespace OddOrder.Isaacs.Ch05

open scoped Pointwise

section

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]

/-- A normal subgroup complementing a Sylow `p`-subgroup has `p'`-order. -/
theorem not_dvd_card_of_isComplement'_sylow {K : Subgroup H} (P : Sylow p H)
    (hC : Subgroup.IsComplement' K (P : Subgroup H)) : ¬ p ∣ Nat.card K := by
  intro hdvd
  have hcardP : Nat.card ↥(P : Subgroup H) = p ^ (Nat.card H).factorization p :=
    P.card_eq_multiplicity
  have hpow : p ^ ((Nat.card H).factorization p + 1) ∣ Nat.card H := by
    conv_rhs => rw [← hC.card_mul_card]
    rw [pow_succ, mul_comm (p ^ _) p, ← hcardP]
    exact mul_dvd_mul hdvd dvd_rfl
  have := (Nat.Prime.pow_dvd_iff_le_factorization hp.out Nat.card_pos.ne').mp hpow
  omega

/-- **Uniqueness of the normal `p`-complement**: two normal subgroups each complementing
a Sylow `p`-subgroup of a finite group coincide.

Each complement has `p'`-order while the quotient by the other has `p`-power order, so
the image of one in the quotient by the other is trivial. -/
theorem eq_of_normal_pcomplement {K K' : Subgroup H} [K.Normal] [K'.Normal]
    {P P' : Sylow p H}
    (hK : Subgroup.IsComplement' K (P : Subgroup H))
    (hK' : Subgroup.IsComplement' K' (P' : Subgroup H)) :
    K = K' := by
  have key : ∀ (L L' : Subgroup H) (Q Q' : Sylow p H), L.Normal → L'.Normal →
      Subgroup.IsComplement' L (Q : Subgroup H) →
      Subgroup.IsComplement' L' (Q' : Subgroup H) → L' ≤ L := by
    intro L L' Q Q' hLn hL'n hL hL'
    have := hLn
    -- the image of `L'` in `H ⧸ L` has order dividing both a `p'`-number and a `p`-power
    have h1 : Nat.card ↥(L'.map (QuotientGroup.mk' L)) ∣ Nat.card L' :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥(L'.map (QuotientGroup.mk' L)) ∣ p ^ (Nat.card H).factorization p := by
      have hquot : Nat.card (H ⧸ L) = p ^ (Nat.card H).factorization p := by
        have hidx : L.index = Nat.card ↥(Q : Subgroup H) := by
          have hmul := hL.card_mul_card
          have hmul' := Subgroup.card_mul_index (H := L)
          exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [hmul, hmul'])
        rw [← Q.card_eq_multiplicity, ← hidx]
        rfl
      rw [← hquot]
      exact Subgroup.card_subgroup_dvd_card _
    -- `p'`-order of `L'` makes it coprime to the `p`-power
    have hcop : Nat.gcd (Nat.card ↥L') (p ^ (Nat.card H).factorization p) = 1 :=
      Nat.Coprime.pow_right _
        ((hp.out.coprime_iff_not_dvd).mpr (not_dvd_card_of_isComplement'_sylow Q' hL')).symm
    have hone : Nat.card ↥(L'.map (QuotientGroup.mk' L)) = 1 :=
      Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h1 h2)
    have hbot : L'.map (QuotientGroup.mk' L) = ⊥ := Subgroup.card_eq_one.mp hone
    have hle : L' ≤ (QuotientGroup.mk' L).ker := by
      rw [← Subgroup.map_eq_bot_iff]
      exact hbot
    rwa [QuotientGroup.ker_mk'] at hle
  exact le_antisymm (key K' K P' P ‹_› ‹_› hK' hK) (key K K' P P' ‹_› ‹_› hK hK')

/-- The normal `p`-complement is fixed by every automorphism of `H`. -/
theorem map_mulAut_of_normal_pcomplement {K : Subgroup H} [K.Normal]
    {P : Sylow p H} (hK : Subgroup.IsComplement' K (P : Subgroup H)) (ψ : MulAut H) :
    K.map ψ.toMonoidHom = K := by
  have hmapn : (K.map ψ.toMonoidHom).Normal :=
    Subgroup.Normal.map ‹K.Normal› ψ.toMonoidHom ψ.surjective
  -- `ψ • P` is a Sylow `p`-subgroup with carrier `ψ(P)`
  have hPcoe : ((ψ • P : Sylow p H) : Subgroup H) = (P : Subgroup H).map ψ.toMonoidHom := by
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hcompl :
      Subgroup.IsComplement' (K.map ψ.toMonoidHom) ((ψ • P : Sylow p H) : Subgroup H) := by
    rw [hPcoe]
    refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
    · rw [(Nat.card_congr (Subgroup.equivMapOfInjective _ _ ψ.injective).toEquiv).symm,
        (Nat.card_congr
          (Subgroup.equivMapOfInjective (P : Subgroup H) _ ψ.injective).toEquiv).symm]
      exact hK.card_mul_card
    · rw [disjoint_iff, ← Subgroup.map_inf _ _ ψ.toMonoidHom ψ.injective,
        disjoint_iff.mp hK.disjoint, Subgroup.map_bot]
  exact eq_of_normal_pcomplement hcompl hK

end

end OddOrder.Isaacs.Ch05

-- ===== OddOrder/GroupTheory/ThompsonSubgroup.lean =====
namespace Subgroup

variable {G : Type*} [Group G]

/-- `J(P) ≤ P`: Thompson subgroup は `P` の部分群. -/
theorem thompsonJ_le (P : Subgroup G) (p : ℕ) : thompsonJ P p ≤ P := by
  refine iSup_le fun E => iSup_le fun hE => ?_
  exact hE.1

end Subgroup

-- ===== OddOrder/Isaacs/Ch06_FrobeniusActions/KernelNilpotent.lean =====
namespace OddOrder.Isaacs.Ch06

open OddOrder.Isaacs.Ch03 (IsAInvariant)

open scoped Pointwise

section

/-- **Solvable case of Thm 6.24** (= Isaacs Thm 6.22 in prime-order-complement form):
a solvable group admitting a Frobenius action by a group of prime order is nilpotent.

Realized inside the semidirect product `N ⋊ A` via BG Thm 3.7
(`isNilpotent_of_normalizing_primeOrder_fixedPointFree`). -/
theorem isNilpotent_of_isFrobeniusAction_of_isSolvable
    {A N : Type*} [Group A] [Finite A] [Group N] [Finite N] [Nontrivial N] [Group.IsSolvable N]
    [MulDistribMulAction A N] (hFrob : IsFrobeniusAction A N)
    (hA : ∃ p : ℕ, p.Prime ∧ Nat.card A = p) :
    Group.IsNilpotent N := by
  classical
  obtain ⟨p, hp, hcardA⟩ := hA
  set φ : A →* MulAut N := MulDistribMulAction.toMulAut A N with hφ
  -- ambient semidirect product
  have hAsolv : Group.IsSolvable A := by
    have : Fact p.Prime := ⟨hp⟩
    have hAcyc : IsCyclic A := isCyclic_of_prime_card hcardA
    exact Group.isSolvable_of_comm fun a b => by
      let := hAcyc.commGroup
      exact mul_comm a b
  have hΓsolv : Group.IsSolvable (N ⋊[φ] A) :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
      (le_of_eq SemidirectProduct.range_inl_eq_ker_rightHom.symm)
  set NΓ : Subgroup (N ⋊[φ] A) := (SemidirectProduct.inl : N →* N ⋊[φ] A).range with hNΓ
  set RΓ : Subgroup (N ⋊[φ] A) := (SemidirectProduct.inr : A →* N ⋊[φ] A).range with hRΓ
  have : Group.IsSolvable ↥(NΓ ⊔ RΓ) := by
    have htop : NΓ ⊔ RΓ = ⊤ := SemidirectProduct.inl_range_sup_inr_range_eq_top
    rw [htop]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := N ⋊[φ] A)).toMonoidHom) Subgroup.topEquiv.injective
  have hNΓnorm : NΓ.Normal := by
    rw [hNΓ, SemidirectProduct.range_inl_eq_ker_rightHom]; infer_instance
  have hnilpNΓ : Group.IsNilpotent ↥NΓ := by
    refine OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
      (N := NΓ) (R := RΓ) ?_ ?_ ?_ ?_ ⟨p, hp, ?_⟩ ?_
    · -- `R` normalizes the normal `NΓ`
      intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro n
      exact ⟨fun hn => hNΓnorm.conj_mem n hn x, fun hn => by
        have := hNΓnorm.conj_mem _ hn x⁻¹
        simpa [mul_assoc] using this⟩
    · -- disjoint
      exact (OddOrder.Isaacs.Ch03.inl_range_isComplement_inr_range φ).disjoint
    · -- `NΓ ≠ ⊥`
      obtain ⟨n₀, hn₀⟩ := exists_ne (1 : N)
      intro hbot
      rw [Subgroup.eq_bot_iff_forall] at hbot
      exact hn₀ (SemidirectProduct.inl_injective (by
        rw [map_one]
        exact hbot _ ⟨n₀, rfl⟩))
    · -- `RΓ ≠ ⊥`
      have : Nontrivial A := by
        have : 1 < Nat.card A := by rw [hcardA]; exact hp.one_lt
        exact Finite.one_lt_card_iff_nontrivial.mp this
      obtain ⟨a₀, ha₀⟩ := exists_ne (1 : A)
      intro hbot
      rw [Subgroup.eq_bot_iff_forall] at hbot
      exact ha₀ (SemidirectProduct.inr_injective (by
        rw [map_one]
        exact hbot _ ⟨a₀, rfl⟩))
    · -- `|RΓ| = p`
      rw [← hcardA]
      exact (Nat.card_congr
        (MonoidHom.ofInjective SemidirectProduct.inr_injective).toEquiv).symm
    · -- fixed-point-freeness in `Γ`
      rintro _ ⟨b, rfl⟩ hb _ ⟨m, rfl⟩ hm hconj
      have hb1 : b ≠ 1 := fun h => hb (by rw [h, map_one])
      have hm1 : m ≠ 1 := fun h => hm (by rw [h, map_one])
      -- `inr b * inl m * (inr b)⁻¹ = inl (φ b m)`
      have haut : (SemidirectProduct.inl ((φ b) m) : N ⋊[φ] A) =
          SemidirectProduct.inr b * SemidirectProduct.inl m * (SemidirectProduct.inr b)⁻¹ := by
        rw [← map_inv]
        exact SemidirectProduct.inl_aut (φ := φ) b m
      rw [← haut] at hconj
      have : (φ b) m = m := SemidirectProduct.inl_injective hconj
      exact hFrob b hb1 m hm1 this
  -- transport nilpotency back to `N`
  have : Group.IsNilpotent ↥NΓ := hnilpNΓ
  exact Group.nilpotent_of_mulEquiv
    (MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := φ))).symm

/-- The center of an `A`-invariant subgroup (as a subgroup of the ambient group) is
`A`-invariant. -/
private theorem aInvariant_center_map {A N : Type*} [Group A] [Group N]
    {φ : A →* MulAut N} {R : Subgroup N} (hR : IsAInvariant φ R) :
    IsAInvariant φ ((Subgroup.center ↥R).map R.subtype) := by
  -- membership description of the center image
  have hmem : ∀ z : N, z ∈ (Subgroup.center ↥R).map R.subtype ↔
      z ∈ R ∧ ∀ y ∈ R, z * y = y * z := by
    intro z
    constructor
    · rintro ⟨⟨z, hzR⟩, hz_cent, rfl⟩
      refine ⟨hzR, fun y hy => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz_cent ⟨y, hy⟩).symm
    · rintro ⟨hzR, hz⟩
      refine ⟨⟨z, hzR⟩, Subgroup.mem_center_iff.mpr fun ⟨y, hy⟩ => ?_, rfl⟩
      exact Subtype.ext (hz y hy).symm
  have hdir : ∀ b : A, ∀ z ∈ (Subgroup.center ↥R).map R.subtype,
      (φ b) z ∈ (Subgroup.center ↥R).map R.subtype := by
    intro b z hz
    rw [hmem] at hz ⊢
    refine ⟨hR.smul_mem b hz.1, fun y hy => ?_⟩
    have hy' : (φ b)⁻¹ y ∈ R := by
      have := hR.smul_mem b⁻¹ hy
      rwa [map_inv] at this
    have hzy := hz.2 _ hy'
    have hyy : (φ b) ((φ b)⁻¹ y) = y := (φ b).apply_symm_apply y
    calc (φ b) z * y = (φ b) z * (φ b) ((φ b)⁻¹ y) := by rw [hyy]
      _ = (φ b) (z * (φ b)⁻¹ y) := by rw [map_mul]
      _ = (φ b) ((φ b)⁻¹ y * z) := by rw [hzy]
      _ = (φ b) ((φ b)⁻¹ y) * (φ b) z := by rw [map_mul]
      _ = y * (φ b) z := by rw [hyy]
  exact OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem.mpr hdir

/-- Induction core for **Isaacs Thm 6.24**: strong induction on `|N|`, with a prime-order
actor `A`. -/
theorem _root_.solution
    {A : Type*} [Group A] [Finite A] {p : ℕ} (hp : p.Prime) (hcardA : Nat.card A = p) :
    ∀ (k : ℕ) (N : Type*) [Group N] [Finite N] [MulDistribMulAction A N],
      Nat.card N ≤ k → IsFrobeniusAction A N → Group.IsNilpotent N := by
  classical
  intro k
  induction k with
  | zero =>
    intro N _ _ _ hle _
    have := Nat.card_pos (α := N)
    omega
  | succ k IH =>
    intro N _ _ _ hle hFrob
    rcases subsingleton_or_nontrivial N with hsub | hnt
    · infer_instance
    set φ : A →* MulAut N := MulDistribMulAction.toMulAut A N with hφ_def
    by_cases hM : ∃ M : Subgroup N, M.Normal ∧ IsAInvariant φ M ∧ M ≠ ⊥ ∧ M ≠ ⊤
    · -- Case 1: a proper nontrivial `A`-invariant normal subgroup exists.
      obtain ⟨M, hMn, hMinv, hMbot, hMtop⟩ := hM
      have := hMn
      have hMsmul : ∀ a : A, ∀ m ∈ M, a • m ∈ M := fun a m hm => hMinv.smul_mem a hm
      -- `M` is nilpotent by induction
      let : MulDistribMulAction A ↥M :=
        IsFrobeniusAction.invariantSubgroupMulDistribMulAction M hMsmul
      have hFM := hFrob.subgroup M hMsmul
      have hltM : Nat.card ↥M ≤ k := by
        have hdvd := Subgroup.card_subgroup_dvd_card M
        have hle' := Nat.le_of_dvd Nat.card_pos hdvd
        have hne : Nat.card ↥M ≠ Nat.card N :=
          fun h => hMtop (Subgroup.eq_top_of_card_eq _ h)
        omega
      have hnilpM : Group.IsNilpotent ↥M := IH ↥M hltM hFM
      -- `N/M` is nilpotent by induction (Cor 6.2)
      let : MulDistribMulAction A (N ⧸ M) :=
        IsFrobeniusAction.invariantQuotientMulDistribMulAction M hMsmul
      have hFQ := hFrob.quotient M hMsmul
      have hltQ : Nat.card (N ⧸ M) ≤ k := by
        have h2 : 1 < Nat.card ↥M := (Subgroup.one_lt_card_iff_ne_bot M).mpr hMbot
        have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup M
        have hqpos : 0 < Nat.card (N ⧸ M) := Nat.card_pos
        have hlt : Nat.card (N ⧸ M) < Nat.card N := by
          rw [hmul]
          exact (lt_mul_iff_one_lt_right hqpos).mpr h2
        omega
      have hnilpQ : Group.IsNilpotent (N ⧸ M) := IH (N ⧸ M) hltQ hFQ
      -- hence `N` is solvable, and the solvable case applies
      have := hnilpM
      have := hnilpQ
      have : Group.IsSolvable N :=
        Group.isSolvable_of_ker_le_range M.subtype (QuotientGroup.mk' M)
          (le_of_eq (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))
      exact isNilpotent_of_isFrobeniusAction_of_isSolvable hFrob ⟨p, hp, hcardA⟩
    · -- Case 2: no proper nontrivial `A`-invariant normal subgroup.
      by_cases hpg : ∃ r : ℕ, r.Prime ∧ IsPGroup r N
      · obtain ⟨r, hr, hrN⟩ := hpg
        have : Fact r.Prime := ⟨hr⟩
        exact hrN.isNilpotent
      exfalso
      -- choose an odd prime `r ∣ |N|`
      obtain ⟨r, hr, hrdvd, hr2⟩ : ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card N ∧ r ≠ 2 := by
        by_contra hcon
        push Not at hcon
        exact hpg ⟨2, Nat.prime_two, IsPGroup.of_card
          (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
            fun {d} hd hdd => hcon d hd hdd)⟩
      have : Fact r.Prime := ⟨hr⟩
      -- coprime action, `A`-invariant Sylow `r`-subgroup
      have hCop : Nat.Coprime (Nat.card A) (Nat.card N) := by
        have : Fintype A := Fintype.ofFinite A
        have : Fintype N := Fintype.ofFinite N
        have := hFrob.coprime_card
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at this
        exact this.symm
      have hAsolv : Group.IsSolvable A := by
        have : Fact p.Prime := ⟨hp⟩
        have hAcyc : IsCyclic A := isCyclic_of_prime_card hcardA
        exact Group.isSolvable_of_comm fun a b => by
          let := hAcyc.commGroup
          exact mul_comm a b
      obtain ⟨R, hRinv⟩ :=
        OddOrder.Isaacs.Ch04.exists_aInvariant_sylow (φ := φ) hCop (Or.inl hAsolv) r
      -- `R` is nontrivial and proper
      have hR_ne_bot : (R : Subgroup N) ≠ ⊥ := by
        intro hbot
        have hcard := R.card_eq_multiplicity
        rw [hbot, Subgroup.card_bot] at hcard
        have hpos := hr.factorization_pos_of_dvd Nat.card_pos.ne' hrdvd
        exact absurd hcard.symm (Nat.one_lt_pow hpos.ne' hr.one_lt).ne'
      have hR_ne_top : (R : Subgroup N) ≠ ⊤ := by
        intro htop
        refine hpg ⟨r, hr, ?_⟩
        have hpgR := R.isPGroup'
        rw [htop] at hpgR
        exact hpgR.of_equiv Subgroup.topEquiv
      have : Nontrivial ↥(R : Subgroup N) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hR_ne_bot
      -- the center image `Z(R)` and the Thompson subgroup `J(R)`
      set ZI : Subgroup N :=
        (Subgroup.center ↥(R : Subgroup N)).map (R : Subgroup N).subtype with hZI_def
      set J : Subgroup N := Subgroup.thompsonJ (R : Subgroup N) r with hJ_def
      have hZinv : IsAInvariant φ ZI := aInvariant_center_map hRinv
      have hJinv : IsAInvariant φ J := by
        intro a
        have hsmul_eq : (φ a) • J = J.map (φ a).toMonoidHom := by
          rw [Subgroup.pointwise_smul_def]; rfl
        have hRmap : (R : Subgroup N).map (φ a).toMonoidHom = (R : Subgroup N) := by
          have hsmul_eq' : (φ a) • (R : Subgroup N) = (R : Subgroup N).map (φ a).toMonoidHom := by
            rw [Subgroup.pointwise_smul_def]; rfl
          rw [← hsmul_eq']
          exact hRinv a
        rw [hsmul_eq, hJ_def,
          ← Subgroup.thompsonJ_map_of_injective (f := (φ a).toMonoidHom) (φ a).injective,
          hRmap]
      have hZ_ne_bot : ZI ≠ ⊥ := by
        have : Nontrivial (Subgroup.center ↥(R : Subgroup N)) :=
          R.isPGroup'.center_nontrivial
        obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center ↥(R : Subgroup N))
        intro hbot
        rw [Subgroup.eq_bot_iff_forall] at hbot
        have h1 : ((z : ↥(R : Subgroup N)) : N) = 1 := hbot _ ⟨(z : ↥(R : Subgroup N)), z.2, rfl⟩
        exact hz (Subtype.ext (Subtype.ext h1))
      have hJ_ne_bot : J ≠ ⊥ := Subgroup.thompsonJ_ne_bot R.isPGroup' hR_ne_bot
      have hZI_le_R : ZI ≤ (R : Subgroup N) := Subgroup.map_subtype_le _
      have hJ_le_R : J ≤ (R : Subgroup N) := Subgroup.thompsonJ_le _ _
      -- normality of `ZI` or `J` in `N` would contradict the case assumption
      have hnot_normal : ∀ X : Subgroup N, IsAInvariant φ X → X ≠ ⊥ →
          X ≤ (R : Subgroup N) → ¬ X.Normal := by
        intro X hXinv hXbot hXle hXnorm
        exact hM ⟨X, hXnorm, hXinv, hXbot,
          fun htop => hR_ne_top (top_le_iff.mp (htop ▸ hXle))⟩
      -- a proper `A`-invariant subgroup is nilpotent (induction), so it has a normal
      -- `r`-complement
      have hlocal : ∀ L : Subgroup N, IsAInvariant φ L → L ≠ ⊤ →
          OddOrder.Isaacs.Ch05.HasNormalPComplement r ↥L := by
        intro L hLinv hLtop
        have hLsmul : ∀ a : A, ∀ m ∈ L, a • m ∈ L := fun a m hm => hLinv.smul_mem a hm
        let : MulDistribMulAction A ↥L :=
          IsFrobeniusAction.invariantSubgroupMulDistribMulAction L hLsmul
        have hFL := hFrob.subgroup L hLsmul
        have hltL : Nat.card ↥L ≤ k := by
          have hdvd := Subgroup.card_subgroup_dvd_card L
          have hle' := Nat.le_of_dvd Nat.card_pos hdvd
          have hne : Nat.card ↥L ≠ Nat.card N :=
            fun h => hLtop (Subgroup.eq_top_of_card_eq _ h)
          omega
        have : Group.IsNilpotent ↥L := IH ↥L hltL hFL
        exact OddOrder.Isaacs.Ch05.hasNormalPComplement_of_isNilpotent
      -- the two local subgroups of Thm 7.1 are proper
      have hCZ_ne_top : Subgroup.centralizer (ZI : Set N) ≠ ⊤ := by
        intro htop
        refine hnot_normal ZI hZinv hZ_ne_bot hZI_le_R ⟨fun n hn g => ?_⟩
        have hgZ : g ∈ Subgroup.centralizer (ZI : Set N) := htop ▸ Subgroup.mem_top g
        rw [Subgroup.mem_centralizer_iff] at hgZ
        have hcomm := hgZ n hn
        rw [show g * n * g⁻¹ = n from by rw [← hcomm]; group]
        exact hn
      have hNJ_ne_top : Subgroup.normalizer (J : Set N) ≠ ⊤ := by
        intro htop
        refine hnot_normal J hJinv hJ_ne_bot hJ_le_R ⟨fun n hn g => ?_⟩
        have hgJ : g ∈ Subgroup.normalizer (J : Set N) := htop ▸ Subgroup.mem_top g
        exact (Subgroup.mem_normalizer_iff.mp hgJ n).mp hn
      -- Thompson's theorem gives a normal `r`-complement of `N`
      obtain ⟨K, hKn, hKcompl⟩ :=
        OddOrder.Isaacs.Ch07.thompson_normal_p_complement_of_local_hypotheses R hr2
          (hlocal _ hZinv.centralizer hCZ_ne_top)
          (hlocal _ hJinv.normalizer hNJ_ne_top)
      have := hKn
      -- `K` is `A`-invariant, nontrivial, and proper: contradiction
      have hKinv : IsAInvariant φ K := by
        refine OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem.mpr fun a m hm => ?_
        have hfix := OddOrder.Isaacs.Ch05.map_mulAut_of_normal_pcomplement
          (P := default) (hKcompl default) (φ a)
        rw [← hfix]
        exact ⟨m, hm, rfl⟩
      have hK_ne_top : K ≠ ⊤ := by
        intro htop
        have hc := hKcompl R
        rw [htop, Subgroup.isComplement'_top_left] at hc
        exact hR_ne_bot hc
      have hK_ne_bot : K ≠ ⊥ := by
        intro hbot
        have hc := hKcompl R
        rw [hbot, Subgroup.isComplement'_bot_left] at hc
        refine hpg ⟨r, hr, ?_⟩
        have hpgR := R.isPGroup'
        rw [hc] at hpgR
        exact hpgR.of_equiv Subgroup.topEquiv
      exact hM ⟨K, hKn, hKinv, hK_ne_bot, hK_ne_top⟩

end

end OddOrder.Isaacs.Ch06

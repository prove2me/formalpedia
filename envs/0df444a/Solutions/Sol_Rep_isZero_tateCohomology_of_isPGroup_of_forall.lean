-- Prove2me | solution 1 for Rep.isZero_tateCohomology_of_isPGroup_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4389100d-1bf6-5507-8bae-e4672ecc0a54

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_Rep_isZero_tateCohomology_of_subsingleton
import Theorems.Thm_groupCohomology_nonempty_quotientToInvariants_iso_of_forall_isZero
import Theorems.Thm_Rep_nonempty_tateCohomology_res_iso_res_dimShiftDownObj
import Theorems.Thm_Rep_nonempty_tateCohomology_iso_dimShiftDownObj
import Theorems.Thm_Rep_nonempty_tateCohomology_iso_add_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_isZero_tateCohomology_of_isPGroup_of_forall
p2m_attr_erase "simp" "Rep.coe_tateδneg2_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply"

set_option autoImplicit false
universe u
open CategoryTheory Rep
set_option maxHeartbeats 1600000

theorem solution {k P : Type u} [CommRing k] [Group P] [Fintype P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (B : Rep.{u} k P)
    (h : ∀ (Q : Type u) [Group Q] [Fintype Q] (g : Q →* P), Function.Injective g →
      ∃ q : ℤ, CategoryTheory.Limits.IsZero ((Rep.res g B).tateCohomology q) ∧
        CategoryTheory.Limits.IsZero ((Rep.res g B).tateCohomology (q + 1)))
    (n : ℤ) : CategoryTheory.Limits.IsZero (B.tateCohomology n) := by
  classical

  suffices main : ∀ (m : ℕ) (P : Type u) [Group P] [Fintype P], Fintype.card P = m → IsPGroup p P →
      ∀ (B : Rep.{u} k P), (∀ (Q : Type u) [Group Q] [Fintype Q] (g : Q →* P), Function.Injective g →
        ∃ q : ℤ, CategoryTheory.Limits.IsZero ((Rep.res g B).tateCohomology q) ∧
          CategoryTheory.Limits.IsZero ((Rep.res g B).tateCohomology (q + 1))) →
      ∀ n : ℤ, CategoryTheory.Limits.IsZero (B.tateCohomology n) from main _ P rfl hP B h n
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro P _ _ hcard hP B h n
  by_cases htriv : Subsingleton P
  · exact Rep.isZero_tateCohomology_of_subsingleton B n
  ·
    have hp : p.Prime := Fact.out
    obtain ⟨kk, hkpos, hcardP⟩ := (IsPGroup.nontrivial_iff_card hP).1 (not_subsingleton_iff_nontrivial.1 htriv)
    obtain ⟨N, hNn, hNidx⟩ : ∃ N : Subgroup P, N.Normal ∧ N.index = p := by
      obtain ⟨N, hN⟩ := Sylow.exists_subgroup_card_pow_prime p (show p ^ (kk - 1) ∣ Nat.card P from
        hcardP ▸ pow_dvd_pow p (Nat.sub_le kk 1))
      have hidx : N.index = p := by
        have h1 := N.card_mul_index
        rw [hN, hcardP, show kk = (kk - 1) + 1 from (Nat.sub_add_cancel hkpos).symm, pow_succ] at h1
        exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h1
      refine ⟨N, Subgroup.normal_of_index_eq_minFac_card ?_, hidx⟩
      rw [hidx, hcardP]
      have hmp : (p ^ kk).minFac.Prime := Nat.minFac_prime (by
        have := Nat.one_lt_pow hkpos.ne' hp.one_lt; omega)
      exact ((Nat.prime_dvd_prime_iff_eq hmp hp).1 (hmp.dvd_of_dvd_pow (Nat.minFac_dvd _))).symm
    haveI := hNn

    have hNB : ∀ n : ℤ, CategoryTheory.Limits.IsZero ((Rep.res N.subtype B).tateCohomology n) := by
      refine ih (Fintype.card N) ?_ ↥N rfl (hP.to_subgroup N) (Rep.res N.subtype B) ?_
      · rw [← hcard, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, ← N.card_mul_index, hNidx]
        exact lt_mul_of_one_lt_right (Nat.card_pos) hp.one_lt
      · intro Q _ _ g hg
        exact h Q (N.subtype.comp g) (N.subtype_injective.comp hg)

    have hshift : ∀ (X : Rep.{u} k P), (∀ n : ℤ, CategoryTheory.Limits.IsZero ((Rep.res N.subtype X).tateCohomology n)) →
        ∀ n : ℤ, CategoryTheory.Limits.IsZero ((Rep.res N.subtype X.dimShiftDownObj).tateCohomology n) := by
      intro X hX n
      obtain ⟨e⟩ := Rep.nonempty_tateCohomology_res_iso_res_dimShiftDownObj N X (n - 1)
      have := hX (n - 1)
      rw [show n - 1 + 1 = n by ring] at e
      exact this.of_iso e.symm

    have hper : ∀ (X : Rep.{u} k P), (∀ n : ℤ, CategoryTheory.Limits.IsZero ((Rep.res N.subtype X).tateCohomology n)) →
        ∀ m : ℕ, (CategoryTheory.Limits.IsZero (X.tateCohomology ((m + 1 : ℕ) : ℤ)) ↔
          CategoryTheory.Limits.IsZero (X.tateCohomology ((m + 3 : ℕ) : ℤ))) := by
      intro X hX m

      have hXN : ∀ i : ℕ, CategoryTheory.Limits.IsZero (groupCohomology (Rep.res N.subtype X) (i + 1)) := fun i => hX (i + 1 : ℕ)
      obtain ⟨e₁⟩ := groupCohomology.nonempty_quotientToInvariants_iso_of_forall_isZero N X hXN m
      obtain ⟨e₃⟩ := groupCohomology.nonempty_quotientToInvariants_iso_of_forall_isZero N X hXN (m + 2)

      haveI : Fintype (P ⧸ N) := inferInstance
      haveI hcyc : IsCyclic (P ⧸ N) := isCyclic_of_prime_card (p := p) (by rw [← Subgroup.index_eq_card, hNidx])
      letI : CommGroup (P ⧸ N) := IsCyclic.commGroup
      obtain ⟨c, hc⟩ : ∃ c : P ⧸ N, ∀ x, x ∈ Subgroup.zpowers c := IsCyclic.exists_generator
      obtain ⟨eper⟩ := Rep.nonempty_tateCohomology_iso_add_two (X.quotientToInvariants N) c hc ((m + 1 : ℕ) : ℤ)

      have hcast : ((m + 1 : ℕ) : ℤ) + 2 = ((m + 3 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast] at eper
      have e13 : groupCohomology (X.quotientToInvariants N) (m + 1) ≅ groupCohomology (X.quotientToInvariants N) (m + 3) := eper
      constructor
      · intro h1
        have h1' : CategoryTheory.Limits.IsZero (groupCohomology X (m + 1)) := h1
        have h3 : CategoryTheory.Limits.IsZero (groupCohomology X (m + 3)) := ((h1'.of_iso e₁).of_iso e13.symm).of_iso e₃.symm
        exact h3
      · intro h3
        have h3' : CategoryTheory.Limits.IsZero (groupCohomology X (m + 3)) := h3
        have h1 : CategoryTheory.Limits.IsZero (groupCohomology X (m + 1)) := ((h3'.of_iso e₃).of_iso e13).of_iso e₁.symm
        exact h1

    have hper' : ∀ (j : ℕ) (X : Rep.{u} k P), (∀ n : ℤ, CategoryTheory.Limits.IsZero ((Rep.res N.subtype X).tateCohomology n)) →
        ∀ a : ℤ, 1 ≤ a + j → (CategoryTheory.Limits.IsZero (X.tateCohomology a) ↔
          CategoryTheory.Limits.IsZero (X.tateCohomology (a + 2))) := by
      intro j
      induction j with
      | zero =>
        intro X hX a ha
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = (m + 1 : ℕ) := ⟨(a - 1).toNat, by omega⟩
        rw [show ((m + 1 : ℕ) : ℤ) + 2 = ((m + 3 : ℕ) : ℤ) by push_cast; ring]
        exact hper X hX m
      | succ j ihj =>
        intro X hX a ha
        obtain ⟨e₀⟩ := Rep.nonempty_tateCohomology_iso_dimShiftDownObj X a
        obtain ⟨e₂⟩ := Rep.nonempty_tateCohomology_iso_dimShiftDownObj X (a + 2)
        have hih := ihj X.dimShiftDownObj (hshift X hX) (a + 1) (by omega)
        rw [show a + 1 + 2 = a + 2 + 1 by ring] at hih
        exact ⟨fun h0 => (hih.1 (h0.of_iso e₀.symm)).of_iso e₂, fun h2 => (hih.2 (h2.of_iso e₂.symm)).of_iso e₀⟩

    obtain ⟨q₀, hq₀, hq₁⟩ := h P (MonoidHom.id P) Function.injective_id
    have hq₀' : CategoryTheory.Limits.IsZero (B.tateCohomology q₀) := hq₀
    have hq₁' : CategoryTheory.Limits.IsZero (B.tateCohomology (q₀ + 1)) := hq₁
    have hstep : ∀ a : ℤ, (CategoryTheory.Limits.IsZero (B.tateCohomology a) ↔ CategoryTheory.Limits.IsZero (B.tateCohomology (a + 2))) :=
      fun a => hper' (1 - a).toNat B hNB a (by omega)

    have hall : ∀ i : ℕ, CategoryTheory.Limits.IsZero (B.tateCohomology (q₀ + 2 * i)) ∧ CategoryTheory.Limits.IsZero (B.tateCohomology (q₀ + 1 + 2 * i)) ∧
        CategoryTheory.Limits.IsZero (B.tateCohomology (q₀ - 2 * i)) ∧ CategoryTheory.Limits.IsZero (B.tateCohomology (q₀ + 1 - 2 * i)) := by
      intro i
      induction i with
      | zero => simpa using ⟨hq₀', hq₁', hq₀', hq₁'⟩
      | succ i ihi =>
        obtain ⟨h1, h2, h3, h4⟩ := ihi
        refine ⟨?_, ?_, ?_, ?_⟩
        · have := (hstep (q₀ + 2 * i)).1 h1; push_cast; rwa [show q₀ + 2 * (↑i + 1) = q₀ + 2 * i + 2 by ring]
        · have := (hstep (q₀ + 1 + 2 * i)).1 h2; push_cast; rwa [show q₀ + 1 + 2 * (↑i + 1) = q₀ + 1 + 2 * i + 2 by ring]
        · have := (hstep (q₀ - 2 * (i + 1 : ℕ))).2; push_cast at this ⊢
          exact this (by rwa [show q₀ - 2 * (↑i + 1) + 2 = q₀ - 2 * i by ring])
        · have := (hstep (q₀ + 1 - 2 * (i + 1 : ℕ))).2; push_cast at this ⊢
          exact this (by rwa [show q₀ + 1 - 2 * (↑i + 1) + 2 = q₀ + 1 - 2 * i by ring])

    obtain ⟨i, hi | hi | hi | hi⟩ : ∃ i : ℕ, n = q₀ + 2 * i ∨ n = q₀ + 1 + 2 * i ∨ n = q₀ - 2 * i ∨ n = q₀ + 1 - 2 * i := by
      rcases Int.emod_two_eq_zero_or_one (n - q₀) with h0 | h1
      · rcases le_or_gt q₀ n with hle | hlt
        · exact ⟨((n - q₀) / 2).toNat, Or.inl (by omega)⟩
        · exact ⟨((q₀ - n) / 2).toNat, Or.inr (Or.inr (Or.inl (by omega)))⟩
      · rcases le_or_gt (q₀ + 1) n with hle | hlt
        · exact ⟨((n - q₀ - 1) / 2).toNat, Or.inr (Or.inl (by omega))⟩
        · exact ⟨((q₀ + 1 - n) / 2).toNat, Or.inr (Or.inr (Or.inr (by omega)))⟩
    · rw [hi]; exact (hall i).1
    · rw [hi]; exact (hall i).2.1
    · rw [hi]; exact (hall i).2.2.1
    · rw [hi]; exact (hall i).2.2.2

end S_Rep_isZero_tateCohomology_of_isPGroup_of_forall
end P2MW
export P2MW.S_Rep_isZero_tateCohomology_of_isPGroup_of_forall (solution)

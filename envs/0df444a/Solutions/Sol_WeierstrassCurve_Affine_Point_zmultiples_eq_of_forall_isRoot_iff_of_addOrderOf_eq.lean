-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d5fd7a4c-e288-5936-884f-ad6864346e91

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq

set_option autoImplicit false

theorem solution
    (Ω : Type) [Field Ω] [DecidableEq Ω] (W : WeierstrassCurve Ω) (M' : ℕ) [NeZero M']
    (H : AddSubgroup W.toAffine.Point) (hH : IsAddCyclic H ∧ Nat.card H = M')
    (h : ↥M'.primeFactors → Polynomial Ω) (h0 : ∀ p, h p ≠ 0)
    (hroots : ∀ (p : ↥M'.primeFactors) (x₁ : Ω),
      (h p).IsRoot x₁ ↔ ∃ (P : W.toAffine.Point) (y₁ : Ω) (h₁ : W.toAffine.Nonsingular x₁ y₁),
        P ∈ H ∧ addOrderOf P = (p : ℕ) ^ M'.factorization (p : ℕ) ∧ P = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁)
    (g : W.toAffine.Point)
    (hg : addOrderOf g = M' ∧
      ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Ω) (h₁ : W.toAffine.Nonsingular x₁ y₁),
        n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
        (h p).IsRoot x₁) :
    AddSubgroup.zmultiples g = H := by
  classical
  obtain ⟨hord, hcut⟩ := hg
  have hM0 : M' ≠ 0 := NeZero.ne M'
  haveI hHfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hH.2]; exact hM0)
  have hcardG : Nat.card (AddSubgroup.zmultiples g) = M' := by rw [Nat.card_zmultiples, hord]
  haveI hGfin : Finite (AddSubgroup.zmultiples g) := Nat.finite_of_card_ne_zero (by rw [hcardG]; exact hM0)

  have key : ∀ p : ↥M'.primeFactors,
      addOrderOf ((M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g) = (p : ℕ) ^ M'.factorization (p : ℕ) ∧
        (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g ∈ H := by
    intro p
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have hpk : (p : ℕ) ^ M'.factorization (p : ℕ) ∣ M' := Nat.ordProj_dvd M' p
    have hordp : addOrderOf ((M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g) =
        (p : ℕ) ^ M'.factorization (p : ℕ) := by
      have hn0 : M' / (p : ℕ) ^ M'.factorization (p : ℕ) ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hpk) (pow_pos hp.pos _)).ne'
      rw [addOrderOf_nsmul_of_dvd hn0 (by rw [hord]; exact Nat.div_dvd_of_dvd hpk), hord,
        Nat.div_div_self hpk hM0]
    refine ⟨hordp, ?_⟩
    have hk : 0 < M'.factorization (p : ℕ) := hp.factorization_pos_of_dvd hM0 (Nat.dvd_of_mem_primeFactors p.2)
    have hne : (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g ≠ 0 := by
      intro h0'
      rw [h0', addOrderOf_zero] at hordp
      have : 1 < (p : ℕ) ^ M'.factorization (p : ℕ) := Nat.one_lt_pow hk.ne' hp.one_lt
      omega

    rcases hgp : (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g with _ | @⟨x₁, y₁, h₁⟩
    · exact absurd hgp hne
    · have hroot : (h p).IsRoot x₁ := hcut p _ x₁ y₁ h₁ hgp hordp
      obtain ⟨P, y₂, h₂, hPH, -, hPeq⟩ := (hroots p x₁).mp hroot
      rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₂.left h₁.left rfl with hy | hy
      · subst hy
        rw [hPeq] at hPH
        exact hPH
      · subst hy
        have hneg : P = -WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ := by
          rw [hPeq, WeierstrassCurve.Affine.Point.neg_some]
        have := H.neg_mem hPH
        rwa [hneg, neg_neg] at this

  set I : AddSubgroup W.toAffine.Point := AddSubgroup.zmultiples g ⊓ H with hI
  haveI hIfin : Finite I :=
    Finite.of_injective (AddSubgroup.inclusion (inf_le_right : I ≤ H)) (AddSubgroup.inclusion_injective _)
  have hIpos : 0 < Nat.card I := Nat.card_pos
  have hdiv : M' ∣ Nat.card I := by
    rw [← Nat.factorization_le_iff_dvd hM0 hIpos.ne', Finsupp.le_def]
    intro p
    by_cases hp : p ∈ M'.primeFactors
    · obtain ⟨hordp, hmemH⟩ := key ⟨p, hp⟩
      have hmem : (M' / p ^ M'.factorization p) • g ∈ I :=
        ⟨AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples g) _, hmemH⟩
      have hd := AddSubgroup.addOrderOf_dvd_natCard I hmem
      rw [hordp] at hd
      exact ((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hIpos.ne').mp hd
    · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
      rw [hp]; exact Nat.zero_le _
  have hIG : I = AddSubgroup.zmultiples g :=
    AddSubgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardG]; exact Nat.le_of_dvd hIpos hdiv)
  have hIH : I = H :=
    AddSubgroup.eq_of_le_of_card_ge inf_le_right (by rw [hH.2]; exact Nat.le_of_dvd hIpos hdiv)
  exact hIG.symm.trans hIH

end S_WeierstrassCurve_Affine_Point_zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq (solution)

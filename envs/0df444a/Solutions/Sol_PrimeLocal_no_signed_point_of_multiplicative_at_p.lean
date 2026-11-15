-- Prove2me | solution 1 for PrimeLocal.no_signed_point_of_multiplicative_at_p
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:13:24.543986+00:00
-- url     : https://prove2.me/submissions/7f3c1a7d-eeed-4548-9d72-6d279634c560

import Theorems.Thm_WeierstrassCurve_exists_atP_filtration_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_det_galoisRep_surjOn_inertia
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_neg_of_sq_eq_prime
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

namespace PrimeLocal
/-- A ramified quadratic signed point contradicts the full inertia determinant image. -/
theorem _root_.solution (W' : WeierstrassCurve ℤ) (hΔ : W'.Δ ≠ 0) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpΔ : (p : ℤ) ∣ W'.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W'.c₄) (Q' : ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQ' : addOrderOf Q' = p) (s : AlgebraicClosure ℚ) (hs : s ^ 2 = (p : AlgebraicClosure ℚ)) (hsign : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (σ s = s → σ • Q' = Q') ∧ (σ s = -s → σ • Q' = -Q')) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hQzero : p • Q' = 0 := by rw [← hQ']; exact addOrderOf_nsmul_eq_zero Q'
  have hell : (W'.map (Int.castRingHom ℚ)).IsElliptic := by
    refine (WeierstrassCurve.isElliptic_iff _).mpr (isUnit_iff_ne_zero.mpr ?_)
    rw [WeierstrassCurve.map_Δ, eq_intCast]
    exact_mod_cast hΔ
  haveI := hell
  let V := Submodule.torsionBy ℤ ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p
  have hcard : Nat.card V = p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (W'.map (Int.castRingHom ℚ))
      (Nat.cast_ne_zero.mpr hp.ne_zero)
  haveI : Finite V := Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero 2 hp.ne_zero)
  obtain ⟨A, hA, _⟩ := ValuationSubring.exists_isFrobeniusAt_rat p hp
  obtain ⟨F, hF, hFcard, hFstab, hFabs⟩ :=
    WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction
      W' p hp2 hΔ hpΔ hpc₄ A hA 1 le_rfl
  simp only [pow_one] at hF hFcard hFabs
  let N : Submodule (ZMod p) V :=
    { carrier := {x | (x : ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) ∈ F}
      zero_mem' := F.zero_mem
      add_mem' := fun hx hy => F.add_mem hx hy
      smul_mem' := by
        intro c x hx
        rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
        exact F.nsmul_mem hx c.val }
  have hNcard : Nat.card N = p := by
    have hc : Nat.card N = Nat.card F := Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun x => ⟨⟨x.1, by
          rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
          exact ((hF x.1).mp x.2).1⟩, x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    exact hc.trans hFcard
  have hNdim : Module.finrank (ZMod p) N = 1 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod p) (V := N)
    rw [hNcard, Nat.card_zmod] at hh
    have hh : p ^ 1 = p ^ Module.finrank (ZMod p) N := (pow_one p).trans hh
    exact (Nat.pow_right_injective hp.two_le hh).symm
  let q : V := ⟨Q', by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact hQzero⟩
  have hqne : q ≠ 0 := by
    intro hz
    have hz' : Q' = 0 := congrArg Subtype.val hz
    simp [hz'] at hQ'
    omega
  obtain ⟨τ, hτ, hτs⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_neg_of_sq_eq_prime hp hp2 A hA s hs
  have htau : τ • Q' = -Q' := (hsign τ).2 hτs
  have htwice : 2 • Q' ∈ F := by
    have h := F.neg_mem (hFabs τ hτ Q' hQzero)
    rw [htau] at h
    simpa [two_nsmul] using h
  have hqF : Q' ∈ F := by
    have hodd := hp.odd_of_ne_two hp2
    obtain ⟨k, hk⟩ := hodd
    have heq : (k + 1) • (2 • Q') = Q' := by
      rw [← mul_nsmul, show 2 * (k + 1) = p + 1 by omega, add_nsmul, hQzero]
      simp
    rw [← heq]
    exact F.nsmul_mem htwice (k + 1)
  have hqN : q ∈ N := hqF
  have haction : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      σ • q = LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (K := AlgebraicClosure ℚ) ℚ (W'.map (Int.castRingHom ℚ)) p σ) • q := by
    intro σ hσ
    let f : V →ₗ[ZMod p] V := WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (K := AlgebraicClosure ℚ) ℚ (W'.map (Int.castRingHom ℚ)) p σ
    have habs : ∀ x : V, f x - x ∈ N := by
      intro x
      exact hFabs σ hσ x.1 (by
        have hx := x.2
        rwa [Submodule.mem_torsionBy_iff, natCast_zsmul] at hx)
    have hstable : N ≤ N.comap f := by
      intro x hx
      have hh := N.add_mem (habs x) hx
      simpa using hh
    have hquot : N.mapQ N f hstable = LinearMap.id := by
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := N.mkQ_surjective x
      change N.mkQ (f x) = N.mkQ x
      exact (Submodule.Quotient.eq N).mpr (habs x)
    obtain ⟨a, ha, _⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hNdim (f.restrict hstable)
    have hd : LinearMap.det f = a := by
      rw [LinearMap.det_eq_det_mul_det N f hstable, hquot, ha]
      simp [LinearMap.det_smul, hNdim]
    have hh := congrArg (fun g : N →ₗ[ZMod p] N => g ⟨q, hqN⟩) ha
    have hv := congrArg (fun x : N => (x : V)) hh
    change f q = LinearMap.det f • q
    rw [hd]
    exact hv
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have h := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have := Nat.le_of_dvd (by omega) h
    omega
  obtain ⟨σ, hσ, hd⟩ := WeierstrassCurve.det_galoisRep_surjOn_inertia
    W' p hΔ A hA (Units.mk0 2 htwo)
  have hact := haction σ hσ
  rw [hd] at hact
  change σ • q = (2 : ZMod p) • q at hact
  have hsigma : σ s = s ∨ σ s = -s := by
    have hpow : (σ s) ^ 2 = s ^ 2 := by rw [← map_pow, hs]; simp
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp hpow
  have hsignq : σ • q = q ∨ σ • q = -q := by
    rcases hsigma with hh | hh
    · exact Or.inl (Subtype.ext ((hsign σ).1 hh))
    · exact Or.inr (Subtype.ext ((hsign σ).2 hh))
  rcases hsignq with hh | hh
  · have hz : (1 - (2 : ZMod p)) • q = 0 := by
      rw [sub_smul, one_smul, ← hact, hh, sub_self]
    exact hqne ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  · have hz : (-1 - (2 : ZMod p)) • q = 0 := by
      rw [sub_smul, neg_one_smul, ← hact, hh, sub_self]
    have hthree : (-1 - (2 : ZMod p)) ≠ 0 := by
      intro hh
      have h3 : (3 : ZMod p) = 0 := by linear_combination -hh
      have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    exact hqne ((smul_eq_zero.mp hz).resolve_left hthree)

end PrimeLocal

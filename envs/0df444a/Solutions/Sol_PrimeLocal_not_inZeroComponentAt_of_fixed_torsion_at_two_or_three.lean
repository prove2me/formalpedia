-- Prove2me | solution 1 for PrimeLocal.not_inZeroComponentAt_of_fixed_torsion_at_two_or_three
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:29:31.377168+00:00
-- url     : https://prove2.me/submissions/c4a1969a-b7e9-47f0-a027-4c97941dd113

import Theorems.Thm_MazurP23_card_zeroComponent_prime_torsion
import Theorems.Thm_MazurP23_LinearMap_sub_det_smul_mem_of_fixed_line
import Theorems.Thm_MazurP23_inZeroComponentAt_smul_sub_or_add_of_mem_decompositionSubgroup
import Theorems.Thm_MazurP23_det_galoisRep_frobenius
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
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
/-- A rational prime-order point lies outside the identity component at multiplicative
reduction over two or three: Frobenius would otherwise force its residue prime to
be congruent to one or minus one modulo the torsion prime. -/
theorem _root_.solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p q : ℕ} (hq : q.Prime) (hq23 : q = 2 ∨ q = 3) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (hp : p.Prime) (hp7 : 7 ≤ p) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) (hQord : addOrderOf Q = p) : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ¬ W.InZeroComponentAt A Q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpq : p ≠ q := by rcases hq23 with rfl | rfl <;> omega
  have hp2 : p ≠ 2 := by omega
  have hq2 : 2 ≤ q := hq.two_le
  have hqsmall : q + 1 < p := by rcases hq23 with rfl | rfl <;> omega
  have hQtor : p • Q = 0 := by rw [← hQord]; exact addOrderOf_nsmul_eq_zero Q
  have hell : (W.map (Int.castRingHom ℚ)).IsElliptic := by
    refine (WeierstrassCurve.isElliptic_iff _).mpr (isUnit_iff_ne_zero.mpr ?_)
    rw [WeierstrassCurve.map_Δ, eq_intCast]
    exact_mod_cast hΔ
  have := hell
  let V := Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p
  have hcard : Nat.card V = p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (W.map (Int.castRingHom ℚ))
      (Nat.cast_ne_zero.mpr hp.ne_zero)
  have : Finite V := Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero 2 hp.ne_zero)
  have hdim : Module.finrank (ZMod p) V = 2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hcard, Nat.card_zmod] at hh
    exact (Nat.pow_right_injective hp.two_le hh).symm
  intro A hA hQin
  obtain ⟨M, hMiff, hMstable, _⟩ :=
    WeierstrassCurve.exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
      W hq hΔ hqΔ hqc₄ A hA hp
  have hMcard : Nat.card M = p := by
    have he : M ≃ {x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point //
        p • x = 0 ∧ W.InZeroComponentAt A x} :=
      { toFun := fun m => ⟨m.1.1, ⟨by
          have hh := m.1.2
          rwa [Submodule.mem_torsionBy_iff, natCast_zsmul] at hh,
          (hMiff m.1).mp m.2⟩⟩
        invFun := fun x => ⟨⟨x.1, by
          rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
          exact x.2.1⟩, (hMiff _).mpr x.2.2⟩
        left_inv := fun m => rfl
        right_inv := fun x => rfl }
    exact (Nat.card_congr he).trans
      (MazurP23.card_zeroComponent_prime_torsion W hq hΔ hqΔ hqc₄ A hA p hpq hcard)
  have hMdim : Module.finrank (ZMod p) M = 1 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod p) (V := M)
    rw [hMcard, Nat.card_zmod] at hh
    have hh : p ^ 1 = p ^ Module.finrank (ZMod p) M := (pow_one p).trans hh
    exact (Nat.pow_right_injective hp.two_le hh).symm
  let v : V := ⟨Q, by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact hQtor⟩
  have hvne : v ≠ 0 := by
    intro hz
    have hz' : Q = 0 := congrArg Subtype.val hz
    simp [hz'] at hQord
    omega
  have hvM : v ∈ M := (hMiff v).mpr hQin
  obtain ⟨σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hq A hA
  let f : V →ₗ[ZMod p] V := WeierstrassCurve.Affine.Point.galoisRepModuleEnd
    (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ
  have hstable : M ≤ M.comap f := by
    intro x hx
    exact hMstable σ hσ.mem_decompositionSubgroup x hx
  obtain ⟨a, ha, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hMdim (f.restrict hstable)
  have hfv : f v = v := Subtype.ext (hQfix σ)
  have hav : a • v = v := by
    have hh := congrArg (fun g : M →ₗ[ZMod p] M => g ⟨v, hvM⟩) ha
    have hh' := congrArg (fun x : M => (x : V)) hh
    exact hh'.symm.trans hfv
  have haone : a = 1 := by
    have hz : (a - 1) • v = 0 := by rw [sub_smul, one_smul, hav, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hvne)
  have hfix : ∀ x ∈ M, f x = x := by
    intro x hx
    have hh := congrArg (fun g : M →ₗ[ZMod p] M => g ⟨x, hx⟩) ha
    have hh' := congrArg (fun y : M => (y : V)) hh
    simpa [haone] using hh'
  have hdet : LinearMap.det f = (q : ZMod p) :=
    MazurP23.det_galoisRep_frobenius W p hΔ hq hpq.symm A hA hσ
  have hMtop : M ≠ ⊤ := by
    intro ht
    have hh : Module.finrank (ZMod p) M = 2 := by
      rw [ht]
      simpa using hdim
    omega
  have hex : ∃ x : V, x ∉ M := by
    by_contra hn
    push_neg at hn
    apply hMtop
    exact top_unique (fun x _ => hn x)
  obtain ⟨x, hxM⟩ := hex
  have hxout : ¬ W.InZeroComponentAt A x.1 := fun hx => hxM ((hMiff x).mpr hx)
  have hxdet : f x - (q : ZMod p) • x ∈ M := by
    rw [← hdet]
    exact MazurP23.LinearMap.sub_det_smul_mem_of_fixed_line hdim f M hMdim hfix x
  have hxtor : p • (x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 := by
    have hh := x.2
    rwa [Submodule.mem_torsionBy_iff, natCast_zsmul] at hh
  have hqnp : ¬ q ∣ p := fun hh => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hh).symm
  have hsign := MazurP23.inZeroComponentAt_smul_sub_or_add_of_mem_decompositionSubgroup
    W hq hΔ hqΔ hqc₄ A hA hσ.mem_decompositionSubgroup
    (hp.odd_of_ne_two hp2) hp.one_lt hqnp x.1 hxtor hxout
  have hcancel : ∀ c : ZMod p, c ≠ 0 → c • x ∈ M → False := by
    intro c hc hx
    apply hxM
    have hh := M.smul_mem c⁻¹ hx
    simpa [smul_smul, inv_mul_cancel₀ hc] using hh
  rcases hsign with hsub | hadd
  · have hh : f x - x ∈ M := (hMiff _).mpr hsub
    have hm : ((q : ZMod p) - 1) • x ∈ M := by
      convert M.sub_mem hh hxdet using 1
      simp only [sub_smul, one_smul]
      abel
    apply hcancel ((q : ZMod p) - 1) _ hm
    intro hz
    have hz' : ((q - 1 : ℕ) : ZMod p) = 0 := by
      simpa only [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one] using hz
    have hdvd := (ZMod.natCast_eq_zero_iff (q - 1) p).mp hz'
    have hle := Nat.le_of_dvd (by have := hq.two_le; omega : 0 < q - 1) hdvd
    omega
  · have hh : f x + x ∈ M := (hMiff _).mpr hadd
    have hm : ((q : ZMod p) + 1) • x ∈ M := by
      convert M.sub_mem hh hxdet using 1
      simp only [add_smul, one_smul]
      abel
    apply hcancel ((q : ZMod p) + 1) _ hm
    intro hz
    have hz' : ((q + 1 : ℕ) : ZMod p) = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hz
    have hdvd := (ZMod.natCast_eq_zero_iff (q + 1) p).mp hz'
    have hle := Nat.le_of_dvd (by omega : 0 < q + 1) hdvd
    omega

end PrimeLocal

-- Prove2me | solution 1 for PowerSeries.exists_monic_natDegree_eq_mul_of_map_eq_mul_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5a092c26-34f6-5470-8509-bf6a567b9e74

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_exists_monic_natDegree_eq_mul_of_map_eq_mul_X_pow

set_option autoImplicit false

open IsLocalRing PowerSeries

set_option maxHeartbeats 3200000 in
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    {k : Type} [Field k] (θ : A →+* k) (hθ : ∀ a : A, θ a = 0 ↔ a ∈ maximalIdeal A)
    (g : PowerSeries A) (N : ℕ) (u : PowerSeries k) (hu : IsUnit u)
    (hg : PowerSeries.map θ g = u * PowerSeries.X ^ N) :
    ∃ (P : Polynomial A) (U : PowerSeries A),
      P.Monic ∧ P.natDegree = N ∧ (∀ i : ℕ, i < N → P.coeff i ∈ maximalIdeal A) ∧
      IsUnit U ∧ g = (P : PowerSeries A) * U := by
  classical
  set m : Ideal A := maximalIdeal A with hm

  have hθm : ∀ a ∈ m, θ a = 0 := fun a ha => (hθ a).mpr ha
  let θbar : A ⧸ m →+* k := Ideal.Quotient.lift m θ hθm
  have hθbar : ∀ a : A, θbar (Ideal.Quotient.mk m a) = θ a := fun a => rfl
  have hθbar_inj : Function.Injective θbar := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hθbar] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hθ a).mp hx)
  have hcomp : θbar.comp (Ideal.Quotient.mk m) = θ := RingHom.ext hθbar

  set gq : PowerSeries (A ⧸ m) := PowerSeries.map (Ideal.Quotient.mk m) g with hgq
  have hmapmap : PowerSeries.map θbar gq = u * PowerSeries.X ^ N := by
    rw [hgq, ← hg, ← hcomp, PowerSeries.map_comp]; rfl
  have hcoeff : ∀ i : ℕ, θbar (PowerSeries.coeff i gq) = if N ≤ i then PowerSeries.coeff (i - N) u else 0 := by
    intro i
    rw [← PowerSeries.coeff_map, hmapmap, PowerSeries.coeff_mul_X_pow']
  have hu0 : PowerSeries.coeff 0 u ≠ 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (PowerSeries.isUnit_iff_constantCoeff.mp hu).ne_zero
  have hgq_order : gq.order = N := by
    rw [PowerSeries.order_eq_nat]
    constructor
    · intro h0
      have := hcoeff N
      rw [h0, map_zero, if_pos le_rfl, Nat.sub_self] at this
      exact hu0 this.symm
    · intro i hi
      apply hθbar_inj
      rw [hcoeff i, if_neg (not_le.mpr hi), map_zero]
  have hgq0 : gq ≠ 0 := by
    intro h
    have := hcoeff N
    rw [h, map_zero, map_zero, if_pos le_rfl, Nat.sub_self] at this
    exact hu0 this.symm

  have hgres : g.map (IsLocalRing.residue A) ≠ 0 := by
    have : g.map (IsLocalRing.residue A) = gq := by rw [hgq]; rfl
    rw [this]; exact hgq0
  obtain ⟨f, h, H⟩ := PowerSeries.exists_isWeierstrassFactorization hgres
  have hmtop : maximalIdeal A ≠ ⊤ := Ideal.IsMaximal.ne_top (IsLocalRing.maximalIdeal.isMaximal A)
  have hdeg : f.natDegree = N := by
    have h1 := H.natDegree_eq_toNat_order_map_of_ne_top hmtop
    have h2 : (g.map (Ideal.Quotient.mk (maximalIdeal A))).order = N := by rw [← hm, ← hgq]; exact hgq_order
    rw [h2] at h1
    simpa using h1
  refine ⟨f, h, H.isDistinguishedAt.monic, hdeg, ?_, H.isUnit, H.eq_mul⟩
  intro i hi
  exact H.isDistinguishedAt.mem (by rw [hdeg]; exact hi)

end S_PowerSeries_exists_monic_natDegree_eq_mul_of_map_eq_mul_X_pow
end P2MW
export P2MW.S_PowerSeries_exists_monic_natDegree_eq_mul_of_map_eq_mul_X_pow (solution)

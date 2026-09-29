-- Prove2me | solution 1 for PDivisibleGroup.cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8716a0dd-9798-50fd-89d6-719b7259c67e

import Mathlib
import Definitions.Def_PDivisibleGroup_CompletedPoints
import Theorems.Thm_PDivisibleGroup_Hopf_nsmulAlgHom_sub_nsmul_mem_augIdeal_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero

set_option autoImplicit false

open PDivisibleGroup Coalgebra

namespace PDivFilt

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
variable (S : Type) [CommRing S] [Algebra R S]

abbrev J (i : ℕ) : Ideal (S ⧸ Ideal.span {(p : S) ^ (i + 1)}) :=
  Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : S) ^ (i + 1)}) ((p : S) ^ i)}

theorem sub_mem_J_of_reduceModPow_eq (i : ℕ) {x y : S ⧸ Ideal.span {(p : S) ^ (i + 1)}}
    (hxy : reduceModPow R p S i x = reduceModPow R p S i y) : x - y ∈ J (p := p) S i := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [reduceModPow_mk, reduceModPow_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hxy
  obtain ⟨c, hc⟩ := hxy
  rw [← map_sub, ← hc, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem p_nsmul_eq_zero_of_mem_J (i : ℕ) {x : S ⧸ Ideal.span {(p : S) ^ (i + 1)}} (hx : x ∈ J (p := p) S i) :
    p • x = 0 := by
  rw [Ideal.mem_span_singleton'] at hx
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk _) p, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.mem_span_singleton'.2 ⟨b, ?_⟩
  ring

theorem J_sq_eq_bot {i : ℕ} (hi : 1 ≤ i) : J (p := p) S i * J (p := p) S i = ⊥ := by
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_bot, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, ← pow_add]
  exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (p : S) (by omega)) (Ideal.mem_span_singleton_self _)

variable {S}

theorem pow_p_eq_one_of_forall_sub_mem_J {i : ℕ} (hi : 1 ≤ i) {w : ℕ}
    (f : G.Point (S ⧸ Ideal.span {(p : S) ^ (i + 1)}) w)
    (hf : ∀ a : G.level w, Point.toAlgHom f a - algebraMap R _ (counit (R := R) a) ∈ J (p := p) S i) :
    f ^ p = 1 := by

  have hI : ∀ a ∈ Hopf.augIdeal R (G.level w), Point.toAlgHom f a ∈ J (p := p) S i := by
    intro a ha
    have h1 := hf a
    rwa [(Hopf.mem_augIdeal_iff R _ a).1 ha, map_zero, sub_zero] at h1
  have hmapI : (Hopf.augIdeal R (G.level w)).map (Point.toAlgHom f) ≤ J (p := p) S i := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun a ha => hI a ha

  have hI2 : ∀ q ∈ Hopf.augIdeal R (G.level w) ^ 2, Point.toAlgHom f q = 0 := by
    intro q hq
    have h1 : Point.toAlgHom f q ∈ ((Hopf.augIdeal R (G.level w)) ^ 2).map (Point.toAlgHom f) :=
      Ideal.mem_map_of_mem _ hq
    rw [pow_two, Ideal.map_mul] at h1
    have h2 : (Hopf.augIdeal R (G.level w)).map (Point.toAlgHom f) * (Hopf.augIdeal R (G.level w)).map (Point.toAlgHom f)
        ≤ J (p := p) S i * J (p := p) S i := Ideal.mul_mono hmapI hmapI
    have h3 := h2 h1
    rw [J_sq_eq_bot S hi] at h3
    exact h3
  refine Point.ext fun a => ?_
  rw [Point.toAlgHom_pow, AlgHom.comp_apply, Point.one_apply]

  set a₀ := a - algebraMap R (G.level w) (counit (R := R) a) with ha₀
  have ha₀I : a₀ ∈ Hopf.augIdeal R (G.level w) := Hopf.sub_algebraMap_counit_mem_augIdeal R _ a
  have hdec : a = algebraMap R (G.level w) (counit (R := R) a) + a₀ := by rw [ha₀]; abel

  set q := Hopf.nsmulAlgHom R (G.level w) p a₀ - p • a₀ with hq
  have hqI2 : q ∈ Hopf.augIdeal R (G.level w) ^ 2 := Hopf.nsmulAlgHom_sub_nsmul_mem_augIdeal_sq p ha₀I
  have hns : Hopf.nsmulAlgHom R (G.level w) p a₀ = p • a₀ + q := by rw [hq]; abel
  conv_lhs => rw [hdec]
  rw [map_add, Hopf.nsmulAlgHom_algebraMap, hns, map_add, map_add, AlgHom.commutes, map_nsmul,
    hI2 q hqI2, p_nsmul_eq_zero_of_mem_J S i (hI a₀ ha₀I), add_zero, add_zero]

end PDivFilt

open PDivFilt in

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (S : Type) [CommRing S] [Algebra R S] (g : G.CPoints S) {i : ℕ} (hi : 1 ≤ i)
    (hg : G.cpointsProj S i g = 0) :
    G.cpointsProj S (i + 1) (p • g) = 0 := by
  obtain ⟨w, f, hf⟩ := Points.exists_mkAdd G (G.cpointsProj S (i + 1) g)

  have hred : G.pointMap (reduceModPow R p S i) w f = 1 := by
    apply G.pointsMkAdd_injective w
    change G.pointsMkAdd _ w (Additive.ofMul (G.pointMap (reduceModPow R p S i) w f)) = G.pointsMkAdd _ w (Additive.ofMul 1)
    rw [← pointsMap_pointsMkAdd, hf, pointsMap_reduceModPow_cpointsProj_succ, hg, ofMul_one, map_zero]
  have hfJ : ∀ a : G.level w, Point.toAlgHom f a - algebraMap R _ (counit (R := R) a) ∈ J (p := p) S i := by
    intro a
    refine sub_mem_J_of_reduceModPow_eq (R := R) S i ?_
    have h1 := DFunLike.congr_fun (congrArg Point.toAlgHom hred) a
    rw [toAlgHom_pointMap, AlgHom.comp_apply, Point.one_apply] at h1
    rw [h1, AlgHom.commutes]
  rw [map_nsmul, ← hf, ← map_nsmul, ← ofMul_pow, pow_p_eq_one_of_forall_sub_mem_J G hi f hfJ, ofMul_one, map_zero]

end S_PDivisibleGroup_cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero
end P2MW
export P2MW.S_PDivisibleGroup_cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero (solution)

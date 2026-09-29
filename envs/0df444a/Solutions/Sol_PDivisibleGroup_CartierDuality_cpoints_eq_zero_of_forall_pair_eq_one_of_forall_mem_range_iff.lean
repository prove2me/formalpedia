-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9c382e20-02ad-505e-870d-d6788a08e35f

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_CompletedPoints
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_PDivisibleGroup_cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero
import Theorems.Thm_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
import Theorems.Thm_PDivisibleGroup_existsUnique_cpointsMap_ofId_eq_of_forall_smul_eq_of_forall_mem_range_iff
import Theorems.Thm_PDivisibleGroup_Hopf_nsmulAlgHom_sub_nsmul_mem_augIdeal_sq
import Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff
p2m_attr_erase "instance" "PrimaryTorsion.instSMul PrimaryTorsion.instModule PadicComplex.smulCommClass_gal_padic PadicComplex.smulCommClass_padic_gal PadicComplex.uniformContinuousConstSMul_gal PadicComplex.mulSemiringAction"
p2m_attr_erase "simp" "PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul PadicComplex.galAlgHom_apply PadicComplex.smul_algebraMap PadicComplex.norm_smul_eq PadicComplex.nnnorm_smul_eq PadicComplex.smul_coe"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open PDivisibleGroup Filter Topology

namespace PDivStep4R

variable (p : ℕ) [Fact p.Prime]

abbrev O (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] : Subalgebra R (PadicAlgCl p) :=
  integralClosure R (PadicAlgCl p)

abbrev K : Type := PadicAlgCl p

abbrev Oq (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] (i : ℕ) : Type := O p R ⧸ Ideal.span {(p : O p R) ^ i}

abbrev Gal : Type := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p

def Restricts {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)] (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R) : Prop :=
  ∀ a : O p R, ((σ' a : O p R) : PadicAlgCl p) = σ a

def ι (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] : O p R →+* ℂ_[p] :=
  (algebraMap (PadicAlgCl p) ℂ_[p]).comp (O p R).val.toRingHom

abbrev OK (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] : Prop := ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1

abbrev BaseHyp (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] : Prop :=
  ∀ x : PadicAlgCl p, x ∈ Set.range (algebraMap R (PadicAlgCl p)) ↔ x ∈ K ∧ ‖x‖ ≤ 1
section Base

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]

variable {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable (hR : BaseHyp p E R) (hinj : Function.Injective (algebraMap R (PadicAlgCl p)))

include hR in
theorem algebraMap_mem_K (r : R) : algebraMap R (PadicAlgCl p) r ∈ E := ((hR _).1 ⟨r, rfl⟩).1

include hR in
theorem norm_algebraMap_le_one (r : R) : ‖algebraMap R (PadicAlgCl p) r‖ ≤ 1 := ((hR _).1 ⟨r, rfl⟩).2

include hR in
theorem exists_algebraMap_eq {x : PadicAlgCl p} (hxK : x ∈ E) (hxn : ‖x‖ ≤ 1) :
    ∃ r : R, algebraMap R (PadicAlgCl p) r = x := (hR x).2 ⟨hxK, hxn⟩

theorem algebraMap_padicInt_mem_K (a : ℤ_[p]) : algebraMap ℤ_[p] (PadicAlgCl p) a ∈ E := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p)]
  exact E.algebraMap_mem _

theorem norm_algebraMap_padicInt_le_one (a : ℤ_[p]) : ‖algebraMap ℤ_[p] (PadicAlgCl p) a‖ ≤ 1 := by
  rw [PadicAlgCl.ringOfIntegers.norm_algebraMap_padicInt]
  exact PadicInt.norm_le_one a

def eR : R ≃+* (algebraMap R (PadicAlgCl p)).range :=
  RingEquiv.ofBijective (algebraMap R (PadicAlgCl p)).rangeRestrict
    ⟨fun a b hab => hinj (by
        have := congrArg (fun z : (algebraMap R (PadicAlgCl p)).range => (z : PadicAlgCl p)) hab
        simpa only [RingHom.coe_rangeRestrict] using this),
      RingHom.rangeRestrict_surjective _⟩

theorem coe_eR (r : R) : ((eR p hinj r : (algebraMap R (PadicAlgCl p)).range) : PadicAlgCl p) =
    algebraMap R (PadicAlgCl p) r := by
  rw [eR, RingEquiv.ofBijective_apply, RingHom.coe_rangeRestrict]

theorem algebraMap_eR_symm (y : (algebraMap R (PadicAlgCl p)).range) :
    algebraMap R (PadicAlgCl p) ((eR p hinj).symm y) = y := by
  rw [← coe_eR p hinj, RingEquiv.apply_symm_apply]

def φZ : ℤ_[p] →+* R :=
  (eR p hinj).symm.toRingHom.comp
    ((algebraMap ℤ_[p] (PadicAlgCl p)).codRestrict (algebraMap R (PadicAlgCl p)).range fun a =>
      RingHom.mem_range.mpr ((hR _).2 ⟨algebraMap_padicInt_mem_K p a, norm_algebraMap_padicInt_le_one p a⟩))

theorem algebraMap_φZ (a : ℤ_[p]) :
    algebraMap R (PadicAlgCl p) (φZ p hR hinj a) = algebraMap ℤ_[p] (PadicAlgCl p) a := by
  rw [φZ, RingHom.comp_apply]
  exact algebraMap_eR_symm p hinj _

include hR hinj in

theorem mem_O_of_norm_le_one {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) : x ∈ O p R := by
  have hint : IsIntegral ℤ_[p] x := (PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p x).mpr hx
  have hcomp : (algebraMap R (PadicAlgCl p)).comp (φZ p hR hinj) =
      (RingHom.id (PadicAlgCl p)).comp (algebraMap ℤ_[p] (PadicAlgCl p)) :=
    RingHom.ext fun a => by rw [RingHom.comp_apply, algebraMap_φZ]; rfl
  exact hint.map_of_comp_eq (φZ p hR hinj) (RingHom.id (PadicAlgCl p)) hcomp

include hR in

theorem norm_coe_le_one (c : O p R) : ‖(c : PadicAlgCl p)‖ ≤ 1 := by
  obtain ⟨f, hf, hfx⟩ := c.2
  set x : PadicAlgCl p := (c : PadicAlgCl p)
  by_contra hlt
  push Not at hlt
  set n := f.natDegree with hn
  have heval : x ^ n = -∑ i ∈ Finset.range n, algebraMap R (PadicAlgCl p) (f.coeff i) * x ^ i := by
    have h1 : Polynomial.eval₂ (algebraMap R (PadicAlgCl p)) x f = 0 := hfx
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at h1
    have hlead : f.coeff n = 1 := hf
    rw [hlead, map_one, one_mul] at h1
    exact eq_neg_of_add_eq_zero_right h1
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · rw [hn0, Finset.range_zero, Finset.sum_empty, neg_zero, pow_zero] at heval
    exact one_ne_zero heval
  have hne : (Finset.range n).Nonempty := ⟨0, Finset.mem_range.2 hnpos⟩
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
    (fun i => algebraMap R (PadicAlgCl p) (f.coeff i) * x ^ i)
  rw [Finset.mem_range] at hi
  have hterm : ‖algebraMap R (PadicAlgCl p) (f.coeff i) * x ^ i‖ < ‖x‖ ^ n := by
    rw [norm_mul, norm_pow]
    calc ‖algebraMap R (PadicAlgCl p) (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
          gcongr; exact norm_algebraMap_le_one p hR _
      _ = ‖x‖ ^ i := one_mul _
      _ < ‖x‖ ^ n := pow_lt_pow_right₀ hlt hi
  have hxn : ‖x‖ ^ n = ‖∑ i ∈ Finset.range n, algebraMap R (PadicAlgCl p) (f.coeff i) * x ^ i‖ := by
    rw [← norm_pow, heval, norm_neg]
  rw [hxn] at hterm
  exact absurd (hle.trans_lt hterm) (lt_irrefl _)

include hR hinj in

theorem oK : OK p R := fun x =>
  ⟨fun hx => norm_coe_le_one p hR ⟨x, hx⟩, fun hx => mem_O_of_norm_le_one p hR hinj hx⟩

theorem norm_coe_p : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  exact (PadicAlgCl.norm_extends (p := p) (p : ℚ_[p])).trans (Padic.norm_p (p := p))

include hR hinj in

theorem mem_span_of_algebraMap_mem (k : ℕ) (r : R)
    (hr : algebraMap R (O p R) r ∈ Ideal.span {(p : O p R) ^ k}) : r ∈ Ideal.span {(p : R) ^ k} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hr
  have hp0 : (p : PadicAlgCl p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpk0 : (p : PadicAlgCl p) ^ k ≠ 0 := pow_ne_zero _ hp0
  have hcK : algebraMap R (PadicAlgCl p) r = (c : PadicAlgCl p) * (p : PadicAlgCl p) ^ k := by
    have := congrArg (fun z : O p R => (z : PadicAlgCl p)) hc
    simp only [Subalgebra.coe_mul, SubmonoidClass.coe_pow] at this
    exact this.symm

  have hpK : (p : PadicAlgCl p) ∈ E := by exact_mod_cast E.natCast_mem p
  have hcmem : (c : PadicAlgCl p) ∈ E := by
    have h1 : (c : PadicAlgCl p) = algebraMap R (PadicAlgCl p) r / (p : PadicAlgCl p) ^ k := by
      rw [hcK, mul_div_cancel_right₀ _ hpk0]
    rw [h1]
    exact div_mem (algebraMap_mem_K p hR r) (pow_mem hpK k)
  obtain ⟨s, hs⟩ := exists_algebraMap_eq p hR hcmem (norm_coe_le_one p hR c)
  refine Ideal.mem_span_singleton'.2 ⟨s, hinj ?_⟩
  rw [map_mul, map_pow, map_natCast, hs, ← hcK]

include hR hinj in

theorem isNilpotent_mk_of_isNilpotent_mk (r : R)
    (hr : IsNilpotent (Ideal.Quotient.mk (Ideal.span {(p : O p R) ^ 1}) (algebraMap R (O p R) r))) :
    IsNilpotent (Ideal.Quotient.mk (Ideal.span {(p : R) ^ 1}) r) := by
  obtain ⟨n, hn⟩ := hr
  refine ⟨n, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn ⊢
  exact mem_span_of_algebraMap_mem p hR hinj 1 (r ^ n) (by rwa [map_pow])

abbrev OKint (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Type := PadicAlgCl.ringOfIntegers p K

include hR hinj in

theorem exists_uniformiser [FiniteDimensional ℚ_[p] E] :
    ∃ (ϖ : R) (e : ℕ), ϖ ^ e ∈ Ideal.span {(p : R)} ∧
      ∀ x : R, IsNilpotent (Ideal.Quotient.mk (Ideal.span {(p : R) ^ 1}) x) → x ∈ Ideal.span {ϖ} := by
  obtain ⟨-, hDVR, -⟩ := PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p E

  have hmem : ∀ r : R, algebraMap R (PadicAlgCl p) r ∈ PadicAlgCl.ringOfIntegers p E := fun r =>
    (PadicAlgCl.mem_ringOfIntegers_iff p E _).2
      ⟨(PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p _).2 (norm_algebraMap_le_one p hR r), algebraMap_mem_K p hR r⟩
  let f : R →+* OKint p E := (algebraMap R (PadicAlgCl p)).codRestrict (PadicAlgCl.ringOfIntegers p E) hmem
  have hf : ∀ r, ((f r : OKint p E) : PadicAlgCl p) = algebraMap R (PadicAlgCl p) r := fun r => rfl
  have hfinj : Function.Injective f := fun a b hab => hinj (by rw [← hf, ← hf, hab])
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨r, hr⟩ := exists_algebraMap_eq p hR (PadicAlgCl.ringOfIntegers.coe_mem y)
      (PadicAlgCl.ringOfIntegers.norm_le_one_of_isIntegral p (PadicAlgCl.ringOfIntegers.isIntegral_coe y))
    exact ⟨r, Subtype.ext (by rw [hf, hr])⟩
  let e : R ≃+* OKint p E := RingEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have he : ∀ r, e r = f r := fun r => rfl

  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible (OKint p E)
  have hp0 : (p : OKint p E) ≠ 0 := by
    intro h0
    have : ((p : OKint p E) : PadicAlgCl p) = 0 := by rw [h0]; rfl
    rw [show ((p : OKint p E) : PadicAlgCl p) = (p : PadicAlgCl p) from rfl] at this
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ₀

  refine ⟨e.symm ϖ₀, n, ?_, ?_⟩
  · refine Ideal.mem_span_singleton'.2 ⟨e.symm (u : OKint p E), ?_⟩
    apply e.injective
    rw [map_mul, map_pow, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, map_natCast, mul_comm]
    exact hu
  · intro x hx
    obtain ⟨m, hm⟩ := hx
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton] at hm

    have h1 : (p : OKint p E) ∣ e x ^ m := by
      obtain ⟨c, hc⟩ := hm
      exact ⟨e c, by rw [← map_pow, hc, map_mul, map_natCast]⟩
    have hnpos : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hu
      exact PadicAlgCl.ringOfIntegers.not_isUnit_natCast p E (IsUnit.of_mul_eq_one _ hu)
    have h2 : ϖ₀ ∣ (p : OKint p E) := by
      have h3 : ϖ₀ ∣ (p : OKint p E) * u := by rw [hu]; exact dvd_pow_self ϖ₀ hnpos
      exact (Units.dvd_mul_right).1 h3
    have hprime : Prime ϖ₀ := hϖ₀.prime
    have h3 : ϖ₀ ∣ e x := hprime.dvd_of_dvd_pow (h2.trans h1)
    obtain ⟨c, hc⟩ := h3
    refine Ideal.mem_span_singleton'.2 ⟨e.symm c, ?_⟩
    apply e.injective
    rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, mul_comm]
    exact hc.symm

end Base

section Unipotent

variable {R : Type} [CommRing R] {h : ℕ} (G : PDivisibleGroup R p h)
variable {L : Type} [CommRing L] [Algebra R L]

open Coalgebra in

theorem sub_mem_sq_of_forall_sub_mem (hpL : (p : L) = 0) {w : ℕ} (f : G.Point L w) (N : Ideal L)
    (hf : ∀ a : G.level w, Point.toAlgHom f a - algebraMap R L (counit (R := R) a) ∈ N) (a : G.level w) :
    Point.toAlgHom (f ^ p) a - algebraMap R L (counit (R := R) a) ∈ N ^ 2 := by

  have hI : ∀ a ∈ Hopf.augIdeal R (G.level w), Point.toAlgHom f a ∈ N := by
    intro a ha
    have h1 := hf a
    rwa [(Hopf.mem_augIdeal_iff R _ a).1 ha, map_zero, sub_zero] at h1
  have hmapI : (Hopf.augIdeal R (G.level w)).map (Point.toAlgHom f) ≤ N := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun a ha => hI a ha

  have hI2 : ∀ q ∈ Hopf.augIdeal R (G.level w) ^ 2, Point.toAlgHom f q ∈ N ^ 2 := by
    intro q hq
    have h1 : Point.toAlgHom f q ∈ ((Hopf.augIdeal R (G.level w)) ^ 2).map (Point.toAlgHom f) :=
      Ideal.mem_map_of_mem _ hq
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hmapI 2 h1
  rw [Point.toAlgHom_pow, AlgHom.comp_apply]

  set a₀ := a - algebraMap R (G.level w) (counit (R := R) a) with ha₀
  have ha₀I : a₀ ∈ Hopf.augIdeal R (G.level w) := Hopf.sub_algebraMap_counit_mem_augIdeal R _ a
  have hdec : a = algebraMap R (G.level w) (counit (R := R) a) + a₀ := by rw [ha₀]; abel

  set q := Hopf.nsmulAlgHom R (G.level w) p a₀ - p • a₀ with hq
  have hqI2 : q ∈ Hopf.augIdeal R (G.level w) ^ 2 := Hopf.nsmulAlgHom_sub_nsmul_mem_augIdeal_sq p ha₀I
  have hns : Hopf.nsmulAlgHom R (G.level w) p a₀ = p • a₀ + q := by rw [hq]; abel
  have hp0 : (p • Point.toAlgHom f a₀ : L) = 0 := by rw [nsmul_eq_mul, hpL, zero_mul]
  have key : Point.toAlgHom f (Hopf.nsmulAlgHom R (G.level w) p a) =
      algebraMap R L (counit (R := R) a) + Point.toAlgHom f q := by
    conv_lhs => rw [hdec]
    rw [map_add, Hopf.nsmulAlgHom_algebraMap, hns, map_add, map_add, AlgHom.commutes, map_nsmul, hp0, zero_add]
  rw [key, add_sub_cancel_left]
  exact hI2 q hqI2

open Coalgebra in

theorem sub_mem_pow_of_forall_sub_mem (hpL : (p : L) = 0) {w : ℕ} (N : Ideal L) (k : ℕ) :
    ∀ (f : G.Point L w), (∀ a : G.level w, Point.toAlgHom f a - algebraMap R L (counit (R := R) a) ∈ N) →
      ∀ a : G.level w, Point.toAlgHom (f ^ p ^ k) a - algebraMap R L (counit (R := R) a) ∈ N ^ 2 ^ k := by
  induction k with
  | zero => intro f hf a; rw [pow_zero, pow_one, pow_zero, pow_one]; exact hf a
  | succ k ih =>
      intro f hf a
      rw [pow_succ p k, pow_mul f, pow_succ 2 k, pow_mul N]
      exact sub_mem_sq_of_forall_sub_mem p G hpL (f ^ p ^ k) (N ^ 2 ^ k) (ih f hf) a

open Coalgebra in

theorem cpointsProj_one_pow_nsmul_eq_zero (ϖ : R) (e : ℕ) (hϖ : ϖ ^ e ∈ Ideal.span {(p : R)})
    (hnil : ∀ x : R, IsNilpotent (Ideal.Quotient.mk (Ideal.span {(p : R) ^ 1}) x) → x ∈ Ideal.span {ϖ})
    (g : G.CPoints R)
    (hg : ∀ (w : ℕ) (f : G.Point (R ⧸ Ideal.span {(p : R) ^ 1}) w),
      G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj R 1 g →
      ∀ a : G.level w, IsNilpotent (Point.toAlgHom f a - algebraMap R _ (counit (R := R) a))) :
    G.cpointsProj R 1 (p ^ e • g) = 0 := by
  obtain ⟨w, f, hf⟩ := Points.exists_mkAdd G (G.cpointsProj R 1 g)
  set L := R ⧸ Ideal.span {(p : R) ^ 1}
  have hpL : (p : L) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : R) ^ 1})), Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact Ideal.mem_span_singleton_self _

  set N : Ideal L := Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : R) ^ 1}) ϖ} with hN
  have hNe : N ^ e = ⊥ := by
    rw [hN, Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact hϖ

  have hfN : ∀ a : G.level w, Point.toAlgHom f a - algebraMap R L (counit (R := R) a) ∈ N := by
    intro a
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (Point.toAlgHom f a - algebraMap R L (counit (R := R) a))
    have hxnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {(p : R) ^ 1}) x) := by rw [hx]; exact hg w f hf a
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hnil x hxnil)
    rw [← hx, ← hc, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

  have hle : N ^ 2 ^ e ≤ N ^ e := Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le
  have hone : f ^ p ^ e = 1 := by
    refine Point.ext fun a => ?_
    have h1 := hle (sub_mem_pow_of_forall_sub_mem p G hpL N e f hfN a)
    rw [hNe, Ideal.mem_bot, sub_eq_zero] at h1
    rw [h1, Point.one_apply]
  rw [map_nsmul, ← hf, ← map_nsmul, ← ofMul_pow, hone, ofMul_one, map_zero]

theorem cpointsProj_succ_pow_nsmul (g : G.CPoints R) (hg : G.cpointsProj R 1 g = 0) (m : ℕ) :
    G.cpointsProj R (m + 1) (p ^ m • g) = 0 := by
  induction m with
  | zero => rwa [pow_zero, one_smul]
  | succ m ih =>
      have e : p ^ (m + 1) • g = p • (p ^ m • g) := by rw [pow_succ, mul_nsmul]
      rw [e]
      exact G.cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero R (p ^ m • g) (Nat.le_add_left 1 m) ih

end Unipotent

section Main

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
variable (hR : BaseHyp p E R) (hinj : Function.Injective (algebraMap R (PadicAlgCl p)))
variable {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')

def KerP (Y : G.CPoints (O p R)) : Prop :=
  ∀ (y : TateModule p (G'.Points (PadicAlgCl p))) (i w : ℕ), i ≤ w →
    ∀ (f : G.Point (Oq p R i) w),
      G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (O p R) i Y →
    ∀ (ψ : G'.Point (O p R) w),
      G'.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul (G'.pointMap (O p R).val w ψ)) =
        (y : ℕ → G'.Points (PadicAlgCl p)) w →
      D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ i})) w ψ) = 1

open Coalgebra in

def G1P (X : G.CPoints (O p R)) : Prop :=
  ∀ (w : ℕ) (f : G.Point (Oq p R 1) w),
    G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (O p R) 1 X →
    ∀ a : G.level w, IsNilpotent (Point.toAlgHom f a - algebraMap R _ (counit (R := R) a))

def InvP (X : G.CPoints (O p R)) : Prop :=
  ∀ (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R), Restricts p σ σ' → σ' • X = X

theorem invP_cpointsMap (g : G.CPoints R) : InvP p (G.cpointsMap (Algebra.ofId R (O p R)) g) := by
  intro σ σ' _
  have h1 : σ'.toAlgHom.comp (Algebra.ofId R (O p R)) = Algebra.ofId R (O p R) :=
    AlgHom.ext fun r => σ'.toAlgHom.commutes r
  have e1 := DFunLike.congr_fun (G.cpointsMap_comp (Algebra.ofId R (O p R)) σ'.toAlgHom) g
  rw [h1, AddMonoidHom.comp_apply] at e1
  rw [CPoints.smul_def]
  exact e1.symm

include hR hinj in

theorem cpointsMap_ofId_injective : Function.Injective (G.cpointsMap (Algebra.ofId R (O p R))) := by
  intro a b hab
  obtain ⟨x₀, -, huniq⟩ := G.existsUnique_cpointsMap_ofId_eq_of_forall_smul_eq_of_forall_mem_range_iff p E hR hinj
    (G.cpointsMap (Algebra.ofId R (O p R)) a) (fun σ σ' hσ => invP_cpointsMap p a σ σ' hσ)
  rw [huniq a rfl, huniq b hab.symm]

abbrev ιq (i : ℕ) : (R ⧸ Ideal.span {(p : R) ^ i}) →ₐ[R] Oq p R i :=
  mapModPow R p R (Algebra.ofId R (O p R)) i

open Coalgebra in

theorem g1P_cpointsMap (g : G.CPoints R) (hg : G.cpointsProj R 1 g = 0) :
    G1P p (G.cpointsMap (Algebra.ofId R (O p R)) g) := by
  intro w f hf a
  rw [cpointsProj_cpointsMap, hg, map_zero] at hf
  have h0 : G.pointsMkAdd (Oq p R 1) w (Additive.ofMul f) = G.pointsMkAdd (Oq p R 1) w (Additive.ofMul 1) := by
    rw [hf, ofMul_one, map_zero]
  have h1 : f = 1 := G.pointsMkAdd_injective w h0
  rw [h1, Point.one_apply, sub_self]
  exact IsNilpotent.zero

include hR hinj in
open Coalgebra in

theorem isNilpotent_of_g1P_cpointsMap (g : G.CPoints R) (hg : G1P p (G.cpointsMap (Algebra.ofId R (O p R)) g))
    (w : ℕ) (f : G.Point (R ⧸ Ideal.span {(p : R) ^ 1}) w)
    (hf : G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj R 1 g) (a : G.level w) :
    IsNilpotent (Point.toAlgHom f a - algebraMap R _ (counit (R := R) a)) := by

  have hf' : G.pointsMkAdd _ w (Additive.ofMul (G.pointMap (ιq p 1) w f)) =
      G.cpointsProj (O p R) 1 (G.cpointsMap (Algebra.ofId R (O p R)) g) := by
    rw [← pointsMap_pointsMkAdd, hf, cpointsProj_cpointsMap]
  have h1 := hg w _ hf' a
  rw [toAlgHom_pointMap, AlgHom.comp_apply, ← (ιq p 1).commutes, ← map_sub] at h1

  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (Point.toAlgHom f a - algebraMap R _ (counit (R := R) a))
  rw [← hx] at h1 ⊢
  refine isNilpotent_mk_of_isNilpotent_mk p hR hinj x ?_
  have h2 : ιq p 1 (Ideal.Quotient.mk (Ideal.span {(p : R) ^ 1}) x) =
      Ideal.Quotient.mk (Ideal.span {(p : O p R) ^ 1}) (algebraMap R (O p R) x) := mapModPow_mk R p R _ 1 x
  rw [← h2]
  exact h1

def Adm (X : G.CPoints (O p R)) : Prop := KerP p D X ∧ G1P p X ∧ InvP p X

variable (hO : OK p R)

include hO in

theorem step2 :
    (∀ Y, KerP p D Y → ∀ n : ℕ, KerP p D (n • Y)) ∧
    (∀ Y, KerP p D Y → ∀ k : ℕ, p ^ k • Y = 0 → Y = 0) ∧
    (∀ X, KerP p D X → G1P p X → InvP p X →
      ∃ X₁, KerP p D X₁ ∧ G1P p X₁ ∧ InvP p X₁ ∧ p • X₁ = X) := by
  have H := D.nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff p hO
    {Y | KerP p D Y} {X | G1P p X} {X | InvP p X} (fun _ => Iff.rfl) (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  refine ⟨fun Y hY n => H.1 Y hY n, fun Y hY k hk => H.2.1 Y hY k hk, fun X h1 h2 h3 => ?_⟩
  obtain ⟨X₁, hX₁, h4, h5, h6⟩ := H.2.2 X h1 h2 h3
  exact ⟨X₁, hX₁, h4, h5, h6⟩

include hO in

theorem root_step (X : G.CPoints (O p R)) (hX : Adm p D X) : ∃ X₁ : G.CPoints (O p R), Adm p D X₁ ∧ p • X₁ = X := by
  obtain ⟨X₁, h1, h2, h3, h4⟩ := (step2 p D hO).2.2 X hX.1 hX.2.1 hX.2.2
  exact ⟨X₁, ⟨h1, h2, h3⟩, h4⟩

def rootSeq (X : G.CPoints (O p R)) (hX : Adm p D X) : ℕ → {Y : G.CPoints (O p R) // Adm p D Y}
  | 0 => ⟨X, hX⟩
  | m + 1 =>
      ⟨(root_step p D hO (rootSeq X hX m).1 (rootSeq X hX m).2).choose,
        (root_step p D hO (rootSeq X hX m).1 (rootSeq X hX m).2).choose_spec.1⟩

theorem p_nsmul_rootSeq_succ (X : G.CPoints (O p R)) (hX : Adm p D X) (m : ℕ) :
    p • (rootSeq p D hO X hX (m + 1)).1 = (rootSeq p D hO X hX m).1 :=
  (root_step p D hO (rootSeq p D hO X hX m).1 (rootSeq p D hO X hX m).2).choose_spec.2

theorem pow_nsmul_rootSeq (X : G.CPoints (O p R)) (hX : Adm p D X) (m : ℕ) :
    p ^ m • (rootSeq p D hO X hX m).1 = X := by
  induction m with
  | zero => rw [pow_zero, one_smul]; rfl
  | succ m ih => rw [pow_succ, mul_nsmul', p_nsmul_rootSeq_succ, ih]

include hR hinj hO in

theorem eq_zero_of_cpointsProj_one_eq_zero (g : G.CPoints R) (hg1 : G.cpointsProj R 1 g = 0)
    (hK : KerP p D (G.cpointsMap (Algebra.ofId R (O p R)) g)) : g = 0 := by
  have hX : Adm p D (G.cpointsMap (Algebra.ofId R (O p R)) g) := ⟨hK, g1P_cpointsMap p g hg1, invP_cpointsMap p g⟩
  obtain ⟨ϖ, e, hϖ, hnil⟩ := exists_uniformiser p hR hinj (E := E)
  refine cpointsProj_ext G R fun i => ?_
  rw [map_zero]
  cases i with
  | zero => exact cpointsProj_zero G R g
  | succ m =>

      set Y := rootSeq p D hO _ hX (m + e) with hY
      obtain ⟨gm, hgm, -⟩ := G.existsUnique_cpointsMap_ofId_eq_of_forall_smul_eq_of_forall_mem_range_iff p E hR hinj
        Y.1 Y.2.2.2

      have hgm1 : G.cpointsProj R 1 (p ^ e • gm) = 0 :=
        cpointsProj_one_pow_nsmul_eq_zero p G ϖ e hϖ hnil gm
          (isNilpotent_of_g1P_cpointsMap p E hR hinj gm (by rw [hgm]; exact Y.2.2.1))
      have hpow : p ^ m • (p ^ e • gm) = g := by
        apply cpointsMap_ofId_injective p E hR hinj
        rw [← mul_nsmul', ← pow_add, map_nsmul, hgm, hY, pow_nsmul_rootSeq]
      rw [← hpow]
      exact cpointsProj_succ_pow_nsmul p G _ hgm1 m

end Main

end PDivStep4R

end

open PDivStep4R in

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
    (hR : ∀ x : PadicAlgCl p, x ∈ Set.range (algebraMap R (PadicAlgCl p)) ↔ x ∈ K ∧ ‖x‖ ≤ 1)
    (hinj : Function.Injective (algebraMap R (PadicAlgCl p)))
    {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (g : G.CPoints R)
    (hg : ∀ (y : TateModule p (G'.Points (PadicAlgCl p))) (i w : ℕ), i ≤ w →
      ∀ (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
          Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i}) w),
        G.pointsMkAdd _ w (Additive.ofMul f) =
          G.cpointsProj (integralClosure R (PadicAlgCl p)) i
            (G.cpointsMap (Algebra.ofId R (integralClosure R (PadicAlgCl p))) g) →
      ∀ (ψ : G'.Point (integralClosure R (PadicAlgCl p)) w),
        G'.pointsMkAdd (PadicAlgCl p) w
            (Additive.ofMul (G'.pointMap (integralClosure R (PadicAlgCl p)).val w ψ)) =
          (y : ℕ → G'.Points (PadicAlgCl p)) w →
        D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R
            (Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i})) w ψ) = 1) :
    g = 0 := by
  have hO : OK p R := oK p hR hinj

  have hK : KerP p D (G.cpointsMap (Algebra.ofId R (O p R)) g) := hg

  obtain ⟨v, f, hf⟩ := PDivisibleGroup.Points.exists_mkAdd G (G.cpointsProj R 1 g)
  have hv1 : G.cpointsProj R 1 (p ^ v • g) = 0 := by
    rw [map_nsmul, ← hf, G.nsmul_pointsMkAdd_eq_zero v f]

  have hv : p ^ v • g = 0 := eq_zero_of_cpointsProj_one_eq_zero p K hR hinj D hO _ hv1 (by
    rw [map_nsmul]; exact (step2 p D hO).1 _ hK (p ^ v))

  have hX : G.cpointsMap (Algebra.ofId R (O p R)) g = 0 :=
    (step2 p D hO).2.1 _ hK v (by rw [← map_nsmul, hv, map_zero])
  exact cpointsMap_ofId_injective p K hR hinj (by rw [hX, map_zero])

end S_PDivisibleGroup_CartierDuality_cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff (solution)

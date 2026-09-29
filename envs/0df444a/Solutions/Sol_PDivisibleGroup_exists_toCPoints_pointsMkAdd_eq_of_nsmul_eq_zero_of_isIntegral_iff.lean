-- Prove2me | solution 1 for PDivisibleGroup.exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8762795d-c03d-5a84-8e33-c8fdfd5d55b8

import Mathlib
import Definitions.Def_PDivisibleGroup_CompletedPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff

set_option autoImplicit false

noncomputable section

open PDivisibleGroup Filter Topology Polynomial

namespace PDivK1TorsR

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)]

abbrev O : Subalgebra R (PadicAlgCl p) := integralClosure R (PadicAlgCl p)

abbrev K : Type := PadicAlgCl p

abbrev Oq (i : ℕ) : Type := O p R ⧸ Ideal.span {(p : O p R) ^ i}

abbrev OK : Prop := ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1

def ι : O p R →+* ℂ_[p] := (algebraMap (PadicAlgCl p) ℂ_[p]).comp (O p R).val.toRingHom

theorem ι_apply (c : O p R) : ι p R c = ((c : PadicAlgCl p) : ℂ_[p]) := rfl

def φ : R →+* ℂ_[p] := (algebraMap (PadicAlgCl p) ℂ_[p]).comp (algebraMap R (PadicAlgCl p))

theorem φ_apply (r : R) : φ p R r = ((algebraMap R (PadicAlgCl p) r : PadicAlgCl p) : ℂ_[p]) := rfl

theorem ι_comp_algebraMap : (ι p R).comp (algebraMap R (O p R)) = φ p R :=
  RingHom.ext fun _ => rfl

variable {R}
variable (hO : OK p R)

theorem norm_add_le_max (a b : ℂ_[p]) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := PadicComplex.isNonarchimedean p a b

include hO in
theorem norm_ι_le_one (c : O p R) : ‖ι p R c‖ ≤ 1 := by
  rw [ι_apply, PadicComplex.norm_extends]
  exact (hO (c : PadicAlgCl p)).mp c.2

include hO in
theorem norm_φ_le_one (r : R) : ‖φ p R r‖ ≤ 1 := by
  rw [← ι_comp_algebraMap]; exact norm_ι_le_one p hO _

theorem norm_coe_p : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  exact (PadicAlgCl.norm_extends (p := p) (p : ℚ_[p])).trans (Padic.norm_p (p := p))

theorem norm_ι_p_pow (v : ℕ) : ‖ι p R ((p : O p R) ^ v)‖ = (p : ℝ) ^ (-(v : ℤ)) := by
  rw [map_pow, map_natCast, norm_pow]
  have h1 : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p]
    exact (PadicComplex.norm_extends' (p := p) (p : ℚ_[p])).trans (Padic.norm_p (p := p))
  rw [h1, zpow_neg, zpow_natCast, inv_pow]

include hO in
theorem norm_ι_le_of_mem_span (v : ℕ) {c : O p R} (hc : c ∈ Ideal.span {(p : O p R) ^ v}) :
    ‖ι p R c‖ ≤ (p : ℝ) ^ (-(v : ℤ)) := by
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
  rw [map_mul, norm_mul, norm_ι_p_pow]
  calc ‖ι p R d‖ * (p : ℝ) ^ (-(v : ℤ)) ≤ 1 * (p : ℝ) ^ (-(v : ℤ)) :=
        mul_le_mul_of_nonneg_right (norm_ι_le_one p hO d) (by positivity)
    _ = (p : ℝ) ^ (-(v : ℤ)) := one_mul _

include hO in

theorem mem_span_of_norm_ι_le (v : ℕ) (c : O p R) (hc : ‖ι p R c‖ ≤ (p : ℝ) ^ (-(v : ℤ))) :
    c ∈ Ideal.span {(p : O p R) ^ v} := by
  have hp0 : (p : PadicAlgCl p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpv0 : (p : PadicAlgCl p) ^ v ≠ 0 := pow_ne_zero _ hp0
  have hppos : (0 : ℝ) < (p : ℝ) ^ v := pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) v
  have hc' : ‖(c : PadicAlgCl p)‖ ≤ ((p : ℝ) ^ v)⁻¹ := by
    rw [ι_apply, PadicComplex.norm_extends] at hc
    rwa [zpow_neg, zpow_natCast] at hc
  set d : PadicAlgCl p := (c : PadicAlgCl p) / (p : PadicAlgCl p) ^ v with hd
  have hdn : ‖d‖ ≤ 1 := by
    rw [hd, norm_div, norm_pow, norm_coe_p, inv_pow, div_le_one (inv_pos.mpr hppos)]
    exact hc'
  have hdint : IsIntegral R d := (hO d).mpr hdn
  refine Ideal.mem_span_singleton'.mpr ⟨⟨d, hdint⟩, Subtype.ext ?_⟩
  change d * (((p : O p R) ^ v : O p R) : PadicAlgCl p) = (c : PadicAlgCl p)
  have hcoe : (((p : O p R) ^ v : O p R) : PadicAlgCl p) = (p : PadicAlgCl p) ^ v := by
    rw [SubmonoidClass.coe_pow]; rfl
  rw [hcoe, hd, div_mul_cancel₀ _ hpv0]

theorem pow_antitone {v w : ℕ} (hvw : v ≤ w) : (p : ℝ) ^ (-(w : ℤ)) ≤ (p : ℝ) ^ (-(v : ℤ)) := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  exact zpow_le_zpow_right₀ hp (by omega)

theorem tendsto_pow_neg : Tendsto (fun v : ℕ => (p : ℝ) ^ (-(v : ℤ))) atTop (𝓝 0) := by
  have : (fun v : ℕ => (p : ℝ) ^ (-(v : ℤ))) = fun v : ℕ => ((p : ℝ)⁻¹) ^ v := by
    funext v; rw [zpow_neg, zpow_natCast, inv_pow]
  rw [this]
  refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
  have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact inv_lt_one_of_one_lt₀ this

theorem eq_zero_of_norm_le_pow (a : ℂ_[p]) (ha : ∀ v : ℕ, ‖a‖ ≤ (p : ℝ) ^ (-(v : ℤ))) : a = 0 := by
  rw [← norm_le_zero_iff]
  exact ge_of_tendsto' (tendsto_pow_neg p) ha

theorem ι_injective : Function.Injective (ι p R) := by
  intro a b hab
  rw [ι_apply, ι_apply] at hab
  exact Subtype.ext (UniformSpace.Completion.coe_injective _ hab)

include hO in

theorem eq_of_forall_mk_eq {c d : O p R}
    (h : ∀ i : ℕ, (Ideal.Quotient.mk (Ideal.span {(p : O p R) ^ i}) c) = Ideal.Quotient.mk _ d) : c = d := by
  rw [← sub_eq_zero]
  apply ι_injective p
  rw [map_zero]
  refine eq_zero_of_norm_le_pow p _ fun i => norm_ι_le_of_mem_span p hO i ?_
  rw [← Ideal.Quotient.eq]
  exact h i

theorem norm_pow_sub_pow_le (a b : ℂ_[p]) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) : ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  induction n with
  | zero => rw [pow_zero, pow_zero, sub_self, norm_zero]; exact norm_nonneg _
  | succ n ih =>
      have h1 : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
      rw [h1]
      refine (norm_add_le_max p _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        calc ‖a‖ * ‖a ^ n - b ^ n‖ ≤ 1 * ‖a - b‖ := mul_le_mul ha ih (norm_nonneg _) zero_le_one
          _ = ‖a - b‖ := one_mul _
      · rw [norm_mul, norm_pow]
        calc ‖a - b‖ * ‖b‖ ^ n ≤ ‖a - b‖ * 1 :=
              mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hb) (norm_nonneg _)
          _ = ‖a - b‖ := mul_one _

include hO in

theorem norm_eval₂_sub_eval₂_le (P : Polynomial R) (a b : ℂ_[p]) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖P.eval₂ (φ p R) a - P.eval₂ (φ p R) b‖ ≤ ‖a - b‖ := by
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖φ p R (P.coeff n)‖ * ‖a ^ n - b ^ n‖ ≤ 1 * ‖a - b‖ :=
        mul_le_mul (norm_φ_le_one p hO _) (norm_pow_sub_pow_le p a b ha hb n) (norm_nonneg _) zero_le_one
    _ = ‖a - b‖ := one_mul _

theorem exists_coe_eq_of_eval₂_eq_zero (P : Polynomial R) (hP : P.Monic) (ℓ : ℂ_[p]) (hℓ : P.eval₂ (φ p R) ℓ = 0) :
    ∃ r : K p, (r : ℂ_[p]) = ℓ := by
  set Q : Polynomial (K p) := P.map (algebraMap R (K p)) with hQ
  have hQsplit : Q.Splits := IsAlgClosed.splits Q
  have hQmonic : Q.Monic := hP.map _
  have hprod := hQsplit.eq_prod_roots
  rw [hQmonic.leadingCoeff, map_one, one_mul] at hprod
  have hφ : φ p R = (algebraMap (K p) ℂ_[p]).comp (algebraMap R (K p)) := rfl
  have heval : Q.eval₂ (algebraMap (K p) ℂ_[p]) ℓ = 0 := by
    rw [hQ, Polynomial.eval₂_map, ← hφ, hℓ]
  rw [hprod, Polynomial.eval₂_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at heval
  obtain ⟨q, hq, hq0⟩ := heval
  rw [Multiset.mem_map] at hq
  obtain ⟨r, -, rfl⟩ := hq
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at hq0
  exact ⟨r, hq0.symm⟩

include hO in

theorem exists_of_compat (u : ∀ j : ℕ, Oq p R j)
    (hcompat : ∀ j, reduceModPow R p (O p R) j (u (j + 1)) = u j)
    (P : Polynomial R) (hP : P.Monic) (hPu : ∀ j, Polynomial.aeval (u j) P = 0) :
    ∃ r : O p R, ∀ j, u j = Ideal.Quotient.mk _ r := by
  have hlift : ∀ j, ∃ c : O p R, Ideal.Quotient.mk _ c = u j := fun j => Ideal.Quotient.mk_surjective (u j)
  choose c hc using hlift
  have hcs : ∀ j, c (j + 1) - c j ∈ Ideal.span {(p : O p R) ^ j} := by
    intro j
    rw [← Ideal.Quotient.eq, hc j, ← hcompat j, ← hc (j + 1), reduceModPow_mk]
  have hdist : ∀ {j j' : ℕ}, j ≤ j' → ‖ι p R (c j') - ι p R (c j)‖ ≤ (p : ℝ) ^ (-(j : ℤ)) := by
    intro j j' hjj'
    induction j', hjj' using Nat.le_induction with
    | base => rw [sub_self, norm_zero]; positivity
    | succ j' hjj' ih =>
        have h1 : ‖ι p R (c (j' + 1)) - ι p R (c j')‖ ≤ (p : ℝ) ^ (-(j : ℤ)) := by
          rw [← map_sub]
          exact (norm_ι_le_of_mem_span p hO _ (hcs j')).trans (pow_antitone p hjj')
        calc ‖ι p R (c (j' + 1)) - ι p R (c j)‖
            = ‖(ι p R (c (j' + 1)) - ι p R (c j')) + (ι p R (c j') - ι p R (c j))‖ := by rw [sub_add_sub_cancel]
          _ ≤ _ := (norm_add_le_max p _ _).trans (max_le h1 ih)
  have hp1 : (p : ℝ)⁻¹ < 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact inv_lt_one_of_one_lt₀ this
  have hcauchy : CauchySeq fun j => ι p R (c j) := by
    refine cauchySeq_of_le_geometric ((p : ℝ)⁻¹) 1 hp1 fun j => ?_
    rw [dist_comm, dist_eq_norm, one_mul, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact hdist (Nat.le_succ j)
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hℓj : ∀ j, ‖ℓ - ι p R (c j)‖ ≤ (p : ℝ) ^ (-(j : ℤ)) := by
    intro j
    have ht : Tendsto (fun j' => ‖ι p R (c j') - ι p R (c j)‖) atTop (𝓝 ‖ℓ - ι p R (c j)‖) :=
      (hℓ.sub_const _).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.mpr ⟨j, fun j' hj' => hdist hj'⟩)
  have hℓ1 : ‖ℓ‖ ≤ 1 := by
    have h2 : ℓ = (ℓ - ι p R (c 0)) + ι p R (c 0) := by abel
    rw [h2]
    refine (norm_add_le_max p _ _).trans (max_le ((hℓj 0).trans ?_) (norm_ι_le_one p hO _))
    rw [Nat.cast_zero, neg_zero, zpow_zero]

  have hPc : ∀ j, ‖ι p R (Polynomial.aeval (c j) P)‖ ≤ (p : ℝ) ^ (-(j : ℤ)) := by
    intro j
    refine norm_ι_le_of_mem_span p hO j ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R, ← Polynomial.aeval_algHom_apply,
      Ideal.Quotient.mkₐ_eq_mk, hc j]
    exact hPu j
  have hPℓ : P.eval₂ (φ p R) ℓ = 0 := by
    refine eq_zero_of_norm_le_pow p _ fun j => ?_
    have h1 : P.eval₂ (φ p R) ℓ = (P.eval₂ (φ p R) ℓ - P.eval₂ (φ p R) (ι p R (c j))) + ι p R (Polynomial.aeval (c j) P) := by
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, ι_comp_algebraMap]; abel
    rw [h1]
    refine (norm_add_le_max p _ _).trans (max_le ?_ (hPc j))
    exact (norm_eval₂_sub_eval₂_le p hO P _ _ hℓ1 (norm_ι_le_one p hO _)).trans (hℓj j)

  obtain ⟨r, hr⟩ := exists_coe_eq_of_eval₂_eq_zero p P hP ℓ hPℓ
  have hrn : ‖r‖ ≤ 1 := by rw [← PadicComplex.norm_extends, hr]; exact hℓ1
  have hrint : IsIntegral R r := (hO r).mpr hrn
  refine ⟨⟨r, hrint⟩, fun j => ?_⟩
  rw [← hc j, Ideal.Quotient.eq]
  refine mem_span_of_norm_ι_le p hO j _ ?_
  rw [map_sub, ι_apply]
  change ‖ι p R (c j) - ((r : K p) : ℂ_[p])‖ ≤ _
  rw [hr, norm_sub_rev]
  exact hℓj j

section Main

variable {h : ℕ} (G : PDivisibleGroup R p h) (k : ℕ) (T : G.CPoints (O p R)) (hT : (p ^ k) • T = 0)

omit [Fact p.Prime] [Algebra R (PadicAlgCl p)] in

theorem exists_point_of_nsmul_eq_zero {L : Type} [CommRing L] [Algebra R L] (v : ℕ) (z : G.Points L)
    (hz : (p ^ v) • z = 0) : ∃ f : G.Point L v, G.pointsMkAdd L v (Additive.ofMul f) = z := by
  obtain ⟨m, y, rfl⟩ := Points.exists_mkAdd G z
  set w := max m v
  have hy : G.pointsMkAdd L w (Additive.ofMul (G.pointInclLE L (le_max_left m v) y)) =
      G.pointsMkAdd L m (Additive.ofMul y) := G.pointsMkAdd_pointInclLE _ y
  rw [← hy] at hz ⊢
  set y' := G.pointInclLE L (le_max_left m v) y
  have hpow : y' ^ (p ^ v) = 1 := by
    apply G.pointsMkAdd_injective w
    change G.pointsMkAdd L w (Additive.ofMul (y' ^ p ^ v)) = G.pointsMkAdd L w (Additive.ofMul 1)
    rw [ofMul_pow, map_nsmul, hz, ofMul_one, map_zero]
  obtain ⟨x, hx⟩ := G.exists_pointInclLE_eq_of_pow_eq_one (le_max_right m v) y' hpow
  exact ⟨x, by rw [← hx, pointsMkAdd_pointInclLE]⟩

include hT in
theorem nsmul_cpointsProj (i : ℕ) : (p ^ k) • G.cpointsProj (O p R) i T = 0 := by
  rw [← map_nsmul, hT, map_zero]

def tq (i : ℕ) : G.Point (Oq p R i) k :=
  (exists_point_of_nsmul_eq_zero p G k (G.cpointsProj (O p R) i T) (nsmul_cpointsProj p G k T hT i)).choose

theorem tq_spec (i : ℕ) : G.pointsMkAdd _ k (Additive.ofMul (tq p G k T hT i)) = G.cpointsProj (O p R) i T :=
  (exists_point_of_nsmul_eq_zero p G k (G.cpointsProj (O p R) i T) (nsmul_cpointsProj p G k T hT i)).choose_spec

theorem pointMap_reduce_tq (i : ℕ) : G.pointMap (reduceModPow R p (O p R) i) k (tq p G k T hT (i + 1)) = tq p G k T hT i := by
  apply G.pointsMkAdd_injective k
  change G.pointsMkAdd _ k (Additive.ofMul (G.pointMap (reduceModPow R p (O p R) i) k (tq p G k T hT (i + 1)))) =
    G.pointsMkAdd _ k (Additive.ofMul (tq p G k T hT i))
  rw [← pointsMap_pointsMkAdd, tq_spec, tq_spec, pointsMap_reduceModPow_cpointsProj_succ]

theorem reduce_tq_apply (i : ℕ) (a : G.level k) :
    reduceModPow R p (O p R) i (Point.toAlgHom (tq p G k T hT (i + 1)) a) = Point.toAlgHom (tq p G k T hT i) a := by
  have h1 := DFunLike.congr_fun (congrArg Point.toAlgHom (pointMap_reduce_tq p G k T hT i)) a
  rw [toAlgHom_pointMap, AlgHom.comp_apply] at h1
  exact h1

include hO in

theorem exists_val (a : G.level k) : ∃ r : O p R, ∀ j, Point.toAlgHom (tq p G k T hT j) a = Ideal.Quotient.mk _ r := by
  obtain ⟨P, hP, hPa⟩ := (Algebra.IsIntegral.isIntegral (R := R) a)
  refine exists_of_compat p hO (fun j => Point.toAlgHom (tq p G k T hT j) a) (fun j => reduce_tq_apply p G k T hT j a)
    P hP fun j => ?_
  show Polynomial.aeval (Point.toAlgHom (tq p G k T hT j) a) P = 0
  rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hPa, map_zero]

def tval (a : G.level k) : O p R := (exists_val p hO G k T hT a).choose

theorem tval_spec (a : G.level k) (j : ℕ) : Point.toAlgHom (tq p G k T hT j) a = Ideal.Quotient.mk _ (tval p hO G k T hT a) :=
  (exists_val p hO G k T hT a).choose_spec j

theorem mk_tval (a : G.level k) (j : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(p : O p R) ^ j}) (tval p hO G k T hT a) = Point.toAlgHom (tq p G k T hT j) a :=
  (tval_spec p hO G k T hT a j).symm

def tHom : G.level k →ₐ[R] O p R where
  toFun := tval p hO G k T hT
  map_one' := eq_of_forall_mk_eq p hO fun j => by
    rw [mk_tval, map_one (Point.toAlgHom (tq p G k T hT j)), RingHom.map_one (Ideal.Quotient.mk (Ideal.span {(p : O p R) ^ j}))]
  map_mul' a b := eq_of_forall_mk_eq p hO fun j => by
    rw [mk_tval, map_mul (Point.toAlgHom (tq p G k T hT j)), RingHom.map_mul (Ideal.Quotient.mk (Ideal.span {(p : O p R) ^ j})),
      mk_tval, mk_tval]
  map_zero' := eq_of_forall_mk_eq p hO fun j => by
    rw [mk_tval, map_zero (Point.toAlgHom (tq p G k T hT j)), RingHom.map_zero (Ideal.Quotient.mk (Ideal.span {(p : O p R) ^ j}))]
  map_add' a b := eq_of_forall_mk_eq p hO fun j => by
    rw [mk_tval, map_add (Point.toAlgHom (tq p G k T hT j)), RingHom.map_add (Ideal.Quotient.mk (Ideal.span {(p : O p R) ^ j})),
      mk_tval, mk_tval]
  commutes' r := eq_of_forall_mk_eq p hO fun j => by
    rw [mk_tval, AlgHom.commutes]
    exact ((Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ j})).commutes r).symm

def t : G.Point (O p R) k := Point.ofAlgHom (tHom p hO G k T hT)

theorem pointMap_mk_t (j : ℕ) :
    G.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ j})) k (t p hO G k T hT) = tq p G k T hT j :=
  Point.ext fun a => (tval_spec p hO G k T hT a j).symm

theorem toCPoints_t : G.toCPoints (O p R) (G.pointsMkAdd (O p R) k (Additive.ofMul (t p hO G k T hT))) = T := by
  refine cpointsProj_ext G (O p R) fun j => ?_
  rw [cpointsProj_toCPoints, pointsMap_pointsMkAdd, pointMap_mk_t, tq_spec]

end Main

end PDivK1TorsR

end

open PDivK1TorsR in

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
    (hO : ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1)
    {h : ℕ} (G : PDivisibleGroup R p h) (k : ℕ)
    (T : G.CPoints (integralClosure R (PadicAlgCl p))) (hT : (p ^ k) • T = 0) :
    ∃ t : G.Point (integralClosure R (PadicAlgCl p)) k,
      G.toCPoints (integralClosure R (PadicAlgCl p))
        (G.pointsMkAdd (integralClosure R (PadicAlgCl p)) k (Additive.ofMul t)) = T :=
  ⟨t p hO G k T hT, toCPoints_t p hO G k T hT⟩

end S_PDivisibleGroup_exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff
end P2MW
export P2MW.S_PDivisibleGroup_exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff (solution)

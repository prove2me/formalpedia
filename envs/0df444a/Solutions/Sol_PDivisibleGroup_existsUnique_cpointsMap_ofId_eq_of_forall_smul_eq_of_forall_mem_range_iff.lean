-- Prove2me | solution 1 for PDivisibleGroup.existsUnique_cpointsMap_ofId_eq_of_forall_smul_eq_of_forall_mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b81ec2bc-f1b5-5ccd-90e8-475d06dd08bf

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PDivisibleGroup_CompletedPoints
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_PadicComplex_forall_smul_eq_self_iff_mem_closure
import Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_existsUnique_cpointsMap_ofId_eq_of_forall_smul_eq_of_forall_mem_range_iff

set_option autoImplicit false

open PDivisibleGroup Filter Topology

namespace PDivDESCK

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]

noncomputable abbrev O (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] : Subalgebra R (PadicAlgCl p) :=
  integralClosure R (PadicAlgCl p)

abbrev Gal : Type := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p

def Restricts (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R) : Prop := ∀ a : O p R, ((σ' a : O p R) : PadicAlgCl p) = σ a

noncomputable def ι (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] : O p R →+* ℂ_[p] :=
  (algebraMap (PadicAlgCl p) ℂ_[p]).comp (O p R).val.toRingHom

theorem ι_apply (c : O p R) : ι p R c = ((c : PadicAlgCl p) : ℂ_[p]) := rfl

def BaseHyp (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] : Prop :=
  ∀ x : PadicAlgCl p, x ∈ Set.range (algebraMap R (PadicAlgCl p)) ↔ x ∈ K ∧ ‖x‖ ≤ 1

variable {K}
variable (hR : BaseHyp p K R) (hinj : Function.Injective (algebraMap R (PadicAlgCl p)))

include hR in
theorem algebraMap_mem_K (r : R) : algebraMap R (PadicAlgCl p) r ∈ K := ((hR _).1 ⟨r, rfl⟩).1

include hR in
theorem norm_algebraMap_le_one (r : R) : ‖algebraMap R (PadicAlgCl p) r‖ ≤ 1 := ((hR _).1 ⟨r, rfl⟩).2

include hR in
theorem exists_algebraMap_eq {x : PadicAlgCl p} (hxK : x ∈ K) (hxn : ‖x‖ ≤ 1) :
    ∃ r : R, algebraMap R (PadicAlgCl p) r = x := (hR x).2 ⟨hxK, hxn⟩

theorem algebraMap_padicInt_mem_K (a : ℤ_[p]) : algebraMap ℤ_[p] (PadicAlgCl p) a ∈ K := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p)]
  exact K.algebraMap_mem _

theorem norm_algebraMap_padicInt_le_one (a : ℤ_[p]) : ‖algebraMap ℤ_[p] (PadicAlgCl p) a‖ ≤ 1 := by
  rw [PadicAlgCl.ringOfIntegers.norm_algebraMap_padicInt]
  exact PadicInt.norm_le_one a

noncomputable def eR : R ≃+* (algebraMap R (PadicAlgCl p)).range :=
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

noncomputable def φZ : ℤ_[p] →+* R :=
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

noncomputable def galK (σ : Gal p) (hσ : σ ∈ K.fixingSubgroup) : PadicAlgCl p ≃ₐ[R] PadicAlgCl p :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun r =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (algebraMap_mem_K p hR r)

theorem galK_apply (σ : Gal p) (hσ : σ ∈ K.fixingSubgroup) (x : PadicAlgCl p) : galK p hR σ hσ x = σ x := rfl

noncomputable def restrictK (σ : Gal p) (hσ : σ ∈ K.fixingSubgroup) : O p R ≃ₐ[R] O p R :=
  ((galK p hR σ hσ).subalgebraMap (O p R)).trans
    (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv (galK p hR σ hσ)))

theorem restricts_restrictK (σ : Gal p) (hσ : σ ∈ K.fixingSubgroup) : Restricts p σ (restrictK p hR σ hσ) :=
  fun _ => rfl

theorem norm_add_le_max (a b : ℂ_[p]) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := PadicComplex.isNonarchimedean p a b

include hR in
theorem norm_ι_le_one (c : O p R) : ‖ι p R c‖ ≤ 1 := by
  rw [ι_apply, PadicComplex.norm_extends]
  exact norm_coe_le_one p hR c

theorem norm_coe_p : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  exact (PadicAlgCl.norm_extends (p := p) (p : ℚ_[p])).trans (Padic.norm_p (p := p))

theorem norm_ι_p_pow (v : ℕ) : ‖ι p R ((p : O p R) ^ v)‖ = (p : ℝ) ^ (-(v : ℤ)) := by
  rw [map_pow, map_natCast, norm_pow]
  have h1 : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p]
    exact (PadicComplex.norm_extends' (p := p) (p : ℚ_[p])).trans (Padic.norm_p (p := p))
  rw [h1, zpow_neg, zpow_natCast, inv_pow]

include hR in

theorem norm_ι_le_of_mem_span (v : ℕ) {c : O p R} (hc : c ∈ Ideal.span {(p : O p R) ^ v}) :
    ‖ι p R c‖ ≤ (p : ℝ) ^ (-(v : ℤ)) := by
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
  rw [map_mul, norm_mul, norm_ι_p_pow]
  calc ‖ι p R d‖ * (p : ℝ) ^ (-(v : ℤ)) ≤ 1 * (p : ℝ) ^ (-(v : ℤ)) :=
        mul_le_mul_of_nonneg_right (norm_ι_le_one p hR d) (by positivity)
    _ = (p : ℝ) ^ (-(v : ℤ)) := one_mul _

include hR hinj in

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
  refine Ideal.mem_span_singleton'.mpr ⟨⟨d, mem_O_of_norm_le_one p hR hinj hdn⟩, Subtype.ext ?_⟩
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

variable (K) in

theorem exists_coe_eq_of_forall_smul_eq [FiniteDimensional ℚ_[p] K] (c : ℂ_[p])
    (hc : ∀ σ : Gal p, σ ∈ K.fixingSubgroup → σ • c = c) : ∃ k : K, ((k : PadicAlgCl p) : ℂ_[p]) = c := by
  have h := (PadicComplex.forall_smul_eq_self_iff_mem_closure p K c).1 hc
  let L : K →ₗ[ℚ_[p]] ℂ_[p] :=
    ((Algebra.linearMap (PadicAlgCl p) ℂ_[p]).restrictScalars ℚ_[p]).comp K.val.toLinearMap
  have hrange : (Set.range fun k : K => ((k : PadicAlgCl p) : ℂ_[p])) = (LinearMap.range L : Set ℂ_[p]) := by
    ext z
    simp only [Set.mem_range, SetLike.mem_coe, LinearMap.mem_range]
    rfl
  haveI : CompleteSpace ℚ_[p] := inferInstance
  have hclosed : IsClosed (LinearMap.range L : Set ℂ_[p]) := (LinearMap.range L).closed_of_finiteDimensional
  rw [hrange, hclosed.closure_eq] at h
  obtain ⟨k, hk⟩ := (LinearMap.mem_range).1 h
  exact ⟨k, hk⟩

theorem ι_algebraMap (a : R) : ι p R (algebraMap R (O p R) a) = ((algebraMap R (PadicAlgCl p) a : PadicAlgCl p) : ℂ_[p]) := by
  rw [ι_apply, Subalgebra.coe_algebraMap]

section ScalarDescent

variable (k : ℕ) (u : ∀ j : ℕ, O p R ⧸ Ideal.span {(p : O p R) ^ (k + j)})
  (hcompat : ∀ j, reduceModPow R p (O p R) (k + j) (u (j + 1)) = u j)
  (hfix : ∀ (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R), Restricts p σ σ' →
    ∀ j, mapModPow R p (O p R) (AlgEquiv.toAlgHom σ') (k + j) (u j) = u j)

noncomputable def lift (j : ℕ) : O p R := (Ideal.Quotient.mk_surjective (u j)).choose

theorem mk_lift (j : ℕ) : Ideal.Quotient.mk _ (lift p k u j) = u j :=
  (Ideal.Quotient.mk_surjective (u j)).choose_spec

include hcompat in
theorem lift_succ_sub_lift (j : ℕ) :
    lift p k u (j + 1) - lift p k u j ∈ Ideal.span {(p : O p R) ^ (k + j)} := by
  rw [← Ideal.Quotient.eq, mk_lift, ← hcompat j, ← mk_lift p k u (j + 1)]
  rfl

include hR hcompat in
theorem norm_lift_sub_lift {j j' : ℕ} (hjj' : j ≤ j') :
    ‖ι p R (lift p k u j') - ι p R (lift p k u j)‖ ≤ (p : ℝ) ^ (-((k + j : ℕ) : ℤ)) := by
  induction j', hjj' using Nat.le_induction with
  | base => rw [sub_self, norm_zero]; positivity
  | succ j' hjj' ih =>
      have h1 : ‖ι p R (lift p k u (j' + 1)) - ι p R (lift p k u j')‖ ≤ (p : ℝ) ^ (-((k + j : ℕ) : ℤ)) := by
        rw [← map_sub]
        exact (norm_ι_le_of_mem_span p hR _ (lift_succ_sub_lift p k u hcompat j')).trans
          (pow_antitone p (by omega))
      calc ‖ι p R (lift p k u (j' + 1)) - ι p R (lift p k u j)‖
          = ‖(ι p R (lift p k u (j' + 1)) - ι p R (lift p k u j')) + (ι p R (lift p k u j') - ι p R (lift p k u j))‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ _ := (norm_add_le_max p _ _).trans (max_le h1 ih)

include hR hcompat in

theorem exists_limit : ∃ ℓ : ℂ_[p], ∀ j, ‖ℓ - ι p R (lift p k u j)‖ ≤ (p : ℝ) ^ (-((k + j : ℕ) : ℤ)) := by
  have hp1 : (p : ℝ)⁻¹ < 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact inv_lt_one_of_one_lt₀ this
  have hcs : CauchySeq fun j => ι p R (lift p k u j) := by
    refine cauchySeq_of_le_geometric ((p : ℝ)⁻¹) 1 hp1 fun j => ?_
    rw [dist_comm, dist_eq_norm, one_mul, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact (norm_lift_sub_lift p hR k u hcompat (Nat.le_succ j)).trans (pow_antitone p (by omega))
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨ℓ, fun j => ?_⟩
  have ht : Tendsto (fun j' => ‖ι p R (lift p k u j') - ι p R (lift p k u j)‖) atTop
      (𝓝 ‖ℓ - ι p R (lift p k u j)‖) := (hℓ.sub_const _).norm
  exact le_of_tendsto ht (Filter.eventually_atTop.mpr ⟨j, fun j' hj' => norm_lift_sub_lift p hR k u hcompat hj'⟩)

include hR hinj hcompat hfix in

theorem exists_base [FiniteDimensional ℚ_[p] K] :
    ∃ a : R, ∀ j, u j = Ideal.Quotient.mk _ (algebraMap R (O p R) a) := by
  obtain ⟨ℓ, hℓ⟩ := exists_limit p hR k u hcompat

  have hgal : ∀ σ : Gal p, σ ∈ K.fixingSubgroup → σ • ℓ = ℓ := by
    intro σ hσ
    rw [← sub_eq_zero]
    refine eq_zero_of_norm_le_pow p _ fun j => ?_
    have hσ' := restricts_restrictK p hR σ hσ

    have hmem : restrictK p hR σ hσ (lift p k u j) - lift p k u j ∈ Ideal.span {(p : O p R) ^ (k + j)} := by
      rw [← Ideal.Quotient.eq]
      have := hfix σ (restrictK p hR σ hσ) hσ' j
      rw [← mk_lift p k u j, mapModPow_mk] at this
      exact this
    have h1 : σ • ℓ - ℓ = σ • (ℓ - ι p R (lift p k u j)) +
        (ι p R (restrictK p hR σ hσ (lift p k u j) - lift p k u j)) + (ι p R (lift p k u j) - ℓ) := by
      rw [smul_sub, map_sub]
      have h2 : σ • ι p R (lift p k u j) = ι p R (restrictK p hR σ hσ (lift p k u j)) := by
        rw [ι_apply, ι_apply, hσ', ← PadicComplex.smul_coe]
      rw [h2]; abel
    rw [h1]
    refine (norm_add_le_max p _ _).trans (max_le ((norm_add_le_max p _ _).trans (max_le ?_ ?_)) ?_)
    · rw [PadicComplex.norm_smul_eq]
      exact (hℓ j).trans (pow_antitone p (by omega))
    · exact (norm_ι_le_of_mem_span p hR _ hmem).trans (pow_antitone p (by omega))
    · rw [norm_sub_rev]
      exact (hℓ j).trans (pow_antitone p (by omega))

  obtain ⟨q, hq⟩ := exists_coe_eq_of_forall_smul_eq p K ℓ hgal
  have hqn : ‖(q : PadicAlgCl p)‖ ≤ 1 := by
    have h1 : ‖ℓ‖ ≤ 1 := by
      have h2 : ℓ = (ℓ - ι p R (lift p k u 0)) + ι p R (lift p k u 0) := by abel
      rw [h2]
      refine (norm_add_le_max p _ _).trans (max_le ((hℓ 0).trans ?_) (norm_ι_le_one p hR _))
      exact zpow_le_one_of_nonpos₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le) (by omega)
    rwa [← hq, PadicComplex.norm_extends] at h1
  obtain ⟨a, ha⟩ := exists_algebraMap_eq p hR q.2 hqn
  refine ⟨a, fun j => ?_⟩
  rw [← mk_lift p k u j, Ideal.Quotient.eq]
  refine mem_span_of_norm_ι_le p hR hinj _ _ ?_
  rw [map_sub, ι_algebraMap, ha, hq, norm_sub_rev]
  exact hℓ j

end ScalarDescent

include hR hinj in

theorem mem_span_of_algebraMap_mem (k : ℕ) (a : R)
    (ha : algebraMap R (O p R) a ∈ Ideal.span {(p : O p R) ^ k}) :
    a ∈ Ideal.span {(p : R) ^ k} := by
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp ha
  have hp0 : (p : PadicAlgCl p) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

  have hs' : (s : PadicAlgCl p) * (p : PadicAlgCl p) ^ k = algebraMap R (PadicAlgCl p) a := by
    have := congrArg (fun z : O p R => (z : PadicAlgCl p)) hs
    simp only [Subalgebra.coe_mul, SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap] at this
    exact this

  have hsK : (s : PadicAlgCl p) ∈ K := by
    have h1 : (s : PadicAlgCl p) = algebraMap R (PadicAlgCl p) a / (p : PadicAlgCl p) ^ k := by
      rw [← hs', mul_div_cancel_right₀ _ hp0]
    rw [h1]
    exact K.div_mem (algebraMap_mem_K p hR a) (pow_mem (K.natCast_mem p) k)
  obtain ⟨b, hb⟩ := exists_algebraMap_eq p hR hsK (norm_coe_le_one p hR s)
  refine Ideal.mem_span_singleton'.mpr ⟨b, hinj ?_⟩
  rw [map_mul, map_pow, map_natCast, hb, hs']

noncomputable abbrev ιk (k : ℕ) :
    (R ⧸ Ideal.span {(p : R) ^ k}) →ₐ[R] (O p R ⧸ Ideal.span {(p : O p R) ^ k}) :=
  mapModPow R p R (Algebra.ofId R (O p R)) k

theorem ιk_mk (k : ℕ) (a : R) :
    ιk p k (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (algebraMap R (O p R) a) := rfl

include hR hinj in

theorem ιk_injective (k : ℕ) : Function.Injective (ιk p (R := R) k) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [ιk_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_of_algebraMap_mem p hR hinj k a hz)

include hR hinj in

theorem exists_algHom_comp_eq {A : Type} [CommRing A] [Algebra R A] (k : ℕ)
    (f : A →ₐ[R] O p R ⧸ Ideal.span {(p : O p R) ^ k}) (hf : ∀ a, f a ∈ (ιk p (R := R) k).range) :
    ∃ g : A →ₐ[R] R ⧸ Ideal.span {(p : R) ^ k}, (ιk p k).comp g = f := by
  let e := AlgEquiv.ofInjective (ιk p (R := R) k) (ιk_injective p hR hinj k)
  refine ⟨(AlgEquiv.toAlgHom e.symm).comp (f.codRestrict (ιk p (R := R) k).range hf), AlgHom.ext fun a => ?_⟩
  have h1 : ∀ z, ιk p k z = ((e z : (ιk p (R := R) k).range) : O p R ⧸ Ideal.span {(p : O p R) ^ k}) := fun z =>
    (AlgEquiv.ofInjective_apply (ιk p (R := R) k) (ιk_injective p hR hinj k) z).symm
  rw [AlgHom.comp_apply, h1]
  change ((e (e.symm (f.codRestrict (ιk p (R := R) k).range hf a)) : (ιk p (R := R) k).range) : _) = f a
  rw [AlgEquiv.apply_symm_apply]
  rfl

section Trans

variable {R₀ : Type} [CommRing R₀] {q hh : ℕ} (G : PDivisibleGroup R₀ q hh)

noncomputable def transLE {v w : ℕ} (hvw : v ≤ w) : G.level w →ₐ[R₀] G.level v :=
  Nat.leRec (motive := fun w _ => G.level w →ₐ[R₀] G.level v) (AlgHom.id R₀ _)
    (fun w _ ih => ih.comp (G.transitionAlgHom w)) hvw

@[scoped simp] theorem transLE_self (v : ℕ) : transLE G (le_refl v) = AlgHom.id R₀ _ := by
  rw [transLE, Nat.leRec_self]

theorem transLE_succ {v w : ℕ} (hvw : v ≤ w) :
    transLE G (Nat.le_succ_of_le hvw) = (transLE G hvw).comp (G.transitionAlgHom w) := by
  rw [transLE, Nat.leRec_succ (h1 := hvw)]
  rfl

theorem transLE_surjective {v w : ℕ} (hvw : v ≤ w) : Function.Surjective (transLE G hvw) := by
  induction hvw with
  | refl => rw [transLE_self]; exact Function.surjective_id
  | step hvw ih =>
      rw [transLE_succ]
      exact ih.comp (G.transitionAlgHom_surjective _)

theorem toAlgHom_pointInclLE {L : Type} [CommRing L] [Algebra R₀ L] {v w : ℕ} (hvw : v ≤ w)
    (x : G.Point L v) :
    Point.toAlgHom (G.pointInclLE L hvw x) = (Point.toAlgHom x).comp (transLE G hvw) := by
  induction hvw with
  | refl => rw [G.pointInclLE_self, transLE_self, AlgHom.comp_id]
  | step hvw ih =>
      rw [G.pointInclLE_succ hvw, toAlgHom_pointIncl, ih, transLE_succ, AlgHom.comp_assoc]

end Trans

section Main

variable {h : ℕ} (G : PDivisibleGroup R p h) (x : G.CPoints (O p R))

noncomputable def lv (j : ℕ) : ℕ := (Points.exists_mkAdd G (G.cpointsProj (O p R) j x)).choose

noncomputable def rp (j : ℕ) : G.Point (O p R ⧸ Ideal.span {(p : O p R) ^ j}) (lv p G x j) :=
  (Points.exists_mkAdd G (G.cpointsProj (O p R) j x)).choose_spec.choose

theorem mk_rp (j : ℕ) :
    G.pointsMkAdd _ (lv p G x j) (Additive.ofMul (rp p G x j)) = G.cpointsProj (O p R) j x :=
  (Points.exists_mkAdd G (G.cpointsProj (O p R) j x)).choose_spec.choose_spec

noncomputable def L : ℕ → ℕ
  | 0 => lv p G x 0
  | j + 1 => L j + lv p G x (j + 1)

theorem lv_le_L (j : ℕ) : lv p G x j ≤ L p G x j := by
  cases j with
  | zero => exact le_refl _
  | succ j => exact Nat.le_add_left _ _

theorem L_le_succ (j : ℕ) : L p G x j ≤ L p G x (j + 1) := Nat.le_add_right _ _

noncomputable def F (j : ℕ) : G.Point (O p R ⧸ Ideal.span {(p : O p R) ^ j}) (L p G x j) :=
  G.pointInclLE _ (lv_le_L p G x j) (rp p G x j)

theorem mk_F (j : ℕ) : G.pointsMkAdd _ (L p G x j) (Additive.ofMul (F p G x j)) = G.cpointsProj (O p R) j x := by
  rw [F, pointsMkAdd_pointInclLE, mk_rp]

theorem F_compat (j : ℕ) (a : G.level (L p G x (j + 1))) :
    reduceModPow R p (O p R) j (Point.toAlgHom (F p G x (j + 1)) a) =
      Point.toAlgHom (F p G x j) (transLE G (L_le_succ p G x j) a) := by
  have hc := G.pointsMap_reduceModPow_cpointsProj_succ (O p R) j x
  rw [← mk_F, ← mk_F, pointsMap_pointsMkAdd, ← G.pointsMkAdd_pointInclLE (L_le_succ p G x j),
    pointsMkAdd_eq_pointsMkAdd_iff] at hc
  have h1 := congrArg Point.toAlgHom hc
  rw [toAlgHom_pointMap, toAlgHom_pointInclLE] at h1
  exact DFunLike.congr_fun h1 a

theorem F_fix (σ' : O p R ≃ₐ[R] O p R) (hσx : σ' • x = x) (j : ℕ) (a : G.level (L p G x j)) :
    mapModPow R p (O p R) (AlgEquiv.toAlgHom σ') j (Point.toAlgHom (F p G x j) a) =
      Point.toAlgHom (F p G x j) a := by
  have hc : G.cpointsProj (O p R) j (σ' • x) = G.cpointsProj (O p R) j x := by rw [hσx]
  rw [CPoints.smul_def, cpointsProj_cpointsMap, ← mk_F, pointsMap_pointsMkAdd,
    pointsMkAdd_eq_pointsMkAdd_iff] at hc
  have h1 := congrArg Point.toAlgHom hc
  rw [toAlgHom_pointMap] at h1
  exact DFunLike.congr_fun h1 a

noncomputable def pre (k : ℕ) (a : G.level (L p G x k)) : ∀ j : ℕ, G.level (L p G x (k + j))
  | 0 => a
  | j + 1 => (transLE_surjective G (L_le_succ p G x (k + j)) (pre k a j)).choose

theorem transLE_pre_succ (k : ℕ) (a : G.level (L p G x k)) (j : ℕ) :
    transLE G (L_le_succ p G x (k + j)) (pre p G x k a (j + 1)) = pre p G x k a j :=
  (transLE_surjective G (L_le_succ p G x (k + j)) (pre p G x k a j)).choose_spec

noncomputable def uu (k : ℕ) (a : G.level (L p G x k)) (j : ℕ) : O p R ⧸ Ideal.span {(p : O p R) ^ (k + j)} :=
  Point.toAlgHom (F p G x (k + j)) (pre p G x k a j)

theorem uu_zero (k : ℕ) (a : G.level (L p G x k)) : uu p G x k a 0 = Point.toAlgHom (F p G x k) a := rfl

theorem uu_compat (k : ℕ) (a : G.level (L p G x k)) (j : ℕ) :
    reduceModPow R p (O p R) (k + j) (uu p G x k a (j + 1)) = uu p G x k a j := by
  change reduceModPow R p (O p R) (k + j) (Point.toAlgHom (F p G x (k + j + 1)) (pre p G x k a (j + 1))) = _
  rw [F_compat, transLE_pre_succ]
  rfl

include hR hinj in

theorem pointsMap_ιk_injective (k : ℕ) : Function.Injective (G.pointsMap (ιk p (R := R) k)) :=
  G.pointsMap_injective_of_injective _ (ιk_injective p hR hinj k)

variable [FiniteDimensional ℚ_[p] K]

include hR hinj in

theorem F_apply_mem_range
    (hx : ∀ (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R), Restricts p σ σ' → σ' • x = x)
    (k : ℕ) (a : G.level (L p G x k)) :
    Point.toAlgHom (F p G x k) a ∈ (ιk p (R := R) k).range := by
  obtain ⟨a₀, ha₀⟩ := exists_base p hR hinj k (uu p G x k a) (uu_compat p G x k a)
    (fun σ σ' hσ j => F_fix p G x σ' (hx σ σ' hσ) (k + j) (pre p G x k a j))
  refine ⟨Ideal.Quotient.mk _ a₀, ?_⟩
  rw [← uu_zero, ha₀ 0]
  rfl

include hR hinj in

theorem exists_g (hx : ∀ (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R), Restricts p σ σ' → σ' • x = x) (k : ℕ) :
    ∃ g : G.level (L p G x k) →ₐ[R] R ⧸ Ideal.span {(p : R) ^ k},
      (ιk p k).comp g = Point.toAlgHom (F p G x k) :=
  exists_algHom_comp_eq p hR hinj k _ (F_apply_mem_range p hR hinj G x hx k)

section X0

variable (hx : ∀ (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R), Restricts p σ σ' → σ' • x = x)

noncomputable def gg (k : ℕ) : G.level (L p G x k) →ₐ[R] R ⧸ Ideal.span {(p : R) ^ k} :=
  (exists_g p hR hinj G x hx k).choose

theorem ιk_comp_gg (k : ℕ) : (ιk p k).comp (gg p hR hinj G x hx k) = Point.toAlgHom (F p G x k) :=
  (exists_g p hR hinj G x hx k).choose_spec

noncomputable def comp₀ (k : ℕ) : G.Points (R ⧸ Ideal.span {(p : R) ^ k}) :=
  G.pointsMkAdd _ (L p G x k) (Additive.ofMul (Point.ofAlgHom (gg p hR hinj G x hx k)))

theorem pointMap_ιk_gg (k : ℕ) :
    G.pointMap (ιk p k) (L p G x k) (Point.ofAlgHom (gg p hR hinj G x hx k)) = F p G x k :=
  Point.ext fun a => DFunLike.congr_fun (ιk_comp_gg p hR hinj G x hx k) a

theorem pointsMap_ιk_comp₀ (k : ℕ) :
    G.pointsMap (ιk p k) (comp₀ p hR hinj G x hx k) = G.cpointsProj (O p R) k x := by
  rw [comp₀, pointsMap_pointsMkAdd, pointMap_ιk_gg, mk_F]

theorem comp₀_compat (k : ℕ) :
    G.pointsMap (reduceModPow R p R k) (comp₀ p hR hinj G x hx (k + 1)) = comp₀ p hR hinj G x hx k := by
  apply pointsMap_ιk_injective p hR hinj G k
  have hcomm : (ιk p k).comp (reduceModPow R p R k) =
      (reduceModPow R p (O p R) k).comp (ιk p (R := R) (k + 1)) :=
    (reduceModPow_comp_mapModPow R p R (Algebra.ofId R (O p R)) k).symm
  rw [pointsMap_ιk_comp₀, ← AddMonoidHom.comp_apply, ← pointsMap_comp, hcomm, pointsMap_comp,
    AddMonoidHom.comp_apply, pointsMap_ιk_comp₀]
  exact G.pointsMap_reduceModPow_cpointsProj_succ (O p R) k x

noncomputable def x₀ : G.CPoints R := ⟨comp₀ p hR hinj G x hx, comp₀_compat p hR hinj G x hx⟩

theorem cpointsProj_x₀ (k : ℕ) : G.cpointsProj R k (x₀ p hR hinj G x hx) = comp₀ p hR hinj G x hx k := rfl

theorem cpointsMap_x₀ : G.cpointsMap (Algebra.ofId R (O p R)) (x₀ p hR hinj G x hx) = x := by
  refine cpointsProj_ext G (O p R) fun k => ?_
  rw [cpointsProj_cpointsMap, cpointsProj_x₀]
  exact pointsMap_ιk_comp₀ p hR hinj G x hx k

end X0

omit [FiniteDimensional ℚ_[p] K] in
include hR hinj in

theorem cpointsMap_ofId_injective : Function.Injective (G.cpointsMap (Algebra.ofId R (O p R))) := by
  intro y y' hyy'
  refine cpointsProj_ext G R fun k => pointsMap_ιk_injective p hR hinj G k ?_
  have := congrArg (G.cpointsProj (O p R) k) hyy'
  rwa [cpointsProj_cpointsMap, cpointsProj_cpointsMap] at this

end Main

end PDivDESCK
p2m_reactivate "P2MW.S_PDivisibleGroup_existsUnique_cpointsMap_ofId_eq_of_forall_smul_eq_of_forall_mem_range_iff.PDivDESCK"

open PDivDESCK in

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
    (hR : ∀ x : PadicAlgCl p, x ∈ Set.range (algebraMap R (PadicAlgCl p)) ↔ x ∈ K ∧ ‖x‖ ≤ 1)
    (hinj : Function.Injective (algebraMap R (PadicAlgCl p)))
    {h : ℕ} (G : PDivisibleGroup R p h)
    (x : G.CPoints (integralClosure R (PadicAlgCl p)))
    (hx : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (σ' : integralClosure R (PadicAlgCl p) ≃ₐ[R] integralClosure R (PadicAlgCl p)),
      (∀ a : integralClosure R (PadicAlgCl p),
          ((σ' a : integralClosure R (PadicAlgCl p)) : PadicAlgCl p) = σ a) →
      σ' • x = x) :
    ∃! x₀ : G.CPoints R,
      G.cpointsMap (Algebra.ofId R (integralClosure R (PadicAlgCl p))) x₀ = x := by
  exact ⟨x₀ p hR hinj G x hx, cpointsMap_x₀ p hR hinj G x hx, fun y hy =>
    cpointsMap_ofId_injective p hR hinj G (hy.trans (cpointsMap_x₀ p hR hinj G x hx).symm)⟩

end S_PDivisibleGroup_existsUnique_cpointsMap_ofId_eq_of_forall_smul_eq_of_forall_mem_range_iff
end P2MW
export P2MW.S_PDivisibleGroup_existsUnique_cpointsMap_ofId_eq_of_forall_smul_eq_of_forall_mem_range_iff (solution)

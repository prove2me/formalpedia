-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/377624af-6b2d-5c48-aec2-830b710eeac1

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_CompletedPoints
import Definitions.Def_PDivisibleGroup_PrimaryTorsion
import Theorems.Thm_PDivisibleGroup_exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff
import Theorems.Thm_PDivisibleGroup_CartierDuality_pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff
import Theorems.Thm_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one
import Theorems.Thm_PDivisibleGroup_exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff
import Theorems.Thm_PDivisibleGroup_CartierDuality_exists_points_tateModule_pairing_eq_pair
import Theorems.Thm_PDivisibleGroup_CartierDuality_eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed
import Theorems.Thm_PDivisibleGroup_bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv
import Theorems.Thm_CartierDual_basisPairing_eq_and_map_convMul_and_comp_and_transpose
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open PDivisibleGroup Filter Topology
open scoped TensorProduct

namespace PDivStep2R

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

section Base

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]

theorem ι_apply (c : O p R) : ι p R c = ((c : PadicAlgCl p) : ℂ_[p]) := rfl

def galR {σ : Gal p} {σ' : O p R ≃ₐ[R] O p R} (hσ : Restricts p σ σ') : K p ≃ₐ[R] K p :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun r => by
    have h1 := hσ (algebraMap R (O p R) r)
    rw [AlgEquiv.commutes] at h1
    exact h1.symm

theorem galR_apply {σ : Gal p} {σ' : O p R ≃ₐ[R] O p R} (hσ : Restricts p σ σ') (x : K p) : galR p hσ x = σ x := rfl

theorem norm_coe_p : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  exact (PadicAlgCl.norm_extends (p := p) (p : ℚ_[p])).trans (Padic.norm_p (p := p))

variable (hO : OK p R)

theorem norm_add_le_max (a b : ℂ_[p]) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := PadicComplex.isNonarchimedean p a b

include hO in
theorem norm_ι_le_one (c : O p R) : ‖ι p R c‖ ≤ 1 := by
  rw [ι_apply, PadicComplex.norm_extends]
  exact (hO (c : PadicAlgCl p)).mp c.2

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

include hO in
theorem mk_eq_one_iff_of_forall (c : O p R) :
    (∀ i : ℕ, Ideal.Quotient.mk (Ideal.span {(p : O p R) ^ i}) c = 1) ↔ c = 1 :=
  ⟨fun h => eq_of_forall_mk_eq p hO fun i => by rw [h i, map_one], fun h i => by rw [h, map_one]⟩

end Base

section Level

variable {R : Type} [CommRing R] {q hh : ℕ} {G G' : PDivisibleGroup R q hh} (D : G.CartierDuality G')
variable {L : Type} [CommRing L] [Algebra R L]

def dualPt (v : ℕ) (ψ : G'.Point L v) : CartierDual R (G.level v) →ₐ[R] L :=
  (Point.toAlgHom ψ).comp ((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] G'.level v)

theorem dualPt_apply (v : ℕ) (ψ : G'.Point L v) (φ : CartierDual R (G.level v)) :
    dualPt D v ψ φ = Point.toAlgHom ψ ((D.equiv v).symm φ) := rfl

abbrev bas (G : PDivisibleGroup R q hh) (v : ℕ) := Module.Free.chooseBasis R (G.level v)

theorem pair_eq (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v f ψ = ∑ i, (Point.toAlgHom f) (bas G v i) *
      dualPt D v ψ (CartierDual.ofDual R (G.level v) ((bas G v).coord i)) := by
  rw [CartierDuality.pair_def]; rfl

theorem pair_eq_conv (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v f ψ = ∑ i, (Point.toConv f) (bas G v i) *
      dualPt D v ψ (CartierDual.ofDual R (G.level v) ((bas G v).coord i)) := pair_eq D v f ψ

theorem pair_mul_left (v : ℕ) (f g : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v (f * g) ψ = D.pair L v f ψ * D.pair L v g ψ := by
  rw [pair_eq_conv, pair_eq_conv, pair_eq_conv]
  exact (CartierDual.basisPairing_eq_and_map_convMul_and_comp_and_transpose.{0,0,0,0,0,0,0,0}
    (bas G v) L).2.2.2.1 (Point.toConv f) (Point.toConv g) (dualPt D v ψ)

theorem dualPt_mul (v : ℕ) (ψ ψ' : G'.Point L v) :
    dualPt D v (ψ * ψ') = WithConv.ofConv (WithConv.toConv (dualPt D v ψ) * WithConv.toConv (dualPt D v ψ')) := by
  unfold dualPt
  exact AlgHom.convMul_comp_bialgHom_distrib (Point.toConv ψ) (Point.toConv ψ') _

theorem pair_mul_right (v : ℕ) (f : G.Point L v) (ψ ψ' : G'.Point L v) :
    D.pair L v f (ψ * ψ') = D.pair L v f ψ * D.pair L v f ψ' := by
  rw [pair_eq, pair_eq, pair_eq, dualPt_mul]
  exact (CartierDual.basisPairing_eq_and_map_convMul_and_comp_and_transpose.{0,0,0,0,0,0,0,0}
    (bas G v) L).2.2.2.2.1 (Point.toAlgHom f)
    (WithConv.toConv (dualPt D v ψ)) (WithConv.toConv (dualPt D v ψ'))

theorem pair_one_left (v : ℕ) (ψ : G'.Point L v) : D.pair L v 1 ψ = 1 := by
  rw [pair_eq_conv]
  exact (CartierDual.basisPairing_eq_and_map_convMul_and_comp_and_transpose.{0,0,0,0,0,0,0,0}
    (bas G v) L).2.2.2.2.2.1 (dualPt D v ψ)

theorem pair_pointMap {L' : Type} [CommRing L'] [Algebra R L'] (φ : L →ₐ[R] L')
    (v : ℕ) (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L' v (G.pointMap φ v f) (G'.pointMap φ v ψ) = φ (D.pair L v f ψ) := by
  rw [pair_eq, pair_eq]
  have key := (CartierDual.basisPairing_eq_and_map_convMul_and_comp_and_transpose.{0,0,0,0,0,0,0,0}
    (bas G v) L).2.1 φ (Point.toAlgHom f).toLinearMap
    ((dualPt D v ψ).toLinearMap.comp (CartierDual.ofDual R (G.level v)).toLinearMap)
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) key.symm
  rfl

theorem exists_point_of_nsmul_eq_zero (G : PDivisibleGroup R q hh) (v : ℕ) (z : G.Points L)
    (hz : (q ^ v) • z = 0) : ∃ f : G.Point L v, G.pointsMkAdd L v (Additive.ofMul f) = z := by
  obtain ⟨m, y, rfl⟩ := Points.exists_mkAdd G z
  set w := max m v
  have hy : G.pointsMkAdd L w (Additive.ofMul (G.pointInclLE L (le_max_left m v) y)) =
      G.pointsMkAdd L m (Additive.ofMul y) := G.pointsMkAdd_pointInclLE _ y
  rw [← hy] at hz ⊢
  set y' := G.pointInclLE L (le_max_left m v) y
  have hpow : y' ^ (q ^ v) = 1 := by
    apply G.pointsMkAdd_injective w
    change G.pointsMkAdd L w (Additive.ofMul (y' ^ q ^ v)) = G.pointsMkAdd L w (Additive.ofMul 1)
    rw [ofMul_pow, map_nsmul, hz, ofMul_one, map_zero]
  obtain ⟨x, hx⟩ := G.exists_pointInclLE_eq_of_pow_eq_one (le_max_right m v) y' hpow
  exact ⟨x, by rw [← hx, pointsMkAdd_pointInclLE]⟩

end Level

section Reductions

variable (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)]

abbrev maxI : Ideal (O p R) := (Ideal.span {(p : O p R)}).radical

theorem span_pow_succ_le_maxI (i : ℕ) : Ideal.span {(p : O p R) ^ (i + 1)} ≤ maxI p R := by
  refine (Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self (p : O p R) (Nat.succ_ne_zero i))).trans ?_
  exact Ideal.le_radical

abbrev kO : Type := O p R ⧸ maxI p R

def resQ (i : ℕ) : Oq p R (i + 1) →ₐ[R] kO p R := Ideal.Quotient.factorₐ R (span_pow_succ_le_maxI p R i)

theorem resQ_mk (i : ℕ) (s : O p R) : resQ p R i (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk (maxI p R) s := rfl

theorem resQ_comp_mkₐ (i : ℕ) :
    (resQ p R i).comp (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ (i + 1)})) = Ideal.Quotient.mkₐ R (maxI p R) := by
  refine AlgHom.ext fun s => ?_
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, resQ_mk, Ideal.Quotient.mkₐ_eq_mk]

theorem resQ_eq_zero_iff (i : ℕ) (x : Oq p R (i + 1)) : resQ p R i x = 0 ↔ IsNilpotent x := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [resQ_mk, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n * (i + 1), ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_mul]
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hn
    rw [← ht, mul_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rintro ⟨n, hn⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
    exact ⟨n, Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self (p : O p R) (Nat.succ_ne_zero i)) hn⟩

theorem resQ_eq_iff (i : ℕ) (x y : Oq p R (i + 1)) : resQ p R i x = resQ p R i y ↔ IsNilpotent (x - y) := by
  rw [← sub_eq_zero, ← map_sub, resQ_eq_zero_iff]

def factorLE {i j : ℕ} (hij : i ≤ j) : Oq p R j →ₐ[R] Oq p R i :=
  Ideal.Quotient.factorₐ R (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hij))

theorem factorLE_mk {i j : ℕ} (hij : i ≤ j) (s : O p R) : factorLE p R hij (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ s := rfl

theorem factorLE_self (i : ℕ) : factorLE p R (le_refl i) = AlgHom.id R _ := by
  refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun s => ?_)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, factorLE_mk, AlgHom.id_apply]

theorem factorLE_succ {i j : ℕ} (hij : i ≤ j) :
    factorLE p R (Nat.le_succ_of_le hij) = (factorLE p R hij).comp (reduceModPow R p (O p R) j) := by
  refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun s => ?_)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, factorLE_mk,
    reduceModPow_mk, factorLE_mk]

theorem resQ_comp_factorLE (i : ℕ) :
    (resQ p R 0).comp (factorLE p R (Nat.le_add_left 1 i : 1 ≤ i + 1)) = resQ p R i := by
  refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun s => ?_)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, factorLE_mk, resQ_mk,
    Ideal.Quotient.mkₐ_eq_mk, resQ_mk]

variable {R}

theorem maxI_le_comap (σ' : O p R ≃ₐ[R] O p R) : maxI p R ≤ (maxI p R).comap σ'.toAlgHom := by
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 hx
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hn
  refine Ideal.mem_comap.2 (Ideal.mem_radical_iff.2 ⟨n, Ideal.mem_span_singleton'.2 ⟨σ' t, ?_⟩⟩)
  change σ' t * (p : O p R) = (σ' x) ^ n
  rw [← map_pow, ← ht, map_mul, map_natCast]

def resAut (σ' : O p R ≃ₐ[R] O p R) : kO p R →ₐ[R] kO p R :=
  Ideal.quotientMapₐ (maxI p R) σ'.toAlgHom (maxI_le_comap p σ')

theorem resAut_mk (σ' : O p R ≃ₐ[R] O p R) (s : O p R) :
    resAut p σ' (Ideal.Quotient.mk (maxI p R) s) = Ideal.Quotient.mk (maxI p R) (σ' s) := rfl

theorem resQ_comp_mapModPow (σ' : O p R ≃ₐ[R] O p R) :
    (resQ p R 0).comp (mapModPow R p (O p R) σ'.toAlgHom 1) = (resAut p σ').comp (resQ p R 0) := by
  refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun s => ?_)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    mapModPow_mk, resQ_mk, resQ_mk, resAut_mk]
  rfl

end Reductions

section Integral

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
variable {h : ℕ} (G : PDivisibleGroup R p h)

theorem isIntegral_apply (w : ℕ) (z : G.Point (K p) w) (a : G.level w) : IsIntegral R (Point.toAlgHom z a) :=
  (Algebra.IsIntegral.isIntegral (R := R) a).map (Point.toAlgHom z)

def intg (w : ℕ) (z : G.Point (K p) w) : G.Point (O p R) w :=
  Point.ofAlgHom ((Point.toAlgHom z).codRestrict (O p R) (isIntegral_apply p G w z))

@[scoped simp] theorem pointMap_val_intg (w : ℕ) (z : G.Point (K p) w) : G.pointMap (O p R).val w (intg p G w z) = z :=
  Point.ext fun _ => rfl

@[scoped simp] theorem intg_pointMap_val (w : ℕ) (z : G.Point (O p R) w) : intg p G w (G.pointMap (O p R).val w z) = z :=
  Point.ext fun _ => Subtype.ext rfl

theorem pointMap_val_injective (w : ℕ) : Function.Injective (G.pointMap (O p R).val w) := fun z z' hzz' => by
  rw [← intg_pointMap_val p G w z, hzz', intg_pointMap_val]

theorem pointMap_val_bijective (w : ℕ) : Function.Bijective (G.pointMap (O p R).val w) :=
  ⟨pointMap_val_injective p G w, fun z => ⟨intg p G w z, pointMap_val_intg p G w z⟩⟩

def eqv (w : ℕ) : G.Point (O p R) w ≃* G.Point (K p) w :=
  MulEquiv.ofBijective (G.pointMap (O p R).val w) (pointMap_val_bijective p G w)

@[scoped simp] theorem eqv_apply (w : ℕ) (z : G.Point (O p R) w) : eqv p G w z = G.pointMap (O p R).val w z := rfl

theorem eqv_symm_apply (w : ℕ) (z : G.Point (K p) w) : (eqv p G w).symm z = intg p G w z := by
  apply (eqv p G w).injective
  rw [MulEquiv.apply_symm_apply, eqv_apply, pointMap_val_intg]

abbrev redO (w : ℕ) : G.Point (O p R) w →* G.Point (O p R ⧸ maxI p R) w :=
  G.pointMap (Ideal.Quotient.mkₐ R (maxI p R)) w

theorem redO_eq_one_iff (w : ℕ) (z : G.Point (O p R) w) :
    redO p G w z = 1 ↔ ∀ a : G.level w, Point.toAlgHom z a - algebraMap R (O p R) (Coalgebra.counit a) ∈ maxI p R := by
  constructor
  · intro hz a
    have h1 := DFunLike.congr_fun (congrArg Point.toAlgHom hz) a
    rw [toAlgHom_pointMap, AlgHom.comp_apply, Point.one_apply, Ideal.Quotient.mkₐ_eq_mk,
      IsScalarTower.algebraMap_apply R (O p R) (O p R ⧸ maxI p R), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq] at h1
    exact h1
  · intro hz
    refine Point.ext fun a => ?_
    rw [toAlgHom_pointMap, AlgHom.comp_apply, Point.one_apply, Ideal.Quotient.mkₐ_eq_mk,
      IsScalarTower.algebraMap_apply R (O p R) (O p R ⧸ maxI p R), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq]
    exact hz a

def H (w : ℕ) : Subgroup (G.Point (K p) w) :=
  (MonoidHom.ker (redO p G w)).comap (eqv p G w).symm.toMonoidHom

theorem mem_H_iff (w : ℕ) (z : G.Point (K p) w) : z ∈ H p G w ↔ redO p G w (intg p G w z) = 1 := by
  rw [H, Subgroup.mem_comap, MonoidHom.mem_ker]
  change redO p G w ((eqv p G w).symm z) = 1 ↔ _
  rw [eqv_symm_apply]

theorem pointMap_val_mem_H_iff (w : ℕ) (z : G.Point (O p R) w) :
    G.pointMap (O p R).val w z ∈ H p G w ↔ redO p G w z = 1 := by
  rw [mem_H_iff, intg_pointMap_val]

theorem mem_H_of_pointIncl_mem (w : ℕ) (z : G.Point (K p) w) (hz : G.pointIncl (K p) w z ∈ H p G (w + 1)) :
    z ∈ H p G w := by
  rw [mem_H_iff] at hz ⊢
  have h1 : intg p G (w + 1) (G.pointIncl (K p) w z) = G.pointIncl (O p R) w (intg p G w z) := by
    apply pointMap_val_injective p G (w + 1)
    rw [pointMap_val_intg, pointMap_pointIncl, pointMap_val_intg]
  rw [h1, pointMap_pointIncl] at hz
  exact G.pointIncl_injective w (by rw [hz, map_one])

abbrev redQ (i w : ℕ) : G.Point (Oq p R (i + 1)) w →* G.Point (kO p R) w := G.pointMap (resQ p R i) w

theorem redQ_eq_one_iff (i w : ℕ) (f : G.Point (Oq p R (i + 1)) w) :
    redQ p G i w f = 1 ↔
      ∀ a : G.level w, IsNilpotent (Point.toAlgHom f a - algebraMap R (Oq p R (i + 1)) (Coalgebra.counit a)) := by
  constructor
  · intro hf a
    have h1 := DFunLike.congr_fun (congrArg Point.toAlgHom hf) a
    rw [toAlgHom_pointMap, AlgHom.comp_apply, Point.one_apply, ← (resQ p R i).commutes, resQ_eq_iff] at h1
    exact h1
  · intro hf
    refine Point.ext fun a => ?_
    rw [toAlgHom_pointMap, AlgHom.comp_apply, Point.one_apply, ← (resQ p R i).commutes, resQ_eq_iff]
    exact hf a

abbrev redPts (i : ℕ) : G.Points (Oq p R (i + 1)) →+ G.Points (kO p R) := G.pointsMap (resQ p R i)

theorem redPts_pointsMkAdd_eq_zero_iff (i w : ℕ) (f : G.Point (Oq p R (i + 1)) w) :
    redPts p G i (G.pointsMkAdd _ w (Additive.ofMul f)) = 0 ↔ redQ p G i w f = 1 := by
  rw [pointsMap_pointsMkAdd]
  have h0 : (0 : G.Points (kO p R)) = G.pointsMkAdd (kO p R) w (Additive.ofMul 1) := by
    rw [ofMul_one, map_zero]
  rw [h0, pointsMkAdd_eq_pointsMkAdd_iff]

def G1 : AddSubgroup (G.CPoints (O p R)) := (AddMonoidHom.ker (redPts p G 0)).comap (G.cpointsProj (O p R) 1)

theorem mem_G1_iff (X : G.CPoints (O p R)) : X ∈ G1 p G ↔ redPts p G 0 (G.cpointsProj (O p R) 1 X) = 0 := Iff.rfl

theorem mem_G1_iff_forall (X : G.CPoints (O p R)) :
    X ∈ G1 p G ↔ ∀ (w : ℕ) (f : G.Point (Oq p R 1) w),
      G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (O p R) 1 X →
      ∀ a : G.level w, IsNilpotent (Point.toAlgHom f a - algebraMap R (Oq p R 1) (Coalgebra.counit a)) := by
  rw [mem_G1_iff]
  constructor
  · intro hX w f hf
    rw [← redQ_eq_one_iff, ← redPts_pointsMkAdd_eq_zero_iff, hf]
    exact hX
  · intro hX
    obtain ⟨w, f, hf⟩ := Points.exists_mkAdd G (G.cpointsProj (O p R) 1 X)
    rw [← hf, redPts_pointsMkAdd_eq_zero_iff, redQ_eq_one_iff]
    exact hX w f hf

end Integral

section G1Props

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
variable {h : ℕ} (G : PDivisibleGroup R p h)

theorem pointsMap_factorLE_cpointsProj (X : G.CPoints (O p R)) {i j : ℕ} (hij : i ≤ j) :
    G.pointsMap (factorLE p R hij) (G.cpointsProj (O p R) j X) = G.cpointsProj (O p R) i X := by
  induction hij with
  | refl => rw [factorLE_self, pointsMap_id]; rfl
  | step hij ih =>
      rw [factorLE_succ p R hij, pointsMap_comp, AddMonoidHom.comp_apply,
        pointsMap_reduceModPow_cpointsProj_succ, ih]

theorem redQ_eq_one_of_mem_G1 {X : G.CPoints (O p R)} (hX : X ∈ G1 p G) (i w : ℕ) (f : G.Point (Oq p R (i + 1)) w)
    (hf : G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (O p R) (i + 1) X) : redQ p G i w f = 1 := by
  rw [← redPts_pointsMkAdd_eq_zero_iff, hf]
  change G.pointsMap (resQ p R i) (G.cpointsProj (O p R) (i + 1) X) = 0
  rw [← resQ_comp_factorLE, pointsMap_comp, AddMonoidHom.comp_apply, pointsMap_factorLE_cpointsProj]
  exact hX

theorem isNilpotent_of_mem_G1 {X : G.CPoints (O p R)} (hX : X ∈ G1 p G) (i w : ℕ) (f : G.Point (Oq p R (i + 1)) w)
    (hf : G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (O p R) (i + 1) X) (a : G.level w) :
    IsNilpotent (Point.toAlgHom f a - algebraMap R (Oq p R (i + 1)) (Coalgebra.counit a)) :=
  (redQ_eq_one_iff p G i w f).1 (redQ_eq_one_of_mem_G1 p G hX i w f hf) a

theorem toCPoints_mem_G1 (v : ℕ) (z : G.Point (O p R) v) (hz : redO p G v z = 1) :
    G.toCPoints (O p R) (G.pointsMkAdd (O p R) v (Additive.ofMul z)) ∈ G1 p G := by
  rw [mem_G1_iff, cpointsProj_toCPoints, ← AddMonoidHom.comp_apply, ← pointsMap_comp, resQ_comp_mkₐ,
    pointsMap_pointsMkAdd]
  change G.pointsMkAdd (kO p R) v (Additive.ofMul (redO p G v z)) = 0
  rw [hz, ofMul_one, map_zero]

theorem smul_mem_G1 (σ' : O p R ≃ₐ[R] O p R) {X : G.CPoints (O p R)} (hX : X ∈ G1 p G) : σ' • X ∈ G1 p G := by
  rw [mem_G1_iff, CPoints.smul_def, cpointsProj_cpointsMap, ← AddMonoidHom.comp_apply, ← pointsMap_comp,
    resQ_comp_mapModPow, pointsMap_comp, AddMonoidHom.comp_apply]
  rw [mem_G1_iff] at hX
  change G.pointsMap (resAut p σ') (redPts p G 0 (G.cpointsProj (O p R) 1 X)) = 0
  rw [hX, map_zero]

end G1Props

section TatePlumbing

variable {M N : Type} [AddCommGroup M] [AddCommGroup N]

def tmap (φ : M →+ N) : TateModule p M →ₗ[ℤ_[p]] TateModule p N where
  toFun x := ⟨fun n => φ ((x : ℕ → M) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero], by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    change φ (((x + y : TateModule p M) : ℕ → M) n) = φ ((x : ℕ → M) n) + φ ((y : ℕ → M) n)
    rw [AddSubgroup.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    change φ (((a • x : TateModule p M) : ℕ → M) n) = ((a • _ : TateModule p N) : ℕ → N) n
    rw [TateModule.smul_apply, TateModule.smul_apply, map_zsmul])

@[scoped simp] theorem tmap_apply (φ : M →+ N) (x : TateModule p M) (n : ℕ) :
    ((tmap p φ x : TateModule p N) : ℕ → N) n = φ ((x : ℕ → M) n) := rfl

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
variable {h : ℕ} {G G' : PDivisibleGroup R p h}
variable (G')

def eT : TateModule p (G'.Points (O p R)) ≃ₗ[ℤ_[p]] TateModule p (G'.Points (K p)) :=
  (G'.bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv (K p)).2.2.2.choose

theorem eT_apply (x : TateModule p (G'.Points (O p R))) (n : ℕ) :
    ((eT p G' x : TateModule p (G'.Points (K p))) : ℕ → G'.Points (K p)) n =
      G'.pointsMap (O p R).val ((x : ℕ → G'.Points (O p R)) n) :=
  (G'.bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv (K p)).2.2.2.choose_spec.1 x n

abbrev yO (y : TateModule p (G'.Points (K p))) : TateModule p (G'.Points (O p R)) := (eT p G').symm y

theorem pointsMap_val_yO (y : TateModule p (G'.Points (K p))) (n : ℕ) :
    G'.pointsMap (O p R).val ((yO p G' y : ℕ → G'.Points (O p R)) n) = (y : ℕ → G'.Points (K p)) n := by
  rw [← eT_apply, LinearEquiv.apply_symm_apply]

def yqLin (i : ℕ) : TateModule p (G'.Points (K p)) →ₗ[ℤ_[p]] TateModule p (G'.Points (Oq p R i)) :=
  (tmap p (G'.pointsMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ i})))).comp (eT p G').symm.toLinearMap

abbrev yq (i : ℕ) (y : TateModule p (G'.Points (K p))) : TateModule p (G'.Points (Oq p R i)) := yqLin p G' i y

theorem yq_apply (i : ℕ) (y : TateModule p (G'.Points (K p))) (n : ℕ) :
    ((yq p G' i y : TateModule p (G'.Points (Oq p R i))) : ℕ → G'.Points (Oq p R i)) n =
      G'.pointsMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ i})) ((yO p G' y : ℕ → G'.Points (O p R)) n) :=
  rfl

theorem rep_iff (y : TateModule p (G'.Points (K p))) (w : ℕ) (ψ : G'.Point (O p R) w) :
    G'.pointsMkAdd (K p) w (Additive.ofMul (G'.pointMap (O p R).val w ψ)) = (y : ℕ → G'.Points (K p)) w ↔
      G'.pointsMkAdd (O p R) w (Additive.ofMul ψ) = (yO p G' y : ℕ → G'.Points (O p R)) w := by
  rw [← pointsMap_pointsMkAdd, ← pointsMap_val_yO]
  exact (G'.pointsMap_injective_of_injective _ Subtype.val_injective).eq_iff

theorem pointsMkAdd_pointMap_mk_of_rep (i : ℕ) (y : TateModule p (G'.Points (K p))) (w : ℕ) (ψ : G'.Point (O p R) w)
    (hψ : G'.pointsMkAdd (K p) w (Additive.ofMul (G'.pointMap (O p R).val w ψ)) = (y : ℕ → G'.Points (K p)) w) :
    G'.pointsMkAdd (Oq p R i) w (Additive.ofMul (G'.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ i})) w ψ)) =
      ((yq p G' i y : TateModule p (G'.Points (Oq p R i))) : ℕ → G'.Points (Oq p R i)) w := by
  rw [yq_apply, ← (rep_iff p G' y w ψ).1 hψ, pointsMap_pointsMkAdd]

def liftO (y : TateModule p (G'.Points (K p))) (w : ℕ) : G'.Point (O p R) w :=
  (exists_point_of_nsmul_eq_zero G' w ((yO p G' y : ℕ → G'.Points (O p R)) w)
    (by rw [← natCast_zsmul]; exact TateModule.torsion _ w)).choose

theorem pointsMkAdd_liftO (y : TateModule p (G'.Points (K p))) (w : ℕ) :
    G'.pointsMkAdd (O p R) w (Additive.ofMul (liftO p G' y w)) = (yO p G' y : ℕ → G'.Points (O p R)) w :=
  (exists_point_of_nsmul_eq_zero G' w ((yO p G' y : ℕ → G'.Points (O p R)) w)
    (by rw [← natCast_zsmul]; exact TateModule.torsion _ w)).choose_spec

theorem rep_liftO (y : TateModule p (G'.Points (K p))) (w : ℕ) :
    G'.pointsMkAdd (K p) w (Additive.ofMul (G'.pointMap (O p R).val w (liftO p G' y w))) = (y : ℕ → G'.Points (K p)) w :=
  (rep_iff p G' y w _).2 (pointsMkAdd_liftO p G' y w)

end TatePlumbing

section Values

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
variable {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')

def αq (i : ℕ) : G.Points (Oq p R i) →+
    (TateModule p (G'.Points (Oq p R i)) →ₗ[ℤ_[p]] PrimaryTorsion p (Additive (Oq p R i)ˣ)) :=
  (D.exists_points_tateModule_pairing_eq_pair (Oq p R i)).choose

theorem αq_level (i v : ℕ) (f : G.Point (Oq p R i) v) (t : TateModule p (G'.Points (Oq p R i))) (ψ : G'.Point (Oq p R i) v)
    (hψ : G'.pointsMkAdd (Oq p R i) v (Additive.ofMul ψ) = (t : ℕ → G'.Points (Oq p R i)) v) :
    ((Additive.toMul ((αq p D i (G.pointsMkAdd (Oq p R i) v (Additive.ofMul f)) t :
        PrimaryTorsion p (Additive (Oq p R i)ˣ)) : Additive (Oq p R i)ˣ) : (Oq p R i)ˣ) : Oq p R i) = D.pair (Oq p R i) v f ψ := by
  have hspec := (D.exists_points_tateModule_pairing_eq_pair (Oq p R i)).choose_spec.1 v f t ψ hψ
  exact hspec

def cvAdd (y : TateModule p (G'.Points (K p))) (i : ℕ) : G.CPoints (O p R) →+ Additive (Oq p R i)ˣ :=
  (PrimaryTorsion p (Additive (Oq p R i)ˣ)).subtype.comp
    (((LinearMap.applyₗ (yq p G' i y)).toAddMonoidHom.comp (αq p D i)).comp (G.cpointsProj (O p R) i))

theorem cvAdd_apply (y : TateModule p (G'.Points (K p))) (i : ℕ) (Y : G.CPoints (O p R)) :
    cvAdd p D y i Y = ((αq p D i (G.cpointsProj (O p R) i Y) (yq p G' i y) : PrimaryTorsion p (Additive (Oq p R i)ˣ)) :
      Additive (Oq p R i)ˣ) := rfl

def cvu (Y : G.CPoints (O p R)) (y : TateModule p (G'.Points (K p))) (i : ℕ) : (Oq p R i)ˣ :=
  Additive.toMul (cvAdd p D y i Y)

abbrev cv (Y : G.CPoints (O p R)) (y : TateModule p (G'.Points (K p))) (i : ℕ) : Oq p R i := (cvu p D Y y i : Oq p R i)

theorem cv_eq_pair (Y : G.CPoints (O p R)) (y : TateModule p (G'.Points (K p))) (i w : ℕ)
    (f : G.Point (Oq p R i) w) (hf : G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (O p R) i Y)
    (ψ : G'.Point (O p R) w)
    (hψ : G'.pointsMkAdd (K p) w (Additive.ofMul (G'.pointMap (O p R).val w ψ)) = (y : ℕ → G'.Points (K p)) w) :
    cv p D Y y i = D.pair (Oq p R i) w f (G'.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ i})) w ψ) := by
  have h1 := αq_level p D i w f (yq p G' i y) _ (pointsMkAdd_pointMap_mk_of_rep p G' i y w ψ hψ)
  rw [hf] at h1
  exact h1

theorem cvu_add_left (Y Y' : G.CPoints (O p R)) (y : TateModule p (G'.Points (K p))) (i : ℕ) :
    cvu p D (Y + Y') y i = cvu p D Y y i * cvu p D Y' y i :=
  congrArg Additive.toMul (map_add (cvAdd p D y i) Y Y')

theorem cvu_add_right (Y : G.CPoints (O p R)) (y y' : TateModule p (G'.Points (K p))) (i : ℕ) :
    cvu p D Y (y + y') i = cvu p D Y y i * cvu p D Y y' i := by
  have h1 : yq p G' i (y + y') = yq p G' i y + yq p G' i y' := map_add (yqLin p G' i) y y'
  have h2 := map_add (αq p D i (G.cpointsProj (O p R) i Y)) (yq p G' i y) (yq p G' i y')
  rw [← h1] at h2
  have h3 := congrArg (fun t : PrimaryTorsion p (Additive (Oq p R i)ˣ) => Additive.toMul (t : Additive (Oq p R i)ˣ)) h2
  exact h3

theorem cvu_zero_left (y : TateModule p (G'.Points (K p))) (i : ℕ) : cvu p D 0 y i = 1 :=
  congrArg Additive.toMul (map_zero (cvAdd p D y i))

theorem cvu_neg_left (Y : G.CPoints (O p R)) (y : TateModule p (G'.Points (K p))) (i : ℕ) :
    cvu p D (-Y) y i = (cvu p D Y y i)⁻¹ :=
  congrArg Additive.toMul (map_neg (cvAdd p D y i) Y)

theorem cvu_sub_left (Y Y' : G.CPoints (O p R)) (y : TateModule p (G'.Points (K p))) (i : ℕ) :
    cvu p D (Y - Y') y i = cvu p D Y y i * (cvu p D Y' y i)⁻¹ := by
  rw [sub_eq_add_neg, cvu_add_left, cvu_neg_left]

theorem cvu_nsmul_left (n : ℕ) (Y : G.CPoints (O p R)) (y : TateModule p (G'.Points (K p))) (i : ℕ) :
    cvu p D (n • Y) y i = cvu p D Y y i ^ n :=
  congrArg Additive.toMul (map_nsmul (cvAdd p D y i) n Y)

theorem cvu_psmul_right (Y : G.CPoints (O p R)) (y : TateModule p (G'.Points (K p))) (i : ℕ) :
    cvu p D Y ((p : ℤ_[p]) • y) i = cvu p D Y y i ^ p := by
  have h1 : yq p G' i ((p : ℤ_[p]) • y) = (p : ℤ_[p]) • yq p G' i y := map_smul (yqLin p G' i) _ y
  have h2 := map_smul (αq p D i (G.cpointsProj (O p R) i Y)) (p : ℤ_[p]) (yq p G' i y)
  rw [← h1, PrimaryTorsion.natCast_smul_eq_nsmul] at h2
  have h3 := congrArg (fun t : PrimaryTorsion p (Additive (Oq p R i)ˣ) => Additive.toMul (t : Additive (Oq p R i)ˣ)) h2
  simp only [AddSubgroup.coe_nsmul, toMul_nsmul] at h3
  exact h3

theorem reduceModPow_cv (Y : G.CPoints (O p R)) (y : TateModule p (G'.Points (K p))) (i : ℕ) :
    reduceModPow R p (O p R) i (cv p D Y y (i + 1)) = cv p D Y y i := by
  obtain ⟨w, f, hf⟩ := Points.exists_mkAdd G (G.cpointsProj (O p R) (i + 1) Y)
  have hf' : G.pointsMkAdd _ w (Additive.ofMul (G.pointMap (reduceModPow R p (O p R) i) w f)) =
      G.cpointsProj (O p R) i Y := by
    rw [← pointsMap_pointsMkAdd, hf, pointsMap_reduceModPow_cpointsProj_succ]
  rw [cv_eq_pair p D Y y (i + 1) w f hf (liftO p G' y w) (rep_liftO p G' y w),
    cv_eq_pair p D Y y i w _ hf' (liftO p G' y w) (rep_liftO p G' y w), ← pair_pointMap]
  congr 1

def KerA (Y : G.CPoints (O p R)) : Prop := ∀ (y : TateModule p (G'.Points (K p))) (i : ℕ), cvu p D Y y i = 1

theorem KerA.add {Y Y' : G.CPoints (O p R)} (hY : KerA p D Y) (hY' : KerA p D Y') : KerA p D (Y + Y') :=
  fun y i => by rw [cvu_add_left, hY y i, hY' y i, one_mul]

theorem KerA.sub {Y Y' : G.CPoints (O p R)} (hY : KerA p D Y) (hY' : KerA p D Y') : KerA p D (Y - Y') :=
  fun y i => by rw [cvu_sub_left, hY y i, hY' y i, inv_one, one_mul]

theorem KerA.nsmul {Y : G.CPoints (O p R)} (hY : KerA p D Y) (n : ℕ) : KerA p D (n • Y) :=
  fun y i => by rw [cvu_nsmul_left, hY y i, one_pow]

theorem KerA.zero : KerA p D (0 : G.CPoints (O p R)) := fun y i => cvu_zero_left p D y i

theorem restricts_symm {σ : Gal p} {σ' : O p R ≃ₐ[R] O p R} (hσ : Restricts p σ σ') : Restricts p σ.symm σ'.symm := by
  intro a
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, ← hσ, AlgEquiv.apply_symm_apply]

theorem mapModPow_symm_comp (σ' : O p R ≃ₐ[R] O p R) (i : ℕ) :
    (mapModPow R p (O p R) σ'.toAlgHom i).comp (mapModPow R p (O p R) σ'.symm.toAlgHom i) = AlgHom.id R _ := by
  rw [← mapModPow_comp, show σ'.toAlgHom.comp σ'.symm.toAlgHom = AlgHom.id R _
    from AlgHom.ext fun a => σ'.apply_symm_apply a, mapModPow_id]

theorem mapModPow_comp_symm (σ' : O p R ≃ₐ[R] O p R) (i : ℕ) :
    (mapModPow R p (O p R) σ'.symm.toAlgHom i).comp (mapModPow R p (O p R) σ'.toAlgHom i) = AlgHom.id R _ := by
  rw [← mapModPow_comp, show σ'.symm.toAlgHom.comp σ'.toAlgHom = AlgHom.id R _
    from AlgHom.ext fun a => σ'.symm_apply_apply a, mapModPow_id]

theorem pointMap_val_pointMap_symm {σ : Gal p} {σ' : O p R ≃ₐ[R] O p R} (hσ : Restricts p σ σ') (w : ℕ)
    (ψ : G'.Point (O p R) w) :
    G'.pointMap (O p R).val w (G'.pointMap σ'.symm.toAlgHom w ψ) =
      G'.pointMap (galR p (restricts_symm p hσ) : K p →ₐ[R] K p) w
        (G'.pointMap (O p R).val w ψ) := by
  refine Point.ext fun a => ?_
  rw [toAlgHom_pointMap, toAlgHom_pointMap, toAlgHom_pointMap, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply]
  exact restricts_symm p hσ _

theorem KerA.map (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R) (hσ : Restricts p σ σ') {Y : G.CPoints (O p R)}
    (hY : KerA p D Y) : KerA p D (G.cpointsMap σ'.toAlgHom Y) := by
  intro y i
  apply Units.ext

  obtain ⟨w, f, hf⟩ := Points.exists_mkAdd G (G.cpointsProj (O p R) i (G.cpointsMap σ'.toAlgHom Y))
  have hψ := rep_liftO p G' y w

  have hf₀rep : G.pointsMkAdd _ w (Additive.ofMul (G.pointMap (mapModPow R p (O p R) σ'.symm.toAlgHom i) w f)) =
      G.cpointsProj (O p R) i Y := by
    have h1 : G.cpointsProj (O p R) i Y = G.pointsMap (mapModPow R p (O p R) σ'.symm.toAlgHom i)
        (G.cpointsProj (O p R) i (G.cpointsMap σ'.toAlgHom Y)) := by
      have e1 := DFunLike.congr_fun (G.pointsMap_comp (mapModPow R p (O p R) σ'.toAlgHom i)
        (mapModPow R p (O p R) σ'.symm.toAlgHom i)) (G.cpointsProj (O p R) i Y)
      rw [mapModPow_comp_symm, pointsMap_id, AddMonoidHom.id_apply, AddMonoidHom.comp_apply] at e1
      rw [cpointsProj_cpointsMap]
      exact e1
    rw [h1, ← hf, pointsMap_pointsMkAdd]

  have hψ₀rep : G'.pointsMkAdd (K p) w (Additive.ofMul (G'.pointMap (O p R).val w
      (G'.pointMap σ'.symm.toAlgHom w (liftO p G' y w)))) =
      ((G'.tateModuleRep (K p) (galR p (restricts_symm p hσ)) y : TateModule p (G'.Points (K p))) :
        ℕ → G'.Points (K p)) w := by
    rw [pointMap_val_pointMap_symm p hσ, tateModuleRep_apply, ← Points.smul_pointsMkAdd, hψ]

  have h1 : cv p D Y (G'.tateModuleRep (K p) (galR p (restricts_symm p hσ)) y) i = 1 := by
    change ((cvu p D Y (G'.tateModuleRep (K p) (galR p (restricts_symm p hσ)) y) i : (Oq p R i)ˣ) : Oq p R i) = 1
    rw [hY _ i, Units.val_one]
  rw [cv_eq_pair p D Y _ i w _ hf₀rep _ hψ₀rep] at h1

  have hf' : f = G.pointMap (mapModPow R p (O p R) σ'.toAlgHom i) w
      (G.pointMap (mapModPow R p (O p R) σ'.symm.toAlgHom i) w f) := by
    have e1 := DFunLike.congr_fun (G.pointMap_comp (mapModPow R p (O p R) σ'.symm.toAlgHom i)
      (mapModPow R p (O p R) σ'.toAlgHom i) w) f
    rw [mapModPow_symm_comp, pointMap_id, MonoidHom.id_apply, MonoidHom.comp_apply] at e1
    exact e1
  have hψ' : G'.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ i})) w (liftO p G' y w) =
      G'.pointMap (mapModPow R p (O p R) σ'.toAlgHom i) w
        (G'.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ i})) w
          (G'.pointMap σ'.symm.toAlgHom w (liftO p G' y w))) := by
    refine Point.ext fun a => ?_
    simp only [toAlgHom_pointMap, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, mapModPow_mk]
    change _ = Ideal.Quotient.mk _ (σ' (σ'.symm (Point.toAlgHom (liftO p G' y w) a)))
    rw [AlgEquiv.apply_symm_apply]
  change cv p D (G.cpointsMap σ'.toAlgHom Y) y i = 1
  rw [cv_eq_pair p D _ y i w f hf _ hψ, hf', hψ', pair_pointMap, h1, map_one]

theorem KerA.smul (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R) (hσ : Restricts p σ σ') {Y : G.CPoints (O p R)}
    (hY : KerA p D Y) : KerA p D (σ' • Y) := by
  rw [CPoints.smul_def]
  exact KerA.map p D σ σ' hσ hY

end Values

section Torsion

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
variable (hO : OK p R)
variable {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')

include D in

theorem exists_tate_of_point_one (ψ : G'.Point (K p) 1) :
    ∃ y : TateModule p (G'.Points (K p)), (y : ℕ → G'.Points (K p)) 1 = G'.pointsMkAdd (K p) 1 (Additive.ofMul ψ) := by
  have key := (D.mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one (K p)).2 (fun w => ⊥)
    (fun w z hz => by
      rw [Subgroup.mem_bot] at hz ⊢
      exact G.pointIncl_injective w (by rw [hz, map_one])) ψ
    (fun z hz => by rw [Subgroup.mem_bot] at hz; rw [hz, pair_one_left])
  obtain ⟨y, hy, -⟩ := key
  exact ⟨y, hy⟩

include hO in

theorem eq_zero_of_p_nsmul_eq_zero (Y : G.CPoints (O p R)) (hY : p • Y = 0) (hK : KerA p D Y) : Y = 0 := by
  obtain ⟨t, ht⟩ := G.exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff p hO 1 Y (by rw [pow_one]; exact hY)

  have hpair : ∀ ψ : G'.Point (O p R) 1, D.pair (O p R) 1 t ψ = 1 := by
    intro ψ
    obtain ⟨y, hy⟩ := exists_tate_of_point_one p D (G'.pointMap (O p R).val 1 ψ)
    refine (mk_eq_one_iff_of_forall p hO _).1 fun i => ?_
    have hrep : G.pointsMkAdd _ 1 (Additive.ofMul (G.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ i})) 1 t)) =
        G.cpointsProj (O p R) i Y := by
      rw [← ht, cpointsProj_toCPoints, pointsMap_pointsMkAdd]
    have h1 := cv_eq_pair p D Y y i 1 _ hrep ψ hy.symm
    rw [pair_pointMap, Ideal.Quotient.mkₐ_eq_mk] at h1
    rw [← h1]
    change ((cvu p D Y y i : (Oq p R i)ˣ) : Oq p R i) = 1
    rw [hK y i, Units.val_one]

  have hperf := (D.eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed (K p) 1).1
    (G.pointMap (O p R).val 1 t) (fun ψK => by
      rw [← pointMap_val_intg p G' 1 ψK, pair_pointMap, hpair]; rfl)
  have ht1 : t = 1 := pointMap_val_injective p G 1 (by rw [hperf, map_one])
  rw [← ht, ht1, ofMul_one, map_zero, map_zero]

include hO in

theorem eq_zero_of_pow_nsmul_eq_zero (k : ℕ) : ∀ (Y : G.CPoints (O p R)), p ^ k • Y = 0 → KerA p D Y → Y = 0 := by
  induction k with
  | zero => intro Y hY _; rwa [pow_zero, one_smul] at hY
  | succ k ih =>
      intro Y hY hK
      have h1 : p • (p ^ k • Y) = 0 := by rw [← mul_nsmul, ← pow_succ, hY]
      have h2 : p ^ k • Y = 0 := eq_zero_of_p_nsmul_eq_zero p hO D _ h1 (hK.nsmul p D (p ^ k))
      exact ih Y h2 hK

end Torsion

section Scalar

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
variable (hO : OK p R)

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

theorem exists_coe_eq_of_pow_eq_one (ℓ : ℂ_[p]) (hℓ : ℓ ^ p = 1) : ∃ r : K p, (r : ℂ_[p]) = ℓ := by
  set F : Polynomial (K p) := Polynomial.X ^ p - 1 with hF
  have hFsplit : F.Splits := IsAlgClosed.splits F
  have hF0 : F ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (Fact.out : p.Prime).pos 1
  have hprod := hFsplit.eq_prod_roots
  have hlc : F.leadingCoeff = 1 := by
    rw [hF]; exact Polynomial.monic_X_pow_sub_C 1 (Fact.out : p.Prime).ne_zero

  have heval : Polynomial.eval₂ (algebraMap (K p) ℂ_[p]) ℓ F = 0 := by
    rw [hF, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, hℓ, sub_self]
  rw [hprod, hlc, map_one, one_mul, Polynomial.eval₂_multiset_prod, Multiset.prod_eq_zero_iff,
    Multiset.mem_map] at heval
  obtain ⟨q, hq, hq0⟩ := heval
  rw [Multiset.mem_map] at hq
  obtain ⟨r, -, rfl⟩ := hq
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at hq0
  exact ⟨r, hq0.symm⟩

include hO in

theorem exists_root_of_unity (u : ∀ j : ℕ, Oq p R j)
    (hcompat : ∀ j, reduceModPow R p (O p R) j (u (j + 1)) = u j) (hpow : ∀ j, u j ^ p = 1) :
    ∃ ζ : O p R, ζ ^ p = 1 ∧ ∀ j, u j = Ideal.Quotient.mk _ ζ := by

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
  have hℓpow : ℓ ^ p = 1 := by
    rw [← sub_eq_zero]
    refine eq_zero_of_norm_le_pow p _ fun j => ?_
    have h1 : ℓ ^ p - 1 = (ℓ ^ p - ι p R (c j) ^ p) + ι p R (c j ^ p - 1) := by
      rw [map_sub, map_pow, map_one]; abel
    have h2 : c j ^ p - 1 ∈ Ideal.span {(p : O p R) ^ j} := by
      rw [← Ideal.Quotient.eq, map_pow, hc j, hpow j, map_one]
    rw [h1]
    refine (norm_add_le_max p _ _).trans (max_le ?_ (norm_ι_le_of_mem_span p hO j h2))
    exact (norm_pow_sub_pow_le p _ _ hℓ1 (norm_ι_le_one p hO _) p).trans (hℓj j)

  obtain ⟨r, hr⟩ := exists_coe_eq_of_pow_eq_one p ℓ hℓpow
  have hrn : ‖r‖ ≤ 1 := by rw [← PadicComplex.norm_extends, hr]; exact hℓ1
  have hrint : IsIntegral R r := (hO r).mpr hrn
  refine ⟨⟨r, hrint⟩, ?_, fun j => ?_⟩
  · apply ι_injective p
    rw [map_pow, ι_apply, map_one]
    change (r : ℂ_[p]) ^ p = 1
    rw [hr, hℓpow]
  · rw [← hc j, Ideal.Quotient.eq]
    refine mem_span_of_norm_ι_le p hO j _ ?_
    rw [map_sub, ι_apply]
    change ‖ι p R (c j) - ((r : K p) : ℂ_[p])‖ ≤ _
    rw [hr, norm_sub_rev]
    exact hℓj j

end Scalar

section Root

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
variable (hO : OK p R)
variable {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable {X X' : G.CPoints (O p R)}

theorem cv_root_pow (hX' : p • X' = X) (hK : KerA p D X) (y : TateModule p (G'.Points (K p))) (j : ℕ) :
    cv p D X' y j ^ p = 1 := by
  change ((cvu p D X' y j : (Oq p R j)ˣ) : Oq p R j) ^ p = 1
  rw [← Units.val_pow_eq_pow_val, ← cvu_nsmul_left, hX', hK y j, Units.val_one]

def ζ (hX' : p • X' = X) (hK : KerA p D X) (y : TateModule p (G'.Points (K p))) : O p R :=
  (exists_root_of_unity p hO (fun j => cv p D X' y j) (fun j => reduceModPow_cv p D X' y j)
    (fun j => cv_root_pow p D hX' hK y j)).choose

theorem ζ_pow (hX' : p • X' = X) (hK : KerA p D X) (y : TateModule p (G'.Points (K p))) :
    ζ p hO D hX' hK y ^ p = 1 :=
  (exists_root_of_unity p hO (fun j => cv p D X' y j) (fun j => reduceModPow_cv p D X' y j)
    (fun j => cv_root_pow p D hX' hK y j)).choose_spec.1

theorem cv_eq_mk_ζ (hX' : p • X' = X) (hK : KerA p D X) (y : TateModule p (G'.Points (K p))) (j : ℕ) :
    cv p D X' y j = Ideal.Quotient.mk _ (ζ p hO D hX' hK y) :=
  (exists_root_of_unity p hO (fun j => cv p D X' y j) (fun j => reduceModPow_cv p D X' y j)
    (fun j => cv_root_pow p D hX' hK y j)).choose_spec.2 j

theorem ζ_ne_zero (hX' : p • X' = X) (hK : KerA p D X) (y : TateModule p (G'.Points (K p))) :
    ζ p hO D hX' hK y ≠ 0 := by
  intro h0
  have := ζ_pow p hO D hX' hK y
  rw [h0, zero_pow (Fact.out : p.Prime).ne_zero] at this
  exact zero_ne_one this

theorem ζ_add (hX' : p • X' = X) (hK : KerA p D X) (y y' : TateModule p (G'.Points (K p))) :
    ζ p hO D hX' hK (y + y') = ζ p hO D hX' hK y * ζ p hO D hX' hK y' := by
  refine eq_of_forall_mk_eq p hO fun j => ?_
  rw [map_mul, ← cv_eq_mk_ζ, ← cv_eq_mk_ζ, ← cv_eq_mk_ζ]
  change ((cvu p D X' (y + y') j : (Oq p R j)ˣ) : Oq p R j) = _
  rw [cvu_add_right, Units.val_mul]

theorem ζ_psmul (hX' : p • X' = X) (hK : KerA p D X) (y : TateModule p (G'.Points (K p))) :
    ζ p hO D hX' hK ((p : ℤ_[p]) • y) = 1 := by
  refine (mk_eq_one_iff_of_forall p hO _).1 fun j => ?_
  rw [← cv_eq_mk_ζ]
  change ((cvu p D X' ((p : ℤ_[p]) • y) j : (Oq p R j)ˣ) : Oq p R j) = 1
  rw [cvu_psmul_right, Units.val_pow_eq_pow_val]
  exact cv_root_pow p D hX' hK y j

theorem ζ_eq_of_apply_one_eq (hX' : p • X' = X) (hK : KerA p D X) (y y' : TateModule p (G'.Points (K p)))
    (hyy' : (y : ℕ → G'.Points (K p)) 1 = (y' : ℕ → G'.Points (K p)) 1) : ζ p hO D hX' hK y = ζ p hO D hX' hK y' := by
  have h0 : TateModule.proj p (G'.Points (K p)) 1 (y - y') = 0 := by
    rw [TateModule.proj_apply, AddSubgroup.coe_sub, Pi.sub_apply, hyy', sub_self]
  have h1 := TateModule.pow_smul_shiftOfProjEqZero 1 (y - y') h0
  rw [pow_one] at h1
  have h2 : y = y' + (p : ℤ_[p]) • TateModule.shiftOfProjEqZero 1 (y - y') h0 := by rw [h1]; abel
  rw [h2, ζ_add, ζ_psmul, mul_one]

def ych (ψ : G'.Point (K p) 1) : TateModule p (G'.Points (K p)) := (exists_tate_of_point_one p D ψ).choose

theorem ych_spec (ψ : G'.Point (K p) 1) :
    ((ych p D ψ : TateModule p (G'.Points (K p))) : ℕ → G'.Points (K p)) 1 = G'.pointsMkAdd (K p) 1 (Additive.ofMul ψ) :=
  (exists_tate_of_point_one p D ψ).choose_spec

def χbar (hX' : p • X' = X) (hK : KerA p D X) : G'.Point (K p) 1 →* (K p)ˣ where
  toFun ψ := Units.mk0 ((ζ p hO D hX' hK (ych p D ψ) : O p R) : K p)
    (fun h0 => ζ_ne_zero p hO D hX' hK _ (Subtype.ext h0))
  map_one' := by
    apply Units.ext
    rw [Units.val_mk0, Units.val_one]
    have h1 : ζ p hO D hX' hK (ych p D 1) = ζ p hO D hX' hK 0 := by
      apply ζ_eq_of_apply_one_eq
      rw [ych_spec, ofMul_one, map_zero]; rfl
    have h2 : ζ p hO D hX' hK 0 = 1 := by
      have h3 := ζ_add p hO D hX' hK 0 0
      rw [add_zero, left_eq_mul₀ (ζ_ne_zero p hO D hX' hK 0)] at h3
      exact h3
    rw [h1, h2]; rfl
  map_mul' ψ ψ' := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, ← Subalgebra.coe_mul, ← ζ_add]
    refine congrArg (fun x : O p R => (x : K p)) (ζ_eq_of_apply_one_eq p hO D hX' hK _ _ ?_)
    rw [ych_spec, AddSubgroup.coe_add, Pi.add_apply, ych_spec, ych_spec, ofMul_mul, map_add]

theorem χbar_apply (hX' : p • X' = X) (hK : KerA p D X) (ψ : G'.Point (K p) 1) :
    ((χbar p hO D hX' hK ψ : (K p)ˣ) : K p) = ((ζ p hO D hX' hK (ych p D ψ) : O p R) : K p) := rfl

theorem ζ_eq_one_of_lifts (hX' : p • X' = X) (hK : KerA p D X) (hG1 : X' ∈ G1 p G)
    (y : TateModule p (G'.Points (K p)))
    (hy : ∀ (w : ℕ) (ψ : G'.Point (K p) w),
      G'.pointsMkAdd (K p) w (Additive.ofMul ψ) = (y : ℕ → G'.Points (K p)) w → ∀ z ∈ H p G w, D.pair (K p) w z ψ = 1) :
    ζ p hO D hX' hK y = 1 := by
  refine (mk_eq_one_iff_of_forall p hO _).1 fun j => ?_
  rw [← cv_eq_mk_ζ]
  cases j with
  | zero =>
      haveI : Subsingleton (Oq p R 0) := Ideal.Quotient.subsingleton_iff.mpr (by
        rw [pow_zero, Ideal.span_singleton_one])
      exact Subsingleton.elim _ _
  | succ j =>
      obtain ⟨w, f, hf⟩ := Points.exists_mkAdd G (G.cpointsProj (O p R) (j + 1) X')
      rw [cv_eq_pair p D X' y (j + 1) w f hf (liftO p G' y w) (rep_liftO p G' y w)]
      refine D.pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff p hO (j + 1) w f
        (isNilpotent_of_mem_G1 p G hG1 j w f hf) (liftO p G' y w) fun z hz => ?_
      have hzH : G.pointMap (O p R).val w z ∈ H p G w := by
        rw [pointMap_val_mem_H_iff, redO_eq_one_iff]
        exact hz
      have h1 := hy w _ (rep_liftO p G' y w) _ hzH
      rw [pair_pointMap] at h1
      exact Subtype.ext h1

variable (hX' : p • X' = X) (hK : KerA p D X) (hG1 : X' ∈ G1 p G)

def zK : G.Point (K p) 1 :=
  ((D.eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed (K p) 1).2.2.1 (χbar p hO D hX' hK)).choose

theorem pair_zK (ψ : G'.Point (K p) 1) : D.pair (K p) 1 (zK p hO D hX' hK) ψ = χbar p hO D hX' hK ψ :=
  ((D.eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed (K p) 1).2.2.1 (χbar p hO D hX' hK)).choose_spec ψ

include hG1 in

theorem zK_mem_H : zK p hO D hX' hK ∈ H p G 1 := by
  refine (D.mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one (K p)).1 1 (H p G 1) _
    fun ψ hψ => ?_
  obtain ⟨y, hy1, hy⟩ := (D.mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one (K p)).2
    (H p G) (fun w z hz => mem_H_of_pointIncl_mem p G w z hz) ψ hψ
  rw [pair_zK, χbar_apply, ζ_eq_of_apply_one_eq p hO D hX' hK (ych p D ψ) y (by rw [ych_spec, hy1]),
    ζ_eq_one_of_lifts p hO D hX' hK hG1 y hy]
  rfl

abbrev zO : G.Point (O p R) 1 := intg p G 1 (zK p hO D hX' hK)

def X₁ : G.CPoints (O p R) := X' - G.toCPoints (O p R) (G.pointsMkAdd (O p R) 1 (Additive.ofMul (zO p hO D hX' hK)))

include hG1 in
theorem X₁_mem_G1 : X₁ p hO D hX' hK ∈ G1 p G := by
  refine sub_mem hG1 (toCPoints_mem_G1 p G 1 _ ?_)
  have := zK_mem_H p hO D hX' hK hG1
  rwa [mem_H_iff] at this

theorem p_nsmul_X₁ : p • X₁ p hO D hX' hK = X := by
  have h1 : p • G.pointsMkAdd (O p R) 1 (Additive.ofMul (zO p hO D hX' hK)) = 0 := by
    have := G.nsmul_pointsMkAdd_eq_zero 1 (zO p hO D hX' hK)
    rwa [pow_one] at this
  rw [X₁, nsmul_sub, hX', ← map_nsmul, h1, map_zero, sub_zero]

theorem cvu_toCPoints_zO (y : TateModule p (G'.Points (K p))) (j : ℕ) :
    cvu p D (G.toCPoints (O p R) (G.pointsMkAdd (O p R) 1 (Additive.ofMul (zO p hO D hX' hK)))) y j = cvu p D X' y j := by
  apply Units.ext
  have hrep : G.pointsMkAdd _ 1 (Additive.ofMul (G.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ j})) 1
      (zO p hO D hX' hK))) = G.cpointsProj (O p R) j (G.toCPoints (O p R) (G.pointsMkAdd (O p R) 1 (Additive.ofMul (zO p hO D hX' hK)))) := by
    rw [cpointsProj_toCPoints, pointsMap_pointsMkAdd]
  change cv p D _ y j = cv p D X' y j
  rw [cv_eq_pair p D _ y j 1 _ hrep (liftO p G' y 1) (rep_liftO p G' y 1), pair_pointMap, cv_eq_mk_ζ p hO D hX' hK,
    Ideal.Quotient.mkₐ_eq_mk]
  refine congrArg (Ideal.Quotient.mk _) (Subtype.ext ?_)
  change (O p R).val (D.pair (O p R) 1 (zO p hO D hX' hK) (liftO p G' y 1)) = _
  rw [← pair_pointMap, pointMap_val_intg, pair_zK, χbar_apply]
  exact congrArg (fun x : O p R => (x : K p)) (ζ_eq_of_apply_one_eq p hO D hX' hK _ _ (by rw [ych_spec, rep_liftO]))

theorem KerA_X₁ : KerA p D (X₁ p hO D hX' hK) := by
  intro y j
  rw [X₁, cvu_sub_left, cvu_toCPoints_zO, mul_inv_cancel]

include hO in

theorem eq_of_p_nsmul_eq {Y Y' : G.CPoints (O p R)} (hY : KerA p D Y) (hY' : KerA p D Y') (h : p • Y = p • Y') :
    Y = Y' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_p_nsmul_eq_zero p hO D _ ?_ (hY.sub p D hY')
  rw [nsmul_sub, h, sub_self]

theorem smul_X₁ (hinv : ∀ (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R), Restricts p σ σ' → σ' • X = X)
    (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R) (hσ : Restricts p σ σ') : σ' • X₁ p hO D hX' hK = X₁ p hO D hX' hK := by
  refine eq_of_p_nsmul_eq p hO D ((KerA_X₁ p hO D hX' hK).smul p D σ σ' hσ) (KerA_X₁ p hO D hX' hK) ?_
  rw [CPoints.smul_def, ← map_nsmul, p_nsmul_X₁, ← CPoints.smul_def, hinv σ σ' hσ]

include hO in

theorem root_step (X : G.CPoints (O p R)) (hG1 : X ∈ G1 p G) (hK : KerA p D X)
    (hinv : ∀ (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R), Restricts p σ σ' → σ' • X = X) :
    ∃ X₁ : G.CPoints (O p R), X₁ ∈ G1 p G ∧ KerA p D X₁ ∧
      (∀ (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R), Restricts p σ σ' → σ' • X₁ = X₁) ∧ p • X₁ = X := by
  obtain ⟨X', hX'1, hX'⟩ := G.exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff p hO X
    ((mem_G1_iff_forall p G X).1 hG1)
  have hG1' : X' ∈ G1 p G := (mem_G1_iff_forall p G X').2 hX'1
  exact ⟨X₁ p hO D hX' hK, X₁_mem_G1 p hO D hX' hK hG1', KerA_X₁ p hO D hX' hK, smul_X₁ p hO D hX' hK hinv, p_nsmul_X₁ p hO D hX' hK⟩

end Root

section Dictionary

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
variable {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')

def KerP (Y : G.CPoints (O p R)) : Prop :=
  ∀ (y : TateModule p (G'.Points (PadicAlgCl p))) (i w : ℕ), i ≤ w →
    ∀ (f : G.Point (Oq p R i) w),
      G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (O p R) i Y →
    ∀ (ψ : G'.Point (O p R) w),
      G'.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul (G'.pointMap (O p R).val w ψ)) =
        (y : ℕ → G'.Points (PadicAlgCl p)) w →
      D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ i})) w ψ) = 1

theorem kerA_iff_kerP (Y : G.CPoints (O p R)) : KerA p D Y ↔ KerP p D Y := by
  constructor
  · intro hY y i w hiw f hf ψ hψ
    rw [← cv_eq_pair p D Y y i w f hf ψ hψ]
    change ((cvu p D Y y i : (Oq p R i)ˣ) : Oq p R i) = 1
    rw [hY y i, Units.val_one]
  · intro hg y i
    apply Units.ext
    obtain ⟨v, f₀, hf₀⟩ := PDivisibleGroup.Points.exists_mkAdd G (G.cpointsProj (O p R) i Y)
    have hf : G.pointsMkAdd _ (max v i) (Additive.ofMul (G.pointInclLE _ (le_max_left v i) f₀)) =
        G.cpointsProj (O p R) i Y := by
      rw [PDivisibleGroup.pointsMkAdd_pointInclLE, hf₀]
    change cv p D _ y i = 1
    rw [cv_eq_pair p D _ y i (max v i) _ hf (liftO p G' y (max v i)) (rep_liftO p G' y (max v i))]
    exact hg y i (max v i) (le_max_right v i) _ hf _ (rep_liftO p G' y (max v i))

end Dictionary

end PDivStep2R
p2m_reactivate "P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff.PDivStep2R"

end
p2m_reactivate "P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff.PDivStep2R"

open PDivStep2R in

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
    (hO : ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1)
    {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (Ker G₁ Inv : Set (G.CPoints (integralClosure R (PadicAlgCl p))))
    (hKer : ∀ Y, Y ∈ Ker ↔
      ∀ (y : TateModule p (G'.Points (PadicAlgCl p))) (i w : ℕ), i ≤ w →
        ∀ (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
            Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i}) w),
          G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (integralClosure R (PadicAlgCl p)) i Y →
        ∀ (ψ : G'.Point (integralClosure R (PadicAlgCl p)) w),
          G'.pointsMkAdd (PadicAlgCl p) w
              (Additive.ofMul (G'.pointMap (integralClosure R (PadicAlgCl p)).val w ψ)) =
            (y : ℕ → G'.Points (PadicAlgCl p)) w →
          D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R
              (Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i})) w ψ) = 1)
    (hG₁ : ∀ X, X ∈ G₁ ↔
      ∀ (w : ℕ) (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
          Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ 1}) w),
        G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (integralClosure R (PadicAlgCl p)) 1 X →
        ∀ a : G.level w,
          IsNilpotent (PDivisibleGroup.Point.toAlgHom f a - algebraMap R _ (Coalgebra.counit a)))
    (hInv : ∀ X, X ∈ Inv ↔
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (σ' : integralClosure R (PadicAlgCl p) ≃ₐ[R] integralClosure R (PadicAlgCl p)),
        (∀ a : integralClosure R (PadicAlgCl p),
            ((σ' a : integralClosure R (PadicAlgCl p)) : PadicAlgCl p) = σ a) →
        σ' • X = X) :
    (∀ Y ∈ Ker, ∀ n : ℕ, n • Y ∈ Ker) ∧
    (∀ Y ∈ Ker, ∀ k : ℕ, p ^ k • Y = 0 → Y = 0) ∧
    (∀ X ∈ Ker, X ∈ G₁ → X ∈ Inv → ∃ X₁ ∈ Ker, X₁ ∈ G₁ ∧ X₁ ∈ Inv ∧ p • X₁ = X) := by
  have hK : ∀ Y, Y ∈ Ker ↔ KerA p D Y := fun Y => (hKer Y).trans (kerA_iff_kerP p D Y).symm
  have hG : ∀ X, X ∈ G₁ ↔ X ∈ G1 p G := fun X => (hG₁ X).trans (mem_G1_iff_forall p G X).symm
  have hI : ∀ X, X ∈ Inv ↔ ∀ (σ : Gal p) (σ' : O p R ≃ₐ[R] O p R), Restricts p σ σ' → σ' • X = X :=
    fun X => hInv X
  refine ⟨fun Y hY n => (hK _).2 (((hK Y).1 hY).nsmul p D n), fun Y hY k hk =>
    eq_zero_of_pow_nsmul_eq_zero p hO D k Y hk ((hK Y).1 hY), fun X hXK hXG hXI => ?_⟩
  obtain ⟨X₁, h1, h2, h3, h4⟩ := root_step p hO D X ((hG X).1 hXG) ((hK X).1 hXK) ((hI X).1 hXI)
  exact ⟨X₁, (hK X₁).2 h2, (hG X₁).2 h1, (hI X₁).2 h3, h4⟩

end S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff (solution)

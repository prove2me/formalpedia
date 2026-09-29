-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f6f95153-c1d3-5b06-baa4-ec5057bc51d4

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Theorems.Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
import Theorems.Thm_Algebra_Etale_eq_of_forall_algHom_apply_eq
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff

set_option autoImplicit false

noncomputable section

open PDivisibleGroup Coalgebra
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct"

namespace PDivOrthCR

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)]

abbrev O : Subalgebra R (PadicAlgCl p) := integralClosure R (PadicAlgCl p)

abbrev K : Type := PadicAlgCl p

abbrev Oq (i : ℕ) : Type := O p R ⧸ Ideal.span {(p : O p R) ^ i}

abbrev maxI : Ideal (O p R) := (Ideal.span {(p : O p R)}).radical

abbrev OK : Prop := ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1

variable {R}
variable (hO : OK p R)

theorem norm_coe_p : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  exact (PadicAlgCl.norm_extends (p := p) (p : ℚ_[p])).trans (Padic.norm_p (p := p))

include hO in
theorem norm_le_one (c : O p R) : ‖(c : K p)‖ ≤ 1 :=
  (hO (c : PadicAlgCl p)).mp c.2

include hO in
theorem mem_maxI_of_norm_lt_one (c : O p R) (hc : ‖(c : K p)‖ < 1) : c ∈ maxI p R := by
  have hp : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hp hc
  refine Ideal.mem_radical_iff.2 ⟨n, Ideal.mem_span_singleton'.2 ?_⟩
  have hp0 : (p : PadicAlgCl p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set d : K p := (c : K p) ^ n / (p : K p) with hd
  have hdn : ‖d‖ ≤ 1 := by
    rw [hd, norm_div, norm_pow, norm_coe_p, div_le_iff₀ (by positivity), one_mul]
    exact hn.le
  have hdint : IsIntegral R d := (hO d).mpr hdn
  refine ⟨⟨d, hdint⟩, Subtype.ext ?_⟩
  change d * (p : K p) = (c : K p) ^ n
  rw [hd, div_mul_cancel₀ _ hp0]

include hO in

theorem isUnit_of_not_mem_maxI (c : O p R) (hc : c ∉ maxI p R) : IsUnit c := by
  have h1 : ‖(c : K p)‖ = 1 := by
    rcases (norm_le_one p hO c).lt_or_eq with hlt | heq
    · exact absurd (mem_maxI_of_norm_lt_one p hO c hlt) hc
    · exact heq
  have hc0 : (c : K p) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
  have hinv : IsIntegral R (c : K p)⁻¹ := by
    refine (hO _).mpr ?_
    rw [norm_inv, h1, inv_one]
  refine isUnit_iff_exists_inv.2 ⟨⟨(c : K p)⁻¹, hinv⟩, Subtype.ext ?_⟩
  change (c : K p) * (c : K p)⁻¹ = 1
  exact mul_inv_cancel₀ hc0

section Points

variable {h : ℕ} (G : PDivisibleGroup R p h) (w : ℕ)

theorem isIntegral_apply (z : G.level w →ₐ[R] K p) (a : G.level w) : IsIntegral R (z a) :=
  (Algebra.IsIntegral.isIntegral (R := R) a).map z

def intg (z : G.level w →ₐ[R] K p) : G.Point (O p R) w :=
  Point.ofAlgHom (z.codRestrict (O p R) (isIntegral_apply p G w z))

@[scoped simp] theorem coe_intg_apply (z : G.level w →ₐ[R] K p) (a : G.level w) :
    ((Point.toAlgHom (intg p G w z) a : O p R) : K p) = z a := rfl

scoped instance finite_point_K : Finite (G.level w →ₐ[R] K p) :=
  Nat.finite_of_card_ne_zero (by
    rw [HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R (G.level w) (K p), G.finrank_level]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

theorem toAlgHom_val_injective : Function.Injective fun z : G.Point (O p R) w => (O p R).val.comp (Point.toAlgHom z) := by
  intro z z' hzz'
  refine Point.ext fun a => Subtype.ext ?_
  exact DFunLike.congr_fun hzz' a

scoped instance finite_point_O : Finite (G.Point (O p R) w) :=
  Finite.of_injective _ (toAlgHom_val_injective p G w)

end Points

section Alg

variable {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G') (w : ℕ)

abbrev B : Type := O p R ⊗[R] G.level w

abbrev bas := Module.Free.chooseBasis R (G.level w)

def coef (ψ : G'.Point (O p R) w) (j : Module.Free.ChooseBasisIndex R (G.level w)) : O p R :=
  Point.toAlgHom ψ ((D.toDualEquiv w).symm ((bas p (G := G) w).coord j))

def u (ψ : G'.Point (O p R) w) : B p (G := G) w := ∑ j, coef p D w ψ j ⊗ₜ[R] bas p (G := G) w j

def ev {L : Type} [CommRing L] [Algebra R L] (φ : O p R →ₐ[R] L) (z : G.level w →ₐ[R] L) :
    B p (G := G) w →ₐ[R] L :=
  Algebra.TensorProduct.lift φ z (fun _ _ => Commute.all _ _)

theorem ev_tmul {L : Type} [CommRing L] [Algebra R L] (φ : O p R →ₐ[R] L) (z : G.level w →ₐ[R] L)
    (c : O p R) (x : G.level w) : ev p w φ z (c ⊗ₜ x) = φ c * z x :=
  Algebra.TensorProduct.lift_tmul _ _ _ c x

theorem ev_u {L : Type} [CommRing L] [Algebra R L] (φ : O p R →ₐ[R] L) (z : G.level w →ₐ[R] L)
    (ψ : G'.Point (O p R) w) :
    ev p w φ z (u p D w ψ) = D.pair L w (Point.ofAlgHom z) (G'.pointMap φ w ψ) := by
  rw [u, map_sum, CartierDuality.pair_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_tmul, mul_comm]
  rfl

end Alg

section Inject

variable {h : ℕ} (G : PDivisibleGroup R p h) (w : ℕ)

abbrev BK : Type := K p ⊗[R] G.level w

scoped instance etale_BK : Algebra.Etale (K p) (BK p G w) :=
  HopfAlgebra.algebra_etale_of_module_finite_of_charZero (K p) (BK p G w)

def ιB : B p (G := G) w →ₐ[R] BK p G w :=
  Algebra.TensorProduct.map ((O p R).val) (AlgHom.id R (G.level w))

theorem ιB_tmul (c : O p R) (x : G.level w) : ιB p G w (c ⊗ₜ x) = (c : K p) ⊗ₜ x := rfl

theorem ιB_toLinearMap : (ιB p G w).toLinearMap = LinearMap.rTensor (G.level w) (O p R).val.toLinearMap := by
  refine TensorProduct.ext' fun c x => ?_
  rfl

theorem ιB_injective : Function.Injective (ιB p G w) := by
  have h1 : Function.Injective (LinearMap.rTensor (G.level w) (O p R).val.toLinearMap) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  intro x y hxy
  apply h1
  have := congrArg (fun f => f) hxy
  rw [← ιB_toLinearMap]
  exact hxy

def evK (χ : BK p G w →ₐ[K p] K p) : B p (G := G) w →ₐ[R] K p := (χ.restrictScalars R).comp (ιB p G w)

def ptK (χ : BK p G w →ₐ[K p] K p) : G.level w →ₐ[R] K p :=
  (χ.restrictScalars R).comp ((ιB p G w).comp Algebra.TensorProduct.includeRight)

theorem evK_tmul (χ : BK p G w →ₐ[K p] K p) (c : O p R) (x : G.level w) :
    evK p G w χ (c ⊗ₜ x) = (c : K p) * ptK p G w χ x := by
  have h1 : (c ⊗ₜ[R] x : B p (G := G) w) = (c ⊗ₜ 1) * (1 ⊗ₜ x) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h1, map_mul]
  have h2 : evK p G w χ (c ⊗ₜ 1) = (c : K p) := by
    change χ (ιB p G w (c ⊗ₜ 1)) = _
    rw [ιB_tmul]
    exact χ.commutes (c : K p)
  rw [h2]
  rfl

theorem evK_eq_ev (χ : BK p G w →ₐ[K p] K p) : evK p G w χ = ev p w (O p R).val (ptK p G w χ) := by
  refine Algebra.TensorProduct.ext' fun c x => ?_
  rw [evK_tmul, ev_tmul]
  rfl

theorem eq_zero_of_forall_evK (x : B p (G := G) w) (hx : ∀ χ : BK p G w →ₐ[K p] K p, evK p G w χ x = 0) : x = 0 := by
  apply ιB_injective p G w
  rw [map_zero]
  refine Algebra.Etale.eq_of_forall_algHom_apply_eq (K := K p) (Ω := K p) fun χ => ?_
  rw [map_zero]
  exact hx χ

end Inject

section Main

variable {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G') (w : ℕ)

def RedO (z : G.Point (O p R) w) : Prop :=
  ∀ a : G.level w, Point.toAlgHom z a - algebraMap R (O p R) (counit (R := R) a) ∈ maxI p R

theorem exists_witness (z : G.Point (O p R) w) (hz : ¬ RedO p w z) :
    ∃ g : G.level w, Point.toAlgHom z g - algebraMap R (O p R) (counit (R := R) g) ∉ maxI p R :=
  not_forall.mp hz

def wit (z : G.Point (O p R) w) (hz : ¬ RedO p w z) : G.level w := (exists_witness p w z hz).choose

theorem wit_spec (z : G.Point (O p R) w) (hz : ¬ RedO p w z) :
    Point.toAlgHom z (wit p w z hz) - algebraMap R (O p R) (counit (R := R) (wit p w z hz)) ∉ maxI p R :=
  (exists_witness p w z hz).choose_spec

open Classical in

def α (z : G.Point (O p R) w) : B p (G := G) w :=
  if hz : RedO p w z then 1 else 1 ⊗ₜ wit p w z hz - Point.toAlgHom z (wit p w z hz) ⊗ₜ 1

scoped instance fintypePointO : Fintype (G.Point (O p R) w) := Fintype.ofFinite _

def a : B p (G := G) w := ∏ z : G.Point (O p R) w, α p w z

theorem α_of_not (z : G.Point (O p R) w) (hz : ¬ RedO p w z) :
    α p w z = 1 ⊗ₜ wit p w z hz - Point.toAlgHom z (wit p w z hz) ⊗ₜ 1 := by
  rw [α, dif_neg hz]

theorem α_of (z : G.Point (O p R) w) (hz : RedO p w z) : α p w z = 1 := by
  rw [α, dif_pos hz]

variable (ψ : G'.Point (O p R) w)
  (hψ : ∀ z : G.Point (O p R) w, RedO p w z → D.pair (O p R) w z ψ = 1)

include hψ in

theorem a_mul_u_sub_one : a p w * (u p D w ψ - 1) = 0 := by
  refine eq_zero_of_forall_evK p G w _ fun χ => ?_
  rw [map_mul, map_sub, map_one, evK_eq_ev, ev_u]

  set z := intg p G w (ptK p G w χ) with hz
  have hzval : G.pointMap (O p R).val w z = Point.ofAlgHom (ptK p G w χ) := Point.ext fun a => rfl
  by_cases hred : RedO p w z
  ·
    have h1 : D.pair (K p) w (Point.ofAlgHom (ptK p G w χ)) (G'.pointMap (O p R).val w ψ) = 1 := by
      rw [← hzval, CartierDuality.pair_def]
      have h2 := hψ z hred
      rw [CartierDuality.pair_def] at h2
      have h3 := congrArg ((O p R).val) h2
      rw [map_sum, map_one] at h3
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h3
      rw [map_mul]; rfl
    rw [h1, sub_self, mul_zero]
  ·
    have h1 : ev p w (O p R).val (ptK p G w χ) (a p w) = 0 := by
      rw [a, map_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ z) ?_
      rw [α_of_not p w z hred, map_sub, ev_tmul, ev_tmul, map_one, map_one, one_mul, mul_one, sub_eq_zero]
      exact (coe_intg_apply p G w (ptK p G w χ) _).symm
    rw [h1, zero_mul]

variable {i : ℕ} (f : G.Point (Oq p R i) w)
  (hf : ∀ a : G.level w, IsNilpotent (Point.toAlgHom f a - algebraMap R (Oq p R i) (counit (R := R) a)))

abbrev Θ : B p (G := G) w →ₐ[R] Oq p R i :=
  ev p w (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ i})) (Point.toAlgHom f)

include hO hf in

theorem isUnit_Θ_α (z : G.Point (O p R) w) : IsUnit (Θ p w f (α p w z)) := by
  by_cases hz : RedO p w z
  · rw [α_of p w z hz, map_one]; exact isUnit_one
  · rw [α_of_not p w z hz, map_sub, ev_tmul, ev_tmul, map_one, map_one, one_mul, mul_one]
    set g := wit p w z hz with hg
    have hsplit : Point.toAlgHom f g - Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ i}) (Point.toAlgHom z g) =
        (Point.toAlgHom f g - algebraMap R (Oq p R i) (counit (R := R) g)) -
          Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ i})
            (Point.toAlgHom z g - algebraMap R (O p R) (counit (R := R) g)) := by
      rw [map_sub, AlgHom.commutes]; abel
    rw [hsplit]
    have hunit : IsUnit (Ideal.Quotient.mkₐ R (Ideal.span {(p : O p R) ^ i})
        (Point.toAlgHom z g - algebraMap R (O p R) (counit (R := R) g))) :=
      (isUnit_of_not_mem_maxI p hO _ (wit_spec p w z hz)).map _
    have := (hf g).isUnit_add_left_of_commute hunit.neg (Commute.all _ _)
    rwa [neg_add_eq_sub] at this

include hO hf in
theorem isUnit_Θ_a : IsUnit (Θ p w f (a p w)) := by
  rw [a, map_prod]
  exact Finset.prod_induction _ IsUnit (fun _ _ hx hy => hx.mul hy) isUnit_one
    (fun z _ => isUnit_Θ_α p hO w f hf z)

end Main

end PDivOrthCR
p2m_reactivate "P2MW.S_PDivisibleGroup_CartierDuality_pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff.PDivOrthCR"

open PDivOrthCR in

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
    (hO : ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1)
    {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (i w : ℕ)
    (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
      Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i}) w)
    (hf : ∀ a : G.level w,
      IsNilpotent (PDivisibleGroup.Point.toAlgHom f a - algebraMap R _ (Coalgebra.counit a)))
    (ψ : G'.Point (integralClosure R (PadicAlgCl p)) w)
    (hψ : ∀ z : G.Point (integralClosure R (PadicAlgCl p)) w,
      (∀ a : G.level w, PDivisibleGroup.Point.toAlgHom z a -
          algebraMap R (integralClosure R (PadicAlgCl p)) (Coalgebra.counit a) ∈
        (Ideal.span {(p : integralClosure R (PadicAlgCl p))}).radical) →
      D.pair (integralClosure R (PadicAlgCl p)) w z ψ = 1) :
    D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R
      (Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i})) w ψ) = 1 := by

  have h0 := congrArg (Θ p w f) (a_mul_u_sub_one p D w ψ hψ)
  rw [map_mul, map_zero, (isUnit_Θ_a p hO w f hf).mul_right_eq_zero, map_sub, map_one, sub_eq_zero, ev_u] at h0
  exact h0

end
end S_PDivisibleGroup_CartierDuality_pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff (solution)

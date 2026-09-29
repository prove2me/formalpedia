-- Prove2me | solution 1 for PDivisibleGroup.finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/66180d2e-3014-54be-b40c-1733ddf74290

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Theorems.Thm_PDivisibleGroup_CartierDuality_finrank_cotangent_one_add_finrank_cotangent_one_eq_height
import Theorems.Thm_PDivisibleGroup_exists_isCartierDual
import Theorems.Thm_CartierDual_pow_apply_pow_eq_apply_nsmulAlgHom_pow
import Theorems.Thm_PDivisibleGroup_ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot
import Theorems.Thm_IsLocalRing_exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct
open Coalgebra Bialgebra

universe u v

section InlinedHopfIdealQuotient
noncomputable section HIQ

p2m_open_scoped "TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct"
open Coalgebra Bialgebra WithConv

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one ofAlgHom mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul mul_antipode_lTensor_comul counit_antipode mul_antipode_rTensor_comul_apply coaction coaction_apply hopfKer exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective"
p2m_open "HopfAlgebra"

section AntipodeAlgHom

variable (R : Type*) [CommSemiring R] (H : Type*) [CommSemiring H] [HopfAlgebra R H]

def antipodeAlgHom : H →ₐ[R] H :=
  AlgHom.ofLinearMap (antipode R) antipode_one fun a b => by
    rw [antipode_mul, mul_comm]

@[scoped simp] theorem antipodeAlgHom_apply (x : H) : antipodeAlgHom R H x = antipode R x := rfl

theorem antipodeAlgHom_toLinearMap : (antipodeAlgHom R H).toLinearMap = antipode R := rfl

variable {R H}
variable {A : Type*} [CommSemiring A] [Algebra R A]

theorem lift_comp_antipodeAlgHom_apply (φ : H →ₐ[R] A) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift φ (φ.comp (antipodeAlgHom R H)) (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R H ((antipode R).lTensor H z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem lift_antipodeAlgHom_comp_apply (φ : H →ₐ[R] A) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift (φ.comp (antipodeAlgHom R H)) φ (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R H ((antipode R).rTensor H z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem convMul_comp_antipodeAlgHom (φ : H →ₐ[R] A) :
    toConv φ * toConv (φ.comp (antipodeAlgHom R H)) = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (toConv φ * toConv (φ.comp (antipodeAlgHom R H))) x = (1 : WithConv (H →ₐ[R] A)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, ofConv_toConv, ofConv_toConv,
    lift_comp_antipodeAlgHom_apply, mul_antipode_lTensor_comul_apply, AlgHom.commutes]

theorem comp_antipodeAlgHom_convMul (φ : H →ₐ[R] A) :
    toConv (φ.comp (antipodeAlgHom R H)) * toConv φ = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (toConv (φ.comp (antipodeAlgHom R H)) * toConv φ) x = (1 : WithConv (H →ₐ[R] A)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, ofConv_toConv, ofConv_toConv,
    lift_antipodeAlgHom_comp_apply, mul_antipode_rTensor_comul_apply, AlgHom.commutes]

theorem isUnit_toConv_algHom (φ : H →ₐ[R] A) : IsUnit (toConv φ) :=
  isUnit_iff_exists.2 ⟨_, convMul_comp_antipodeAlgHom φ, comp_antipodeAlgHom_convMul φ⟩

end AntipodeAlgHom

section ConvComp

variable {R : Type*} [CommSemiring R] {H G : Type*} [CommSemiring H] [CommSemiring G]
  [Bialgebra R H] [Bialgebra R G]
variable (A : Type*) [CommSemiring A] [Algebra R A]

def convCompMonoidHom (π : H →ₐc[R] G) : WithConv (G →ₐ[R] A) →* WithConv (H →ₐ[R] A) where
  toFun f := toConv (f.ofConv.comp (π : H →ₐ[R] G))
  map_one' := by
    refine WithConv.ext ?_
    simp only [ofConv_toConv, AlgHom.convOne_def, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  map_mul' f g := by
    rw [AlgHom.convMul_comp_bialgHom_distrib]

@[scoped simp] theorem convCompMonoidHom_apply (π : H →ₐc[R] G) (f : WithConv (G →ₐ[R] A)) :
    convCompMonoidHom A π f = toConv (f.ofConv.comp (π : H →ₐ[R] G)) := rfl

end ConvComp

end HopfAlgebra
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra"

section IsHopfIdeal'

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

namespace Ideal p2m_export "Ideal" "map_le_iff_le_comap height Cotangent Quotient.eq_zero_iff_mem quotientKerAlgEquivOfSurjective mul_mem_right Quotient.mkₐ pow_le_pow_right toCotangent_surjective Quotient.liftₐ map_span radical sum_mem quotientEquivAlg mem_bot span isPrime_bot span_singleton_eq_bot Quotient.algHom_ext map_quotient_self zero_eq_bot Quotient.mk Quotient.liftₐ_apply mul_mem_left map_id map Quotient.lift_mk mem_sup_left ext span_eq mem_toCotangent_ker Quotient.liftₐ_comp pow_mem_of_mem mem_map_of_mem span_le mem_sup_right mem_comap pow_mem_pow map_mono pow_right_mono comap mem_span_range_iff_exists_fun Quotient.mkₐ_eq_mk subset_span exists_pow_le_of_le_radical_of_fg mem_map_iff_of_surjective Quotient.mk_surjective toCotangent" end Ideal
namespace Ideal
p2m_open_scoped "Ideal" in

private class _root_.Ideal.IsHopfIdeal' (I : Ideal H) : Prop where
  map_mkₐ_comul_eq_zero : ∀ x ∈ I,
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) x) = 0
  counit_eq_zero : ∀ x ∈ I, Coalgebra.counit (R := R) x = 0
  antipode_mem : ∀ x ∈ I, HopfAlgebra.antipode R x ∈ I

end Ideal
p2m_export "" "Ideal.IsHopfIdeal'"
p2m_export_all "" "Ideal.IsHopfIdeal'"
p2m_open_scoped "Ideal" in
scoped instance Ideal.isHopfIdeal_bot : (⊥ : Ideal H).IsHopfIdeal' R where
  map_mkₐ_comul_eq_zero x hx := by rw [(Ideal.mem_bot).1 hx]; simp
  counit_eq_zero x hx := by rw [(Ideal.mem_bot).1 hx]; simp
  antipode_mem x hx := by rw [(Ideal.mem_bot).1 hx]; simp

p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal"
end IsHopfIdeal'
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one ofAlgHom mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul mul_antipode_lTensor_comul counit_antipode mul_antipode_rTensor_comul_apply coaction coaction_apply hopfKer exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective"
p2m_open "HopfAlgebra"

namespace HopfIdealQuotient

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]
variable (I : Ideal H) [hI : I.IsHopfIdeal' R]

private def _root_.HopfAlgebra.HopfIdealQuotient.comul : H ⧸ I →ₐ[R] (H ⧸ I) ⊗[R] (H ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (comulAlgHom R H))
    (fun x hx => hI.map_mkₐ_comul_eq_zero x hx)

p2m_export "HopfAlgebra.HopfIdealQuotient" "comul"
theorem comul_comp_mkₐ :
    (comul R I).comp (Ideal.Quotient.mkₐ R I) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
        (comulAlgHom R H) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem comul_mk (x : H) :
    comul R I (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

private def _root_.HopfAlgebra.HopfIdealQuotient.counit : H ⧸ I →ₐ[R] R :=
  Ideal.Quotient.liftₐ I (counitAlgHom R H) (fun x hx => hI.counit_eq_zero x hx)

p2m_export "HopfAlgebra.HopfIdealQuotient" "counit"
theorem counit_comp_mkₐ : (counit R I).comp (Ideal.Quotient.mkₐ R I) = counitAlgHom R H :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem counit_mk (x : H) :
    counit R I (Ideal.Quotient.mk I x) = Coalgebra.counit (R := R) x := rfl

private def _root_.HopfAlgebra.HopfIdealQuotient.antipode : H ⧸ I →ₐ[R] H ⧸ I :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R I).comp (antipodeAlgHom R H)) (fun x hx => by
    simp only [AlgHom.comp_apply, antipodeAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hI.antipode_mem x hx)

p2m_export "HopfAlgebra.HopfIdealQuotient" "antipode"
theorem antipode_comp_mkₐ :
    (antipode R I).comp (Ideal.Quotient.mkₐ R I) =
      (Ideal.Quotient.mkₐ R I).comp (antipodeAlgHom R H) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem antipode_mk (x : H) :
    antipode R I (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (HopfAlgebra.antipode R x) := rfl

private theorem map_apply_eq_linearMap {A B C D : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] C) (g : B →ₐ[R] D) (z : A ⊗[R] B) :
    Algebra.TensorProduct.map f g z = TensorProduct.map f.toLinearMap g.toLinearMap z := rfl

private theorem _root_.HopfAlgebra.HopfIdealQuotient.rTensor_counit_comul :
    (Algebra.TensorProduct.map (counit R I) (.id R (H ⧸ I))).comp (comul R I) =
      (Algebra.TensorProduct.lid R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.lid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (counitAlgHom R H).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.lTensor R) ∘ₗ
          ((counitAlgHom R H).toLinearMap.rTensor H) from
      (LinearMap.lTensor_comp_rTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom R H).toLinearMap.rTensor H) (Coalgebra.comul x) = 1 ⊗ₜ x from
    Coalgebra.rTensor_counit_comul x]
  simp

p2m_export "HopfAlgebra.HopfIdealQuotient" "rTensor_counit_comul"
private theorem _root_.HopfAlgebra.HopfIdealQuotient.lTensor_counit_comul :
    (Algebra.TensorProduct.map (.id R (H ⧸ I)) (counit R I)).comp (comul R I) =
      (Algebra.TensorProduct.rid R R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.rid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap (counitAlgHom R H).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.rTensor R) ∘ₗ
          ((counitAlgHom R H).toLinearMap.lTensor H) from
      (LinearMap.rTensor_comp_lTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom R H).toLinearMap.lTensor H) (Coalgebra.comul x) = x ⊗ₜ 1 from
    Coalgebra.lTensor_counit_comul x]
  simp

p2m_export "HopfAlgebra.HopfIdealQuotient" "lTensor_counit_comul"

private theorem assoc_map_map_apply {A B : Type*} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) (z : (A ⊗[R] A) ⊗[R] A) :
    (Algebra.TensorProduct.assoc R R R B B B)
        (Algebra.TensorProduct.map (Algebra.TensorProduct.map f f) f z) =
      Algebra.TensorProduct.map f (Algebra.TensorProduct.map f f)
        (Algebra.TensorProduct.assoc R R R A A A z) := by
  induction z with
  | zero => simp
  | tmul xy c =>
    induction xy with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coassoc :
    (Algebra.TensorProduct.assoc R R R (H ⧸ I) (H ⧸ I) (H ⧸ I)).toAlgHom.comp
        ((Algebra.TensorProduct.map (comul R I) (.id R (H ⧸ I))).comp (comul R I)) =
      (Algebra.TensorProduct.map (.id R (H ⧸ I)) (comul R I)).comp (comul R I) := by
  refine Ideal.Quotient.algHom_ext R ?_
  refine AlgHom.ext fun x => ?_
  set π := Ideal.Quotient.mkₐ R I

  have hL : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.map (comul R I) (.id R (H ⧸ I)) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.map π π) π
          (Algebra.TensorProduct.map (comulAlgHom R H) (.id R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hR : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.map (.id R (H ⧸ I)) (comul R I) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map π (Algebra.TensorProduct.map π π)
          (Algebra.TensorProduct.map (.id R H) (comulAlgHom R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hx : comul R I (π x) = Algebra.TensorProduct.map π π (comulAlgHom R H x) := by
    simp [π, Ideal.Quotient.mkₐ_eq_mk]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, hx, hL, hR, assoc_map_map_apply]
  congr 1
  have hassoc : ∀ z : (H ⊗[R] H) ⊗[R] H,
      Algebra.TensorProduct.assoc R R R H H H z = TensorProduct.assoc R H H H z := by
    intro z
    induction z with
    | zero => simp
    | tmul xy c =>
      induction xy with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [map_apply_eq_linearMap, map_apply_eq_linearMap, hassoc]
  exact Coalgebra.coassoc_apply x

scoped instance instBialgebra : Bialgebra R (H ⧸ I) :=
  Bialgebra.ofAlgHom (comul R I) (counit R I) (coassoc R I) (rTensor_counit_comul R I)
    (lTensor_counit_comul R I)

theorem comulAlgHom_eq : comulAlgHom R (H ⧸ I) = comul R I := rfl

theorem counitAlgHom_eq : counitAlgHom R (H ⧸ I) = counit R I := rfl

theorem coalgebra_comul_mk (x : H) :
    Coalgebra.comul (R := R) (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

theorem coalgebra_counit_mk (x : H) :
    Coalgebra.counit (R := R) (Ideal.Quotient.mk I x) = Coalgebra.counit (R := R) x := rfl

private theorem lift_antipode_id_comp_map :
    (Algebra.TensorProduct.lift (antipode R I) (.id R (H ⧸ I)) fun _ _ => .all _ _).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)) =
      (Ideal.Quotient.mkₐ R I).comp
        (Algebra.TensorProduct.lift (antipodeAlgHom R H) (.id R H) fun _ _ => .all _ _) := by
  ext x
  · simp [Ideal.Quotient.mkₐ_eq_mk]
  · simp [Ideal.Quotient.mkₐ_eq_mk]

private theorem lift_id_antipode_comp_map :
    (Algebra.TensorProduct.lift (.id R (H ⧸ I)) (antipode R I) fun _ _ => .all _ _).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)) =
      (Ideal.Quotient.mkₐ R I).comp
        (Algebra.TensorProduct.lift (.id R H) (antipodeAlgHom R H) fun _ _ => .all _ _) := by
  ext x
  · simp [Ideal.Quotient.mkₐ_eq_mk]
  · simp [Ideal.Quotient.mkₐ_eq_mk]

private theorem lift_antipodeAlgHom_id_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (antipodeAlgHom R H) (.id R H) fun _ _ => .all _ _).comp
        (comulAlgHom R H) = (Algebra.ofId R H).comp (counitAlgHom R H) := by
  refine AlgHom.ext fun x => ?_
  have h := lift_antipodeAlgHom_comp_apply (AlgHom.id R H) (Coalgebra.comul (R := R) x)
  simp only [AlgHom.id_comp] at h
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, h, mul_antipode_rTensor_comul_apply]
  simp [Algebra.ofId_apply]

private theorem lift_id_antipodeAlgHom_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (.id R H) (antipodeAlgHom R H) fun _ _ => .all _ _).comp
        (comulAlgHom R H) = (Algebra.ofId R H).comp (counitAlgHom R H) := by
  refine AlgHom.ext fun x => ?_
  have h := lift_comp_antipodeAlgHom_apply (AlgHom.id R H) (Coalgebra.comul (R := R) x)
  simp only [AlgHom.id_comp] at h
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, h, mul_antipode_lTensor_comul_apply]
  simp [Algebra.ofId_apply]

theorem mul_antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode R I) (.id R (H ⧸ I)) fun _ _ => .all _ _).comp
        (comulAlgHom R (H ⧸ I)) =
      (Algebra.ofId R (H ⧸ I)).comp (counitAlgHom R (H ⧸ I)) := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [comulAlgHom_eq, counitAlgHom_eq, AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc,
    lift_antipode_id_comp_map, AlgHom.comp_assoc, lift_antipodeAlgHom_id_comp_comulAlgHom,
    AlgHom.comp_assoc, counit_comp_mkₐ, ← AlgHom.comp_assoc]
  congr 1

theorem mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (.id R (H ⧸ I)) (antipode R I) fun _ _ => .all _ _).comp
        (comulAlgHom R (H ⧸ I)) =
      (Algebra.ofId R (H ⧸ I)).comp (counitAlgHom R (H ⧸ I)) := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [comulAlgHom_eq, counitAlgHom_eq, AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc,
    lift_id_antipode_comp_map, AlgHom.comp_assoc, lift_id_antipodeAlgHom_comp_comulAlgHom,
    AlgHom.comp_assoc, counit_comp_mkₐ, ← AlgHom.comp_assoc]
  congr 1

scoped instance instHopfAlgebra : HopfAlgebra R (H ⧸ I) :=
  HopfAlgebra.ofAlgHom (antipode R I) (mul_antipode_rTensor_comul R I)
    (mul_antipode_lTensor_comul R I)

theorem hopf_antipode_mk (x : H) :
    HopfAlgebra.antipode R (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk I (HopfAlgebra.antipode R x) := rfl

scoped instance instIsCocomm [Coalgebra.IsCocomm R H] : Coalgebra.IsCocomm R (H ⧸ I) where
  comm_comp_comul := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [LinearMap.comp_apply, coalgebra_comul_mk]
    conv_rhs => rw [← Coalgebra.comm_comp_comul R H]
    rw [LinearMap.comp_apply]
    generalize Coalgebra.comul (R := R) x = z
    induction z with
    | zero => simp
    | tmul a b => simp
    | add z w hz hw => simp only [map_add, hz, hw]

end HopfIdealQuotient
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient"

section Maps

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

def quotientBialgHom (I : Ideal H) [I.IsHopfIdeal' R] : H →ₐc[R] H ⧸ I :=
  BialgHom.ofAlgHom (Ideal.Quotient.mkₐ R I) (HopfIdealQuotient.counit_comp_mkₐ R I)
    (HopfIdealQuotient.comul_comp_mkₐ R I).symm

@[scoped simp] theorem quotientBialgHom_apply (I : Ideal H) [I.IsHopfIdeal' R] (x : H) :
    quotientBialgHom R I x = Ideal.Quotient.mk I x := rfl

theorem quotientBialgHom_toAlgHom (I : Ideal H) [I.IsHopfIdeal' R] :
    (quotientBialgHom R I : H →ₐ[R] H ⧸ I) = Ideal.Quotient.mkₐ R I := rfl

theorem quotientBialgHom_surjective (I : Ideal H) [I.IsHopfIdeal' R] :
    Function.Surjective (quotientBialgHom R I) :=
  Ideal.Quotient.mk_surjective

end Maps
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient"

end HopfAlgebra
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient"

end HIQ
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient"

end InlinedHopfIdealQuotient
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient"

noncomputable section

namespace PDivFrobKer

open Function IsLocalRing

section HopfIdeal

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (v : ℕ)
  (H : Type v) [CommRing H] [HopfAlgebra k H]

omit [CharP k p] in
theorem add_pow_char' {T : Type*} [CommRing T] (hT : (p : T) = 0) (x y : T) :
    (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow_prime_eq (Fact.out : p.Prime), hT, zero_mul, zero_mul, zero_mul, add_zero]

omit [CharP k p] in
theorem add_pow_q {T : Type*} [CommRing T] (hT : (p : T) = 0) (x y : T) :
    (x + y) ^ p ^ v = x ^ p ^ v + y ^ p ^ v := by
  induction v with
  | zero => rw [pow_zero, pow_one, pow_one, pow_one]
  | succ v ih => rw [pow_succ, pow_mul, ih, add_pow_char' p hT, ← pow_mul, ← pow_mul]

omit [CharP k p] in
theorem sum_pow_q {T : Type*} [CommRing T] (hT : (p : T) = 0) {ι : Type*} (s : Finset ι)
    (f : ι → T) : (∑ i ∈ s, f i) ^ p ^ v = ∑ i ∈ s, f i ^ p ^ v := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_q p v hT, ih]

private theorem _root_.PDivFrobKer.cast_eq_zero (T : Type*) [Ring T] [Algebra k T] : (p : T) = 0 := by
  rw [← map_natCast (algebraMap k T), CharP.cast_eq_zero, map_zero]

p2m_export "PDivFrobKer" "cast_eq_zero"

abbrev I : Ideal H := RingHom.ker (counitAlgHom k H)

abbrev J : Ideal H := Ideal.span ((fun a : H => a ^ p ^ v) '' (I k H : Set H))

omit [Fact p.Prime] [CharP k p] in
theorem mem_I_iff (a : H) : a ∈ I k H ↔ counit (R := k) a = 0 := RingHom.mem_ker

omit [Fact p.Prime] [CharP k p] in
theorem pow_mem_J {a : H} (ha : a ∈ I k H) : a ^ p ^ v ∈ J k p v H :=
  Ideal.subset_span ⟨a, ha, rfl⟩

omit [CharP k p] in
theorem J_le_I : J k p v H ≤ I k H := by
  rw [Ideal.span_le]
  rintro _ ⟨a, ha, rfl⟩
  exact Ideal.pow_mem_of_mem _ ha _ (pow_pos (Fact.out : p.Prime).pos v)

omit [CharP k p] in

theorem J_le_sq (hv : 1 ≤ v) : J k p v H ≤ I k H ^ 2 := by
  rw [Ideal.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have h2 : 2 ≤ p ^ v := le_trans (Fact.out : p.Prime).two_le
    (by simpa using Nat.pow_le_pow_right (Fact.out : p.Prime).pos hv)
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h2
  change a ^ p ^ v ∈ I k H ^ 2
  rw [hm, pow_add]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha 2)

def π : H →ₗ[k] H := LinearMap.id - Algebra.linearMap k H ∘ₗ Coalgebra.counit

omit [Fact p.Prime] [CharP k p] in
theorem π_apply (a : H) : π k H a = a - algebraMap k H (counit (R := k) a) := rfl

omit [Fact p.Prime] [CharP k p] in
theorem π_mem (a : H) : π k H a ∈ I k H := by
  rw [mem_I_iff, π_apply, map_sub, counit_algebraMap, sub_self]

omit [Fact p.Prime] [CharP k p] in

theorem comul_eq (x : H) :
    comul (R := k) x = x ⊗ₜ[k] (1 : H) + LinearMap.lTensor H (π k H) (comul (R := k) x) := by
  have h1 : LinearMap.lTensor H (Algebra.linearMap k H ∘ₗ Coalgebra.counit) (comul (R := k) x) =
      x ⊗ₜ[k] (1 : H) := by
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul,
      LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]
  rw [π, LinearMap.lTensor_sub, LinearMap.sub_apply, LinearMap.lTensor_id, LinearMap.id_apply, h1,
    add_sub_cancel]

theorem map_mk_comul_pow_eq_zero {x : H} (hx : x ∈ I k H) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (J k p v H)) (Ideal.Quotient.mkₐ k (J k p v H))
      (comul (R := k) (x ^ p ^ v)) = 0 := by
  have hp0 : (p : H ⊗[k] H) = 0 := cast_eq_zero k p (H ⊗[k] H)
  rw [comul_pow, comul_eq k H x, add_pow_q p v hp0, map_add]
  have h1 : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (J k p v H)) (Ideal.Quotient.mkₐ k (J k p v H))
      ((x ⊗ₜ[k] (1 : H)) ^ p ^ v) = 0 := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.map_tmul,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_J k p v H hx),
      TensorProduct.zero_tmul]
  rw [h1, zero_add]
  obtain ⟨ι, s, f, g, hrep⟩ :=
    (⟨_, _, _, _, (Coalgebra.Repr.arbitrary k x).eq⟩ :
      ∃ (ι : Type v) (s : Finset ι) (f g : ι → H), ∑ i ∈ s, f i ⊗ₜ[k] g i = comul (R := k) x)
  rw [← hrep, map_sum, sum_pow_q p v hp0, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.map_tmul,
    Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_J k p v H (π_mem k H (g i))), TensorProduct.tmul_zero]

theorem isHopfIdeal_J : (J k p v H).IsHopfIdeal' k where
  map_mkₐ_comul_eq_zero := by
    intro y hy
    have hle : J k p v H ≤ RingHom.ker
        ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (J k p v H)) (Ideal.Quotient.mkₐ k (J k p v H))).comp
          (comulAlgHom k H)) := by
      rw [Ideal.span_le]
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      exact map_mk_comul_pow_eq_zero k p v H ha
    exact hle hy
  counit_eq_zero y hy := (mem_I_iff k H y).1 (J_le_I k p v H hy)
  antipode_mem := by
    intro y hy
    have hle : J k p v H ≤ (J k p v H).comap (HopfAlgebra.antipodeAlgHom k H) := by
      rw [Ideal.span_le]
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_pow, HopfAlgebra.antipodeAlgHom_apply]
      refine pow_mem_J k p v H ?_
      rw [mem_I_iff, HopfAlgebra.counit_antipode]
      exact (mem_I_iff k H a).1 ha
    exact hle hy

end HopfIdeal
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient"

section Count

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (v : ℕ)
  (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]

attribute [local instance] isHopfIdeal_J

local notation "B" => A ⧸ J k p v A

scoped instance finite_quot : Module.Finite k B :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ k (J k p v A)).toLinearMap Ideal.Quotient.mk_surjective

abbrev πJ : A →ₐc[k] B := HopfAlgebra.quotientBialgHom k (J k p v A)

theorem πJ_apply (x : A) : πJ k p v A x = Ideal.Quotient.mk (J k p v A) x := rfl

theorem πJ_surjective : Surjective (πJ k p v A) := Ideal.Quotient.mk_surjective

abbrev K : Subalgebra k A := HopfAlgebra.hopfKer (πJ k p v A)

theorem finrank_K_mul :
    Module.finrank k ↥(K k p v A) * Module.finrank k B = Module.finrank k A := by
  obtain ⟨-, -, -, hrank⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
      (πJ k p v A) (πJ_surjective k p v A)
  have h := hrank ⟨⊥, Ideal.isPrime_bot⟩
  rwa [Module.rankAtStalk_eq_finrank_of_free] at h

end Count
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient"

section Pairing

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
  {A : Type v} [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
  [Coalgebra.IsCocomm R A]

omit [Fact p.Prime] [CharP R p] [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A] in
theorem nsmulAlgHom_comp_nsmulAlgHom (m n : ℕ) :
    (PDivisibleGroup.Hopf.nsmulAlgHom R A m).comp (PDivisibleGroup.Hopf.nsmulAlgHom R A n) =
      PDivisibleGroup.Hopf.nsmulAlgHom R A (m * n) := by
  rw [PDivisibleGroup.Hopf.nsmulAlgHom_mul]
  apply WithConv.toConv_injective
  rw [WithConv.toConv_ofConv]
  exact (PDivisibleGroup.Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom
    (PDivisibleGroup.Hopf.nsmulAlgHom R A m) n).symm

theorem pow_q_apply_pow_q (v : ℕ) (φ : CartierDual R A) (a : A) :
    (φ ^ p ^ v) (a ^ p ^ v) = φ (PDivisibleGroup.Hopf.nsmulAlgHom R A (p ^ v) a) ^ p ^ v := by
  induction v generalizing a with
  | zero => rw [pow_zero, pow_one, pow_one, pow_one, PDivisibleGroup.Hopf.nsmulAlgHom_one]; rfl
  | succ v ih =>
    rw [pow_succ, pow_mul, pow_mul, CartierDual.pow_apply_pow_eq_apply_nsmulAlgHom_pow,
      map_pow (PDivisibleGroup.Hopf.nsmulAlgHom R A p), ih, ← pow_mul, ← AlgHom.comp_apply,
      nsmulAlgHom_comp_nsmulAlgHom]

end Pairing
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient"

section Kill

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (v : ℕ)
  (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]

theorem apply_mul_eq_sum (ψ : CartierDual k A) {ι : Type*} (s : Finset ι) (f g : ι → CartierDual k A)
    (h : ∑ j ∈ s, f j ⊗ₜ[k] g j = comul (R := k) ψ) (b x : A) :
    ψ (b * x) = ∑ j ∈ s, f j b * g j x := by
  rw [← CartierDual.comul_pairing, ← h, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]
  rfl

theorem comul_pow_q (ψ : CartierDual k A) {ι : Type*} (s : Finset ι) (f g : ι → CartierDual k A)
    (h : ∑ j ∈ s, f j ⊗ₜ[k] g j = comul (R := k) ψ) :
    ∑ j ∈ s, (f j ^ p ^ v) ⊗ₜ[k] (g j ^ p ^ v) = comul (R := k) (ψ ^ p ^ v) := by
  have hp0 : (p : CartierDual k A ⊗[k] CartierDual k A) = 0 := cast_eq_zero k p _
  have hc : comul (R := k) (ψ ^ p ^ v) = comul (R := k) ψ ^ p ^ v := comul_pow ψ _
  rw [hc, ← h]
  refine Eq.trans ?_ (sum_pow_q p v hp0 s fun j => f j ⊗ₜ[k] g j).symm
  exact Finset.sum_congr rfl fun j _ => (Algebra.TensorProduct.tmul_pow (f j) (g j) (p ^ v)).symm

theorem pow_apply_one (ψ : CartierDual k A) (n : ℕ) : (ψ ^ n) (1 : A) = ψ 1 ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, CartierDual.one_apply, counit_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, CartierDual.mul_apply, comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.dualDistrib_apply, CartierDual.toDual_apply, CartierDual.toDual_apply, ih]

end Kill
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient"

section KillG

variable (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (v : ℕ) {h : ℕ} (G : PDivisibleGroup k p h)

theorem pow_q_apply_eq_zero_of_mem_J (hv : 1 ≤ v) {x : G.level v} (hx : x ∈ J k p v (G.level v)) :
    ∀ ψ : CartierDual k (G.level v), (ψ ^ p ^ v) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    intro ψ
    rw [pow_q_apply_pow_q, PDivisibleGroup.nsmulAlgHom_pow_level_apply, (mem_I_iff k _ a).1 ha, map_zero,
      map_zero, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
  | zero => intro ψ; exact map_zero (ψ ^ p ^ v)
  | add x y _ _ hx hy => intro ψ; rw [map_add, hx, hy, add_zero]
  | smul b x _ hx =>
    intro ψ
    obtain ⟨ι, s, f, g, hrep⟩ :=
      (⟨_, _, _, _, (Coalgebra.Repr.arbitrary k ψ).eq⟩ :
        ∃ (ι : Type) (s : Finset ι) (f g : ι → CartierDual k (G.level v)),
          ∑ i ∈ s, f i ⊗ₜ[k] g i = comul (R := k) ψ)
    rw [smul_eq_mul, apply_mul_eq_sum k _ (ψ ^ p ^ v) s _ _ (comul_pow_q k p v _ ψ s f g hrep)]
    exact Finset.sum_eq_zero fun j _ => by rw [hx (g j), mul_zero]

end KillG
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient"

section Small

variable (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (v : ℕ) {h : ℕ}
  (G : PDivisibleGroup k p h)

attribute [local instance] isHopfIdeal_J

abbrev Jd : Ideal (CartierDual k (G.level v)) := J k p v (CartierDual k (G.level v))

theorem mul_apply_eq_zero_of_mem_K (hv : 1 ≤ v) {a : G.level v} (ha : a ∈ K k p v (G.level v))
    {θ : CartierDual k (G.level v)} (hθ : θ ∈ Jd k p v G) :
    ∀ χ : CartierDual k (G.level v), (χ * θ) a = 0 := by
  induction hθ using Submodule.span_induction with
  | mem θ hθ =>
    obtain ⟨φ, hφ, rfl⟩ := hθ
    intro χ
    have hφ1 : φ 1 = 0 := by
      have := (mem_I_iff k _ φ).1 hφ
      rwa [CartierDual.counit_apply] at this

    set B := G.level v ⧸ J k p v (G.level v)
    let φ' : G.level v →ₗ[k] k := CartierDual.toDual k _ (φ ^ p ^ v)
    have hle : (J k p v (G.level v)).restrictScalars k ≤ LinearMap.ker φ' := fun x hx =>
      pow_q_apply_eq_zero_of_mem_J k p v G hv hx φ
    let ψ' : B →ₗ[k] k :=
      (((J k p v (G.level v)).restrictScalars k).liftQ φ' hle).comp
        (Submodule.Quotient.restrictScalarsEquiv k (J k p v (G.level v))).symm.toLinearMap
    have hψ' : ∀ x : G.level v, ψ' (Ideal.Quotient.mk (J k p v (G.level v)) x) = (φ ^ p ^ v) x := by
      intro x
      change ((J k p v (G.level v)).restrictScalars k).liftQ φ' hle
        ((Submodule.Quotient.restrictScalarsEquiv k (J k p v (G.level v))).symm (Submodule.Quotient.mk x)) = _
      rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]
      rfl

    let ℓ : G.level v ⊗[k] B →ₗ[k] k :=
      LinearMap.mul' k k ∘ₗ TensorProduct.map (CartierDual.toDual k _ χ) ψ'
    have hℓ : ∀ (x : G.level v) (y : B), ℓ (x ⊗ₜ[k] y) = χ x * ψ' y := fun x y => by
      change LinearMap.mul' k k (TensorProduct.map (CartierDual.toDual k _ χ) ψ' (x ⊗ₜ[k] y)) = _
      rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
      rfl
    have hco : HopfAlgebra.coaction (πJ k p v (G.level v)) a = a ⊗ₜ[k] 1 := ha

    obtain ⟨ι, s, f, g, hrep⟩ :=
      (⟨_, _, _, _, (Coalgebra.Repr.arbitrary k a).eq⟩ :
        ∃ (ι : Type) (s : Finset ι) (f g : ι → G.level v), ∑ i ∈ s, f i ⊗ₜ[k] g i = comul (R := k) a)
    have h1 : ℓ (HopfAlgebra.coaction (πJ k p v (G.level v)) a) = (χ * φ ^ p ^ v) a := by
      rw [HopfAlgebra.coaction_apply, CartierDual.mul_apply, ← hrep]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show χ (f i) * ψ' (Ideal.Quotient.mk _ (g i)) = χ (f i) * (φ ^ p ^ v) (g i)
      rw [hψ']
    have h2 : ℓ (a ⊗ₜ[k] (1 : B)) = 0 := by
      rw [hℓ, ← map_one (Ideal.Quotient.mk (J k p v (G.level v))), hψ', pow_apply_one k, hφ1,
        zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), mul_zero]
    rw [← h1, hco, h2]
  | zero => intro χ; rw [mul_zero]; rfl
  | add x y _ _ hx hy => intro χ; rw [mul_add]; change (χ * x) a + (χ * y) a = 0; rw [hx, hy, add_zero]
  | smul c x _ hx => intro χ; rw [smul_eq_mul, ← mul_assoc]; exact hx (χ * c)

theorem apply_eq_zero_of_mem_K (hv : 1 ≤ v) {a : G.level v} (ha : a ∈ K k p v (G.level v))
    {θ : CartierDual k (G.level v)} (hθ : θ ∈ Jd k p v G) : θ a = 0 := by
  have := mul_apply_eq_zero_of_mem_K k p v G hv ha hθ 1
  rwa [one_mul] at this

def W : Submodule k (Module.Dual k (G.level v)) :=
  ((Jd k p v G).restrictScalars k).map (CartierDual.toDual k (G.level v)).toLinearMap

theorem K_le_dualCoannihilator (hv : 1 ≤ v) :
    (K k p v (G.level v)).toSubmodule ≤ (W k p v G).dualCoannihilator := by
  intro a ha
  rw [Submodule.mem_dualCoannihilator]
  rintro _ ⟨θ, hθ, rfl⟩
  exact apply_eq_zero_of_mem_K k p v G hv ha hθ

theorem finrank_quotient_add {T : Type} [CommRing T] [Algebra k T] [Module.Finite k T] (𝔞 : Ideal T) :
    Module.finrank k (T ⧸ 𝔞) + Module.finrank k ↥(𝔞.restrictScalars k) = Module.finrank k T := by
  let f : T →ₗ[k] T ⧸ 𝔞 := (Ideal.Quotient.mkₐ k 𝔞).toLinearMap
  have hker : LinearMap.ker f = 𝔞.restrictScalars k := by
    ext x
    rw [LinearMap.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.2 Ideal.Quotient.mk_surjective
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, hker] at h
  exact h

theorem finrank_K_le (hv : 1 ≤ v) :
    Module.finrank k ↥(K k p v (G.level v)) ≤
      Module.finrank k (CartierDual k (G.level v) ⧸ Jd k p v G) := by
  have h1 : Module.finrank k ↥(K k p v (G.level v)) ≤ Module.finrank k ↥(W k p v G).dualCoannihilator :=
    Submodule.finrank_mono (K_le_dualCoannihilator k p v G hv)
  have h2 := Subspace.finrank_add_finrank_dualCoannihilator_eq (W k p v G)
  have h3 : Module.finrank k ↥(W k p v G) = Module.finrank k ↥((Jd k p v G).restrictScalars k) :=
    LinearEquiv.finrank_map_eq _ _
  have h4 := finrank_quotient_add k (Jd k p v G)
  have h6 : Module.finrank k (CartierDual k (G.level v)) = Module.finrank k (G.level v) :=
    CartierDual.finrank_eq k (G.level v)
  omega

theorem map_J_equiv {G' : PDivisibleGroup k p h} (D : G.CartierDuality G') :
    (J k p v (G'.level v)).map ((D.equiv v).toAlgEquiv : G'.level v →ₐ[k] CartierDual k (G.level v)) =
      Jd k p v G := by
  set e := ((D.equiv v).toAlgEquiv : G'.level v →ₐ[k] CartierDual k (G.level v))
  have he : ∀ x, e x = D.equiv v x := fun x => rfl
  have hesurj : Surjective e := (D.equiv v).toAlgEquiv.surjective
  rw [Ideal.map_span, ← Set.image_comp]
  congr 1
  ext θ
  simp only [Set.mem_image, Function.comp_apply, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨e a, ?_, (map_pow e a _).symm⟩
    rw [mem_I_iff, he, CoalgHomClass.counit_comp_apply]
    exact (mem_I_iff k _ a).1 ha
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨a, rfl⟩ := hesurj φ
    refine ⟨a, ?_, by rw [map_pow]⟩
    rw [mem_I_iff]
    have := (mem_I_iff k _ (e a)).1 hφ
    rwa [he, CoalgHomClass.counit_comp_apply] at this

theorem finrank_quot_Jd_eq {G' : PDivisibleGroup k p h} (D : G.CartierDuality G') :
    Module.finrank k (CartierDual k (G.level v) ⧸ Jd k p v G) =
      Module.finrank k (G'.level v ⧸ J k p v (G'.level v)) := by
  have e := (Ideal.quotientEquivAlg (J k p v (G'.level v)) (Jd k p v G) (D.equiv v).toAlgEquiv
    (map_J_equiv k p v G D).symm).toLinearEquiv
  exact e.finrank_eq.symm

end Small
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient"

section Upper

variable (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (v : ℕ) {h : ℕ}
  (G : PDivisibleGroup k p h)

theorem cotangentMap_bijective (u : ℕ) (hu : 1 ≤ u) : Bijective (G.cotangentMap u) := by
  refine ⟨?_, G.cotangentMap_surjective u⟩
  have hpu : (p : k) ^ u = 0 := by
    rw [CharP.cast_eq_zero, zero_pow (by omega)]
  rw [← LinearMap.ker_eq_bot, (G.ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot u).1, hpu,
    Ideal.span_singleton_eq_bot.2 rfl, Submodule.bot_smul]

def equivOne : (j : ℕ) → (G.Cotangent (1 + j) ≃ₗ[k] G.Cotangent 1)
  | 0 => LinearEquiv.refl k _
  | j + 1 =>
    (LinearEquiv.ofBijective (G.cotangentMap (1 + j))
      (cotangentMap_bijective k p G (1 + j) (Nat.le_add_right 1 j))).trans (equivOne j)

theorem finrank_cotangent_eq (hv : 1 ≤ v) :
    Module.finrank k (G.Cotangent v) = Module.finrank k (G.Cotangent 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, v = 1 + j := ⟨v - 1, by omega⟩
  exact (equivOne k p G j).finrank_eq

abbrev C : Type := G.level v ⧸ J k p v (G.level v)

def εC : C k p v G →ₐ[k] k :=
  Ideal.Quotient.liftₐ (J k p v (G.level v)) (counitAlgHom k (G.level v))
    fun a ha => (mem_I_iff k _ a).1 (J_le_I k p v _ ha)

theorem εC_mk (a : G.level v) : εC k p v G (Ideal.Quotient.mk _ a) = counit (R := k) a := by
  rw [εC, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

def nC : Ideal (C k p v G) := (I k (G.level v)).map (Ideal.Quotient.mk (J k p v (G.level v)))

theorem ker_εC : RingHom.ker (εC k p v G) = nC k p v G := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, εC_mk] at hx
    exact Ideal.mem_map_of_mem _ ((mem_I_iff k _ a).2 hx)
  · rw [nC, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, εC_mk]
    exact (mem_I_iff k _ a).1 ha

theorem mem_nC_iff (x : C k p v G) : x ∈ nC k p v G ↔ εC k p v G x = 0 := by
  rw [← ker_εC, RingHom.mem_ker]

theorem isNilpotent_nC : IsNilpotent (nC k p v G) := by
  haveI : IsNoetherianRing (G.level v) := isNoetherian_of_tower k (inferInstance : IsNoetherian k _)
  have hrad : I k (G.level v) ≤ (J k p v (G.level v)).radical := fun a ha =>
    ⟨p ^ v, pow_mem_J k p v _ ha⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  refine ⟨N, ?_⟩
  rw [nC, ← Ideal.map_pow, Ideal.zero_eq_bot, eq_bot_iff]
  refine le_trans (Ideal.map_mono hN) ?_
  rw [Ideal.map_quotient_self]

theorem isUnit_of_εC_ne_zero {x : C k p v G} (hx : εC k p v G x ≠ 0) : IsUnit x := by
  have hdec : x = algebraMap k _ (εC k p v G x) + (x - algebraMap k _ (εC k p v G x)) := by abel
  rw [hdec]
  refine IsNilpotent.isUnit_add_left_of_commute ?_ ((isUnit_iff_ne_zero.2 hx).map (algebraMap k _))
    (Commute.all _ _)
  obtain ⟨N, hN⟩ := isNilpotent_nC k p v G
  have hmem : x - algebraMap k _ (εC k p v G x) ∈ nC k p v G := by
    rw [mem_nC_iff, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  refine ⟨N, ?_⟩
  have := Ideal.pow_mem_pow hmem N
  rw [hN, Ideal.zero_eq_bot] at this
  exact (Submodule.mem_bot _).1 this

scoped instance nontrivial_C : Nontrivial (C k p v G) :=
  ⟨⟨0, 1, fun h01 => zero_ne_one (α := k) (by simpa using congrArg (εC k p v G) h01)⟩⟩

scoped instance isLocalRing_C : IsLocalRing (C k p v G) := by
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  have key : ∀ x : C k p v G, x ∈ nonunits (C k p v G) → εC k p v G x = 0 := fun x hx => by
    by_contra hcon
    exact hx (isUnit_of_εC_ne_zero k p v G hcon)
  intro hu
  have h1 : εC k p v G (a + b) = 0 := by rw [map_add, key a ha, key b hb, add_zero]
  exact (hu.map (εC k p v G)).ne_zero h1

theorem maximalIdeal_C : maximalIdeal (C k p v G) = nC k p v G := by
  apply le_antisymm
  · intro x hx
    rw [mem_nC_iff]
    by_contra hcon
    exact hx (isUnit_of_εC_ne_zero k p v G hcon)
  · intro x hx
    rw [mem_nC_iff] at hx
    intro hu
    exact (hu.map (εC k p v G)).ne_zero hx

theorem isAdicComplete_of_isNilpotent {T : Type*} [CommRing T] (𝔞 : Ideal T) (h𝔞 : IsNilpotent 𝔞) :
    IsAdicComplete 𝔞 T := by
  obtain ⟨N, hN⟩ := h𝔞
  have hz : ∀ m, N ≤ m → 𝔞 ^ m • (⊤ : Submodule T T) = ⊥ := fun m hm => by
    apply le_antisymm _ bot_le
    calc 𝔞 ^ m • (⊤ : Submodule T T) ≤ 𝔞 ^ N • ⊤ := Submodule.smul_mono_left (Ideal.pow_le_pow_right hm)
      _ = ⊥ := by rw [hN, Submodule.zero_eq_bot, Submodule.bot_smul]
  haveI : IsHausdorff 𝔞 T := ⟨fun x hx => by
    have h1 := hx N
    rw [hz N le_rfl, SModEq.bot] at h1
    exact h1⟩
  haveI : IsPrecomplete 𝔞 T := ⟨fun f hf => ⟨f N, fun m => by
    by_cases hm : m ≤ N
    · exact hf hm
    · have h1 : f N ≡ f m [SMOD 𝔞 ^ N • (⊤ : Submodule T T)] := hf (le_of_not_ge hm)
      rw [hz N le_rfl, SModEq.bot] at h1
      rw [hz m (le_of_not_ge hm), SModEq.bot]
      exact h1.symm⟩⟩
  exact ⟨⟩

scoped instance isAdicComplete_C : IsAdicComplete (maximalIdeal (C k p v G)) (C k p v G) := by
  rw [maximalIdeal_C]
  exact isAdicComplete_of_isNilpotent _ (isNilpotent_nC k p v G)

scoped instance isAdicComplete_k : IsAdicComplete (maximalIdeal k) k := by
  rw [IsLocalRing.maximalIdeal_eq_bot]
  infer_instance

scoped instance isNoetherianRing_C : IsNoetherianRing (C k p v G) :=
  isNoetherian_of_tower k (inferInstance : IsNoetherian k _)

theorem residue_comp_surjective : Surjective (⇑(residue (C k p v G)) ∘ ⇑(algebraMap k (C k p v G))) := by
  intro q
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective q
  refine ⟨εC k p v G x, ?_⟩
  change residue _ (algebraMap k _ (εC k p v G x)) = residue _ x
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, maximalIdeal_C, mem_nC_iff, map_sub,
    AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

scoped instance finite_cotangent (w : ℕ) : Module.Finite k (G.Cotangent w) := by
  let f : ((G.augIdeal w).restrictScalars k) →ₗ[k] G.Cotangent w :=
    { toFun := fun x => (G.augIdeal w).toCotangent ⟨x.1, x.2⟩
      map_add' := fun x y => by
        rw [← map_add]; rfl
      map_smul' := fun r x => by
        rw [RingHom.id_apply, ← LinearMap.map_smul_of_tower]; rfl }
  refine Module.Finite.of_surjective f fun y => ?_
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ y
  exact ⟨⟨x.1, x.2⟩, rfl⟩

abbrev nn : ℕ := Module.finrank k (G.Cotangent 1)

theorem exists_gens (hv : 1 ≤ v) : ∃ t : Fin (nn k p G) → I k (G.level v),
    Submodule.span k (Set.range fun i => (I k (G.level v)).toCotangent (t i)) = ⊤ := by
  let b : Module.Basis (Fin (nn k p G)) k (G.Cotangent v) :=
    Module.finBasisOfFinrankEq k _ (finrank_cotangent_eq k p v G hv)
  have ht : ∀ i, ∃ t : I k (G.level v), (I k (G.level v)).toCotangent t = b i := fun i =>
    Ideal.toCotangent_surjective _ (b i)
  choose t ht using ht
  refine ⟨t, ?_⟩
  have : (Set.range fun i => (I k (G.level v)).toCotangent (t i)) = Set.range b := by
    congr 1; funext i; exact ht i
  rw [this]
  exact b.span_eq

def tt (hv : 1 ≤ v) : Fin (nn k p G) → I k (G.level v) := (exists_gens k p v G hv).choose

theorem span_tt (hv : 1 ≤ v) :
    Submodule.span k (Set.range fun i => (I k (G.level v)).toCotangent (tt k p v G hv i)) = ⊤ :=
  (exists_gens k p v G hv).choose_spec

def tau (hv : 1 ≤ v) (i : Fin (nn k p G)) : C k p v G := Ideal.Quotient.mk _ (tt k p v G hv i : G.level v)

theorem tau_mem (hv : 1 ≤ v) (i : Fin (nn k p G)) : tau k p v G hv i ∈ nC k p v G :=
  Ideal.mem_map_of_mem _ (tt k p v G hv i).2

theorem tau_pow (hv : 1 ≤ v) (i : Fin (nn k p G)) : tau k p v G hv i ^ p ^ v = 0 := by
  rw [tau, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact pow_mem_J k p v _ (tt k p v G hv i).2

theorem tau_pow_eq_zero_of_le (hv : 1 ≤ v) (i : Fin (nn k p G)) {e : ℕ} (he : p ^ v ≤ e) :
    tau k p v G hv i ^ e = 0 := by
  calc tau k p v G hv i ^ e = tau k p v G hv i ^ p ^ v * tau k p v G hv i ^ (e - p ^ v) := by
        rw [← pow_add, Nat.add_sub_of_le he]
    _ = 0 := by rw [tau_pow]; exact zero_mul _

theorem maximalIdeal_le_gens (hv : 1 ≤ v) :
    maximalIdeal (C k p v G) ≤ Ideal.span (Set.range (tau k p v G hv)) ⊔ maximalIdeal (C k p v G) ^ 2 ⊔
      (maximalIdeal k).map (algebraMap k (C k p v G)) := by
  intro x hx
  rw [maximalIdeal_C] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  set II := I k (G.level v)
  have hmem : II.toCotangent ⟨a, ha⟩ ∈ Submodule.span k (Set.range fun i => II.toCotangent (tt k p v G hv i)) := by
    rw [span_tt]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hmem
  have hsum : ∑ i, c i • II.toCotangent (tt k p v G hv i) = II.toCotangent (∑ i, c i • tt k p v G hv i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (II.toCotangent.map_smul_of_tower _ _).symm
  rw [hsum] at hc
  have hdiff : a - ((∑ i, c i • tt k p v G hv i : II) : G.level v) ∈ II ^ 2 := by
    have : (⟨a, ha⟩ : II) - (∑ i, c i • tt k p v G hv i) ∈ LinearMap.ker II.toCotangent := by
      rw [LinearMap.mem_ker, map_sub, hc, sub_self]
    rw [Ideal.mem_toCotangent_ker] at this
    exact this
  have hgen : Ideal.Quotient.mk (J k p v (G.level v)) ((∑ i, c i • tt k p v G hv i : II) : G.level v) ∈
      Ideal.span (Set.range (tau k p v G hv)) := by
    rw [Submodule.coe_sum, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have h2 : Ideal.Quotient.mk (J k p v (G.level v)) (a - ((∑ i, c i • tt k p v G hv i : II) : G.level v)) ∈
      nC k p v G ^ 2 := by
    rw [nC, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hdiff
  have hdec : Ideal.Quotient.mk (J k p v (G.level v)) a =
      Ideal.Quotient.mk _ ((∑ i, c i • tt k p v G hv i : II) : G.level v) +
        Ideal.Quotient.mk _ (a - ((∑ i, c i • tt k p v G hv i : II) : G.level v)) := by
    rw [← map_add, add_sub_cancel]
  rw [hdec]
  exact Ideal.mem_sup_left (Ideal.add_mem _ (Ideal.mem_sup_left hgen) (Ideal.mem_sup_right h2))

theorem exists_psi (hv : 1 ≤ v) : ∃ ψ : MvPowerSeries (Fin (nn k p G)) k →ₐ[k] C k p v G,
    (∀ i, ψ (MvPowerSeries.X i) = tau k p v G hv i) ∧ Surjective ψ :=
  IsLocalRing.exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span (residue_comp_surjective k p v G)
    (tau k p v G hv) (fun i => by rw [maximalIdeal_C]; exact tau_mem k p v G hv i) (maximalIdeal_le_gens k p v G hv)

def psi (hv : 1 ≤ v) : MvPowerSeries (Fin (nn k p G)) k →ₐ[k] C k p v G := (exists_psi k p v G hv).choose

theorem psi_X (hv : 1 ≤ v) (i : Fin (nn k p G)) : psi k p v G hv (MvPowerSeries.X i) = tau k p v G hv i :=
  (exists_psi k p v G hv).choose_spec.1 i

theorem psi_surjective (hv : 1 ≤ v) : Surjective (psi k p v G hv) := (exists_psi k p v G hv).choose_spec.2

theorem psi_eq_zero_of_coeff (hv : 1 ≤ v) (N : ℕ) (hN : nC k p v G ^ N = ⊥) (f : MvPowerSeries (Fin (nn k p G)) k)
    (hf : ∀ m : Fin (nn k p G) →₀ ℕ, m.degree < N → MvPowerSeries.coeff m f = 0) : psi k p v G hv f = 0 := by
  have hmem := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero N f hf
  have hle : (Ideal.span (Set.range (MvPowerSeries.X : Fin (nn k p G) → _))).map (psi k p v G hv) ≤
      nC k p v G := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [psi_X]
    exact tau_mem k p v G hv i
  have h2 : psi k p v G hv f ∈ ((Ideal.span (Set.range (MvPowerSeries.X : Fin (nn k p G) → _))) ^ N).map
      (psi k p v G hv) := Ideal.mem_map_of_mem _ hmem
  rw [Ideal.map_pow] at h2
  have h3 := Ideal.pow_right_mono hle N h2
  rw [hN] at h3
  exact (Submodule.mem_bot _).1 h3

def mg (g : Fin (nn k p G) → Fin (p ^ v)) : Fin (nn k p G) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (g i : ℕ)

@[scoped simp] theorem mg_apply (g : Fin (nn k p G) → Fin (p ^ v)) (i : Fin (nn k p G)) : mg k p v G g i = (g i : ℕ) := rfl

def vfam (hv : 1 ≤ v) (g : Fin (nn k p G) → Fin (p ^ v)) : C k p v G := ∏ i, tau k p v G hv i ^ (g i : ℕ)

def mono (hv : 1 ≤ v) (m : Fin (nn k p G) →₀ ℕ) : C k p v G := ∏ i, tau k p v G hv i ^ m i

theorem mono_mg (hv : 1 ≤ v) (g : Fin (nn k p G) → Fin (p ^ v)) : mono k p v G hv (mg k p v G g) = vfam k p v G hv g :=
  rfl

theorem mono_eq_zero (hv : 1 ≤ v) (m : Fin (nn k p G) →₀ ℕ) (hm : ¬ ∀ i, m i < p ^ v) : mono k p v G hv m = 0 := by
  push Not at hm
  obtain ⟨i, hi⟩ := hm
  exact Finset.prod_eq_zero (f := fun j => tau k p v G hv j ^ m j) (Finset.mem_univ i)
    (tau_pow_eq_zero_of_le k p v G hv i hi)

theorem aeval_coe_eq_psi (hv : 1 ≤ v) (P : MvPolynomial (Fin (nn k p G)) k) :
    psi k p v G hv (P : MvPowerSeries (Fin (nn k p G)) k) = MvPolynomial.aeval (tau k p v G hv) P := by
  have hext : (psi k p v G hv).comp (MvPolynomial.coeToMvPowerSeries.algHom k) =
      MvPolynomial.aeval (tau k p v G hv) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
      MvPowerSeries.map_id, MvPolynomial.coe_X, RingHom.id_apply, psi_X, MvPolynomial.aeval_X]
  have hP := DFunLike.congr_fun hext P
  rw [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
      MvPowerSeries.map_id, RingHom.id_apply] at hP
  exact hP

theorem psi_eq_sum (hv : 1 ≤ v) (f : MvPowerSeries (Fin (nn k p G)) k) :
    psi k p v G hv f = ∑ g : Fin (nn k p G) → Fin (p ^ v), (MvPowerSeries.coeff (mg k p v G g) f) • vfam k p v G hv g := by
  classical
  obtain ⟨N, hN⟩ := isNilpotent_nC k p v G
  rw [Ideal.zero_eq_bot] at hN
  set q := p ^ v with hq
  have hq1 : 0 < q := pow_pos (Nat.Prime.pos Fact.out) _
  set D := N + q with hD
  let bnd : Fin (nn k p G) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => D
  have hbnd : ∀ i, bnd i = D := fun i => rfl
  set P := MvPowerSeries.trunc' k bnd f with hP
  have hrest : psi k p v G hv (f - (P : MvPowerSeries (Fin (nn k p G)) k)) = 0 := by
    apply psi_eq_zero_of_coeff k p v G hv (D + 1)
    · exact le_antisymm (le_trans (Ideal.pow_le_pow_right (by omega)) hN.le) bot_le
    · intro m hm
      have hle : m ≤ bnd := by
        rw [Finsupp.le_def]
        intro i
        rw [hbnd]
        have := Finsupp.le_degree i m
        omega
      rw [map_sub, MvPolynomial.coeff_coe, hP, MvPowerSeries.coeff_trunc', if_pos hle, sub_self]
  have hsplit : psi k p v G hv f = psi k p v G hv (P : MvPowerSeries (Fin (nn k p G)) k) := by
    have : f = (P : MvPowerSeries (Fin (nn k p G)) k) + (f - (P : MvPowerSeries (Fin (nn k p G)) k)) := by abel
    conv_lhs => rw [this, map_add]
    rw [hrest, add_zero]
  rw [hsplit, aeval_coe_eq_psi]
  have hPsum : P = ∑ m ∈ Finset.Iic bnd, MvPolynomial.monomial m (MvPowerSeries.coeff m f) := by
    rw [hP]; exact MvPowerSeries.truncFinset_apply f
  rw [hPsum, map_sum]
  have hterm : ∀ m : Fin (nn k p G) →₀ ℕ, MvPolynomial.aeval (tau k p v G hv) (MvPolynomial.monomial m
      (MvPowerSeries.coeff m f)) = (MvPowerSeries.coeff m f) • mono k p v G hv m := by
    intro m
    rw [MvPolynomial.aeval_monomial, mono, Finsupp.prod_fintype]
    · exact (Algebra.smul_def _ _).symm
    · intro i; exact pow_zero _
  simp_rw [hterm]
  rw [← Finset.sum_filter_of_ne (p := fun m => ∀ i, m i < q) (fun m _ hne => by
    by_contra hb
    exact hne (by rw [mono_eq_zero k p v G hv m hb, smul_zero]))]
  refine Finset.sum_nbij' (fun m i => ⟨m i % q, Nat.mod_lt _ hq1⟩) (fun g => mg k p v G g) ?_ ?_ ?_ ?_ ?_
  · intro m _; exact Finset.mem_univ _
  · intro g _
    rw [Finset.mem_filter, Finset.mem_Iic, Finsupp.le_def]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [mg_apply, hbnd]; have := (g i).2; omega
    · exact (g i).2
  · intro m hm
    rw [Finset.mem_filter] at hm
    ext i
    rw [mg_apply]
    exact Nat.mod_eq_of_lt (hm.2 i)
  · intro g _
    funext i
    exact Fin.ext (Nat.mod_eq_of_lt (g i).2)
  · intro m hm
    rw [Finset.mem_filter] at hm
    have hmg : mg k p v G (fun i => ⟨m i % q, Nat.mod_lt _ hq1⟩) = m := by
      ext i; rw [mg_apply]; exact Nat.mod_eq_of_lt (hm.2 i)
    rw [hmg, ← mono_mg, hmg]

theorem span_vfam (hv : 1 ≤ v) : ⊤ ≤ Submodule.span k (Set.range (vfam k p v G hv)) := by
  rintro c -
  obtain ⟨f, rfl⟩ := psi_surjective k p v G hv c
  rw [psi_eq_sum]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

theorem finrank_C_le (hv : 1 ≤ v) : Module.finrank k (C k p v G) ≤ (p ^ v) ^ nn k p G := by
  classical
  have h1 : Module.finrank k (C k p v G) = Module.finrank k (⊤ : Submodule k (C k p v G)) :=
    (finrank_top k (C k p v G)).symm
  have h2 : (⊤ : Submodule k (C k p v G)) = Submodule.span k (Set.range (vfam k p v G hv)) :=
    eq_top_iff.2 (span_vfam k p v G hv) |>.symm
  rw [h1, h2]
  refine le_trans (finrank_range_le_card (vfam k p v G hv)) ?_
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end Upper
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient"

section Main

variable (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] {h : ℕ} (G : PDivisibleGroup k p h)

theorem finrank_zero :
    Module.finrank k (G.level 0 ⧸ J k p 0 (G.level 0)) = 1 := by
  have hJ : J k p 0 (G.level 0) = I k (G.level 0) := by
    apply le_antisymm (J_le_I k p 0 _)
    intro a ha
    have := pow_mem_J k p 0 _ ha
    rwa [pow_zero, pow_one] at this
  have hsurj : Surjective (counitAlgHom k (G.level 0)) := fun c =>
    ⟨algebraMap k _ c, by rw [counitAlgHom_apply, counit_algebraMap]⟩
  rw [hJ]
  exact ((Ideal.quotientKerAlgEquivOfSurjective hsurj).toLinearEquiv.finrank_eq).trans (Module.finrank_self k)

theorem finrank_pos (v : ℕ) (hv : 1 ≤ v) :
    Module.finrank k (G.level v ⧸ J k p v (G.level v)) = p ^ (v * nn k p G) := by
  obtain ⟨G', ⟨D⟩⟩ := G.exists_isCartierDual
  set x := Module.finrank k (G.level v ⧸ J k p v (G.level v))
  set n := nn k p G
  set n' := nn k p G'
  set q := p ^ v with hq
  have hnn' : n + n' = h :=
    PDivisibleGroup.CartierDuality.finrank_cotangent_one_add_finrank_cotangent_one_eq_height D
  have hU : x ≤ q ^ n := finrank_C_le k p v G hv
  have hU' : Module.finrank k (G'.level v ⧸ J k p v (G'.level v)) ≤ q ^ n' := finrank_C_le k p v G' hv
  have hK : Module.finrank k ↥(K k p v (G.level v)) * x = q ^ n * q ^ n' := by
    rw [finrank_K_mul, G.finrank_level v, ← pow_add, hnn', hq, ← pow_mul]
  have hKle : Module.finrank k ↥(K k p v (G.level v)) ≤ q ^ n' :=
    le_trans ((finrank_K_le k p v G hv).trans_eq (finrank_quot_Jd_eq k p v G D)) hU'
  have hqpos : 0 < q ^ n' := pow_pos (pow_pos (Nat.Prime.pos Fact.out) _) _
  have hlow : q ^ n ≤ x := by
    have h1 : q ^ n' * q ^ n ≤ q ^ n' * x := by
      calc q ^ n' * q ^ n = Module.finrank k ↥(K k p v (G.level v)) * x := by rw [hK, mul_comm]
        _ ≤ q ^ n' * x := Nat.mul_le_mul_right _ hKle
    exact Nat.le_of_mul_le_mul_left h1 hqpos
  rw [pow_mul]
  exact le_antisymm hU hlow

end Main
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient"

end PDivFrobKer
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.PDivFrobKer"

end
p2m_reactivate "P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.Ideal P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.HopfAlgebra.HopfIdealQuotient P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one.PDivFrobKer"

open PDivFrobKer in
theorem solution
    {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {h : ℕ}
    (G : PDivisibleGroup k p h) (v : ℕ) :
    Module.finrank k (G.level v ⧸ Ideal.span ((fun a : G.level v => a ^ p ^ v) ''
        (G.augIdeal v : Set (G.level v)))) =
      p ^ (v * Module.finrank k (G.Cotangent 1)) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [zero_mul, pow_zero]
    exact finrank_zero k p G
  · exact finrank_pos k p G v hv

end S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one
end P2MW
export P2MW.S_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one (solution)

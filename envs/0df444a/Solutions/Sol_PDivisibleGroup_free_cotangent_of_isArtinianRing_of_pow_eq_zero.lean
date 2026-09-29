-- Prove2me | solution 1 for PDivisibleGroup.free_cotangent_of_isArtinianRing_of_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0db15b37-5922-502e-ad58-8690171495a4

import Mathlib
import Definitions.Def_PDivisibleGroup_BaseChange
import Theorems.Thm_PDivisibleGroup_ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot
import Theorems.Thm_PDivisibleGroup_cotangentBaseChange_bijective
import Theorems.Thm_IsLocalRing_exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot
import Theorems.Thm_IsLocalRing_exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_MvPowerSeries_algHom_ext_of_apply_X_mem
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Theorems.Thm_PDivisibleGroup_finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_free_cotangent_of_isArtinianRing_of_pow_eq_zero
p2m_attr_erase "instance" "PDivisibleGroup.Points.instAddCommGroup PDivisibleGroup.Points.instInhabited PDivisibleGroup.Point.instCommGroup PDivisibleGroup.pointsDirectedSystem PDivisibleGroup.Points.instDistribMulAction PDivisibleGroup.Point.instCommMonoid TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra"
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "PDivisibleGroup.CartierDuality.mk.injEq PDivisibleGroup.CartierDuality.toDualEquiv_apply PDivisibleGroup.CartierDuality.mk.sizeOf_spec PDivisibleGroup.Points.smul_pointsMkAdd PDivisibleGroup.pointsMkAdd_pointInclLE PDivisibleGroup.Point.toAlgHom_ofAlgHom PDivisibleGroup.pointsMkAdd_pointIncl PDivisibleGroup.pointsMk_pointInclLE PDivisibleGroup.pointIncl_apply PDivisibleGroup.pointInclLE_self PDivisibleGroup.toAlgHom_pointMap PDivisibleGroup.Point.toConv_ofConv PDivisibleGroup.Hopf.antipodeAlgHom_apply PDivisibleGroup.Hopf.convCompMonoidHom_apply PDivisibleGroup.pointsMap_pointsMkAdd PDivisibleGroup.Point.ofAlgHom_toAlgHom PDivisibleGroup.pointsMk_pointIncl PDivisibleGroup.Point.ofConv_toConv TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open scoped TensorProduct
open Coalgebra Bialgebra IsLocalRing Function

namespace PDivFreeCot

section General

theorem isAdicComplete_of_isNilpotent {A : Type*} [CommRing A] (I : Ideal A) (hI : IsNilpotent I)
    (M : Type*) [AddCommGroup M] [Module A M] : IsAdicComplete I M := by
  obtain ⟨N, hN⟩ := hI
  have hz : ∀ m, N ≤ m → I ^ m • (⊤ : Submodule A M) = ⊥ := fun m hm => by
    apply le_antisymm _ bot_le
    calc I ^ m • (⊤ : Submodule A M) ≤ I ^ N • ⊤ := Submodule.smul_mono_left (Ideal.pow_le_pow_right hm)
      _ = ⊥ := by rw [hN, Submodule.zero_eq_bot, Submodule.bot_smul]
  haveI : IsHausdorff I M := ⟨fun x hx => by
    have h := hx N
    rw [hz N le_rfl, SModEq.bot] at h
    exact h⟩
  haveI : IsPrecomplete I M := ⟨fun f hf => ⟨f N, fun m => by
    by_cases hm : m ≤ N
    · exact hf hm
    · have h1 : f N ≡ f m [SMOD I ^ N • (⊤ : Submodule A M)] := hf (le_of_not_ge hm)
      rw [hz N le_rfl, SModEq.bot] at h1
      rw [hz m (le_of_not_ge hm), SModEq.bot]
      exact h1.symm⟩⟩
  exact ⟨⟩

theorem isNilpotent_maximalIdeal (R : Type*) [CommRing R] [IsArtinianRing R] [IsLocalRing R] :
    IsNilpotent (maximalIdeal R) :=
  (isArtinianRing_iff_isNilpotent_maximalIdeal R).1 inferInstance

end General

section Conn

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)

def Iinf : Ideal A := ⨅ j : ℕ, RingHom.ker ε ^ j

theorem Iinf_le_pow (j : ℕ) : Iinf ε ≤ RingHom.ker ε ^ j := iInf_le _ j

theorem Iinf_le_ker : Iinf ε ≤ RingHom.ker ε := by
  simpa only [pow_one] using Iinf_le_pow ε 1

theorem ε_surjective : Surjective ε := fun r => ⟨algebraMap R A r, ε.commutes r⟩

abbrev Q : Type _ := A ⧸ Iinf ε

def εQ : Q ε →ₐ[R] R :=
  Ideal.Quotient.liftₐ (Iinf ε) ε fun a ha => Iinf_le_ker ε ha

@[scoped simp] theorem εQ_mk (a : A) : εQ ε (Ideal.Quotient.mk (Iinf ε) a) = ε a := rfl

theorem εQ_surjective : Surjective (εQ ε) := fun r =>
  ⟨algebraMap R _ r, (εQ ε).commutes r⟩

def Icirc : Ideal (Q ε) := (RingHom.ker ε).map (Ideal.Quotient.mk (Iinf ε))

theorem ker_εQ : RingHom.ker (εQ ε) = Icirc ε := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_map_of_mem _ (by simpa using hx)
  · rw [Icirc, Ideal.map_le_iff_le_comap]
    intro a ha
    simpa using ha

theorem mem_Icirc_iff (x : Q ε) : x ∈ Icirc ε ↔ εQ ε x = 0 := by
  rw [← ker_εQ, RingHom.mem_ker]

section Artin

variable [IsArtinianRing R] [IsLocalRing R] [Module.Finite R A]

include ε in
theorem isNoetherianRing_A : IsNoetherianRing A :=
  isNoetherian_of_tower R (inferInstance : IsNoetherian R A)

theorem exists_pow_stable : ∃ M : ℕ, 0 < M ∧ ∀ j, M ≤ j → RingHom.ker ε ^ j = RingHom.ker ε ^ M := by
  let f : ℕ →o (Submodule R A)ᵒᵈ :=
    ⟨fun j => OrderDual.toDual (((RingHom.ker ε) ^ (j + 1)).restrictScalars R), fun i j hij => by
      change ((RingHom.ker ε) ^ (j + 1)).restrictScalars R ≤ ((RingHom.ker ε) ^ (i + 1)).restrictScalars R
      exact fun x hx => Ideal.pow_le_pow_right (by omega) hx⟩
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨N + 1, Nat.succ_pos N, fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h := hN i (by omega)
  have h' : ((RingHom.ker ε) ^ (N + 1)).restrictScalars R = ((RingHom.ker ε) ^ (i + 1)).restrictScalars R :=
    congrArg OrderDual.ofDual h
  exact ((Submodule.restrictScalars_injective R A A) h').symm

theorem exists_Iinf_eq_pow : ∃ M : ℕ, 0 < M ∧ Iinf ε = RingHom.ker ε ^ M ∧
    IsIdempotentElem (Iinf ε) := by
  obtain ⟨M, hM0, hM⟩ := exists_pow_stable ε
  have hEq : Iinf ε = RingHom.ker ε ^ M := by
    apply le_antisymm (Iinf_le_pow ε M)
    refine le_iInf fun j => ?_
    by_cases hj : M ≤ j
    · rw [hM j hj]
    · exact Ideal.pow_le_pow_right (le_of_not_ge hj)
  refine ⟨M, hM0, hEq, ?_⟩
  change Iinf ε * Iinf ε = Iinf ε
  rw [hEq, ← pow_add, hM (M + M) (by omega)]

theorem exists_idempotent : ∃ e : A, IsIdempotentElem e ∧ Iinf ε = Ideal.span {e} := by
  haveI := isNoetherianRing_A ε
  obtain ⟨M, -, -, hidem⟩ := exists_Iinf_eq_pow ε
  exact (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).1 hidem

theorem isNilpotent_Icirc : IsNilpotent (Icirc ε) := by
  obtain ⟨M, -, hEq, -⟩ := exists_Iinf_eq_pow ε
  refine ⟨M, ?_⟩
  rw [Icirc, ← Ideal.map_pow, ← hEq, Ideal.map_quotient_self]
  rfl

theorem isNilpotent_of_mem_Icirc {x : Q ε} (hx : x ∈ Icirc ε) : IsNilpotent x := by
  obtain ⟨M, hM⟩ := isNilpotent_Icirc ε
  exact ⟨M, by
    have : x ^ M ∈ Icirc ε ^ M := Ideal.pow_mem_pow hx M
    rw [hM] at this
    exact (Submodule.mem_bot _).1 this⟩

theorem isUnit_of_isUnit_εQ {x : Q ε} (hx : IsUnit (εQ ε x)) : IsUnit x := by
  have hdec : x = algebraMap R _ (εQ ε x) + (x - algebraMap R _ (εQ ε x)) := by abel
  rw [hdec]
  refine IsNilpotent.isUnit_add_left_of_commute ?_ (hx.map (algebraMap R (Q ε))) (Commute.all _ _)
  apply isNilpotent_of_mem_Icirc
  rw [mem_Icirc_iff, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

scoped instance nontrivial_Q : Nontrivial (Q ε) :=
  ⟨⟨0, 1, fun h => zero_ne_one (α := R) (by simpa using congrArg (εQ ε) h)⟩⟩

scoped instance isLocalRing_Q : IsLocalRing (Q ε) := by
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  have key : ∀ x : Q ε, x ∈ nonunits (Q ε) → εQ ε x ∈ maximalIdeal R := fun x hx => by
    by_contra hcon
    exact hx (isUnit_of_isUnit_εQ ε (by simpa using hcon))
  intro hu
  have h1 : εQ ε (a + b) ∈ maximalIdeal R := by
    rw [map_add]; exact Ideal.add_mem _ (key a ha) (key b hb)
  exact h1 (hu.map (εQ ε))

theorem maximalIdeal_Q : maximalIdeal (Q ε) = (maximalIdeal R).comap (εQ ε) := by
  haveI : ((maximalIdeal R).comap (εQ ε)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ (εQ_surjective ε)
  exact (IsLocalRing.eq_maximalIdeal inferInstance).symm

theorem Icirc_le_maximalIdeal : Icirc ε ≤ maximalIdeal (Q ε) := by
  rw [maximalIdeal_Q, ← ker_εQ]
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker.1 hx]
  exact Ideal.zero_mem _

theorem isNilpotent_maximalIdeal_Q : IsNilpotent (maximalIdeal (Q ε)) := by
  obtain ⟨e, he⟩ := isNilpotent_maximalIdeal R
  obtain ⟨M, hM⟩ := isNilpotent_Icirc ε
  refine ⟨e * M, ?_⟩
  rw [pow_mul, maximalIdeal_Q]
  have h1 : ((maximalIdeal R).comap (εQ ε)) ^ e ≤ Icirc ε := by
    refine le_trans (Ideal.le_comap_pow _ e) ?_
    rw [he, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot, ker_εQ]
  exact le_antisymm (le_trans (Ideal.pow_right_mono h1 M) hM.le) bot_le

scoped instance isAdicComplete_Q : IsAdicComplete (maximalIdeal (Q ε)) (Q ε) :=
  isAdicComplete_of_isNilpotent _ (isNilpotent_maximalIdeal_Q ε) _

scoped instance isNoetherianRing_Q : IsNoetherianRing (Q ε) := by
  haveI := isNoetherianRing_A ε
  exact Ideal.Quotient.isNoetherianRing _

theorem projective_Q [Module.Free R A] : Module.Projective R (Q ε) := by
  obtain ⟨e, he, hspan⟩ := exists_idempotent ε

  let f : A →ₗ[R] A := LinearMap.mulLeft R (1 - e)
  have hf : ∀ x ∈ (Iinf ε).restrictScalars R, f x = 0 := by
    intro x hx
    change x ∈ Iinf ε at hx
    rw [hspan, Ideal.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    change (1 - e) * (e * c) = 0
    rw [← mul_assoc, sub_mul, one_mul, he.eq, sub_self, zero_mul]
  have hf' : (Iinf ε).restrictScalars R ≤ LinearMap.ker f := fun x hx => hf x hx
  let s : Q ε →ₗ[R] A :=
    ((Iinf ε).restrictScalars R).liftQ f hf' ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv R (Iinf ε)).symm.toLinearMap
  let π : A →ₗ[R] Q ε := (Ideal.Quotient.mkₐ R (Iinf ε)).toLinearMap
  refine Module.Projective.of_split s π ?_
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (Iinf ε) (s (Ideal.Quotient.mk (Iinf ε) a)) = Ideal.Quotient.mk (Iinf ε) a
  have hs : s (Ideal.Quotient.mk (Iinf ε) a) = (1 - e) * a := by
    change ((Iinf ε).restrictScalars R).liftQ f hf'
      ((Submodule.Quotient.restrictScalarsEquiv R (Iinf ε)).symm (Submodule.Quotient.mk a)) = _
    rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]
    rfl
  rw [hs, sub_mul, one_mul, map_sub, sub_eq_self, Ideal.Quotient.eq_zero_iff_mem, hspan]
  exact Ideal.mem_span_singleton.2 (dvd_mul_right e a)

end Artin

end Conn

section Tower

variable {R : Type} [CommRing R] [IsArtinianRing R] [IsLocalRing R] {p h : ℕ}
  (G : PDivisibleGroup R p h)

abbrev εA (w : ℕ) : G.level w →ₐ[R] R := counitAlgHom R (G.level w)

theorem ker_εA (w : ℕ) : RingHom.ker (εA G w) = G.augIdeal w := rfl

abbrev QG (w : ℕ) : Type := Q (εA G w)

theorem Iinf_le_comap (w : ℕ) :
    Iinf (εA G (w + 1)) ≤ (Iinf (εA G w)).comap (G.transitionAlgHom w) := by
  rw [Iinf, Iinf, Ideal.comap_iInf]
  refine iInf_mono fun j => ?_
  exact le_trans (Ideal.pow_right_mono (G.augIdeal_le_comap_transition w) j) (Ideal.le_comap_pow _ j)

def transQ (w : ℕ) : QG G (w + 1) →ₐ[R] QG G w :=
  Ideal.quotientMapₐ _ (G.transitionAlgHom w) (Iinf_le_comap G w)

theorem transQ_mk (w : ℕ) (a : G.level (w + 1)) :
    transQ G w (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (G.transition w a) := rfl

theorem exists_lift_aug (w : ℕ) (a : G.augIdeal w) :
    ∃ b : G.augIdeal (w + 1), G.transition w (b : G.level (w + 1)) = a := by
  obtain ⟨b, hb⟩ := G.transition_surjective w a
  refine ⟨⟨b - algebraMap R _ (counit (R := R) b), PDivisibleGroup.Hopf.sub_algebraMap_counit_mem_augIdeal R _ b⟩, ?_⟩
  have hεa : counit (R := R) (a : G.level w) = 0 := a.2
  change G.transition w (b - algebraMap R _ (counit (R := R) b)) = a
  rw [map_sub, AlgHomClass.commutes, ← G.counit_transition, hb, hεa, map_zero, sub_zero]

def liftAug (w : ℕ) (a : G.augIdeal w) : G.augIdeal (w + 1) := (exists_lift_aug G w a).choose

theorem transition_liftAug (w : ℕ) (a : G.augIdeal w) :
    G.transition w (liftAug G w a : G.level (w + 1)) = a :=
  (exists_lift_aug G w a).choose_spec

abbrev kk (R : Type) [CommRing R] [IsLocalRing R] : Type := ResidueField R

theorem exists_eq_one_tmul {M : Type*} [AddCommGroup M] [Module R M] (z : kk R ⊗[R] M) :
    ∃ y : M, z = (1 : kk R) ⊗ₜ[R] y := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c m =>
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨r • m, ?_⟩
    rw [TensorProduct.tmul_smul, ← ResidueField.algebraMap_eq, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by rw [TensorProduct.tmul_add]⟩

theorem mem_smul_top_of_one_tmul_eq_zero {M : Type*} [AddCommGroup M] [Module R M] (z : M)
    (h0 : (1 : kk R) ⊗ₜ[R] z = 0) : z ∈ (maximalIdeal R • ⊤ : Submodule R M) := by
  have h1 : (TensorProduct.quotTensorEquivQuotSMul M (maximalIdeal R)).symm (Submodule.Quotient.mk z) = 0 := by
    rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk]
    exact h0
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h1
  exact h1

scoped instance finite_cotangent (w : ℕ) : Module.Finite R (G.Cotangent w) := by
  let f : ((G.augIdeal w).restrictScalars R) →ₗ[R] G.Cotangent w :=
    { toFun := fun x => (G.augIdeal w).toCotangent ⟨x.1, x.2⟩
      map_add' := fun x y => by
        rw [← map_add]; rfl
      map_smul' := fun r x => by
        rw [RingHom.id_apply, ← LinearMap.map_smul_of_tower]; rfl }
  refine Module.Finite.of_surjective f fun y => ?_
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ y
  exact ⟨⟨x.1, x.2⟩, rfl⟩

def nG : ℕ := Module.finrank (kk R) (PDivisibleGroup.Hopf.augIdeal (kk R) (kk R ⊗[R] G.level 1)).Cotangent

theorem exists_gens_one : ∃ t : Fin (nG G) → G.augIdeal 1,
    Submodule.span R (Set.range fun i => (G.augIdeal 1).toCotangent (t i)) ⊔
      (maximalIdeal R • ⊤ : Submodule R (G.Cotangent 1)) = ⊤ := by
  let W := kk R ⊗[R] G.Cotangent 1
  let e : W ≃ₗ[kk R] (PDivisibleGroup.Hopf.augIdeal (kk R) (kk R ⊗[R] G.level 1)).Cotangent :=
    LinearEquiv.ofBijective (G.cotangentBaseChange (kk R) 1) (G.cotangentBaseChange_bijective (kk R) 1)
  have hW : Module.finrank (kk R) W = nG G := e.finrank_eq
  let b : Module.Basis (Fin (nG G)) (kk R) W := Module.finBasisOfFinrankEq (kk R) W hW
  have hy : ∀ i, ∃ y : G.Cotangent 1, b i = (1 : kk R) ⊗ₜ[R] y := fun i => exists_eq_one_tmul (b i)
  choose y hy using hy
  have ht : ∀ i, ∃ t : G.augIdeal 1, (G.augIdeal 1).toCotangent t = y i := fun i =>
    Ideal.toCotangent_surjective _ (y i)
  choose t ht using ht
  refine ⟨t, ?_⟩
  rw [eq_top_iff]
  rintro x -

  have hx : (1 : kk R) ⊗ₜ[R] x = ∑ i, b.repr ((1 : kk R) ⊗ₜ[R] x) i • b i := (b.sum_repr _).symm
  have hc : ∀ i, ∃ c : R, residue R c = b.repr ((1 : kk R) ⊗ₜ[R] x) i := fun i =>
    IsLocalRing.residue_surjective _
  choose c hc using hc
  have hsum : (1 : kk R) ⊗ₜ[R] x = (1 : kk R) ⊗ₜ[R] (∑ i, c i • y i) := by
    rw [hx, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc i, hy i, TensorProduct.tmul_smul, ← ResidueField.algebraMap_eq,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]
    rfl
  have hdiff : x - ∑ i, c i • y i ∈ (maximalIdeal R • ⊤ : Submodule R (G.Cotangent 1)) := by
    apply mem_smul_top_of_one_tmul_eq_zero
    rw [TensorProduct.tmul_sub, hsum, sub_self]
  have hmem : ∑ i, c i • y i ∈ Submodule.span R (Set.range fun i => (G.augIdeal 1).toCotangent (t i)) := by
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ?_⟩)
    exact ht i
  have : x = (∑ i, c i • y i) + (x - ∑ i, c i • y i) := by abel
  rw [this]
  exact Submodule.add_mem_sup hmem hdiff

def gens : (d : ℕ) → Fin (nG G) → G.augIdeal (d + 1)
  | 0 => (exists_gens_one G).choose
  | d + 1 => fun i => liftAug G (d + 1) (gens d i)

theorem transition_gens (d : ℕ) (i : Fin (nG G)) :
    G.transition (d + 1) (gens G (d + 1) i : G.level (d + 2)) = gens G d i :=
  transition_liftAug G (d + 1) (gens G d i)

theorem cotangentMap_toCotangent_gens (d : ℕ) (i : Fin (nG G)) :
    G.cotangentMap (d + 1) ((G.augIdeal (d + 2)).toCotangent (gens G (d + 1) i)) =
      (G.augIdeal (d + 1)).toCotangent (gens G d i) := by
  rw [PDivisibleGroup.cotangentMap_toCotangent]
  congr 1
  exact Subtype.ext (transition_gens G d i)

variable (hp : (p : R) ∈ maximalIdeal R)

include hp in

theorem span_gens (d : ℕ) :
    Submodule.span R (Set.range fun i => (G.augIdeal (d + 1)).toCotangent (gens G d i)) ⊔
      (maximalIdeal R • ⊤ : Submodule R (G.Cotangent (d + 1))) = ⊤ := by
  induction d with
  | zero => exact (exists_gens_one G).choose_spec
  | succ d ih =>
    set f := G.cotangentMap (d + 1) with hf
    set N' := Submodule.span R (Set.range fun i => (G.augIdeal (d + 2)).toCotangent (gens G (d + 1) i))
    have hsurj : Surjective f := G.cotangentMap_surjective (d + 1)
    have hmapN : N'.map f =
        Submodule.span R (Set.range fun i => (G.augIdeal (d + 1)).toCotangent (gens G d i)) := by
      have hfun : (⇑f ∘ fun i => (G.augIdeal (d + 2)).toCotangent (gens G (d + 1) i)) =
          fun i => (G.augIdeal (d + 1)).toCotangent (gens G d i) :=
        funext fun i => cotangentMap_toCotangent_gens G d i
      rw [Submodule.map_span, ← Set.range_comp, hfun]
    have hmapM : (maximalIdeal R • ⊤ : Submodule R (G.Cotangent (d + 2))).map f =
        (maximalIdeal R • ⊤ : Submodule R (G.Cotangent (d + 1))) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hsurj]
    have hmap : (N' ⊔ maximalIdeal R • ⊤).map f = ⊤ := by
      rw [Submodule.map_sup, hmapN, hmapM, ih]
    have hker : LinearMap.ker f ≤ (maximalIdeal R • ⊤ : Submodule R (G.Cotangent (d + 2))) := by
      rw [hf, (G.ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot (d + 1)).1]
      refine Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem _).2 ?_)
      exact Ideal.pow_mem_of_mem _ hp _ (Nat.succ_pos d)
    have h2 : Submodule.comap f ((N' ⊔ maximalIdeal R • ⊤).map f) = ⊤ := by
      rw [hmap, Submodule.comap_top]
    rw [Submodule.comap_map_eq] at h2
    apply le_antisymm le_top
    calc (⊤ : Submodule R (G.Cotangent (d + 2))) = N' ⊔ maximalIdeal R • ⊤ ⊔ LinearMap.ker f := h2.symm
      _ ≤ N' ⊔ maximalIdeal R • ⊤ := sup_le le_rfl (le_trans hker le_sup_right)

theorem mem_of_span (d : ℕ)
    (hsp : Submodule.span R (Set.range fun i => (G.augIdeal (d + 1)).toCotangent (gens G d i)) ⊔
      (maximalIdeal R • ⊤ : Submodule R (G.Cotangent (d + 1))) = ⊤)
    (a : G.level (d + 1)) (ha : a ∈ G.augIdeal (d + 1)) :
    a ∈ Ideal.span (Set.range fun i => (gens G d i : G.level (d + 1))) ⊔ G.augIdeal (d + 1) ^ 2 ⊔
      (maximalIdeal R).map (algebraMap R (G.level (d + 1))) := by
  set I := G.augIdeal (d + 1)
  have hx : I.toCotangent ⟨a, ha⟩ ∈ Submodule.span R (Set.range fun i => I.toCotangent (gens G d i)) ⊔
      (maximalIdeal R • ⊤ : Submodule R (G.Cotangent (d + 1))) := by
    rw [hsp]; exact Submodule.mem_top
  obtain ⟨yv, hyv, z, hz, hyz⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hyv

  have hzP : ∃ m : I, (m : G.level (d + 1)) ∈ (maximalIdeal R).map (algebraMap R (G.level (d + 1))) ∧
      I.toCotangent m = z := by
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro r hr w _
      obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective _ w
      refine ⟨r • b, ?_, (I.toCotangent.map_smul_of_tower r b)⟩
      change r • (b : G.level (d + 1)) ∈ _
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr)
    · rintro x y ⟨m₁, hm₁, rfl⟩ ⟨m₂, hm₂, rfl⟩
      exact ⟨m₁ + m₂, Ideal.add_mem _ hm₁ hm₂, map_add _ _ _⟩
  obtain ⟨m, hm, rfl⟩ := hzP
  have hsum : ∑ i, c i • I.toCotangent (gens G d i) = I.toCotangent (∑ i, c i • gens G d i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => (I.toCotangent.map_smul_of_tower _ _).symm
  rw [hsum, ← map_add] at hyz
  have hdiff : ((⟨a, ha⟩ : I) : G.level (d + 1)) - ((∑ i, c i • gens G d i + m : I) : G.level (d + 1)) ∈ I ^ 2 := by
    rw [← Submodule.coe_sub, ← Ideal.toCotangent_eq_zero, map_sub, hyz, sub_self]
  have hgen : ((∑ i, c i • gens G d i : I) : G.level (d + 1)) ∈
      Ideal.span (Set.range fun i => (gens G d i : G.level (d + 1))) := by
    rw [Submodule.coe_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have hdec : a = ((∑ i, c i • gens G d i : I) : G.level (d + 1)) + (a - ((∑ i, c i • gens G d i + m : I) :
      G.level (d + 1))) + (m : G.level (d + 1)) := by
    rw [Submodule.coe_add]; ring
  rw [hdec]
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_sup_left hgen))
    (Ideal.mem_sup_left (Ideal.mem_sup_right hdiff))) (Ideal.mem_sup_right hm)

abbrev PS : Type := MvPowerSeries (Fin (nG G)) R

def tQ (d : ℕ) (i : Fin (nG G)) : QG G (d + 1) := Ideal.Quotient.mk _ (gens G d i : G.level (d + 1))

theorem tQ_mem_Icirc (d : ℕ) (i : Fin (nG G)) : tQ G d i ∈ Icirc (εA G (d + 1)) :=
  Ideal.mem_map_of_mem _ (gens G d i).2

theorem transQ_tQ (d : ℕ) (i : Fin (nG G)) : transQ G (d + 1) (tQ G (d + 1) i) = tQ G d i := by
  rw [tQ, transQ_mk, transition_gens]; rfl

scoped instance isAdicComplete_R : IsAdicComplete (maximalIdeal R) R :=
  isAdicComplete_of_isNilpotent _ (isNilpotent_maximalIdeal R) _

theorem residue_comp_surjective (d : ℕ) :
    Surjective (⇑(residue (QG G (d + 1))) ∘ ⇑(algebraMap R (QG G (d + 1)))) := by
  intro q
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective q
  refine ⟨εQ (εA G (d + 1)) x, ?_⟩
  change residue _ (algebraMap R _ (εQ _ x)) = residue _ x
  have hy : x - algebraMap R _ (εQ (εA G (d + 1)) x) ∈ maximalIdeal (QG G (d + 1)) := by
    apply Icirc_le_maximalIdeal
    rw [mem_Icirc_iff, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hy

include hp in
theorem maximalIdeal_le_gens (d : ℕ) :
    maximalIdeal (QG G (d + 1)) ≤ Ideal.span (Set.range (tQ G d)) ⊔ maximalIdeal (QG G (d + 1)) ^ 2 ⊔
      (maximalIdeal R).map (algebraMap R (QG G (d + 1))) := by
  intro x hx
  set π := Ideal.Quotient.mk (Iinf (εA G (d + 1)))
  have hdec : x = algebraMap R _ (εQ (εA G (d + 1)) x) + (x - algebraMap R _ (εQ (εA G (d + 1)) x)) := by abel
  have h1 : algebraMap R _ (εQ (εA G (d + 1)) x) ∈ (maximalIdeal R).map (algebraMap R (QG G (d + 1))) := by
    apply Ideal.mem_map_of_mem
    rw [maximalIdeal_Q] at hx
    exact hx
  have h2 : x - algebraMap R _ (εQ (εA G (d + 1)) x) ∈ Icirc (εA G (d + 1)) := by
    rw [mem_Icirc_iff, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  obtain ⟨a, ha, hax⟩ := (Ideal.mem_map_iff_of_surjective π Ideal.Quotient.mk_surjective).1 h2
  have ha' := mem_of_span G d (span_gens G hp d) a ha
  have hmap : π a ∈ (Ideal.span (Set.range fun i => (gens G d i : G.level (d + 1))) ⊔ G.augIdeal (d + 1) ^ 2 ⊔
      (maximalIdeal R).map (algebraMap R (G.level (d + 1)))).map π := Ideal.mem_map_of_mem _ ha'
  rw [Ideal.map_sup, Ideal.map_sup, Ideal.map_span, ← Set.range_comp, Ideal.map_pow, Ideal.map_map] at hmap
  have hπt : (⇑π ∘ fun i => (gens G d i : G.level (d + 1))) = tQ G d := rfl
  have hcomp : π.comp (algebraMap R (G.level (d + 1))) = algebraMap R (QG G (d + 1)) := rfl
  rw [hπt, hcomp] at hmap
  have hI2 : (G.augIdeal (d + 1)).map π ^ 2 ≤ maximalIdeal (QG G (d + 1)) ^ 2 :=
    Ideal.pow_right_mono (Icirc_le_maximalIdeal (εA G (d + 1))) 2
  rw [hdec]
  refine Ideal.add_mem _ (Ideal.mem_sup_right h1) ?_
  rw [hax] at hmap
  exact (sup_le_sup (sup_le_sup_left hI2 _) le_rfl) hmap

include hp in
theorem exists_phi (d : ℕ) : ∃ φ : PS G →ₐ[R] QG G (d + 1), (∀ i, φ (MvPowerSeries.X i) = tQ G d i) ∧
    Surjective φ :=
  IsLocalRing.exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span (residue_comp_surjective G d)
    (tQ G d) (fun i => Icirc_le_maximalIdeal _ (tQ_mem_Icirc G d i)) (maximalIdeal_le_gens G hp d)

def phi (d : ℕ) : PS G →ₐ[R] QG G (d + 1) := (exists_phi G hp d).choose

theorem phi_X (d : ℕ) (i : Fin (nG G)) : phi G hp d (MvPowerSeries.X i) = tQ G d i :=
  (exists_phi G hp d).choose_spec.1 i

theorem phi_surjective (d : ℕ) : Surjective (phi G hp d) := (exists_phi G hp d).choose_spec.2

theorem isHausdorff_Icirc (d : ℕ) : IsHausdorff (Icirc (εA G (d + 1))) (QG G (d + 1)) :=
  (isAdicComplete_of_isNilpotent _ (isNilpotent_Icirc _) _).toIsHausdorff

theorem transQ_comp_phi (d : ℕ) : (transQ G (d + 1)).comp (phi G hp (d + 1)) = phi G hp d := by
  haveI := isHausdorff_Icirc G d
  refine MvPowerSeries.algHom_ext_of_apply_X_mem (Icirc (εA G (d + 1))) _ _ (fun i => ?_) (fun i => ?_)
  · rw [AlgHom.comp_apply, phi_X, transQ_tQ]; exact tQ_mem_Icirc G d i
  · rw [AlgHom.comp_apply, phi_X, transQ_tQ, phi_X]

theorem ker_phi_succ_le (d : ℕ) : RingHom.ker (phi G hp (d + 1)) ≤ RingHom.ker (phi G hp d) := by
  intro f hf
  rw [RingHom.mem_ker] at hf ⊢
  rw [← transQ_comp_phi G hp d, AlgHom.comp_apply, hf, map_zero]

theorem ker_phi_antitone : Antitone fun d => RingHom.ker (phi G hp d) :=
  antitone_nat_of_succ_le fun d => ker_phi_succ_le G hp d

theorem map_span_X_le (d : ℕ) :
    (Ideal.span (Set.range (MvPowerSeries.X : Fin (nG G) → PS G))).map (phi G hp d) ≤ Icirc (εA G (d + 1)) := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [phi_X]
  exact tQ_mem_Icirc G d i

theorem phi_eq_zero_of_coeff (d N : ℕ) (hN : Icirc (εA G (d + 1)) ^ N = ⊥) (f : PS G)
    (hf : ∀ m : Fin (nG G) →₀ ℕ, m.degree < N → MvPowerSeries.coeff m f = 0) : phi G hp d f = 0 := by
  have hmem := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero N f hf
  have h2 : phi G hp d f ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin (nG G) → PS G)) ^ N).map (phi G hp d) :=
    Ideal.mem_map_of_mem _ hmem
  rw [Ideal.map_pow] at h2
  have h3 := Ideal.pow_right_mono (map_span_X_le G hp d) N h2
  rw [hN] at h3
  exact (Submodule.mem_bot _).1 h3

end Tower

section FieldInput

variable {R : Type} [CommRing R] [IsArtinianRing R] [IsLocalRing R] {p h : ℕ} [Fact p.Prime]
  (G : PDivisibleGroup R p h) (hp : (p : R) ∈ maximalIdeal R) [CharP (kk R) p]

abbrev Abar (d : ℕ) : Type := kk R ⊗[R] G.level (d + 1)

abbrev Ibar (d : ℕ) : Ideal (Abar G d) := PDivisibleGroup.Hopf.augIdeal (kk R) (Abar G d)

def Jbar (d : ℕ) : Ideal (Abar G d) :=
  Ideal.span ((fun a : Abar G d => a ^ p ^ (d + 1)) '' (Ibar G d : Set (Abar G d)))

abbrev Cb (d : ℕ) : Type := Abar G d ⧸ Jbar G d

theorem finrank_Cb (d : ℕ) : Module.finrank (kk R) (Cb G d) = (p ^ (d + 1)) ^ nG G := by
  have h := PDivisibleGroup.finrank_level_quotient_span_pow_eq_pow_mul_finrank_cotangent_one
    (G.baseChange (kk R)) (d + 1)
  rw [pow_mul] at h
  exact h

def rho (d : ℕ) : G.level (d + 1) →ₐ[R] Cb G d :=
  (Ideal.Quotient.mkₐ R (Jbar G d)).comp
    (Algebra.TensorProduct.includeRight : G.level (d + 1) →ₐ[R] Abar G d)

theorem rho_apply (d : ℕ) (a : G.level (d + 1)) :
    rho G d a = Ideal.Quotient.mk (Jbar G d) ((1 : kk R) ⊗ₜ[R] a) := rfl

theorem rho_surjective (d : ℕ) : Surjective (rho G d) := by
  intro c
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨a, rfl⟩ := exists_eq_one_tmul z
  exact ⟨a, rfl⟩

theorem rho_pow_eq_zero (d : ℕ) {a : G.level (d + 1)} (ha : a ∈ G.augIdeal (d + 1)) :
    rho G d a ^ p ^ (d + 1) = 0 := by
  rw [rho_apply, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨_, G.augIdeal_le_comap_includeRight (kk R) (d + 1) ha, rfl⟩

theorem exists_pow_le_ker_rho (d : ℕ) : ∃ N : ℕ, RingHom.ker (εA G (d + 1)) ^ N ≤ RingHom.ker (rho G d) := by
  haveI : IsNoetherianRing (G.level (d + 1)) := isNoetherianRing_A (εA G (d + 1))
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  intro a ha
  exact ⟨p ^ (d + 1), by rw [RingHom.mem_ker, map_pow]; exact rho_pow_eq_zero G d ha⟩

theorem rho_eq_zero_of_mem_Iinf (d : ℕ) (a : G.level (d + 1)) (ha : a ∈ Iinf (εA G (d + 1))) :
    rho G d a = 0 := by
  obtain ⟨N, hN⟩ := exists_pow_le_ker_rho G d
  exact hN (Iinf_le_pow _ N ha)

def theta (d : ℕ) : QG G (d + 1) →ₐ[R] Cb G d :=
  Ideal.Quotient.liftₐ (Iinf (εA G (d + 1))) (rho G d) (rho_eq_zero_of_mem_Iinf G d)

theorem theta_mk (d : ℕ) (a : G.level (d + 1)) : theta G d (Ideal.Quotient.mk _ a) = rho G d a := by
  rw [theta, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

theorem theta_surjective (d : ℕ) : Surjective (theta G d) := fun c => by
  obtain ⟨a, rfl⟩ := rho_surjective G d c
  exact ⟨Ideal.Quotient.mk _ a, theta_mk G d a⟩

def psi (d : ℕ) : PS G →ₐ[R] Cb G d := (theta G d).comp (phi G hp d)

def tau (d : ℕ) (i : Fin (nG G)) : Cb G d := rho G d (gens G d i)

theorem psi_X (d : ℕ) (i : Fin (nG G)) : psi G hp d (MvPowerSeries.X i) = tau G d i := by
  rw [psi, AlgHom.comp_apply, phi_X, tQ, theta_mk]; rfl

theorem tau_pow (d : ℕ) (i : Fin (nG G)) : tau G d i ^ p ^ (d + 1) = 0 :=
  rho_pow_eq_zero G d (gens G d i).2

theorem tau_pow_eq_zero_of_le (d : ℕ) (i : Fin (nG G)) {e : ℕ} (he : p ^ (d + 1) ≤ e) : tau G d i ^ e = 0 := by
  calc tau G d i ^ e = tau G d i ^ p ^ (d + 1) * tau G d i ^ (e - p ^ (d + 1)) := by
        rw [← pow_add, Nat.add_sub_of_le he]
    _ = 0 := by rw [tau_pow]; exact zero_mul (tau G d i ^ (e - p ^ (d + 1)))

theorem psi_surjective (d : ℕ) : Surjective (psi G hp d) :=
  (theta_surjective G d).comp (phi_surjective G hp d)

def mg (d : ℕ) (g : Fin (nG G) → Fin (p ^ (d + 1))) : Fin (nG G) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (g i : ℕ)

@[scoped simp] theorem mg_apply (d : ℕ) (g : Fin (nG G) → Fin (p ^ (d + 1))) (i : Fin (nG G)) :
    mg G d g i = (g i : ℕ) := rfl

def vfam (d : ℕ) (g : Fin (nG G) → Fin (p ^ (d + 1))) : Cb G d := ∏ i, tau G d i ^ (g i : ℕ)

def mono (d : ℕ) (m : Fin (nG G) →₀ ℕ) : Cb G d := ∏ i, tau G d i ^ m i

theorem mono_mg (d : ℕ) (g : Fin (nG G) → Fin (p ^ (d + 1))) : mono G d (mg G d g) = vfam G d g := rfl

theorem mono_eq_zero (d : ℕ) (m : Fin (nG G) →₀ ℕ) (hm : ¬ ∀ i, m i < p ^ (d + 1)) : mono G d m = 0 := by
  push Not at hm
  obtain ⟨i, hi⟩ := hm
  exact Finset.prod_eq_zero (f := fun j => tau G d j ^ m j) (Finset.mem_univ i)
    (tau_pow_eq_zero_of_le G d i hi)

theorem aeval_coe_eq_psi (d : ℕ) (P : MvPolynomial (Fin (nG G)) R) :
    psi G hp d (P : PS G) = MvPolynomial.aeval (tau G d) P := by
  have hext : (psi G hp d).comp (MvPolynomial.coeToMvPowerSeries.algHom R) = MvPolynomial.aeval (tau G d) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
      MvPowerSeries.map_id, MvPolynomial.coe_X, RingHom.id_apply, psi_X, MvPolynomial.aeval_X]
  have h := DFunLike.congr_fun hext P
  rw [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
      MvPowerSeries.map_id, RingHom.id_apply] at h
  exact h

theorem psi_eq_sum (d : ℕ) (f : PS G) :
    psi G hp d f = ∑ g : Fin (nG G) → Fin (p ^ (d + 1)),
      (MvPowerSeries.coeff (mg G d g) f) • vfam G d g := by
  classical
  obtain ⟨N, hN⟩ := isNilpotent_Icirc (εA G (d + 1))
  set q := p ^ (d + 1) with hq
  have hq1 : 0 < q := pow_pos (Nat.Prime.pos (Fact.out)) _
  set D := N + q with hD
  let bnd : Fin (nG G) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => D
  have hbnd : ∀ i, bnd i = D := fun i => rfl
  set P := MvPowerSeries.trunc' R bnd f with hP

  have hrest : phi G hp d (f - (P : PS G)) = 0 := by
    apply phi_eq_zero_of_coeff G hp d (D + 1)
    · exact le_antisymm (le_trans (Ideal.pow_le_pow_right (by omega)) hN.le) bot_le
    · intro m hm
      have hle : m ≤ bnd := by
        rw [Finsupp.le_def]
        intro i
        rw [hbnd]
        have := Finsupp.le_degree i m
        omega
      rw [map_sub, MvPolynomial.coeff_coe, hP, MvPowerSeries.coeff_trunc', if_pos hle, sub_self]
  have hsplit : psi G hp d f = psi G hp d (P : PS G) := by
    have : f = (P : PS G) + (f - (P : PS G)) := by abel
    conv_lhs => rw [this, map_add]
    rw [show psi G hp d (f - (P : PS G)) = 0 from by rw [psi, AlgHom.comp_apply, hrest, map_zero], add_zero]
  rw [hsplit, aeval_coe_eq_psi]

  have hPsum : P = ∑ m ∈ Finset.Iic bnd, MvPolynomial.monomial m (MvPowerSeries.coeff m f) := by
    rw [hP]; exact MvPowerSeries.truncFinset_apply f
  rw [hPsum, map_sum]
  have hterm : ∀ m : Fin (nG G) →₀ ℕ, MvPolynomial.aeval (tau G d) (MvPolynomial.monomial m
      (MvPowerSeries.coeff m f)) = (MvPowerSeries.coeff m f) • mono G d m := by
    intro m
    rw [MvPolynomial.aeval_monomial, mono, Finsupp.prod_fintype]
    · exact (Algebra.smul_def _ _).symm
    · intro i; exact pow_zero _
  simp_rw [hterm]

  rw [← Finset.sum_filter_of_ne (p := fun m => ∀ i, m i < q) (fun m _ hne => by
    by_contra hb
    exact hne (by rw [mono_eq_zero G d m hb, smul_zero]))]

  refine Finset.sum_nbij' (fun m i => ⟨m i % q, Nat.mod_lt _ hq1⟩) (fun g => mg G d g) ?_ ?_ ?_ ?_ ?_
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
    have hmg : mg G d (fun i => ⟨m i % q, Nat.mod_lt _ hq1⟩) = m := by
      ext i; rw [mg_apply]; exact Nat.mod_eq_of_lt (hm.2 i)
    rw [hmg, ← mono_mg, hmg]

include hp in

theorem span_vfam (d : ℕ) : ⊤ ≤ Submodule.span (kk R) (Set.range (vfam G d)) := by
  rintro c -
  obtain ⟨f, rfl⟩ := psi_surjective G hp d c
  rw [psi_eq_sum]
  refine Submodule.sum_mem _ fun g _ => ?_
  rw [← algebraMap_smul (kk R)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

include hp in

theorem linearIndependent_vfam (d : ℕ) : LinearIndependent (kk R) (vfam G d) := by
  classical
  refine linearIndependent_of_top_le_span_of_card_eq_finrank (span_vfam G hp d) ?_
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, finrank_Cb]

theorem coeff_mem_maximalIdeal_of_phi_eq_zero (d : ℕ) {f : PS G} (hf : phi G hp d f = 0)
    (m : Fin (nG G) →₀ ℕ) (hm : ∀ i, m i < p ^ (d + 1)) :
    MvPowerSeries.coeff m f ∈ maximalIdeal R := by
  have h0 : psi G hp d f = 0 := by rw [psi, AlgHom.comp_apply, hf, map_zero]
  rw [psi_eq_sum] at h0
  simp_rw [← algebraMap_smul (kk R) (MvPowerSeries.coeff _ f) (vfam G d _)] at h0
  have h1 := (Fintype.linearIndependent_iff.1 (linearIndependent_vfam G hp d)) _ h0 fun i => ⟨m i, hm i⟩
  have hmg : mg G d (fun i => ⟨m i, hm i⟩) = m := by ext i; rfl
  rw [hmg] at h1
  rw [← IsLocalRing.residue_eq_zero_iff]
  exact h1

end FieldInput

section Final

variable {R : Type} [CommRing R] [IsArtinianRing R] [IsLocalRing R] {p h : ℕ} [Fact p.Prime]
  (G : PDivisibleGroup R p h) (hp : (p : R) ∈ maximalIdeal R) [CharP (kk R) p]

theorem exists_eq_sum_smul (T : Finset R) (f : PS G)
    (hf : ∀ m, MvPowerSeries.coeff m f ∈ Ideal.span (T : Set R)) :
    ∃ g : R → PS G, f = ∑ a ∈ T, a • g a := by
  have hc : ∀ m : Fin (nG G) →₀ ℕ, ∃ c : R → R, Function.support c ⊆ T ∧ ∑ a ∈ T, c a • a =
      MvPowerSeries.coeff m f := fun m => Submodule.mem_span_finset.1 (hf m)
  choose c _ hc using hc
  refine ⟨fun a => fun m => c m a, ?_⟩
  ext m
  rw [map_sum, ← hc m]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, smul_eq_mul, mul_comm, MvPowerSeries.coeff_apply]

include hp in

theorem coeff_mem_pow (f : PS G) (hf : ∀ d, phi G hp d f = 0) (j : ℕ) :
    ∀ m, MvPowerSeries.coeff m f ∈ maximalIdeal R ^ j := by
  induction j with
  | zero => intro m; rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ j ih =>
    intro m₀
    obtain ⟨T, hT⟩ : (maximalIdeal R ^ j).FG := IsNoetherian.noetherian _
    obtain ⟨g, hg⟩ := exists_eq_sum_smul G T f (fun m => by rw [hT]; exact ih m)

    obtain ⟨d, hd⟩ : ∃ d, ∀ i, m₀ i < p ^ (d + 1) := by
      refine ⟨m₀.degree, fun i => lt_of_le_of_lt (Finsupp.le_degree i m₀) ?_⟩
      calc m₀.degree < p ^ m₀.degree := Nat.lt_pow_self (Nat.Prime.one_lt Fact.out)
        _ ≤ p ^ (m₀.degree + 1) := Nat.pow_le_pow_right (Nat.Prime.pos Fact.out) (Nat.le_succ _)

    haveI : Module.Projective R (QG G (d + 1)) := projective_Q (εA G (d + 1))
    obtain ⟨sec, hsec⟩ := Module.projective_lifting_property (phi G hp d).toLinearMap LinearMap.id
      (phi_surjective G hp d)
    let P : PS G →ₗ[R] PS G := LinearMap.id - sec ∘ₗ (phi G hp d).toLinearMap
    have hPker : ∀ x, phi G hp d (P x) = 0 := fun x => by
      have h1 : phi G hp d (sec (phi G hp d x)) = phi G hp d x := by
        change ((phi G hp d).toLinearMap ∘ₗ sec) (phi G hp d x) = _
        rw [hsec]; rfl
      change phi G hp d (x - sec (phi G hp d x)) = 0
      rw [map_sub, h1, sub_self]
    have hPf : P f = f := by
      change f - sec (phi G hp d f) = f
      rw [hf d, map_zero, sub_zero]
    have hdec : f = ∑ a ∈ T, a • P (g a) := by
      conv_lhs => rw [← hPf, hg]
      rw [map_sum]
      exact Finset.sum_congr rfl fun a _ => map_smul _ _ _
    rw [hdec, map_sum]
    refine Ideal.sum_mem _ fun a ha => ?_
    rw [map_smul, smul_eq_mul, pow_succ]
    refine Ideal.mul_mem_mul ?_ (coeff_mem_maximalIdeal_of_phi_eq_zero G hp d (hPker _) m₀ hd)
    rw [← hT]
    exact Ideal.subset_span ha

include hp in
theorem eq_zero_of_forall_phi (f : PS G) (hf : ∀ d, phi G hp d f = 0) : f = 0 := by
  obtain ⟨e, he⟩ := isNilpotent_maximalIdeal R
  ext m
  have h1 := coeff_mem_pow G hp f hf e m
  rw [he, Ideal.zero_eq_bot] at h1
  rw [(Submodule.mem_bot _).1 h1, map_zero]

include hp in
theorem iInf_ker_phi : (⨅ d, RingHom.ker (phi G hp d)) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_iInf] at hf
  exact (Submodule.mem_bot _).2 (eq_zero_of_forall_phi G hp f fun d => hf d)

include hp in

theorem exists_ker_phi_le (N : ℕ) : ∃ d, RingHom.ker (phi G hp d) ≤ maximalIdeal (PS G) ^ N := by
  haveI : IsNoetherianRing (PS G) := MvPowerSeries.isNoetherianRing_of_finite
  haveI : IsAdicComplete (maximalIdeal (PS G)) (PS G) := MvPowerSeries.isAdicComplete_maximalIdeal
  exact IsLocalRing.exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot _ (ker_phi_antitone G hp)
    (iInf_ker_phi G hp) N

def ccAlg : PS G →ₐ[R] R :=
  { (MvPowerSeries.constantCoeff : PS G →+* R) with
    commutes' := fun r => MvPowerSeries.constantCoeff_C r }

@[scoped simp] theorem ccAlg_apply (f : PS G) : ccAlg G f = MvPowerSeries.constantCoeff f := rfl

theorem maximalIdeal_PS_le : maximalIdeal (PS G) ≤ (maximalIdeal R).comap (ccAlg G) := by
  intro f hf
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ccAlg_apply]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff] at hf
  exact hf

theorem coeff_eq_zero_of_mem_sq (f : PS G) (hf : f ∈ RingHom.ker (ccAlg G) ^ 2) (i : Fin (nG G)) :
    MvPowerSeries.coeff (Finsupp.single i 1) f = 0 := by
  classical
  rw [pow_two] at hf
  refine Submodule.mul_induction_on hf ?_ ?_
  · intro a ha b hb
    rw [RingHom.mem_ker, ccAlg_apply] at ha hb
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hdeg : x.1.degree + x.2.degree = 1 := by
      rw [← map_add, hx, Finsupp.degree_single]
    rcases Nat.eq_zero_or_pos x.1.degree with h0 | h0
    · rw [(Finsupp.degree_eq_zero_iff _).1 h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ha, zero_mul]
    · have h2 : x.2.degree = 0 := by omega
      rw [(Finsupp.degree_eq_zero_iff _).1 h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hb, mul_zero]
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

theorem maximalIdeal_pow_le_sq (e : ℕ) (he : maximalIdeal R ^ e = ⊥) :
    maximalIdeal (PS G) ^ (2 * e) ≤ RingHom.ker (ccAlg G) ^ 2 := by
  rw [pow_mul']
  refine Ideal.pow_right_mono ?_ 2
  refine le_trans (Ideal.pow_right_mono (maximalIdeal_PS_le G) e) (le_trans (Ideal.le_comap_pow _ e) ?_)
  rw [he, ← RingHom.ker_eq_comap_bot]

theorem span_X_le_ker : Ideal.span (Set.range (MvPowerSeries.X : Fin (nG G) → PS G)) ≤ RingHom.ker (ccAlg G) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change ccAlg G (MvPowerSeries.X i) = 0
  rw [ccAlg_apply, MvPowerSeries.constantCoeff_X]

include hp in

theorem εQ_comp_phi (d : ℕ) : (εQ (εA G (d + 1))).comp (phi G hp d) = ccAlg G := by
  refine MvPowerSeries.algHom_ext_of_apply_X_mem (⊥ : Ideal R) _ _ (fun i => ?_) (fun i => ?_)
  · rw [AlgHom.comp_apply, phi_X, tQ, εQ_mk]
    exact (gens G d i).2
  · rw [AlgHom.comp_apply, phi_X, tQ, εQ_mk, ccAlg_apply, MvPowerSeries.constantCoeff_X]
    exact (gens G d i).2

include hp in

theorem Icirc_le_map (d : ℕ) :
    Icirc (εA G (d + 1)) ≤ (Ideal.span (Set.range (MvPowerSeries.X : Fin (nG G) → PS G))).map (phi G hp d) := by
  intro z hz
  obtain ⟨g, rfl⟩ := phi_surjective G hp d z
  rw [mem_Icirc_iff, ← AlgHom.comp_apply, εQ_comp_phi, ccAlg_apply] at hz
  refine Ideal.mem_map_of_mem _ ?_
  have h := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 1 g (fun m hm => ?_)
  · rwa [pow_one] at h
  · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 (by omega)
    rw [hm0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hz]

include hp in

theorem free_cotangent_level (d : ℕ) (e : ℕ) (he : maximalIdeal R ^ e = ⊥)
    (hd : RingHom.ker (phi G hp d) ≤ maximalIdeal (PS G) ^ (2 * e)) :
    Module.Free R (G.Cotangent (d + 1)) := by
  classical
  set I := G.augIdeal (d + 1)
  let vv : Fin (nG G) → G.Cotangent (d + 1) := fun i => I.toCotangent (gens G d i)
  let L : (Fin (nG G) → R) →ₗ[R] G.Cotangent (d + 1) := Fintype.linearCombination R vv

  have hsurj : Surjective L := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson ⊥) ?_
    rw [span_gens G hp d]

  have hinj : Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [Fintype.linearCombination_apply] at hc
    have hsum : ∑ i, c i • vv i = I.toCotangent (∑ i, c i • gens G d i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => (I.toCotangent.map_smul_of_tower _ _).symm
    rw [hsum, Ideal.toCotangent_eq_zero] at hc

    set π := Ideal.Quotient.mk (Iinf (εA G (d + 1)))
    have hπ : π ((∑ i, c i • gens G d i : I) : G.level (d + 1)) ∈ Icirc (εA G (d + 1)) ^ 2 := by
      rw [Icirc, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hc
    let y : PS G := ∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i
    have hy : phi G hp d y = π ((∑ i, c i • gens G d i : I) : G.level (d + 1)) := by
      rw [map_sum, Submodule.coe_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, phi_X, Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul, tQ]
      congr 1
      rw [MvPowerSeries.c_eq_algebraMap, AlgHom.commutes]
      rfl
    have hmem : phi G hp d y ∈ ((Ideal.span (Set.range (MvPowerSeries.X : Fin (nG G) → PS G))) ^ 2).map
        (phi G hp d) := by
      rw [Ideal.map_pow, hy]
      exact Ideal.pow_right_mono (Icirc_le_map G hp d) 2 hπ
    obtain ⟨g₂, hg₂, hg₂y⟩ := (Ideal.mem_map_iff_of_surjective _ (phi_surjective G hp d)).1 hmem
    have hker : y - g₂ ∈ RingHom.ker (phi G hp d) := by
      rw [RingHom.mem_ker, map_sub, hg₂y, sub_self]
    have hsq : y - g₂ ∈ RingHom.ker (ccAlg G) ^ 2 := maximalIdeal_pow_le_sq G e he (hd hker)
    have hg₂' : g₂ ∈ RingHom.ker (ccAlg G) ^ 2 := Ideal.pow_right_mono (span_X_le_ker G) 2 hg₂
    funext i
    have h1 := coeff_eq_zero_of_mem_sq G _ hsq i
    have h2 := coeff_eq_zero_of_mem_sq G _ hg₂' i
    rw [map_sub, h2, sub_zero] at h1
    have hyc : MvPowerSeries.coeff (Finsupp.single i 1) y = c i := by
      change MvPowerSeries.coeff (Finsupp.single i 1) (∑ j, MvPowerSeries.C (c j) * MvPowerSeries.X j) = c i
      rw [map_sum]
      simp_rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
      simp [Finsupp.single_left_inj]
    rw [hyc] at h1
    exact h1
  exact Module.Free.of_equiv (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩)

theorem cotangentMap_bijective_of_pow_eq_zero (u : ℕ) (hu : (p : R) ^ u = 0) :
    Bijective (G.cotangentMap u) := by
  refine ⟨?_, G.cotangentMap_surjective u⟩
  rw [← LinearMap.ker_eq_bot, (G.ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot u).1, hu,
    Ideal.span_singleton_eq_bot.2 rfl, Submodule.bot_smul]

def equivDown (v : ℕ) (hv : (p : R) ^ v = 0) : (j : ℕ) → (G.Cotangent (v + j) ≃ₗ[R] G.Cotangent v)
  | 0 => LinearEquiv.refl R _
  | j + 1 =>
    (LinearEquiv.ofBijective (G.cotangentMap (v + j))
      (cotangentMap_bijective_of_pow_eq_zero G (v + j) (by rw [pow_add, hv, zero_mul]))).trans
      (equivDown v hv j)

end Final

end PDivFreeCot
p2m_reactivate "P2MW.S_PDivisibleGroup_free_cotangent_of_isArtinianRing_of_pow_eq_zero.PDivFreeCot"

open PDivFreeCot IsLocalRing in
theorem solution
    {R : Type} [CommRing R] [IsArtinianRing R] [IsLocalRing R]
    {p h : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h) {v : ℕ} (hv : (p : R) ^ v = 0) :
    Module.Free R (G.Cotangent v) := by
  have hp : (p : R) ∈ maximalIdeal R :=
    Ideal.IsPrime.mem_of_pow_mem inferInstance v (by rw [hv]; exact Ideal.zero_mem _)
  haveI : CharP (kk R) p := by
    refine (CharP.charP_iff_prime_eq_zero Fact.out).2 ?_
    rw [← map_natCast (residue R), IsLocalRing.residue_eq_zero_iff]
    exact hp
  obtain ⟨e, he⟩ := isNilpotent_maximalIdeal R
  rw [Ideal.zero_eq_bot] at he
  obtain ⟨d₀, hd₀⟩ := exists_ker_phi_le G hp (2 * e)
  have hd : RingHom.ker (phi G hp (max d₀ v)) ≤ maximalIdeal (PS G) ^ (2 * e) :=
    le_trans (ker_phi_antitone G hp (le_max_left d₀ v)) hd₀
  have hfree : Module.Free R (G.Cotangent (max d₀ v + 1)) := free_cotangent_level G hp _ e he hd
  obtain ⟨j, hj⟩ : ∃ j, max d₀ v + 1 = v + j := ⟨max d₀ v + 1 - v, by omega⟩
  rw [hj] at hfree
  exact Module.Free.of_equiv (equivDown G v hv j)

end
end S_PDivisibleGroup_free_cotangent_of_isArtinianRing_of_pow_eq_zero
end P2MW
export P2MW.S_PDivisibleGroup_free_cotangent_of_isArtinianRing_of_pow_eq_zero (solution)

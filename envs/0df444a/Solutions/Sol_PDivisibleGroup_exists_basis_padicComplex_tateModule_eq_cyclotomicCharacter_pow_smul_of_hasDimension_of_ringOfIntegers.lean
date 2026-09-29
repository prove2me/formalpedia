-- Prove2me | solution 1 for PDivisibleGroup.exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0217166a-4c12-5785-a030-a215bbcc8905

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_MulSemiringAction_exists_basis_extending_invariants_eq_zpow_smul_and_iff_mem_span_fixedPoints_of_pairing_of_continuous_cocycle
import Theorems.Thm_PadicComplex_eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul
import Theorems.Thm_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle
import Theorems.Thm_PadicComplex_exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup
import Theorems.Thm_PDivisibleGroup_isOpen_setOf_restrictScalars_smul_points_eq
import Theorems.Thm_PDivisibleGroup_nonempty_basis_tateModule_points
import Theorems.Thm_TateModule_nonempty_basis_of_card_torsionBy
import Theorems.Thm_PDivisibleGroup_CartierDuality_exists_tateModule_pairing_eq_pair
import Theorems.Thm_PDivisibleGroup_CartierDuality_bijective_tateModule_pairing_of_isAlgClosed
import Theorems.Thm_PDivisibleGroup_exists_isCartierDual
import Theorems.Thm_PDivisibleGroup_CartierDuality_isCartierDual_symm
import Theorems.Thm_PDivisibleGroup_exists_hasDimension
import Theorems.Thm_PDivisibleGroup_add_eq_height_of_hasDimension_of_cartierDuality
import Theorems.Thm_PDivisibleGroup_CartierDuality_exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers
import Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions PDivisibleGroup.CPoints.instDistribMulAction PrimaryTorsion.instSMul PrimaryTorsion.instModule"
p2m_attr_erase "simp" "CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul PDivisibleGroup.cotangentBaseChange_tmul PDivisibleGroup.baseChange_transition_tmul PDivisibleGroup.cotangentToBaseChange_toCotangent PDivisibleGroup.baseChange_level HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff PDivisibleGroup.cotangentClass_algebraMap PDivisibleGroup.cotangentClass_one PDivisibleGroup.cpointsProj_cpointsMap PDivisibleGroup.pointsMap_reduceModPow_cpointsProj_succ PDivisibleGroup.cpointsProj_toCPoints PDivisibleGroup.mapModPow_mk PDivisibleGroup.reduceModPow_mk PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map"

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace HTPDIVK

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

local notation "Γp" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
local notation "GK" => (K.fixingSubgroup)
local notation "ΓO" => (PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)

variable (Pt : Type) [AddCommGroup Pt]
  [DistribMulAction (PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) Pt]

abbrev T : Type := TateModule p Pt

abbrev V : Type := ℚ_[p] ⊗[ℤ_[p]] T p Pt

abbrev W : Type := ℂ_[p] ⊗[ℚ_[p]] V p Pt

def rT (σ : GK) : T p Pt →ₗ[ℤ_[p]] T p Pt :=
  TateModule.rep p Pt ΓO (PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ)

def rV (σ : GK) : V p Pt →ₗ[ℚ_[p]] V p Pt := (rT p K Pt σ).baseChange ℚ_[p]

def ρ (σ : GK) : W p Pt →ₗ[ℚ_[p]] W p Pt :=
  TensorProduct.map (PadicComplex.galAlgHom p (σ : Γp)).toLinearMap (rV p K Pt σ)

variable {p K Pt}

theorem rT_apply_coe (σ : GK) (x : T p Pt) (n : ℕ) :
    ((rT p K Pt σ x : T p Pt) : ℕ → Pt) n =
      PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ • (x : ℕ → Pt) n := rfl

theorem rT_mul (σ τ : GK) : rT p K Pt (σ * τ) = rT p K Pt σ ∘ₗ rT p K Pt τ := by
  show TateModule.rep p Pt ΓO (PadicAlgCl.ringOfIntegers.galToAlgEquiv p K (σ * τ)) = _
  rw [map_mul, map_mul, Module.End.mul_eq_comp]; rfl

theorem rT_one : rT p K Pt 1 = LinearMap.id := by
  show TateModule.rep p Pt ΓO (PadicAlgCl.ringOfIntegers.galToAlgEquiv p K 1) = _
  rw [map_one, map_one, Module.End.one_eq_id]

theorem rV_mul (σ τ : GK) : rV p K Pt (σ * τ) = rV p K Pt σ ∘ₗ rV p K Pt τ := by
  unfold rV; rw [rT_mul, LinearMap.baseChange_comp]

theorem rV_one : rV p K Pt 1 = LinearMap.id := by
  unfold rV; rw [rT_one, LinearMap.baseChange_id]

theorem rV_tmul (σ : GK) (a : ℚ_[p]) (x : T p Pt) :
    rV p K Pt σ (a ⊗ₜ x) = a ⊗ₜ rT p K Pt σ x := rfl

theorem subgroup_smul_def (σ : GK) (c : ℂ_[p]) : σ • c = (σ : Γp) • c := rfl

variable (p K) in
theorem galAlgHom_mul (σ τ : GK) :
    PadicComplex.galAlgHom p ((σ * τ : GK) : Γp) =
      (PadicComplex.galAlgHom p (σ : Γp)).comp (PadicComplex.galAlgHom p (τ : Γp)) :=
  AlgHom.ext fun x => mul_smul (σ : Γp) (τ : Γp) x

variable (p K) in
theorem galAlgHom_one : PadicComplex.galAlgHom p ((1 : GK) : Γp) = AlgHom.id ℚ_[p] ℂ_[p] :=
  AlgHom.ext fun x => one_smul _ x

theorem ρ_mul (σ τ : GK) : ρ p K Pt (σ * τ) = ρ p K Pt σ ∘ₗ ρ p K Pt τ := by
  unfold ρ
  rw [galAlgHom_mul, rV_mul, AlgHom.comp_toLinearMap, TensorProduct.map_comp]

theorem ρ_one : ρ p K Pt 1 = LinearMap.id := by
  unfold ρ
  rw [galAlgHom_one, rV_one, AlgHom.toLinearMap_id, TensorProduct.map_id]

theorem ρ_mul_apply (σ τ : GK) (w : W p Pt) : ρ p K Pt (σ * τ) w = ρ p K Pt σ (ρ p K Pt τ w) := by
  rw [ρ_mul]; rfl

theorem ρ_one_apply (w : W p Pt) : ρ p K Pt 1 w = w := by
  rw [ρ_one]; rfl

theorem ρ_inv_self_apply (σ : GK) (w : W p Pt) : ρ p K Pt σ⁻¹ (ρ p K Pt σ w) = w := by
  rw [← ρ_mul_apply, inv_mul_cancel, ρ_one]; rfl

theorem ρ_self_inv_apply (σ : GK) (w : W p Pt) : ρ p K Pt σ (ρ p K Pt σ⁻¹ w) = w := by
  rw [← ρ_mul_apply, mul_inv_cancel, ρ_one]; rfl

theorem ρ_surjective (σ : GK) : Function.Surjective (ρ p K Pt σ) :=
  fun w => ⟨ρ p K Pt σ⁻¹ w, ρ_self_inv_apply σ w⟩

theorem ρ_tmul (σ : GK) (c : ℂ_[p]) (v : V p Pt) :
    ρ p K Pt σ (c ⊗ₜ v) = (σ • c) ⊗ₜ rV p K Pt σ v := rfl

theorem smul_smul_gal (σ : GK) (c c' : ℂ_[p]) : σ • (c • c') = (σ • c) • (σ • c') := by
  rw [smul_eq_mul, smul_eq_mul, smul_mul']

theorem ρ_smul (σ : GK) (c : ℂ_[p]) (w : W p Pt) :
    ρ p K Pt σ (c • w) = (σ • c) • ρ p K Pt σ w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul c' v =>
      rw [TensorProduct.smul_tmul', ρ_tmul, ρ_tmul]
      refine Eq.trans ?_ (TensorProduct.smul_tmul' (σ • c) (σ • c') (rV p K Pt σ v)).symm
      rw [smul_smul_gal]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

section chi

variable (p)

def χZ (σ : Γp) : ℤ_[p] :=
  ((cyclotomicCharacter (PadicAlgCl p) p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toRingEquiv : ℤ_[p]ˣ) :
    ℤ_[p])

def ιC : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp (PadicInt.Coe.ringHom (p := p))

theorem ιC_apply (a : ℤ_[p]) : ιC p a = algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p]) := rfl

theorem ιC_injective : Function.Injective (ιC p) :=
  (algebraMap ℚ_[p] ℂ_[p]).injective.comp Subtype.val_injective

theorem smul_ιC (σ : Γp) (a : ℤ_[p]) : σ • ιC p a = ιC p a := by
  rw [ιC_apply, PadicComplex.smul_algebraMap]

def χC : Γp →* ℂ_[p]ˣ :=
  (Units.map ((algebraMap ℚ_[p] ℂ_[p] : ℚ_[p] →+* ℂ_[p]) : ℚ_[p] →* ℂ_[p])).comp <|
    (Units.map (PadicInt.Coe.ringHom (p := p) : ℤ_[p] →* ℚ_[p])).comp <|
      (cyclotomicCharacter (PadicAlgCl p) p).comp
        (MonoidHom.mk' (fun σ : Γp => (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toRingEquiv)
          (fun _ _ => rfl))

theorem χC_coe (σ : Γp) :
    ((χC p σ : ℂ_[p]ˣ) : ℂ_[p]) =
      algebraMap ℚ_[p] ℂ_[p]
        (((cyclotomicCharacter (PadicAlgCl p) p
            (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) := rfl

theorem χC_coe_eq_ιC (σ : Γp) : ((χC p σ : ℂ_[p]ˣ) : ℂ_[p]) = ιC p (χZ p σ) := rfl

theorem smul_χC (σ τ : Γp) : σ • ((χC p τ : ℂ_[p]ˣ) : ℂ_[p]) = χC p τ := by
  rw [χC_coe, PadicComplex.smul_algebraMap]

theorem smul_χC_zpow (σ τ : Γp) (k : ℤ) :
    σ • (((χC p τ : ℂ_[p]ˣ) : ℂ_[p]) ^ k) = ((χC p τ : ℂ_[p]ˣ) : ℂ_[p]) ^ k := by
  rw [← Units.val_zpow_eq_zpow_val, ← map_zpow, smul_χC]

scoped instance neZero_prime_rat : NeZero ((p : ℕ) : ℚ) :=
  ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩

theorem cyclotomicCharacter_localGaloisToGlobal (σ : Γp) :
    cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv =
      cyclotomicCharacter (PadicAlgCl p) p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toRingEquiv := by
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  set a := PadicInt.toZModPow n
    ((cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv : ℤ_[p]ˣ) :
      ℤ_[p]) with ha
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ n)
  have hζ : IsPrimitiveRoot (padicEmbedding p ζ₀) (p ^ n) :=
    hζ₀.map_of_injective (padicEmbedding p).toRingHom.injective
  have hσζ : σ (padicEmbedding p ζ₀) = (padicEmbedding p ζ₀) ^ a.val := by
    rw [← padicEmbedding_localGaloisToGlobal, ← map_pow]
    congr 1
    exact cyclotomicCharacter.spec p (localGaloisToGlobal p σ).toRingEquiv ζ₀ hζ₀.pow_eq_one
  rw [cyclotomicCharacter.toZModPow]
  refine modularCyclotomicCharacter.unique (PadicAlgCl p)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (PadicAlgCl p) (p ^ n))
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toRingEquiv (c := a) fun t ht => ?_
  have ht' : ((t : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ (p ^ n) = 1 := by
    have := (mem_rootsOfUnity _ t).1 ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one ht'
  show σ ((t : (PadicAlgCl p)ˣ) : PadicAlgCl p) = _
  rw [← hi, map_pow, hσζ, ← pow_mul, mul_comm, pow_mul]

theorem continuous_padicInt_coe : Continuous ((↑) : ℤ_[p] → ℚ_[p]) :=
  (AddMonoidHomClass.isometry_of_norm (PadicInt.Coe.ringHom (p := p)) fun _ => rfl).continuous

theorem toRingAut_eq (σ : Γp) :
    MulSemiringAction.toRingAut Γp (PadicAlgCl p) σ =
      (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toRingEquiv :=
  RingEquiv.ext fun _ => rfl

theorem continuous_χZ : Continuous (χZ p) := by
  have h := cyclotomicCharacter.continuous p ℚ_[p] (PadicAlgCl p)
  have h' : Continuous fun σ : Γp =>
      ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut Γp (PadicAlgCl p) σ) :
        ℤ_[p]ˣ) : ℤ_[p]) := Units.continuous_val.comp h
  refine h'.congr fun σ => ?_
  show _ = χZ p σ
  rw [toRingAut_eq]; rfl

theorem continuous_χC_coe : Continuous fun σ : Γp => ((χC p σ : ℂ_[p]ˣ) : ℂ_[p]) :=
  (continuous_algebraMap ℚ_[p] ℂ_[p]).comp ((continuous_padicInt_coe p).comp (continuous_χZ p))

theorem continuous_χC_zpow (k : ℤ) :
    Continuous fun σ : Γp => ((χC p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ k :=
  (continuous_χC_coe p).zpow₀ k fun σ => Or.inl (χC p σ).ne_zero

variable (K)

def χCK : GK →* ℂ_[p]ˣ := (χC p).comp K.fixingSubgroup.subtype

theorem χCK_apply (τ : GK) : χCK p K τ = χC p (τ : Γp) := rfl

theorem χCK_coe_eq_ιC (τ : GK) : ((χCK p K τ : ℂ_[p]ˣ) : ℂ_[p]) = ιC p (χZ p (τ : Γp)) := rfl

theorem smul_χCK (σ τ : GK) : σ • ((χCK p K τ : ℂ_[p]ˣ) : ℂ_[p]) = χCK p K τ :=
  smul_χC p (σ : Γp) (τ : Γp)

theorem smul_χCK_zpow (σ τ : GK) (k : ℤ) :
    σ • (((χCK p K τ : ℂ_[p]ˣ) : ℂ_[p]) ^ k) = ((χCK p K τ : ℂ_[p]ˣ) : ℂ_[p]) ^ k :=
  smul_χC_zpow p (σ : Γp) (τ : Γp) k

theorem continuous_χCK_zpow (k : ℤ) :
    Continuous fun τ : GK => ((χCK p K τ : ℂ_[p]ˣ) : ℂ_[p]) ^ k :=
  (continuous_χC_zpow p k).comp continuous_subtype_val

theorem hH0 (k : ℤ) (hk : k ≠ 0) (c : ℂ_[p])
    (hc : ∀ σ : Γp, σ • c = ((χC p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ k * c) : c = 0 := by
  refine PadicComplex.eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul p k hk c fun σ => ?_
  rw [hc σ, χC_coe, cyclotomicCharacter_localGaloisToGlobal]

theorem hH0K [FiniteDimensional ℚ_[p] K] (k : ℤ) (hk : k ≠ 0) (c : ℂ_[p])
    (hc : ∀ σ : GK, σ • c = ((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) ^ k * c) : c = 0 := by
  by_contra hc0

  let ρ₀ : Γp → ℂ_[p] →+ ℂ_[p] := fun σ => DistribSMul.toAddMonoidHom ℂ_[p] σ
  have hρ₀ : ∀ (σ : Γp) (a w : ℂ_[p]), ρ₀ σ (a • w) = (σ • a) • ρ₀ σ w := fun σ a w =>
    smul_mul' σ a w
  have hρ₀one : ∀ w : ℂ_[p], ρ₀ 1 w = w := fun w => one_smul _ w
  have hρ₀mul : ∀ (σ τ : Γp) (w : ℂ_[p]), ρ₀ (σ * τ) w = ρ₀ σ (ρ₀ τ w) := fun σ τ w => mul_smul σ τ w

  let χk : Γp →* ℂ_[p]ˣ := (zpowGroupHom k).comp (χC p)
  have hχk : ∀ σ : Γp, ((χk σ : ℂ_[p]ˣ) : ℂ_[p]) = ((χC p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ k := fun σ => by
    show (((χC p σ) ^ k : ℂ_[p]ˣ) : ℂ_[p]) = _
    rw [Units.val_zpow_eq_zpow_val]
  have hχkfix : ∀ σ τ : Γp, σ • ((χk τ : ℂ_[p]ˣ) : ℂ_[p]) = χk τ := fun σ τ => by
    rw [hχk, smul_χC_zpow]

  let f : Unit → (ℂ_[p] →ₗ[ℂ_[p]] ℂ_[p]) := fun _ => c⁻¹ • LinearMap.id
  have hf : LinearIndependent ℂ_[p] f := by
    rw [linearIndependent_unique_iff]
    intro h0
    have h1 : f default c = 0 := by rw [h0, LinearMap.zero_apply]
    have h2 : f default c = 1 := by
      show c⁻¹ • ((LinearMap.id : ℂ_[p] →ₗ[ℂ_[p]] ℂ_[p]) c) = 1
      rw [LinearMap.id_apply, smul_eq_mul, inv_mul_cancel₀ hc0]
    rw [h2] at h1
    exact one_ne_zero h1
  have hfK : ∀ σ : Γp, σ ∈ K.fixingSubgroup → ∀ (i : Unit) (x : ℂ_[p]),
      f i (ρ₀ σ x) = (χk σ : ℂ_[p]) * σ • f i x := by
    intro σ hσ i x
    have hcσ : σ • c = ((χC p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ k * c := hc ⟨σ, hσ⟩
    show c⁻¹ • (σ • x) = (χk σ : ℂ_[p]) * σ • (c⁻¹ • x)
    rw [smul_eq_mul, smul_eq_mul, smul_mul', smul_inv'', hcσ, hχk, mul_inv, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ (zpow_ne_zero k (χC p σ).ne_zero), one_mul]

  obtain ⟨f', hf', hf'eq⟩ :=
    PadicComplex.exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup p ρ₀ hρ₀
      hρ₀one hρ₀mul χk hχkfix K f hf hfK
  set d : ℂ_[p] := f' () 1 with hd
  have hd0 : d ≠ 0 := by
    intro hd0
    have hzero : f' () = 0 := by
      refine LinearMap.ext fun x => ?_
      have : f' () x = x * f' () 1 := by
        rw [← smul_eq_mul, ← LinearMap.map_smul, smul_eq_mul, mul_one]
      rw [this, ← hd, hd0, mul_zero, LinearMap.zero_apply]
    exact (linearIndependent_unique_iff.1 hf') hzero

  have hdσ : ∀ σ : Γp, σ • d = ((χC p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ (-k) * d := by
    intro σ
    have h1 : f' () (ρ₀ σ 1) = (χk σ : ℂ_[p]) * σ • f' () 1 := hf'eq σ () 1
    have h2 : ρ₀ σ 1 = 1 := smul_one σ
    rw [h2, ← hd, hχk] at h1
    have hne : ((χC p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ k ≠ 0 := zpow_ne_zero k (χC p σ).ne_zero
    calc σ • d = (((χC p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ k)⁻¹ * ((((χC p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ k) * σ • d) := by
          rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      _ = ((χC p σ : ℂ_[p]ˣ) : ℂ_[p]) ^ (-k) * d := by rw [← h1, zpow_neg]
  exact hd0 (hH0 p (-k) (neg_ne_zero.2 hk) d hdσ)

theorem hH1K [FiniteDimensional ℚ_[p] K] (c : GK → ℂ_[p]) (hc : Continuous c)
    (hcoc : ∀ σ τ : GK,
      c (σ * τ) = c σ + ((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) ^ (-(-1 : ℤ)) * σ • c τ) :
    ∃ b : ℂ_[p], ∀ σ : GK,
      c σ = ((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) ^ (-(-1 : ℤ)) * σ • b - b := by
  have hneg : (-(-1 : ℤ)) = 1 := neg_neg 1
  simp only [hneg] at hcoc ⊢
  obtain ⟨b, hb⟩ :=
    PadicComplex.exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle p K 1
      one_ne_zero c hc (fun σ τ => by rw [hcoc, χCK_apply, χC_coe]; rfl)
  refine ⟨b, fun σ => ?_⟩
  rw [χCK_apply, χC_coe]
  exact hb σ

variable {K}

theorem apply_eq_of_mem_fixingSubgroup {E : IntermediateField ℚ_[p] (PadicAlgCl p)} {g : Γp}
    (hg : g ∈ E.fixingSubgroup) {y : PadicAlgCl p} (hy : y ∈ E) : g y = y :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg y hy

theorem continuous_orbit (b : ℂ_[p]) : Continuous fun σ : Γp => σ • b := by
  refine continuous_iff_continuousAt.2 fun σ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.1
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) b ε hε
  let E : IntermediateField ℚ_[p] (PadicAlgCl p) := IntermediateField.adjoin ℚ_[p] {a}
  haveI : FiniteDimensional ℚ_[p] E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  have hU : IsOpen (E.fixingSubgroup : Set Γp) := IntermediateField.fixingSubgroup_isOpen E
  have hV : IsOpen {x : Γp | σ⁻¹ * x ∈ E.fixingSubgroup} :=
    hU.preimage (continuous_const_mul σ⁻¹)
  have hσV : σ ∈ {x : Γp | σ⁻¹ * x ∈ E.fixingSubgroup} := by
    show σ⁻¹ * σ ∈ E.fixingSubgroup; rw [inv_mul_cancel]; exact Subgroup.one_mem _
  filter_upwards [hV.mem_nhds hσV] with x hx
  set u := σ⁻¹ * x with hu
  have hxu : x = σ * u := by rw [hu, mul_inv_cancel_left]
  have hua : u • ((a : PadicAlgCl p) : ℂ_[p]) = (a : ℂ_[p]) := by
    rw [PadicComplex.smul_coe, apply_eq_of_mem_fixingSubgroup p hx
      (IntermediateField.mem_adjoin_simple_self ℚ_[p] a)]
  rw [dist_eq_norm, hxu, mul_smul, ← smul_sub, PadicComplex.norm_smul_eq]
  have : u • b - b = u • (b - a) - (b - a) := by rw [smul_sub, hua]; abel
  rw [this]
  calc ‖u • (b - ↑a) - (b - ↑a)‖ ≤ max ‖u • (b - ↑a)‖ ‖-(b - ↑a)‖ := by
        rw [sub_eq_add_neg]; exact IsUltrametricDist.norm_add_le_max _ _
    _ = ‖b - ↑a‖ := by rw [norm_neg, PadicComplex.norm_smul_eq, max_self]
    _ < ε := by rwa [← dist_eq_norm]

variable (K) in

theorem continuous_orbitK (b : ℂ_[p]) : Continuous fun σ : GK => σ • b :=
  (continuous_orbit p b).comp continuous_subtype_val

end chi

variable (p K Pt) in

def OpenStab : Prop :=
  ∀ z : Pt, IsOpen {σ : GK | PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ • z = z}

theorem eventually_rT_apply_eq (hstab : OpenStab p K Pt) (x : T p Pt) (n : ℕ) (σ₀ : GK) :
    ∀ᶠ σ in nhds σ₀, ((rT p K Pt σ x : T p Pt) : ℕ → Pt) n = ((rT p K Pt σ₀ x : T p Pt) : ℕ → Pt) n := by
  set y : Pt := (x : ℕ → Pt) n with hy
  have hU : IsOpen {σ : GK | PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ • y = y} := hstab y
  have hV : IsOpen ((fun σ : GK => σ₀⁻¹ * σ) ⁻¹'
      {σ : GK | PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ • y = y}) :=
    hU.preimage (continuous_const_mul σ₀⁻¹)
  have hσ₀ : σ₀ ∈ (fun σ : GK => σ₀⁻¹ * σ) ⁻¹'
      {σ : GK | PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ • y = y} := by
    show PadicAlgCl.ringOfIntegers.galToAlgEquiv p K (σ₀⁻¹ * σ₀) • y = y
    rw [inv_mul_cancel, map_one]; exact one_smul _ y
  filter_upwards [hV.mem_nhds hσ₀] with σ hσ
  have hσ' : PadicAlgCl.ringOfIntegers.galToAlgEquiv p K (σ₀⁻¹ * σ) • y = y := hσ
  rw [rT_apply_coe, rT_apply_coe, ← hy]
  conv_lhs => rw [← mul_inv_cancel_left σ₀ σ, map_mul, mul_smul, hσ']

theorem continuous_coord (hstab : OpenStab p K Pt) (φ : T p Pt →ₗ[ℤ_[p]] ℤ_[p]) (x : T p Pt) :
    Continuous fun σ : GK => φ (rT p K Pt σ x) := by
  refine continuous_iff_continuousAt.2 fun σ₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
  filter_upwards [eventually_rT_apply_eq hstab x n σ₀] with σ hσ
  have hproj : TateModule.proj p Pt n (rT p K Pt σ x - rT p K Pt σ₀ x) = 0 := by
    rw [(TateModule.proj p Pt n).map_sub, sub_eq_zero]; exact hσ
  have hshift := TateModule.pow_smul_shiftOfProjEqZero n _ hproj
  set z := TateModule.shiftOfProjEqZero n _ hproj
  rw [dist_eq_norm, ← φ.map_sub, ← hshift, φ.map_smul, smul_eq_mul, norm_mul, norm_pow,
    PadicInt.norm_p, inv_pow, ← zpow_natCast, ← zpow_neg]
  calc (p : ℝ) ^ (-(n : ℤ)) * ‖φ z‖ ≤ (p : ℝ) ^ (-(n : ℤ)) * 1 := by
        gcongr; exact PadicInt.norm_le_one _
    _ < ε := by rw [mul_one]; exact hn

def e (x : T p Pt) : W p Pt := (1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x)

omit [DistribMulAction ΓO Pt] in
theorem e_add (x y : T p Pt) : e (x + y) = e x + e y := by
  unfold e
  rw [TensorProduct.tmul_add (1 : ℚ_[p]) x y]
  exact TensorProduct.tmul_add (1 : ℂ_[p]) _ _

omit [DistribMulAction ΓO Pt] in
theorem e_zero : e (0 : T p Pt) = 0 := by
  unfold e
  rw [TensorProduct.tmul_zero (T p Pt) (1 : ℚ_[p])]
  exact TensorProduct.tmul_zero (V p Pt) (1 : ℂ_[p])

omit [DistribMulAction ΓO Pt] in
theorem e_smul (a : ℤ_[p]) (x : T p Pt) : e (a • x) = ιC p a • e x := by
  unfold e
  have h1 : (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (a • x) = (a : ℚ_[p]) • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x) := by
    rw [← TensorProduct.smul_tmul a (1 : ℚ_[p]) x]
    refine Eq.trans ?_ (TensorProduct.smul_tmul' (a : ℚ_[p]) (1 : ℚ_[p]) x).symm
    congr 1
  rw [h1, ← TensorProduct.smul_tmul (a : ℚ_[p]) (1 : ℂ_[p]) ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x)]
  refine Eq.trans (TensorProduct.smul_tmul' (a : ℚ_[p]) (1 : ℂ_[p]) _).symm ?_
  rw [ιC_apply, algebraMap_smul]

omit [DistribMulAction ΓO Pt] in
theorem e_sum {ι : Type*} (s : Finset ι) (x : ι → T p Pt) : e (∑ i ∈ s, x i) = ∑ i ∈ s, e (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, e_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, e_add, ih]

theorem ρ_e (σ : GK) (x : T p Pt) : ρ p K Pt σ (e x) = e (rT p K Pt σ x) := by
  unfold e; rw [ρ_tmul, smul_one, rV_tmul]

def bW {ι : Type*} (bT : Module.Basis ι ℤ_[p] (T p Pt)) : Module.Basis ι ℂ_[p] (W p Pt) :=
  Algebra.TensorProduct.basis ℂ_[p] (Algebra.TensorProduct.basis ℚ_[p] bT)

omit [DistribMulAction ΓO Pt] in
theorem bW_apply {ι : Type*} (bT : Module.Basis ι ℤ_[p] (T p Pt)) (i : ι) : bW bT i = e (bT i) := by
  rw [bW, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply]; rfl

omit [DistribMulAction ΓO Pt] in

theorem e_eq_sum {ι : Type*} [Fintype ι] (bT : Module.Basis ι ℤ_[p] (T p Pt)) (x : T p Pt) :
    e x = ∑ j, ιC p (bT.repr x j) • e (bT j) := by
  conv_lhs => rw [← bT.sum_repr x]
  rw [e_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e_smul]

theorem ρ_eq_sum {ι : Type*} [Fintype ι] (bT : Module.Basis ι ℤ_[p] (T p Pt)) (σ : GK) (w : W p Pt) :
    ρ p K Pt σ w = ∑ i, (σ • (bW bT).repr w i) • e (rT p K Pt σ (bT i)) := by
  conv_lhs => rw [← (bW bT).sum_repr w]
  rw [map_sum (ρ p K Pt σ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ρ_smul, bW_apply, ρ_e]

theorem continuous_apply_ρ (hstab : OpenStab p K Pt)
    {ι : Type*} [Fintype ι] (bT : Module.Basis ι ℤ_[p] (T p Pt))
    (f : W p Pt →ₗ[ℂ_[p]] ℂ_[p]) (w : W p Pt) :
    Continuous fun σ : GK => f (ρ p K Pt σ w) := by
  classical
  have h2 : ∀ (σ : GK) (i : ι), f (e (rT p K Pt σ (bT i))) =
      ∑ j, ιC p (bT.repr (rT p K Pt σ (bT i)) j) • f (e (bT j)) := by
    intro σ i
    rw [e_eq_sum bT, map_sum f]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [f.map_smul]
  have hexp : ∀ σ : GK, f (ρ p K Pt σ w) =
      ∑ i, (σ • (bW bT).repr w i) • ∑ j, ιC p (bT.repr (rT p K Pt σ (bT i)) j) • f (e (bT j)) := by
    intro σ
    rw [ρ_eq_sum bT, map_sum f]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [f.map_smul, h2]
  have h3 : ∀ i j, Continuous fun σ : GK => ιC p (bT.repr (rT p K Pt σ (bT i)) j) := fun i j =>
    (continuous_algebraMap ℚ_[p] ℂ_[p]).comp <| (continuous_padicInt_coe p).comp <|
      continuous_coord hstab (bT.coord j) (bT i)
  have h4 : ∀ i, Continuous fun σ : GK =>
      ∑ j, ιC p (bT.repr (rT p K Pt σ (bT i)) j) • f (e (bT j)) :=
    fun i => continuous_finsetSum _ fun j _ => (h3 i j).smul continuous_const
  have h5 : Continuous fun σ : GK => ∑ i, (σ • (bW bT).repr w i) •
      ∑ j, ιC p (bT.repr (rT p K Pt σ (bT i)) j) • f (e (bT j)) :=
    continuous_finsetSum _ fun i _ => (continuous_orbitK p K _).smul (h4 i)
  exact h5.congr fun σ => (hexp σ).symm

def ρm (σ : GK) : W p Pt →+ W p Pt where
  toFun w := (((χCK p K σ)⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) • ρ p K Pt σ w
  map_zero' := by rw [map_zero, smul_zero]
  map_add' x y := by rw [map_add, smul_add]

theorem ρm_apply (σ : GK) (w : W p Pt) :
    ρm σ w = (((χCK p K σ)⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) • ρ p K Pt σ w := rfl

theorem χCK_inv_coe (σ : GK) :
    (((χCK p K σ)⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) ^ (-1 : ℤ) := by
  rw [zpow_neg, zpow_one, Units.val_inv_eq_inv_val]

theorem smul_χCK_inv (σ τ : GK) :
    σ • (((χCK p K τ)⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = (((χCK p K τ)⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) := by
  rw [χCK_inv_coe, smul_χCK_zpow]

theorem ρm_smul (σ : GK) (c : ℂ_[p]) (w : W p Pt) : ρm σ (c • w) = (σ • c) • ρm σ w := by
  rw [ρm_apply, ρm_apply, ρ_smul, smul_smul, smul_smul, mul_comm]

theorem ρm_mul (σ τ : GK) (w : W p Pt) : ρm (σ * τ) w = ρm σ (ρm τ w) := by
  rw [ρm_apply, ρm_apply, ρm_apply, ρ_mul_apply, ρ_smul, smul_χCK_inv, smul_smul, map_mul, mul_inv,
    Units.val_mul]

theorem ρm_one (w : W p Pt) : ρm (1 : GK) w = w := by
  rw [ρm_apply, map_one, inv_one, Units.val_one, one_smul, ρ_one_apply]

theorem ρm_inv_self_apply (σ : GK) (w : W p Pt) : ρm σ⁻¹ (ρm σ w) = w := by
  rw [← ρm_mul, inv_mul_cancel, ρm_one]

theorem ρm_self_inv_apply (σ : GK) (w : W p Pt) : ρm σ (ρm σ⁻¹ w) = w := by
  rw [← ρm_mul, mul_inv_cancel, ρm_one]

theorem continuous_apply_ρm (hstab : OpenStab p K Pt)
    {ι : Type*} [Fintype ι] (bT : Module.Basis ι ℤ_[p] (T p Pt))
    (f : W p Pt →ₗ[ℂ_[p]] ℂ_[p]) (w : W p Pt) :
    Continuous fun σ : GK => f (ρm σ w) := by
  have h : ∀ σ : GK, f (ρm σ w) = ((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) ^ (-1 : ℤ) * f (ρ p K Pt σ w) := by
    intro σ; rw [ρm_apply, f.map_smul, smul_eq_mul, χCK_inv_coe]
  simp only [h]
  exact (continuous_χCK_zpow p K (-1)).mul (continuous_apply_ρ hstab bT f w)

def ρ'fun (σ : GK) (f : W p Pt →ₗ[ℂ_[p]] ℂ_[p]) : W p Pt → ℂ_[p] :=
  fun w => (((χCK p K σ)⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * σ • f (ρm σ⁻¹ w)

theorem ρ'fun_add (σ : GK) (f : W p Pt →ₗ[ℂ_[p]] ℂ_[p]) (x y : W p Pt) :
    ρ'fun σ f (x + y) = ρ'fun σ f x + ρ'fun σ f y := by
  simp only [ρ'fun, map_add, smul_add, mul_add]

theorem ρ'fun_smul (σ : GK) (f : W p Pt →ₗ[ℂ_[p]] ℂ_[p]) (c : ℂ_[p]) (w : W p Pt) :
    ρ'fun σ f (c • w) = c * ρ'fun σ f w := by
  unfold ρ'fun
  rw [ρm_smul, LinearMap.map_smul, smul_eq_mul, smul_mul', smul_smul, mul_inv_cancel, one_smul,
    mul_left_comm]

def ρ'lin (σ : GK) (f : W p Pt →ₗ[ℂ_[p]] ℂ_[p]) : W p Pt →ₗ[ℂ_[p]] ℂ_[p] :=
  { toFun := ρ'fun σ f
    map_add' := ρ'fun_add σ f
    map_smul' := fun c w => by rw [RingHom.id_apply, smul_eq_mul]; exact ρ'fun_smul σ f c w }

theorem ρ'lin_apply (σ : GK) (f : W p Pt →ₗ[ℂ_[p]] ℂ_[p]) (w : W p Pt) :
    ρ'lin σ f w = (((χCK p K σ)⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * σ • f (ρm σ⁻¹ w) := rfl

def ρ' (σ : GK) : (W p Pt →ₗ[ℂ_[p]] ℂ_[p]) →+ (W p Pt →ₗ[ℂ_[p]] ℂ_[p]) where
  toFun := ρ'lin σ
  map_zero' := LinearMap.ext fun w => by
    rw [ρ'lin_apply, LinearMap.zero_apply, LinearMap.zero_apply, smul_zero, mul_zero]
  map_add' f g := LinearMap.ext fun w => by
    simp only [LinearMap.add_apply, ρ'lin_apply, smul_add, mul_add]

theorem ρ'_apply (σ : GK) (f : W p Pt →ₗ[ℂ_[p]] ℂ_[p]) (w : W p Pt) :
    ρ' σ f w = (((χCK p K σ)⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * σ • f (ρm σ⁻¹ w) := rfl

theorem ρ'_smul (σ : GK) (c : ℂ_[p]) (f : W p Pt →ₗ[ℂ_[p]] ℂ_[p]) :
    ρ' σ (c • f) = (σ • c) • ρ' σ f := by
  refine LinearMap.ext fun w => ?_
  rw [ρ'_apply, LinearMap.smul_apply, LinearMap.smul_apply, ρ'_apply, smul_eq_mul, smul_eq_mul,
    smul_mul', mul_left_comm]

theorem ρ'_eq_self_of_invariant (f : W p Pt →ₗ[ℂ_[p]] ℂ_[p])
    (hf : ∀ (σ : GK) (x : W p Pt), f (ρ p K Pt σ x) = σ • f x) (σ : GK) : ρ' σ f = f := by
  refine LinearMap.ext fun w => ?_
  rw [ρ'_apply, ρm_apply, f.map_smul, smul_eq_mul, map_inv, inv_inv, smul_mul', smul_χCK, ← hf,
    ρ_self_inv_apply, ← mul_assoc, Units.inv_mul, one_mul]

def Bev : W p Pt →ₗ[ℂ_[p]] (W p Pt →ₗ[ℂ_[p]] ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] := LinearMap.applyₗ

omit [DistribMulAction ΓO Pt] in
theorem Bev_apply (w : W p Pt) (f : W p Pt →ₗ[ℂ_[p]] ℂ_[p]) : Bev w f = f w := rfl

theorem Bev_ρm_ρ' (σ : GK) (w : W p Pt) (f : W p Pt →ₗ[ℂ_[p]] ℂ_[p]) :
    Bev (ρm σ w) (ρ' σ f) = ((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) ^ (-1 : ℤ) * σ • Bev w f := by
  rw [Bev_apply, Bev_apply, ρ'_apply, ρm_inv_self_apply, χCK_inv_coe]

omit [DistribMulAction ΓO Pt] in
theorem Bev_right_nondegenerate (f : W p Pt →ₗ[ℂ_[p]] ℂ_[p]) (hf : ∀ w : W p Pt, Bev w f = 0) : f = 0 :=
  LinearMap.ext hf

section Gm

variable (p)

open Submodule in

theorem natCard_torsionBy_units (n : ℕ) :
    Nat.card (torsionBy ℤ (Additive (PadicAlgCl p)ˣ) ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 1 := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have e : torsionBy ℤ (Additive (PadicAlgCl p)ˣ) ((p ^ n : ℕ) : ℤ) ≃ rootsOfUnity (p ^ n) (PadicAlgCl p) :=
    ⟨fun u => ⟨Additive.toMul u.1, by
        have hu := u.2
        rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at hu
        rw [mem_rootsOfUnity]
        exact congrArg Additive.toMul hu⟩,
     fun ζ => ⟨Additive.ofMul ζ.1, by
        have hζ := ζ.2
        rw [mem_rootsOfUnity] at hζ
        rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
        exact congrArg Additive.ofMul hζ⟩,
     fun u => rfl, fun ζ => rfl⟩
  rw [pow_one, Nat.card_congr e, HasEnoughRootsOfUnity.natCard_rootsOfUnity (PadicAlgCl p) (p ^ n)]

theorem nonempty_basis_tateUnits :
    Nonempty (Module.Basis (Fin 1) ℤ_[p] (TateModule p (Additive (PadicAlgCl p)ˣ))) :=
  TateModule.nonempty_basis_of_card_torsionBy p 1 (natCard_torsionBy_units p)

private def _root_.HTPDIVK.val (t : TateModule p (Additive (PadicAlgCl p)ˣ)) (v : ℕ) : PadicAlgCl p :=
  ((Additive.toMul ((t : ℕ → Additive (PadicAlgCl p)ˣ) v) : (PadicAlgCl p)ˣ) : PadicAlgCl p)

p2m_export "HTPDIVK" "val"
theorem val_pow (t : TateModule p (Additive (PadicAlgCl p)ˣ)) (v : ℕ) : val p t v ^ (p ^ v) = 1 := by
  have h := TateModule.torsion t v
  rw [natCast_zsmul] at h
  have h' : (Additive.toMul ((t : ℕ → Additive (PadicAlgCl p)ˣ) v)) ^ (p ^ v) = 1 := congrArg Additive.toMul h
  rw [val, ← Units.val_pow_eq_pow_val, h', Units.val_one]

theorem val_smul (a : ℤ_[p]) (t : TateModule p (Additive (PadicAlgCl p)ˣ)) (v : ℕ) :
    val p (a • t) v = val p t v ^ (a.appr v) := by
  rw [val, TateModule.smul_apply, toMul_zsmul, Units.val_zpow_eq_zpow_val, zpow_natCast]
  rfl

theorem eq_χZ_smul_of_val_eq (σ : Γp) (s t : TateModule p (Additive (PadicAlgCl p)ˣ))
    (hst : ∀ v, val p s v = σ (val p t v)) : s = χZ p σ • t := by
  refine Subtype.ext (funext fun v => ?_)
  have hv : val p s v = val p (χZ p σ • t) v := by
    rw [hst, val_smul]
    have hspec := cyclotomicCharacter.spec p (n := v)
      (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toRingEquiv (val p t v) (val_pow p t v)
    have hval : (((cyclotomicCharacter (PadicAlgCl p) p
        (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toRingEquiv).val.toZModPow v).val) = (χZ p σ).appr v := by
      show (PadicInt.toZModPow v (χZ p σ)).val = _
      rw [TateModule.toZModPow_eq_appr, ZMod.val_natCast, Nat.mod_eq_of_lt (PadicInt.appr_lt _ _)]
    rw [hval] at hspec
    exact hspec
  exact congrArg Additive.ofMul (Units.ext hv)

end Gm

section pairing

variable {Pt' : Type} [AddCommGroup Pt']
  [DistribMulAction (PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) Pt']

variable (BT : T p Pt →ₗ[ℤ_[p]] T p Pt' →ₗ[ℤ_[p]] TateModule p (Additive (PadicAlgCl p)ˣ))
  (bμ : Module.Basis (Fin 1) ℤ_[p] (TateModule p (Additive (PadicAlgCl p)ˣ)))

def BZ : T p Pt →ₗ[ℤ_[p]] T p Pt' →ₗ[ℤ_[p]] ℤ_[p] := BT.compr₂ (bμ.coord 0)

omit [DistribMulAction ΓO Pt] [DistribMulAction ΓO Pt'] in
theorem BZ_apply (x : T p Pt) (y : T p Pt') : BZ BT bμ x y = bμ.repr (BT x y) 0 := rfl

omit [DistribMulAction ΓO Pt] [DistribMulAction ΓO Pt'] in
theorem eq_coord_smul (t : TateModule p (Additive (PadicAlgCl p)ˣ)) : t = bμ.repr t 0 • bμ 0 := by
  conv_lhs => rw [← bμ.sum_repr t]
  rw [Fin.sum_univ_one]

theorem BZ_rT (hBT : ∀ (σ : GK) (x : T p Pt) (y : T p Pt') (v : ℕ),
      val p (BT (rT p K Pt σ x) (rT p K Pt' σ y)) v = (σ : Γp) (val p (BT x y) v))
    (σ : GK) (x : T p Pt) (y : T p Pt') :
    BZ BT bμ (rT p K Pt σ x) (rT p K Pt' σ y) = χZ p (σ : Γp) * BZ BT bμ x y := by
  rw [BZ_apply, BZ_apply, eq_χZ_smul_of_val_eq p (σ : Γp) _ _ (hBT σ x y), map_smul, Finsupp.smul_apply,
    smul_eq_mul]

omit [DistribMulAction ΓO Pt] [DistribMulAction ΓO Pt'] in

theorem BZ_nondegenerate (hinj : Function.Injective BT) (hinj' : Function.Injective BT.flip) :
    (BZ BT bμ).Nondegenerate := by
  have hzero : ∀ t : TateModule p (Additive (PadicAlgCl p)ˣ), bμ.repr t 0 = 0 → t = 0 := fun t ht => by
    rw [eq_coord_smul bμ t, ht]; exact zero_smul ℤ_[p] (bμ 0)
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · apply hinj
    rw [map_zero]
    exact LinearMap.ext fun y => hzero _ (hx y)
  · apply hinj'
    rw [map_zero]
    exact LinearMap.ext fun x => hzero _ (hy x)

end pairing

section basechange

variable {Pt' : Type} [AddCommGroup Pt']
  [DistribMulAction (PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) Pt']
variable {h : ℕ} (bT : Module.Basis (Fin h) ℤ_[p] (T p Pt)) (bT' : Module.Basis (Fin h) ℤ_[p] (T p Pt'))
  (B₀ : T p Pt →ₗ[ℤ_[p]] T p Pt' →ₗ[ℤ_[p]] ℤ_[p])

def gramC : Matrix (Fin h) (Fin h) ℂ_[p] := (LinearMap.toMatrix₂ bT bT' B₀).map (ιC p)

def BW : W p Pt →ₗ[ℂ_[p]] W p Pt' →ₗ[ℂ_[p]] ℂ_[p] :=
  Matrix.toLinearMap₂ (bW bT) (bW bT') (gramC bT bT' B₀)

omit [DistribMulAction ΓO Pt] [DistribMulAction ΓO Pt'] in
theorem BW_bW (i j : Fin h) : BW bT bT' B₀ (bW bT i) (bW bT' j) = ιC p (B₀ (bT i) (bT' j)) := by
  rw [BW, Matrix.toLinearMap₂_apply_basis, gramC, Matrix.map_apply, LinearMap.toMatrix₂_apply]

omit [DistribMulAction ΓO Pt] [DistribMulAction ΓO Pt'] in

theorem BW_e_e (t : T p Pt) (t' : T p Pt') : BW bT bT' B₀ (e t) (e t') = ιC p (B₀ t t') := by
  have h0 : B₀ t t' = ∑ i, bT.repr t i * ∑ j, bT'.repr t' j * B₀ (bT i) (bT' j) := by
    conv_lhs => rw [← bT.sum_repr t, ← bT'.sum_repr t']
    rw [LinearMap.map_sum₂ B₀]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul₂ B₀, map_sum (B₀ (bT i)), smul_eq_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [e_eq_sum bT, e_eq_sum bT', h0, map_sum (ιC p), LinearMap.map_sum₂ (BW bT bT' B₀)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul₂ (BW bT bT' B₀), map_sum (BW bT bT' B₀ (e (bT i))), smul_eq_mul, map_mul,
    map_sum (ιC p)]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, map_mul, ← bW_apply, ← bW_apply, BW_bW]

theorem BW_ρ (hB₀ : ∀ (σ : GK) (x : T p Pt) (y : T p Pt'),
      B₀ (rT p K Pt σ x) (rT p K Pt' σ y) = χZ p (σ : Γp) * B₀ x y)
    (σ : GK) (x : W p Pt) (y : W p Pt') :
    BW bT bT' B₀ (ρ p K Pt σ x) (ρ p K Pt' σ y) =
      ((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) * σ • BW bT bT' B₀ x y := by

  have hL : BW bT bT' B₀ (ρ p K Pt σ x) (ρ p K Pt' σ y) =
      ∑ i, (σ • (bW bT).repr x i) * ∑ j, (σ • (bW bT').repr y j) *
        (ιC p (χZ p (σ : Γp)) * ιC p (B₀ (bT i) (bT' j))) := by
    rw [ρ_eq_sum bT, ρ_eq_sum bT', LinearMap.map_sum₂ (BW bT bT' B₀)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul₂ (BW bT bT' B₀), map_sum (BW bT bT' B₀ (e (rT p K Pt σ (bT i)))),
      smul_eq_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, BW_e_e, hB₀, map_mul]
  have hR : BW bT bT' B₀ x y =
      ∑ i, (bW bT).repr x i * ∑ j, (bW bT').repr y j * ιC p (B₀ (bT i) (bT' j)) := by
    conv_lhs => rw [← (bW bT).sum_repr x, ← (bW bT').sum_repr y]
    rw [LinearMap.map_sum₂ (BW bT bT' B₀)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul₂ (BW bT bT' B₀), map_sum (BW bT bT' B₀ (bW bT i)), smul_eq_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, BW_bW]
  rw [hL, hR, Finset.smul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul', Finset.smul_sum]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul', subgroup_smul_def σ (ιC p (B₀ _ _)), smul_ιC, χCK_coe_eq_ιC]
  ring

omit [DistribMulAction ΓO Pt] [DistribMulAction ΓO Pt'] in

theorem BW_nondegenerate (hB₀ : B₀.Nondegenerate) : (BW bT bT' B₀).Nondegenerate := by
  classical
  have hdet : (LinearMap.toMatrix₂ bT bT' B₀).det ≠ 0 :=
    Matrix.nondegenerate_iff_det_ne_zero.1 ((LinearMap.nondegenerate_toMatrix₂_iff bT bT').2 hB₀)
  have hdetC : (gramC bT bT' B₀).det ≠ 0 := by
    rw [gramC, ← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero_iff _ (ιC_injective p)]
    exact hdet
  rw [BW]
  exact (Matrix.nondegenerate_toLinearMap₂_iff (bW bT) (bW bT')).2
    (Matrix.nondegenerate_iff_det_ne_zero.2 hdetC)

include bT bT' in

theorem exists_weightOne
    (hB₀ : ∀ (σ : GK) (x : T p Pt) (y : T p Pt'),
      B₀ (rT p K Pt σ x) (rT p K Pt' σ y) = χZ p (σ : Γp) * B₀ x y)
    (hnd : B₀.Nondegenerate) {n : ℕ} (φ : Fin n → W p Pt' →ₗ[ℂ_[p]] ℂ_[p])
    (hφi : LinearIndependent ℂ_[p] φ)
    (hφ : ∀ (σ : GK) (j : Fin n) (y : W p Pt'), φ j (ρ p K Pt' σ y) = σ • φ j y) :
    ∃ v : Fin n → W p Pt, LinearIndependent ℂ_[p] v ∧
      ∀ (σ : GK) (j : Fin n), ρ p K Pt σ (v j) = ((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) • v j := by
  haveI : FiniteDimensional ℂ_[p] (W p Pt) := Module.Finite.of_basis (bW bT)
  haveI : FiniteDimensional ℂ_[p] (W p Pt') := Module.Finite.of_basis (bW bT')
  have hndW : (BW bT bT' B₀).Nondegenerate := BW_nondegenerate bT bT' B₀ hnd

  have hinj : Function.Injective (BW bT bT' B₀) := by
    intro x x' hxx'
    rw [← sub_eq_zero]
    refine hndW.1 _ fun y => ?_
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero, hxx']
  have hdim : Module.finrank ℂ_[p] (W p Pt) = Module.finrank ℂ_[p] (Module.Dual ℂ_[p] (W p Pt')) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis (bW bT),
      Module.finrank_eq_card_basis (bW bT')]
  let Φ : W p Pt ≃ₗ[ℂ_[p]] Module.Dual ℂ_[p] (W p Pt') :=
    LinearMap.linearEquivOfInjective (BW bT bT' B₀) hinj hdim
  have hΦ : ∀ (g : Module.Dual ℂ_[p] (W p Pt')) (y : W p Pt'), BW bT bT' B₀ (Φ.symm g) y = g y := by
    intro g y
    have : Φ (Φ.symm g) = g := Φ.apply_symm_apply g
    rw [LinearMap.linearEquivOfInjective_apply] at this
    rw [this]
  refine ⟨fun j => Φ.symm (φ j), hφi.map' (Φ.symm : Module.Dual ℂ_[p] (W p Pt') →ₗ[ℂ_[p]] W p Pt)
    Φ.symm.ker, fun σ j => ?_⟩

  rw [← sub_eq_zero]
  refine hndW.1 _ fun y => ?_
  obtain ⟨y', rfl⟩ := ρ_surjective σ y
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero, BW_ρ bT bT' B₀ hB₀, hΦ, map_smul,
    LinearMap.smul_apply, hΦ, hφ, smul_eq_mul]

end basechange

variable (p K Pt) in

theorem exists_basis_sum [FiniteDimensional ℚ_[p] K] (hstab : OpenStab p K Pt)
    {h : ℕ} (bT : Module.Basis (Fin h) ℤ_[p] (T p Pt)) {n n' : ℕ}
    (v : Fin n → W p Pt)
    (hv : ∀ (σ : GK) (i : Fin n), ρ p K Pt σ (v i) = ((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) • v i)
    (hvi : LinearIndependent ℂ_[p] v)
    (f : Fin n' → W p Pt →ₗ[ℂ_[p]] ℂ_[p])
    (hf : ∀ (σ : GK) (j : Fin n') (x : W p Pt), f j (ρ p K Pt σ x) = σ • f j x)
    (hfi : LinearIndependent ℂ_[p] f) (hcard : n + n' = h) :
    ∃ b : Module.Basis (Fin n ⊕ Fin n') ℂ_[p] (W p Pt),
      (∀ (σ : GK) (i : Fin n), ρ p K Pt σ (b (Sum.inl i)) = ((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) • b (Sum.inl i)) ∧
      ∀ (σ : GK) (j : Fin n'), ρ p K Pt σ (b (Sum.inr j)) = b (Sum.inr j) := by
  haveI : FiniteDimensional ℂ_[p] (W p Pt) := Module.Finite.of_basis (bW bT)

  have hvm : ∀ (σ : GK) (i : Fin n), ρm σ (v i) = v i := by
    intro σ i
    rw [ρm_apply, hv, smul_smul, Units.inv_mul, one_smul]

  have hf' : ∀ (σ : GK) (j : Fin n'), ρ' σ (f j) = f j := fun σ j =>
    ρ'_eq_self_of_invariant (f j) (fun τ x => hf τ j x) σ
  have hcard' : Fintype.card (Fin n) + Fintype.card (Fin n') = Module.finrank ℂ_[p] (W p Pt) := by
    rw [Module.finrank_eq_card_basis (bW bT), Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
      hcard]
  have hm : (-1 : ℤ) ≠ 0 := neg_ne_zero.2 one_ne_zero

  obtain ⟨b, hb1, hb2, -⟩ :=
    MulSemiringAction.exists_basis_extending_invariants_eq_zpow_smul_and_iff_mem_span_fixedPoints_of_pairing_of_continuous_cocycle
      (C := ℂ_[p]) (G := GK) (χCK p K) (hH0K p K) (smul_χCK p K) (continuous_χCK_zpow p K) (-1) hm
      (hH1K p K) (W := W p Pt) ρm ρm_smul ρm_mul (fun f' w => continuous_apply_ρm hstab bT f' w)
      (W' := W p Pt →ₗ[ℂ_[p]] ℂ_[p]) ρ' ρ'_smul Bev Bev_ρm_ρ' Bev_right_nondegenerate
      v hvm hvi f hf' hfi hcard'
  refine ⟨b, fun σ i => ?_, fun σ j => ?_⟩
  · rw [hb1]; exact hv σ i
  ·
    have h2 := hb2 σ j
    rw [ρm_apply, ← χCK_inv_coe] at h2
    have h3 := congrArg (fun w => ((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) • w) h2
    simp only [smul_smul, Units.mul_inv, one_smul] at h3
    exact h3

variable (p K Pt) in

theorem exists_basis_fin [FiniteDimensional ℚ_[p] K] (hstab : OpenStab p K Pt)
    {h : ℕ} (bT : Module.Basis (Fin h) ℤ_[p] (T p Pt)) {n n' : ℕ}
    (v : Fin n → W p Pt)
    (hv : ∀ (σ : GK) (i : Fin n), ρ p K Pt σ (v i) = ((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) • v i)
    (hvi : LinearIndependent ℂ_[p] v)
    (f : Fin n' → W p Pt →ₗ[ℂ_[p]] ℂ_[p])
    (hf : ∀ (σ : GK) (j : Fin n') (x : W p Pt), f j (ρ p K Pt σ x) = σ • f j x)
    (hfi : LinearIndependent ℂ_[p] f) (hcard : n + n' = h) :
    ∃ b : Module.Basis (Fin h) ℂ_[p] (W p Pt),
      ∀ (σ : GK) (i : Fin h),
        ρ p K Pt σ (b i) = (((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) ^ (if (i : ℕ) < n then 1 else 0)) • b i := by
  obtain ⟨b, hbχ, hb0⟩ := exists_basis_sum p K Pt hstab bT v hv hvi f hf hfi hcard
  let ε : Fin n ⊕ Fin n' ≃ Fin h := finSumFinEquiv.trans (finCongr hcard)
  refine ⟨b.reindex ε, fun σ i => ?_⟩
  rw [Module.Basis.reindex_apply]
  obtain ⟨k, hk⟩ : ∃ k, ε.symm i = k := ⟨_, rfl⟩
  have hi : i = ε k := by rw [← hk, Equiv.apply_symm_apply]
  rw [hk]
  rcases k with j | j
  · have hlt : (i : ℕ) < n := by
      rw [hi]
      show ((finCongr hcard (finSumFinEquiv (Sum.inl j)) : Fin h) : ℕ) < n
      rw [finCongr_apply, Fin.val_cast, finSumFinEquiv_apply_left, Fin.val_castAdd]
      exact j.2
    rw [if_pos hlt, pow_one]
    exact hbχ σ j
  · have hge : ¬ (i : ℕ) < n := by
      rw [hi]
      show ¬ ((finCongr hcard (finSumFinEquiv (Sum.inr j)) : Fin h) : ℕ) < n
      rw [finCongr_apply, Fin.val_cast, finSumFinEquiv_apply_right, Fin.val_natAdd]
      exact Nat.not_lt.2 (Nat.le_add_right n j)
    rw [if_neg hge, pow_zero, one_smul]
    exact hb0 σ j

section stabilisers

variable (p K)

theorem continuous_fixingSubgroupEquiv [FiniteDimensional ℚ_[p] K] :
    Continuous (IntermediateField.fixingSubgroupEquiv K :
      GK → (PadicAlgCl p ≃ₐ[K] PadicAlgCl p)) := by
  refine continuous_of_continuousAt_one (IntermediateField.fixingSubgroupEquiv K).toMonoidHom ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K (PadicAlgCl p) s).1 hs
  haveI := hE

  let E' : IntermediateField ℚ_[p] (PadicAlgCl p) := IntermediateField.restrictScalars ℚ_[p] E
  haveI : FiniteDimensional ℚ_[p] E := Module.Finite.trans K E
  haveI : FiniteDimensional ℚ_[p] E' := by
    let ι' : E' →ₗ[ℚ_[p]] E :=
      { toFun := fun x => ⟨(x : PadicAlgCl p), x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact Module.Finite.of_injective ι' fun x y hxy => Subtype.ext (congrArg Subtype.val hxy)
  have hO : IsOpen ((E'.fixingSubgroup : Set Γp)) := IntermediateField.fixingSubgroup_isOpen E'
  refine Filter.mem_map.2 (Filter.mem_of_superset ((hO.preimage continuous_subtype_val).mem_nhds ?_)
    fun σ hσ => ?_)
  · show ((1 : GK) : Γp) ∈ E'.fixingSubgroup
    exact Subgroup.one_mem _
  · apply hEs
    show IntermediateField.fixingSubgroupEquiv K σ ∈ E.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx

theorem openStab_points [FiniteDimensional ℚ_[p] K] {h : ℕ}
    (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) : OpenStab p K (G.Points (PadicAlgCl p)) := by
  intro z
  letI : Algebra (PadicAlgCl.ringOfIntegers p K) K :=
    (RingHom.codRestrict (algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) K.toSubring
      (fun x => PadicAlgCl.ringOfIntegers.coe_mem x) :
        PadicAlgCl.ringOfIntegers p K →+* K).toAlgebra
  haveI : IsScalarTower (PadicAlgCl.ringOfIntegers p K) K (PadicAlgCl p) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic K (PadicAlgCl p) := Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K
  have hopen := PDivisibleGroup.isOpen_setOf_restrictScalars_smul_points_eq G K (PadicAlgCl p) z
  have hset : {σ : GK | PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ • z = z} =
      (IntermediateField.fixingSubgroupEquiv K) ⁻¹'
        {σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p |
          σ.restrictScalars (PadicAlgCl.ringOfIntegers p K) • z = z} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [show (IntermediateField.fixingSubgroupEquiv K σ).restrictScalars (PadicAlgCl.ringOfIntegers p K) =
        PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ from AlgEquiv.ext fun _ => rfl]
  rw [hset]
  exact hopen.preimage (continuous_fixingSubgroupEquiv p K)

theorem exists_eq_galToAlgEquiv (σ : Γp) (τ : ΓO) (hτσ : ∀ x : PadicAlgCl p, τ x = σ x) :
    ∃ hσ : σ ∈ K.fixingSubgroup, τ = PadicAlgCl.ringOfIntegers.galToAlgEquiv p K ⟨σ, hσ⟩ := by
  have hσ : σ ∈ K.fixingSubgroup := by
    have hmem := PadicAlgCl.ringOfIntegers.restrictScalarsRat_mem_fixingSubgroup p K τ
    have heq : PadicAlgCl.ringOfIntegers.restrictScalarsRat p K τ = σ := AlgEquiv.ext hτσ
    rwa [heq] at hmem
  exact ⟨hσ, AlgEquiv.ext fun x => hτσ x⟩

end stabilisers

section assembly

variable (p K) [FiniteDimensional ℚ_[p] K]

theorem exists_dual {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n : ℕ}
    (hn : G.HasDimension n) :
    ∃ (G' : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) (_ : G.CartierDuality G') (n' : ℕ),
      G'.HasDimension n' ∧ n + n' = h := by
  obtain ⟨-, hdvr, hcomplete⟩ :=
    PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p K
  haveI := hdvr
  haveI := hcomplete
  have hp : ((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ∈
      IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K) :=
    (IsLocalRing.mem_maximalIdeal _).2 (PadicAlgCl.ringOfIntegers.not_isUnit_natCast p K)
  obtain ⟨G', ⟨D⟩⟩ := PDivisibleGroup.exists_isCartierDual G
  obtain ⟨n', hn'⟩ := PDivisibleGroup.exists_hasDimension hp G'
  exact ⟨G', D, n', hn', PDivisibleGroup.add_eq_height_of_hasDimension_of_cartierDuality hp D hn hn'⟩

theorem exists_weightOne_points {h : ℕ} {G G' : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h}
    (D : G.CartierDuality G') {n : ℕ} (hn : G.HasDimension n)
    (bT : Module.Basis (Fin h) ℤ_[p] (T p (G.Points (PadicAlgCl p))))
    (bT' : Module.Basis (Fin h) ℤ_[p] (T p (G'.Points (PadicAlgCl p)))) :
    ∃ v : Fin n → W p (G.Points (PadicAlgCl p)), LinearIndependent ℂ_[p] v ∧
      ∀ (σ : GK) (j : Fin n),
        ρ p K (G.Points (PadicAlgCl p)) σ (v j) = ((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) • v j := by

  obtain ⟨bμ⟩ := nonempty_basis_tateUnits p

  obtain ⟨BT, hBT, hBTσ⟩ :=
    PDivisibleGroup.CartierDuality.exists_tateModule_pairing_eq_pair D (PadicAlgCl p)
  obtain ⟨hbij', hbij⟩ :=
    PDivisibleGroup.CartierDuality.bijective_tateModule_pairing_of_isAlgClosed D (PadicAlgCl p) BT hBT

  have hB₀ : ∀ (σ : GK) (x : T p (G.Points (PadicAlgCl p))) (y : T p (G'.Points (PadicAlgCl p))),
      BZ BT bμ (rT p K _ σ x) (rT p K _ σ y) = χZ p (σ : Γp) * BZ BT bμ x y :=
    BZ_rT BT bμ fun σ x y v => hBTσ (PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ) x y v
  have hnd : (BZ BT bμ).Nondegenerate := BZ_nondegenerate BT bμ hbij.1 hbij'.1

  have hP11 :=
    PDivisibleGroup.CartierDuality.exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers
      p K D hn
  obtain ⟨φ, hφi, hφ⟩ := hP11
  have hφK : ∀ (σ : GK) (j : Fin n) (y : W p (G'.Points (PadicAlgCl p))),
      φ j (ρ p K _ σ y) = σ • φ j y := fun σ j y =>
    hφ (σ : Γp) (PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ) (fun _ => rfl) j y
  exact exists_weightOne bT bT' (BZ BT bμ) hB₀ hnd φ hφi hφK

theorem exists_invariant_points {h : ℕ} {G G' : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h}
    (D' : G'.CartierDuality G) {n' : ℕ} (hn' : G'.HasDimension n') :
    ∃ ψ : Fin n' → W p (G.Points (PadicAlgCl p)) →ₗ[ℂ_[p]] ℂ_[p], LinearIndependent ℂ_[p] ψ ∧
      ∀ (σ : GK) (j : Fin n') (y : W p (G.Points (PadicAlgCl p))),
        ψ j (ρ p K _ σ y) = σ • ψ j y := by
  have hP11 :=
    PDivisibleGroup.CartierDuality.exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers
      p K D' hn'
  obtain ⟨ψ, hψi, hψ⟩ := hP11
  exact ⟨ψ, hψi, fun σ j y =>
    hψ (σ : Γp) (PadicAlgCl.ringOfIntegers.galToAlgEquiv p K σ) (fun _ => rfl) j y⟩

theorem exists_hodgeTateBasis {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n : ℕ}
    (hn : G.HasDimension n) :
    n ≤ h ∧ ∃ b : Module.Basis (Fin h) ℂ_[p] (W p (G.Points (PadicAlgCl p))),
      ∀ (σ : GK) (i : Fin h),
        ρ p K (G.Points (PadicAlgCl p)) σ (b i) =
          (((χCK p K σ : ℂ_[p]ˣ) : ℂ_[p]) ^ (if (i : ℕ) < n then 1 else 0)) • b i := by
  obtain ⟨G', D, n', hn', hsum⟩ := exists_dual p K G hn
  obtain ⟨D'⟩ := PDivisibleGroup.CartierDuality.isCartierDual_symm D
  refine ⟨hsum ▸ Nat.le_add_right n n', ?_⟩

  obtain ⟨bT⟩ := PDivisibleGroup.nonempty_basis_tateModule_points G (PadicAlgCl p)
  obtain ⟨bT'⟩ := PDivisibleGroup.nonempty_basis_tateModule_points G' (PadicAlgCl p)

  obtain ⟨v, hvi, hv⟩ := exists_weightOne_points p K D hn bT bT'
  obtain ⟨ψ, hψi, hψ⟩ := exists_invariant_points p K D' hn'

  exact exists_basis_fin p K (G.Points (PadicAlgCl p)) (openStab_points p K G) bT v hv hvi ψ hψ hψi hsum

end assembly

end HTPDIVK
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers.HTPDIVK"

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n : ℕ}
    (hn : G.HasDimension n) :
    n ≤ h ∧
    ∃ b : Module.Basis (Fin h) ℂ_[p]
        (ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G.Points (PadicAlgCl p)))),
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ x : PadicAlgCl p, τ x = σ x) → ∀ i : Fin h,
        TensorProduct.map (PadicComplex.galAlgHom p σ).toLinearMap
            ((G.tateModuleRep (PadicAlgCl p) τ).baseChange ℚ_[p]) (b i) =
          (algebraMap ℚ_[p] ℂ_[p]
              (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^
            (if (i : ℕ) < n then 1 else 0) • b i := by
  obtain ⟨hle, b, hb⟩ := HTPDIVK.exists_hodgeTateBasis p K G hn
  refine ⟨hle, b, fun σ τ hτσ i => ?_⟩
  have hστ := HTPDIVK.exists_eq_galToAlgEquiv p K σ τ hτσ
  obtain ⟨hσ, rfl⟩ := hστ
  have := hb ⟨σ, hσ⟩ i
  rw [HTPDIVK.χCK_apply, HTPDIVK.χC_coe] at this
  exact this

end
end S_PDivisibleGroup_exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers (solution)

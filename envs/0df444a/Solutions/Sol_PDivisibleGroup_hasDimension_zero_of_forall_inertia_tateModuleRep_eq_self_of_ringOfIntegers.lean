-- Prove2me | solution 1 for PDivisibleGroup.hasDimension_zero_of_forall_inertia_tateModuleRep_eq_self_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ecd846c2-48a8-539d-aab8-9a6346ca997f

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_PadicComplex_GaloisAction
import Theorems.Thm_PDivisibleGroup_exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers
import Theorems.Thm_PDivisibleGroup_nonempty_basis_tateModule_points
import Theorems.Thm_PDivisibleGroup_isOpen_setOf_restrictScalars_smul_points_eq
import Theorems.Thm_PDivisibleGroup_natCard_torsionBy_points_eq_pow
import Theorems.Thm_PDivisibleGroup_exists_hasDimension
import Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
import Theorems.Thm_PadicComplex_eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul
import Theorems.Thm_PadicComplex_exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_hasDimension_zero_of_forall_inertia_tateModuleRep_eq_self_of_ringOfIntegers
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions PDivisibleGroup.CPoints.instDistribMulAction PrimaryTorsion.instSMul PrimaryTorsion.instModule ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "PDivisibleGroup.CartierDuality.mk.injEq PDivisibleGroup.CartierDuality.toDualEquiv_apply PDivisibleGroup.CartierDuality.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul PDivisibleGroup.cotangentBaseChange_tmul PDivisibleGroup.baseChange_transition_tmul PDivisibleGroup.cotangentToBaseChange_toCotangent PDivisibleGroup.baseChange_level HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff PDivisibleGroup.cotangentClass_algebraMap PDivisibleGroup.cotangentClass_one"
p2m_attr_erase "simp" "PDivisibleGroup.cpointsProj_cpointsMap PDivisibleGroup.pointsMap_reduceModPow_cpointsProj_succ PDivisibleGroup.cpointsProj_toCPoints PDivisibleGroup.mapModPow_mk PDivisibleGroup.reduceModPow_mk PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj"

set_option autoImplicit false

open scoped TensorProduct

namespace C4Kit

theorem toMatrix_mul_map_eq_mul_diagonal {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι] (φ : F →+* F) (g : V →ₛₗ[φ] V) (v b : Module.Basis ι F V)
    (M : Matrix ι ι F) (hM : ∀ k, g (v k) = ∑ j, M j k • v j) (D : ι → F) (hD : ∀ i, g (b i) = D i • b i) :
    M * (v.toMatrix b).map φ = v.toMatrix b * Matrix.diagonal D := by
  ext j i

  have hb : b i = ∑ k, v.toMatrix b k i • v k := by
    simp only [Module.Basis.toMatrix_apply]
    exact (v.sum_repr (b i)).symm
  have h1 : g (b i) = ∑ k, φ (v.toMatrix b k i) • ∑ j, M j k • v j := by
    conv_lhs => rw [hb]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smulₛₗ, hM]
  have h2 : g (b i) = ∑ j, (D i * v.toMatrix b j i) • v j := by
    rw [hD, hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]

  have c1 : v.repr (g (b i)) j = ∑ k, M j k * φ (v.toMatrix b k i) := by
    rw [h1, map_sum]
    simp only [map_smul, map_sum, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finsupp.coe_smul,
      Finset.sum_apply, Pi.smul_apply, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro j' _ hj'; simp [hj']
    · intro h; exact absurd (Finset.mem_univ j) h
  have c2 : v.repr (g (b i)) j = D i * v.toMatrix b j i := by
    rw [h2, map_sum]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, Finsupp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'; simp [hj']
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.map_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rw [← c1, c2, mul_comm]

theorem det_mul_map_det_eq {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι] (φ : F →+* F) (g : V →ₛₗ[φ] V) (v b : Module.Basis ι F V)
    (M : Matrix ι ι F) (hM : ∀ k, g (v k) = ∑ j, M j k • v j) (D : ι → F) (hD : ∀ i, g (b i) = D i • b i) :
    M.det * φ (v.toMatrix b).det = (v.toMatrix b).det * ∏ i, D i := by
  have := congrArg Matrix.det (toMatrix_mul_map_eq_mul_diagonal φ g v b M hM D hD)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at this
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  exact this

theorem det_toMatrix_ne_zero {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι] (v b : Module.Basis ι F V) : (v.toMatrix b).det ≠ 0 := by
  have h := congrArg Matrix.det (v.toMatrix_mul_toMatrix_flip b)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul_eq_one h

end C4Kit

namespace C4Kit

variable (p : ℕ) [Fact p.Prime]

section Semilinear
variable {U : Type*} [AddCommGroup U] [Module ℚ_[p] U]

theorem map_galAlgHom_smul (σ : PadicComplex.Gal p) (f : U →ₗ[ℚ_[p]] U) (c : ℂ_[p]) (w : ℂ_[p] ⊗[ℚ_[p]] U) :
    TensorProduct.map (PadicComplex.galAlgHom p σ).toLinearMap f (c • w) =
      (σ • c) • TensorProduct.map (PadicComplex.galAlgHom p σ).toLinearMap f w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a m =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.smul_tmul']
    congr 1
    change σ • (c • a) = (σ • c) • (σ • a)
    rw [smul_eq_mul, smul_eq_mul, smul_mul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

noncomputable def galSemilinear (σ : PadicComplex.Gal p) (f : U →ₗ[ℚ_[p]] U) :
    (ℂ_[p] ⊗[ℚ_[p]] U) →ₛₗ[MulSemiringAction.toRingHom (PadicComplex.Gal p) ℂ_[p] σ] (ℂ_[p] ⊗[ℚ_[p]] U) where
  toFun := TensorProduct.map (PadicComplex.galAlgHom p σ).toLinearMap f
  map_add' := map_add _
  map_smul' := fun c w => by
    rw [MulSemiringAction.toRingHom_apply]
    exact map_galAlgHom_smul p σ f c w

@[scoped simp] theorem galSemilinear_apply (σ : PadicComplex.Gal p) (f : U →ₗ[ℚ_[p]] U) (w : ℂ_[p] ⊗[ℚ_[p]] U) :
    galSemilinear p σ f w = TensorProduct.map (PadicComplex.galAlgHom p σ).toLinearMap f w := rfl

end Semilinear

section RationalBasis
variable {T : Type*} [AddCommGroup T] [Module ℤ_[p] T] {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def basisC (t : Module.Basis ι ℤ_[p] T) :
    Module.Basis ι ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] T)) :=
  Algebra.TensorProduct.basis ℂ_[p] (Algebra.TensorProduct.basis ℚ_[p] t)

omit [Fintype ι] [DecidableEq ι] in
theorem basisC_apply (t : Module.Basis ι ℤ_[p] T) (k : ι) :
    basisC p t k = (1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] t k) := by
  simp [basisC, Algebra.TensorProduct.basis_apply]

theorem map_galAlgHom_basisC (t : Module.Basis ι ℤ_[p] T) (θ : T →ₗ[ℤ_[p]] T) (σ : PadicComplex.Gal p) (k : ι) :
    TensorProduct.map (PadicComplex.galAlgHom p σ).toLinearMap (θ.baseChange ℚ_[p]) (basisC p t k) =
      ∑ j, (algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (LinearMap.toMatrix t t θ j k))) • basisC p t j := by
  rw [basisC_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, LinearMap.baseChange_tmul]
  have hθ : θ (t k) = ∑ j, LinearMap.toMatrix t t θ j k • t j := by
    conv_lhs => rw [← t.sum_repr (θ (t k))]
    simp only [LinearMap.toMatrix_apply]
  rw [hθ, TensorProduct.tmul_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set m := LinearMap.toMatrix t t θ j k
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
    show (algebraMap ℤ_[p] ℚ_[p] m) ⊗ₜ[ℤ_[p]] t j = (algebraMap ℤ_[p] ℚ_[p] m) • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] t j) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    TensorProduct.tmul_smul, basisC_apply, algebraMap_smul ℂ_[p] ((algebraMap ℤ_[p] ℚ_[p]) m)]

end RationalBasis

end C4Kit
p2m_reactivate "P2MW.S_PDivisibleGroup_hasDimension_zero_of_forall_inertia_tateModuleRep_eq_self_of_ringOfIntegers.C4Kit"

namespace C4Kit

open PadicAlgCl

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

@[reducible] noncomputable def algebraRingOfIntegersField : Algebra (ringOfIntegers p K) K :=
  (({ toFun := fun x => ⟨(x : PadicAlgCl p), ringOfIntegers.coe_mem x⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl } :
      ringOfIntegers p K →+* K)).toAlgebra

theorem exists_finiteDimensional_forall_smul_torsionBy_eq [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (ringOfIntegers p K) p h) (n : ℕ) :
    ∃ K' : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K' ∧
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[ringOfIntegers p K] PadicAlgCl p),
        (∀ t : PadicAlgCl p, τ t = σ t) → σ ∈ K'.fixingSubgroup →
        ∀ z ∈ Submodule.torsionBy ℤ (G.Points (PadicAlgCl p)) ((p ^ n : ℕ) : ℤ), τ • z = z := by
  classical
  letI : Algebra (ringOfIntegers p K) K := algebraRingOfIntegersField p K
  haveI : IsScalarTower (ringOfIntegers p K) K (PadicAlgCl p) :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : Algebra.IsAlgebraic K (PadicAlgCl p) := Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K

  set S : Set (G.Points (PadicAlgCl p)) := ↑(Submodule.torsionBy ℤ (G.Points (PadicAlgCl p)) ((p ^ n : ℕ) : ℤ))
  have hSfin : S.Finite := by
    have hc := PDivisibleGroup.natCard_torsionBy_points_eq_pow G (PadicAlgCl p) n
    have : Finite (Submodule.torsionBy ℤ (G.Points (PadicAlgCl p)) ((p ^ n : ℕ) : ℤ)) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    exact Set.toFinite S
  set U : Set (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :=
    ⋂ z ∈ S, {σ | σ.restrictScalars (ringOfIntegers p K) • z = z}
  have hU : IsOpen U := hSfin.isOpen_biInter fun z _ =>
    PDivisibleGroup.isOpen_setOf_restrictScalars_smul_points_eq G K (PadicAlgCl p) z
  have h1U : (1 : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) ∈ U := by
    refine Set.mem_iInter₂.mpr fun z _ => ?_
    change (AlgEquiv.restrictScalars (ringOfIntegers p K) (1 : PadicAlgCl p ≃ₐ[K] PadicAlgCl p)) • z = z
    have : AlgEquiv.restrictScalars (ringOfIntegers p K) (1 : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) = 1 :=
      AlgEquiv.ext fun _ => rfl
    rw [this, one_smul]
  obtain ⟨E, hEfin, hEU⟩ := (krullTopology_mem_nhds_one_iff K (PadicAlgCl p) U).mp (hU.mem_nhds h1U)
  refine ⟨E.restrictScalars ℚ_[p], ?_, ?_⟩
  · haveI : FiniteDimensional K E := hEfin
    have : FiniteDimensional ℚ_[p] E := FiniteDimensional.trans ℚ_[p] K E
    exact this
  · intro σ τ hτσ hσ z hz
    have hσE : ∀ x ∈ E, σ x = x := fun x hx =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x ((IntermediateField.mem_restrictScalars ℚ_[p]).2 hx)
    have hσK : ∀ k : K, σ (algebraMap K (PadicAlgCl p) k) = algebraMap K (PadicAlgCl p) k := fun k =>
      hσE _ (E.algebraMap_mem k)
    let σK : PadicAlgCl p ≃ₐ[K] PadicAlgCl p := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hσK
    have hσKE : σK ∈ E.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).2 hσE
    have hz' : σK.restrictScalars (ringOfIntegers p K) • z = z := (Set.mem_iInter₂.mp (hEU hσKE)) z hz
    have hτ : σK.restrictScalars (ringOfIntegers p K) = τ := AlgEquiv.ext fun x => (hτσ x).symm
    rwa [hτ] at hz'

theorem exists_finiteDimensional_forall_tateModuleRep_sub_eq_pow_smul [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (ringOfIntegers p K) p h) (n : ℕ) :
    ∃ K' : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K' ∧
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[ringOfIntegers p K] PadicAlgCl p),
        (∀ t : PadicAlgCl p, τ t = σ t) → σ ∈ K'.fixingSubgroup →
        ∀ x : TateModule p (G.Points (PadicAlgCl p)), ∃ s : TateModule p (G.Points (PadicAlgCl p)),
          G.tateModuleRep (PadicAlgCl p) τ x - x = ((p : ℤ_[p]) ^ n) • s := by
  obtain ⟨K', hK', H⟩ := exists_finiteDimensional_forall_smul_torsionBy_eq p K G n
  refine ⟨K', hK', fun σ τ hτσ hσ x => ?_⟩
  have hproj : TateModule.proj p (G.Points (PadicAlgCl p)) n (G.tateModuleRep (PadicAlgCl p) τ x - x) = 0 := by
    rw [map_sub, sub_eq_zero, TateModule.proj_apply, TateModule.proj_apply, PDivisibleGroup.tateModuleRep_apply]
    exact H σ τ hτσ hσ _ (TateModule.proj_mem_torsionBy n x)
  exact ⟨TateModule.shiftOfProjEqZero n _ hproj, (TateModule.pow_smul_shiftOfProjEqZero n _ hproj).symm⟩

end C4Kit
p2m_reactivate "P2MW.S_PDivisibleGroup_hasDimension_zero_of_forall_inertia_tateModuleRep_eq_self_of_ringOfIntegers.C4Kit"

set_option maxHeartbeats 6400000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (Q : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (hQ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ t : PadicAlgCl p, τ t = σ t) →
        σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ z : TateModule p (Q.Points (PadicAlgCl p)), Q.tateModuleRep (PadicAlgCl p) τ z = z) :
    Q.HasDimension 0 := by
  classical

  obtain ⟨_, hdvr, hcomp⟩ := PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p K
  haveI := hdvr
  haveI := hcomp
  have hpm : ((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ∈ IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K) :=
    (IsLocalRing.mem_maximalIdeal _).mpr (PadicAlgCl.ringOfIntegers.not_isUnit_natCast p K)
  obtain ⟨n, hn⟩ := PDivisibleGroup.exists_hasDimension hpm Q
  suffices hn0 : n = 0 by subst hn0; exact hn

  obtain ⟨hnh, b, hb⟩ :=
    PDivisibleGroup.exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers p K Q hn
  obtain ⟨t⟩ := PDivisibleGroup.nonempty_basis_tateModule_points Q (PadicAlgCl p)
  set ρ := Q.tateModuleRep (PadicAlgCl p) with hρ
  let c : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])
  let χ : PadicComplex.Gal p → ℂ_[p] := fun σ =>
    algebraMap ℚ_[p] ℂ_[p] (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])
  let v := C4Kit.basisC p t
  have hP : (v.toMatrix b).det ≠ 0 := C4Kit.det_toMatrix_ne_zero v b
  have hsum : (∑ i : Fin h, (if (i : ℕ) < n then 1 else 0)) = n := by
    rw [Finset.sum_boole]
    have : (Finset.univ.filter fun i : Fin h => (i : ℕ) < n) = Finset.univ.map (Fin.castLEEmb hnh) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
      constructor
      · intro hi; exact ⟨⟨i, hi⟩, Fin.ext rfl⟩
      · rintro ⟨j, rfl⟩; exact j.2
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    rfl
  have hdet : ∀ (σ : PadicComplex.Gal p) (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
      (∀ x, τ x = σ x) → c (LinearMap.det (ρ τ)) * (σ • (v.toMatrix b).det) = (v.toMatrix b).det * (χ σ) ^ n := by
    intro σ τ hτσ
    have key := C4Kit.det_mul_map_det_eq (MulSemiringAction.toRingHom (PadicComplex.Gal p) ℂ_[p] σ)
      (C4Kit.galSemilinear p σ ((ρ τ).baseChange ℚ_[p])) v b ((LinearMap.toMatrix t t (ρ τ)).map c)
      (fun k => C4Kit.map_galAlgHom_basisC p t (ρ τ) σ k) (fun i => χ σ ^ (if (i : ℕ) < n then 1 else 0))
      (fun i => hb σ τ hτσ i)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix, MulSemiringAction.toRingHom_apply,
      Finset.prod_pow_eq_pow_sum, hsum] at key
    exact key

  haveI : Module.Free ℤ_[p] (TateModule p (Q.Points (PadicAlgCl p))) := Module.Free.of_basis t
  haveI : Module.Finite ℤ_[p] (TateModule p (Q.Points (PadicAlgCl p))) := Module.Finite.of_basis t
  have hρunr : ∀ (σ : PadicComplex.Gal p) (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
      (∀ x, τ x = σ x) → σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ρ τ = 1 :=
    fun σ τ hτσ hσ => LinearMap.ext fun z => hQ σ τ hτσ hσ z
  obtain ⟨u, hu, hσu⟩ :=
    PadicComplex.exists_ne_zero_forall_smul_eq_det_mul_of_forall_inertia_eq_one_of_ringOfIntegers p K ρ hρunr
      (C4Kit.exists_finiteDimensional_forall_tateModuleRep_sub_eq_pow_smul p K Q)

  have hcne : ∀ τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p, c (LinearMap.det (ρ τ)) ≠ 0 :=
    fun τ => ((Group.isUnit τ).map (((LinearMap.det : Module.End ℤ_[p] (TateModule p (Q.Points (PadicAlgCl p))) →* ℤ_[p]).comp ρ))
      |>.map c).ne_zero
  by_contra hn0
  have hweight : ∀ σ : PadicComplex.Gal p, σ ∈ K.fixingSubgroup →
      σ • ((v.toMatrix b).det * u) = (χ σ) ^ (n : ℤ) * ((v.toMatrix b).det * u) := by
    intro σ hσ
    have e1 := hdet σ (PadicAlgCl.ringOfIntegers.algEquivOfMemFixingSubgroup p K σ hσ) (fun _ => rfl)
    have e2 := hσu σ (PadicAlgCl.ringOfIntegers.algEquivOfMemFixingSubgroup p K σ hσ) (fun _ => rfl)
    have hd := hcne (PadicAlgCl.ringOfIntegers.algEquivOfMemFixingSubgroup p K σ hσ)
    set d := c (LinearMap.det (ρ (PadicAlgCl.ringOfIntegers.algEquivOfMemFixingSubgroup p K σ hσ))) with hdd
    have e2' : σ • u = d * u := e2
    have eP : σ • (v.toMatrix b).det = (v.toMatrix b).det * χ σ ^ n / d := by
      rw [eq_div_iff hd, mul_comm]; exact e1
    rw [zpow_natCast, smul_mul', eP, e2']
    field_simp
  have h0 := PadicComplex.eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul p K (n : ℤ)
    (by exact_mod_cast hn0) _ hweight
  exact mul_ne_zero hP hu h0

end S_PDivisibleGroup_hasDimension_zero_of_forall_inertia_tateModuleRep_eq_self_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_hasDimension_zero_of_forall_inertia_tateModuleRep_eq_self_of_ringOfIntegers (solution)

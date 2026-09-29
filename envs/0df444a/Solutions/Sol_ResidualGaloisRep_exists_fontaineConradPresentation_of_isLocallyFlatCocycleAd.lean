-- Prove2me | solution 1 for ResidualGaloisRep.exists_fontaineConradPresentation_of_isLocallyFlatCocycleAd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/35b39e14-f907-552c-8d41-349248a22aec

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_HondaSelfExt
import Theorems.Thm_ResidualGaloisRep_exists_unipotent_model_of_isLocallyFlatCocycleAd_of_isLocalRing_cartierDual
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
import Theorems.Thm_HopfAlgebra_exists_coeffAction_forall_apply_comp_eq_smul_of_ne_two
import Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two
import Theorems.Thm_Deformation_DieudonneModule_exists_hondaSystem_addEquiv_smul_eq_map_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_DieudonneModule_map_baseChange_surjective_injective_fontaineHodge_of_range_eq_hopfKer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_fontaineConradPresentation_of_isLocallyFlatCocycleAd
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul ExtCitation.LocalLevel.coe_smul_OO CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply"
p2m_attr_erase "simp" "HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation
open scoped PadicInt TensorProduct

namespace P2PresB

section LinAlg

variable {k : Type} [Field k]

theorem exists_linearMap_of_addEquiv {D₁ D₂ : Type} [AddCommGroup D₁] [Module k D₁] [AddCommGroup D₂]
    [Module k D₂] {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] (ι₁ : D₁ ≃+ M₁) (ι₂ : D₂ ≃+ M₂)
    (T : M₁ →+ M₂) (S₁ : k → M₁ → M₁) (S₂ : k → M₂ → M₂)
    (h₁ : ∀ (a : k) (x : D₁), ι₁ (a • x) = S₁ a (ι₁ x)) (h₂ : ∀ (a : k) (y : D₂), ι₂ (a • y) = S₂ a (ι₂ y))
    (hT : ∀ (a : k) (m : M₁), T (S₁ a m) = S₂ a (T m)) :
    ∃ f : D₁ →ₗ[k] D₂, ∀ x, ι₂ (f x) = T (ι₁ x) := by
  refine ⟨{ toFun := fun x => ι₂.symm (T (ι₁ x))
            map_add' := fun x y => by simp
            map_smul' := fun a x => ι₂.injective ?_ }, fun x => by simp⟩
  simp only [AddEquiv.apply_symm_apply, RingHom.id_apply]
  rw [h₁, hT, h₂, AddEquiv.apply_symm_apply]

theorem range_eq_ker_of_finrank {D E : Type} [AddCommGroup D] [Module k D] [AddCommGroup E] [Module k E]
    [FiniteDimensional k D] [FiniteDimensional k E] (i : D →ₗ[k] E) (q : E →ₗ[k] D)
    (hi : Function.Injective i) (hq : Function.Surjective q) (hqi : ∀ x, q (i x) = 0)
    (hdim : Module.finrank k E = Module.finrank k D + Module.finrank k D) :
    LinearMap.range i = LinearMap.ker q := by
  have hle : LinearMap.range i ≤ LinearMap.ker q := by
    rintro _ ⟨x, rfl⟩
    exact hqi x
  apply Submodule.eq_of_le_of_finrank_eq hle
  have h1 := LinearMap.finrank_range_add_finrank_ker q
  have h2 : Module.finrank k (LinearMap.range i) = Module.finrank k D :=
    LinearMap.finrank_range_of_inj hi
  have h3 : Module.finrank k (LinearMap.range q) = Module.finrank k D := by
    rw [LinearMap.range_eq_top.2 hq, finrank_top]
  omega

end LinAlg

section Splitting

variable {k : Type*} [Field k] {D : Type*} [AddCommGroup D] [Module k D]
  (H : Deformation.HondaSystem (0 : k) D)
  {E : Type*} [AddCommGroup E] [Module k E]

theorem exists_section_map_le
    (q : E →ₗ[k] D) (hq : Function.Surjective q)
    (L_E : Submodule k E) (hL : H.L ≤ L_E.map q) :
    ∃ s : D →ₗ[k] E, q ∘ₗ s = LinearMap.id ∧ ∀ x ∈ H.L, s x ∈ L_E := by
  classical
  let qL : ↥(L_E ⊓ H.L.comap q) →ₗ[k] ↥H.L :=
    LinearMap.codRestrict H.L (q ∘ₗ (L_E ⊓ H.L.comap q).subtype) (fun z => z.2.2)
  have hqL : LinearMap.range qL = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro x
    obtain ⟨y, hy, hyx⟩ := hL x.2
    refine ⟨⟨y, hy, ?_⟩, ?_⟩
    · change q y ∈ H.L
      rw [hyx]; exact x.2
    · apply Subtype.ext
      exact hyx
  obtain ⟨sL, hsL⟩ := qL.exists_rightInverse_of_surjective hqL
  obtain ⟨s₀, hs₀⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl H.L
  let s : D →ₗ[k] E :=
    LinearMap.ofIsCompl hC ((L_E ⊓ H.L.comap q).subtype ∘ₗ sL) (s₀ ∘ₗ C.subtype)
  have hsL' : ∀ u : ↥H.L, q ((sL u : ↥(L_E ⊓ H.L.comap q)) : E) = u := by
    intro u
    have := congrArg (fun f => ((f u : ↥H.L) : D)) hsL
    simpa [qL] using this
  refine ⟨s, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    obtain ⟨u, v, rfl, -⟩ := Submodule.existsUnique_add_of_isCompl hC x
    simp only [LinearMap.coe_comp, Function.comp_apply, map_add, LinearMap.id_coe, id_eq, s,
      LinearMap.ofIsCompl_apply_left, LinearMap.ofIsCompl_apply_right, Submodule.coe_subtype, hsL']
    congr 1
    exact congrArg (fun f => f (v : D)) hs₀
  · intro x hx
    have : s x = ((sL ⟨x, hx⟩ : ↥(L_E ⊓ H.L.comap q)) : E) := by
      have := LinearMap.ofIsCompl_apply_left hC (φ := (L_E ⊓ H.L.comap q).subtype ∘ₗ sL)
        (ψ := s₀ ∘ₗ C.subtype) ⟨x, hx⟩
      simpa [s] using this
    rw [this]
    exact (sL ⟨x, hx⟩).2.1

theorem exists_extPairs_blockIso
    (F_E V_E : Module.End k E) (hFV : F_E ∘ₗ V_E = 0) (hVF : V_E ∘ₗ F_E = 0)
    (L_E : Submodule k E)
    (i : D →ₗ[k] E) (q : E →ₗ[k] D) (hi : Function.Injective i) (hq : Function.Surjective q)
    (hqi : LinearMap.range i = LinearMap.ker q)
    (hiF : ∀ x, i (H.F x) = F_E (i x)) (hiV : ∀ x, i (H.V x) = V_E (i x))
    (hqF : ∀ z, q (F_E z) = H.F (q z)) (hqV : ∀ z, q (V_E z) = H.V (q z))
    (hL₁ : ∀ x ∈ H.L, i x ∈ L_E) (hL₂ : ∀ x, i x ∈ L_E → x ∈ H.L)
    (hL₃ : ∀ z ∈ L_E, q z ∈ H.L) (hL₄ : H.L ≤ L_E.map q) :
    ∃ (XY : Module.End k D × Module.End k D) (Ψ : E ≃ₗ[k] D × D),
      XY ∈ H.extPairs ∧
      (∀ x, Ψ (i x) = (x, 0)) ∧ (∀ z, (Ψ z).2 = q z) ∧
      (∀ z, Ψ (F_E z) = (H.F (Ψ z).1 + XY.1 (Ψ z).2, H.F (Ψ z).2)) ∧
      (∀ z, Ψ (V_E z) = (H.V (Ψ z).1 + XY.2 (Ψ z).2, H.V (Ψ z).2)) ∧
      (∀ z, z ∈ L_E ↔ ((Ψ z).1 ∈ H.L ∧ (Ψ z).2 ∈ H.L)) := by
  classical
  obtain ⟨s, hs, hsL⟩ := exists_section_map_le H q hq L_E hL₄
  have hqs : ∀ y, q (s y) = y := fun y => congrArg (fun f => f y) hs
  have hqi0 : ∀ x, q (i x) = 0 := fun x => by
    have : i x ∈ LinearMap.ker q := hqi ▸ LinearMap.mem_range_self i x
    exact this
  let Φ : D × D →ₗ[k] E := i.coprod s
  have hmem : ∀ z : E, z - s (q z) ∈ LinearMap.range i := by
    intro z
    rw [hqi, LinearMap.mem_ker, map_sub, hqs, sub_self]
  obtain ⟨r₀, hr₀⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hr₀i : ∀ x, r₀ (i x) = x := fun x => congrArg (fun f => f x) hr₀
  let r : E →ₗ[k] D := r₀ ∘ₗ (LinearMap.id - s ∘ₗ q)
  have hr : ∀ z, i (r z) = z - s (q z) := by
    intro z
    obtain ⟨x, hx⟩ := hmem z
    simp only [r, LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply, LinearMap.id_coe, id_eq]
    rw [← hx, hr₀i]
  let Ψl : E →ₗ[k] D × D := r.prod q
  have hΨl : ∀ z, Ψl z = (r z, q z) := fun z => rfl
  have hΦ : ∀ x y, Φ (x, y) = i x + s y := fun x y => rfl
  have hΦΨ : ∀ z, Φ (Ψl z) = z := by
    intro z
    rw [hΨl, hΦ, hr]
    abel
  have hΨΦ : ∀ w, Ψl (Φ w) = w := by
    rintro ⟨x, y⟩
    rw [hΦ, hΨl, Prod.mk.injEq]
    constructor
    · apply hi
      rw [hr, map_add, map_add, hqi0, hqs, map_zero, zero_add, add_sub_cancel_right]
    · rw [map_add, hqi0, hqs, zero_add]
  let Ψ : E ≃ₗ[k] D × D :=
    { Ψl with
      invFun := Φ
      left_inv := hΦΨ
      right_inv := hΨΦ }
  have hΨ : ∀ z, Ψ z = (r z, q z) := fun z => rfl
  have hΨi : ∀ x, Ψ (i x) = (x, 0) := by
    intro x
    have := hΨΦ (x, 0)
    first | exact this | simpa [Φ] using this | (simp [Φ] at this; exact this) | (simp [Φ]; exact this) | (simp [Φ] at this ⊢; exact this)
  have hΨs : ∀ y, Ψ (s y) = (0, y) := by
    intro y
    have := hΨΦ (0, y)
    first | exact this | simpa [Φ] using this | (simp [Φ] at this; exact this) | (simp [Φ]; exact this) | (simp [Φ] at this ⊢; exact this)
  let X : Module.End k D := r ∘ₗ F_E ∘ₗ s
  let Y : Module.End k D := r ∘ₗ V_E ∘ₗ s
  have hdecomp : ∀ z : E, z = i (r z) + s (q z) := fun z => by rw [hr]; abel
  have hΨF : ∀ z, Ψ (F_E z) = (H.F (Ψ z).1 + X (Ψ z).2, H.F (Ψ z).2) := by
    intro z
    conv_lhs => rw [hdecomp z]
    rw [map_add, ← hiF, map_add, hΨi]
    simp only [hΨ, Prod.mk_add_mk, zero_add, hqF, hqs, X, LinearMap.coe_comp, Function.comp_apply]
  have hΨV : ∀ z, Ψ (V_E z) = (H.V (Ψ z).1 + Y (Ψ z).2, H.V (Ψ z).2) := by
    intro z
    conv_lhs => rw [hdecomp z]
    rw [map_add, ← hiV, map_add, hΨi]
    simp only [hΨ, Prod.mk_add_mk, zero_add, hqV, hqs, Y, LinearMap.coe_comp, Function.comp_apply]
  refine ⟨(X, Y), Ψ, ?_, hΨi, fun z => rfl, hΨF, hΨV, ?_⟩
  · rw [Deformation.HondaSystem.mem_extPairs_iff]
    constructor
    · ext y
      have h1 : Ψ (F_E (V_E (s y))) = 0 := by
        rw [← LinearMap.comp_apply, hFV, LinearMap.zero_apply, map_zero]
      rw [hΨF, hΨV, hΨs] at h1
      have := congrArg Prod.fst h1
      simpa [H.toDieudonneDatum.F_V_apply] using this
    · ext y
      have h1 : Ψ (V_E (F_E (s y))) = 0 := by
        rw [← LinearMap.comp_apply, hVF, LinearMap.zero_apply, map_zero]
      rw [hΨV, hΨF, hΨs] at h1
      have := congrArg Prod.fst h1
      simpa [H.toDieudonneDatum.V_F_apply] using this
  · intro z
    constructor
    · intro hz
      refine ⟨?_, hL₃ z hz⟩
      apply hL₂
      rw [hΨ, hr]
      exact L_E.sub_mem hz (hsL _ (hL₃ z hz))
    · rintro ⟨h1, h2⟩
      rw [hdecomp z]
      exact L_E.add_mem (hL₁ _ h1) (hsL _ h2)

end Splitting

section Galois

variable (p : ℕ) [Fact p.Prime]

noncomputable def toLoc :
    (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ≃* primeLocalGaloisGroup (pPrime p) :=
  MulEquiv.refl _

theorem localAut_toLoc (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    ResidualGaloisRep.localAut p (toLoc p σ) = σ := rfl

variable {k : Type} [Field k] (ρbar : ResidualGaloisRep k)

local notation "ιp" => primeLocalToGlobal (pPrime p)
local notation "Gal" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

@[reducible] noncomputable def galAction : DistribMulAction Gal ρbar.V where
  smul σ v := ρbar.ρ (ιp (toLoc p σ)) v
  one_smul v := by
    show ρbar.ρ (ιp (toLoc p 1)) v = v
    rw [map_one, map_one, map_one]
    rfl
  mul_smul σ τ v := by
    show ρbar.ρ (ιp (toLoc p (σ * τ))) v = ρbar.ρ (ιp (toLoc p σ)) (ρbar.ρ (ιp (toLoc p τ)) v)
    rw [map_mul, map_mul, map_mul]
    rfl
  smul_zero σ := map_zero _
  smul_add σ v w := map_add _ _ _

theorem galAction_smul (σ : Gal) (v : ρbar.V) :
    (letI := galAction p ρbar; σ • v) = ρbar.ρ (ιp (toLoc p σ)) v := rfl

variable (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))

def Ec (p : ℕ) [Fact p.Prime] {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (_c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) : Type :=
  ρbar.V × ρbar.V

scoped instance : AddCommGroup (Ec p ρbar c) := inferInstanceAs (AddCommGroup (ρbar.V × ρbar.V))
noncomputable scoped instance : Module k (Ec p ρbar c) := inferInstanceAs (Module k (ρbar.V × ρbar.V))

def toEc : (ρbar.V × ρbar.V) ≃ₗ[k] Ec p ρbar c := LinearEquiv.refl k _

theorem cocycle_mul (σ τ : primeLocalGaloisGroup (pPrime p)) :
    (c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) (σ * τ) =
      ρbar.ρ (ιp σ) * (c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) τ * ρbar.ρ (ιp σ)⁻¹ +
        (c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ := by
  have h := (mem_cocycles₁_iff (c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V)).1 c.2 σ τ
  rw [h]
  exact congrArg₂ (· + ·) (ResidualGaloisRep.adRep_apply ρbar (ιp σ) _) rfl

theorem ρ_inv_apply (σ : primeLocalGaloisGroup (pPrime p)) (v : ρbar.V) :
    ρbar.ρ (ιp σ)⁻¹ (ρbar.ρ (ιp σ) v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem dualLift_one (x : ρbar.V × ρbar.V) : ρbar.dualLiftModuleActAd p c 1 x = x := by
  ext
  · simp [ResidualGaloisRep.dualLiftModuleActAd]
  · simp [ResidualGaloisRep.dualLiftModuleActAd]

theorem dualLift_mul (σ τ : primeLocalGaloisGroup (pPrime p)) (x : ρbar.V × ρbar.V) :
    ρbar.dualLiftModuleActAd p c (σ * τ) x =
      ρbar.dualLiftModuleActAd p c σ (ρbar.dualLiftModuleActAd p c τ x) := by
  ext
  · simp [ResidualGaloisRep.dualLiftModuleActAd]
  · simp only [ResidualGaloisRep.dualLiftModuleActAd, map_mul, Module.End.mul_apply, map_add,
      cocycle_mul, LinearMap.add_apply, ρ_inv_apply]
    abel

theorem dualLift_zero (σ : primeLocalGaloisGroup (pPrime p)) :
    ρbar.dualLiftModuleActAd p c σ 0 = 0 := by
  ext <;> simp [ResidualGaloisRep.dualLiftModuleActAd]

theorem dualLift_add (σ : primeLocalGaloisGroup (pPrime p)) (x y : ρbar.V × ρbar.V) :
    ρbar.dualLiftModuleActAd p c σ (x + y) =
      ρbar.dualLiftModuleActAd p c σ x + ρbar.dualLiftModuleActAd p c σ y := by
  ext <;> simp [ResidualGaloisRep.dualLiftModuleActAd, add_add_add_comm]

theorem dualLift_smul (σ : primeLocalGaloisGroup (pPrime p)) (a : k) (x : ρbar.V × ρbar.V) :
    ρbar.dualLiftModuleActAd p c σ (a • x) = a • ρbar.dualLiftModuleActAd p c σ x := by
  ext <;> simp [ResidualGaloisRep.dualLiftModuleActAd]

noncomputable scoped instance dualLiftAction : DistribMulAction Gal (Ec p ρbar c) where
  smul σ x := toEc p ρbar c (ρbar.dualLiftModuleActAd p c (toLoc p σ) ((toEc p ρbar c).symm x))
  one_smul x := by
    show toEc p ρbar c (ρbar.dualLiftModuleActAd p c (toLoc p 1) ((toEc p ρbar c).symm x)) = x
    rw [map_one, dualLift_one]
    rfl
  mul_smul σ τ x := by
    show toEc p ρbar c (ρbar.dualLiftModuleActAd p c (toLoc p (σ * τ)) ((toEc p ρbar c).symm x)) =
      toEc p ρbar c (ρbar.dualLiftModuleActAd p c (toLoc p σ) ((toEc p ρbar c).symm
        (toEc p ρbar c (ρbar.dualLiftModuleActAd p c (toLoc p τ) ((toEc p ρbar c).symm x)))))
    rw [map_mul, dualLift_mul]
    rfl
  smul_zero σ := by
    show toEc p ρbar c (ρbar.dualLiftModuleActAd p c (toLoc p σ) ((toEc p ρbar c).symm 0)) = 0
    rw [map_zero, dualLift_zero, map_zero]
  smul_add σ x y := by
    show toEc p ρbar c (ρbar.dualLiftModuleActAd p c (toLoc p σ) ((toEc p ρbar c).symm (x + y))) = _
    rw [map_add, dualLift_add, map_add]
    rfl

theorem dualLiftAction_smul (σ : Gal) (x : Ec p ρbar c) :
    σ • x = toEc p ρbar c (ρbar.dualLiftModuleActAd p c (toLoc p σ) ((toEc p ρbar c).symm x)) := rfl

scoped instance : SMulCommClass Gal k (Ec p ρbar c) where
  smul_comm σ a x := by
    rw [dualLiftAction_smul, dualLiftAction_smul, map_smul, dualLift_smul, map_smul]

noncomputable def αE : ρbar.V →+ Ec p ρbar c :=
  ((toEc p ρbar c).toLinearMap ∘ₗ LinearMap.inr k ρbar.V ρbar.V).toAddMonoidHom

noncomputable def βE : Ec p ρbar c →+ ρbar.V :=
  (LinearMap.fst k ρbar.V ρbar.V ∘ₗ (toEc p ρbar c).symm.toLinearMap).toAddMonoidHom

theorem αE_apply (w : ρbar.V) : αE p ρbar c w = toEc p ρbar c (0, w) := rfl

theorem βE_apply (x : Ec p ρbar c) : βE p ρbar c x = ((toEc p ρbar c).symm x).1 := rfl

theorem αE_smul (σ : Gal) (w : ρbar.V) :
    αE p ρbar c ((letI := galAction p ρbar; σ • w)) = σ • αE p ρbar c w := by
  rw [galAction_smul, αE_apply, αE_apply, dualLiftAction_smul, LinearEquiv.symm_apply_apply]
  congr 1
  ext <;> simp [ResidualGaloisRep.dualLiftModuleActAd]

theorem βE_smul (σ : Gal) (x : Ec p ρbar c) :
    βE p ρbar c (σ • x) = (letI := galAction p ρbar; σ • βE p ρbar c x) := by
  rw [galAction_smul, βE_apply, βE_apply, dualLiftAction_smul, LinearEquiv.symm_apply_apply]
  rfl

theorem αE_injective : Function.Injective (αE p ρbar c) := by
  intro w w' h
  have := congrArg (fun x => ((toEc p ρbar c).symm x).2) h
  simpa [αE_apply] using this

theorem βE_surjective : Function.Surjective (βE p ρbar c) := fun v =>
  ⟨toEc p ρbar c (v, 0), by simp [βE_apply]⟩

theorem exact_αE_βE : Function.Exact (αE p ρbar c) (βE p ρbar c) := by
  intro x
  constructor
  · intro hx
    refine ⟨((toEc p ρbar c).symm x).2, ?_⟩
    rw [αE_apply]
    apply (toEc p ρbar c).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    rw [βE_apply] at hx
    ext
    · exact hx.symm
    · rfl
  · rintro ⟨w, rfl⟩
    simp [βE_apply, αE_apply]

end Galois

section Points

variable (p : ℕ) [Fact p.Prime]

abbrev Pts (X : Type) [CommRing X] [HopfAlgebra ℤ_[p] X] : Type := WithConv (X →ₐ[ℤ_[p]] PadicAlgCl p)

variable {X Y Z : Type} [CommRing X] [HopfAlgebra ℤ_[p] X] [CommRing Y] [HopfAlgebra ℤ_[p] Y]
  [CommRing Z] [HopfAlgebra ℤ_[p] Z]

noncomputable def pre (f : X →ₐc[ℤ_[p]] Y) (F : Pts p Y) : Pts p X :=
  WithConv.toConv ((WithConv.ofConv F).comp (f : X →ₐ[ℤ_[p]] Y))

theorem pre_def (f : X →ₐc[ℤ_[p]] Y) (F : Pts p Y) :
    pre p f F = WithConv.toConv ((WithConv.ofConv F).comp (f : X →ₐ[ℤ_[p]] Y)) := rfl

theorem pre_comp (f : X →ₐc[ℤ_[p]] Y) (g : Y →ₐc[ℤ_[p]] Z) (F : Pts p Z) :
    pre p (g.comp f) F = pre p f (pre p g F) :=
  WithConv.ext (AlgHom.ext fun _ => rfl)

end Points

section Fibre

variable (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] (ZMod p)]
variable {X Y Z : Type} [CommRing X] [HopfAlgebra ℤ_[p] X] [CommRing Y] [HopfAlgebra ℤ_[p] Y]
  [CommRing Z] [HopfAlgebra ℤ_[p] Z]

noncomputable abbrev bc (f : X →ₐc[ℤ_[p]] Y) :
    (ZMod p) ⊗[ℤ_[p]] X →ₐc[ZMod p] (ZMod p) ⊗[ℤ_[p]] Y :=
  Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) f

theorem bc_comp (g : Y →ₐc[ℤ_[p]] Z) (f : X →ₐc[ℤ_[p]] Y) :
    bc p (g.comp f) = (bc p g).comp (bc p f) := by
  apply BialgHom.coe_algHom_injective
  rw [BialgHom.comp_toAlgHom, Bialgebra.TensorProduct.map_toAlgHom,
    Bialgebra.TensorProduct.map_toAlgHom, Bialgebra.TensorProduct.map_toAlgHom,
    BialgHom.comp_toAlgHom]
  exact Algebra.TensorProduct.map_id_comp _ _

theorem dmap_comp_apply (g : Y →ₐc[ℤ_[p]] Z) (f : X →ₐc[ℤ_[p]] Y)
    (z : Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] X)) :
    Deformation.DieudonneModule.map (ZMod p) p (bc p (g.comp f)) z =
      Deformation.DieudonneModule.map (ZMod p) p (bc p g)
        (Deformation.DieudonneModule.map (ZMod p) p (bc p f) z) := by
  rw [bc_comp, Deformation.DieudonneModule.map_comp]

theorem includeRight_comp (f : X →ₐc[ℤ_[p]] Y) :
    (Algebra.TensorProduct.includeRight : Y →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] Y).toRingHom.comp
        (f : X →ₐ[ℤ_[p]] Y).toRingHom =
      (bc p f : (ZMod p) ⊗[ℤ_[p]] X →ₐ[ZMod p] (ZMod p) ⊗[ℤ_[p]] Y).toRingHom.comp
        (Algebra.TensorProduct.includeRight : X →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] X).toRingHom := by
  ext x
  change (1 : ZMod p) ⊗ₜ[ℤ_[p]] f x = (bc p f) ((1 : ZMod p) ⊗ₜ[ℤ_[p]] x)
  rw [Bialgebra.TensorProduct.map_tmul]
  rfl

theorem map_mem_fontaineHodge (f : X →ₐc[ℤ_[p]] Y)
    {z : Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] X)}
    (hz : z ∈ Deformation.fontaineHodge (ZMod p) p
      (Algebra.TensorProduct.includeRight : X →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] X).toRingHom) :
    Deformation.DieudonneModule.map (ZMod p) p (bc p f) z ∈ Deformation.fontaineHodge (ZMod p) p
      (Algebra.TensorProduct.includeRight : Y →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] Y).toRingHom :=
  Deformation.map_fontaineHodge_le
    (π := (Algebra.TensorProduct.includeRight : Y →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] Y).toRingHom)
    (Algebra.TensorProduct.includeRight : X →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] X).toRingHom
    (f : X →ₐ[ℤ_[p]] Y).toRingHom (bc p f) (includeRight_comp p f) ⟨z, hz, rfl⟩

end Fibre

section Card

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [Finite k]

theorem natCard_V (ρbar : ResidualGaloisRep k) : Nat.card ρbar.V = Nat.card k ^ 2 := by
  haveI : Finite ρbar.V := Module.finite_of_finite k
  rw [Module.natCard_eq_pow_finrank (K := k) (V := ρbar.V), ρbar.finrank_eq]

theorem natCard_pts_eq_finrank (X : Type) [CommRing X] [HopfAlgebra ℤ_[p] X] [Module.Finite ℤ_[p] X]
    [Module.Free ℤ_[p] X] : Nat.card (Pts p X) = Module.finrank ℤ_[p] X := by
  rw [Nat.card_congr (WithConv.equiv (X →ₐ[ℤ_[p]] PadicAlgCl p))]
  exact HopfAlgebra.natCard_algHom_eq_finrank_of_charZero ℤ_[p] X (PadicAlgCl p)

end Card

section Construction

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] (ZMod p)]

local notation "Gal" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

theorem galois_part [Finite k] (hp2 : p ≠ 2) (ρbar : ResidualGaloisRep k)
    (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
    [Coalgebra.IsCocomm ℤ_[p] H₁] (hrank₁' : ∃ a : ℕ, Module.finrank ℤ_[p] H₁ = p ^ a)
    (e₁ : Pts p H₁ ≃ ρbar.V)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : Pts p H₁),
      (∀ h : H₁, g h = ResidualGaloisRep.localAut p σ (f h)) →
        e₁ g = ρbar.ρ (primeLocalToGlobal (pPrime p) σ) (e₁ f))
    (θ : k → (H₁ →ₐc[ℤ_[p]] H₁))
    (hθ : ∀ (a : k) (f : Pts p H₁),
      e₁ (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H₁ →ₐ[ℤ_[p]] H₁))) = a • e₁ f)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H] (hrankH' : ∃ a : ℕ, Module.finrank ℤ_[p] H = p ^ a)
    (e : Pts p H ≃ ρbar.V × ρbar.V)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : Pts p H),
      (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) → e g = ρbar.dualLiftModuleActAd p c σ (e f)) :
    ∃ (θH : k → (H →ₐc[ℤ_[p]] H)) (π : H →ₐc[ℤ_[p]] H₁) (j : H₁ →ₐc[ℤ_[p]] H),
      (∀ (a : k) (f : Pts p H),
        e (WithConv.toConv ((WithConv.ofConv f).comp (θH a : H →ₐ[ℤ_[p]] H))) = a • e f) ∧
      (∀ a b : k, θH (a * b) = (θH a).comp (θH b)) ∧ θH 1 = BialgHom.id ℤ_[p] H ∧
      (∀ a b : k, WithConv.toConv (θH (a + b) : H →ₐ[ℤ_[p]] H) =
        WithConv.toConv (θH a : H →ₐ[ℤ_[p]] H) * WithConv.toConv (θH b : H →ₐ[ℤ_[p]] H)) ∧
      WithConv.toConv (θH 0 : H →ₐ[ℤ_[p]] H) = 1 ∧
      (∀ f : Pts p H₁, e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[ℤ_[p]] H₁))) = (0, e₁ f)) ∧
      (∀ f : Pts p H, e₁ (WithConv.toConv ((WithConv.ofConv f).comp (j : H₁ →ₐ[ℤ_[p]] H))) = (e f).1) ∧
      Function.Surjective π ∧ Function.Injective j ∧
      (j : H₁ →ₐ[ℤ_[p]] H).range = HopfAlgebra.hopfKer π ∧
      (∀ a : k, (θ a).comp π = π.comp (θH a)) ∧
      (∀ a : k, (θH a).comp j = j.comp (θ a)) := by
  classical
  letI := galAction p ρbar
  have he₁_act' : ∀ (σ : Gal) (f f' : Pts p H₁), (∀ x : H₁, f' x = σ (f x)) → e₁ f' = σ • e₁ f :=
    fun σ f f' h => he₁_act (toLoc p σ) f f' h
  let e' : Pts p H ≃ Ec p ρbar c := e.trans (toEc p ρbar c).toEquiv
  have he'_apply : ∀ f, e' f = toEc p ρbar c (e f) := fun f => rfl
  have he'_add : ∀ f g, e' (f * g) = e' f + e' g := by
    intro f g
    rw [he'_apply, he'_apply, he'_apply, he_add, map_add]
  have he'_act : ∀ (σ : Gal) (f f' : Pts p H), (∀ x : H, f' x = σ (f x)) → e' f' = σ • e' f := by
    intro σ f f' h
    rw [he'_apply, he'_apply, dualLiftAction_smul, LinearEquiv.symm_apply_apply,
      he_act (toLoc p σ) f f' h]

  obtain ⟨θH, hθH, hθH_mul, hθH_one, hθH_add, hθH_zero⟩ :=
    HopfAlgebra.exists_coeffAction_forall_apply_comp_eq_smul_of_ne_two (k := k) p hp2 H hrankH' e' he'_add
      he'_act
  have hθH' : ∀ (a : k) (f : Pts p H),
      e (WithConv.toConv ((WithConv.ofConv f).comp (θH a : H →ₐ[ℤ_[p]] H))) = a • e f := by
    intro a f
    have := hθH a f
    exact (toEc p ρbar c).injective (by rw [← he'_apply, this, he'_apply, map_smul])

  obtain ⟨π, j, hπ, hj, hπs, hji, hrange⟩ :=
    HopfAlgebra.exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two p hp2
      (αE p ρbar c) (βE p ρbar c) (αE_smul p ρbar c) (βE_smul p ρbar c)
      (αE_injective p ρbar c) (βE_surjective p ρbar c) (exact_αE_βE p ρbar c)
      H₁ hrank₁' e₁ he₁_add he₁_act' H hrankH' e' he'_add he'_act H₁ hrank₁' e₁ he₁_add he₁_act'
  have hπ' : ∀ f : Pts p H₁, e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[ℤ_[p]] H₁))) =
      (0, e₁ f) := by
    intro f
    apply (toEc p ρbar c).injective
    rw [← he'_apply, hπ, αE_apply]
  have hj' : ∀ f : Pts p H, e₁ (WithConv.toConv ((WithConv.ofConv f).comp (j : H₁ →ₐ[ℤ_[p]] H))) =
      (e f).1 := by
    intro f
    rw [hj, βE_apply, he'_apply, LinearEquiv.symm_apply_apply]

  have hθπ : ∀ a : k, (θ a).comp π = π.comp (θH a) := by
    intro a
    let φ : ρbar.V →+ Ec p ρbar c := (αE p ρbar c).comp (DistribSMul.toAddMonoidHom ρbar.V a)
    have hφ : ∀ (σ : Gal) (m : ρbar.V), φ (σ • m) = σ • φ m := by
      intro σ m
      change αE p ρbar c (a • (σ • m)) = σ • αE p ρbar c (a • m)
      rw [galAction_smul, ← map_smul, ← galAction_smul p ρbar σ (a • m)]
      exact αE_smul p ρbar c σ (a • m)
    have hu := HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
      p hp2 H₁ hrank₁' e₁ he₁_add he₁_act' H hrankH' e' he'_add he'_act φ hφ
    refine hu.unique (fun f => ?_) (fun f => ?_)
    · change e' (pre p ((θ a).comp π) f) = αE p ρbar c (a • e₁ f)
      rw [pre_comp, he'_apply, pre_def, hπ', pre_def, hθ, αE_apply]
    · change e' (pre p (π.comp (θH a)) f) = αE p ρbar c (a • e₁ f)
      rw [pre_comp, he'_apply, pre_def, hθH', pre_def, hπ', αE_apply, Prod.smul_mk, smul_zero]
  have hθj : ∀ a : k, (θH a).comp j = j.comp (θ a) := by
    intro a
    let φ : Ec p ρbar c →+ ρbar.V := (DistribSMul.toAddMonoidHom ρbar.V a).comp (βE p ρbar c)
    have hφ : ∀ (σ : Gal) (m : Ec p ρbar c), φ (σ • m) = σ • φ m := by
      intro σ m
      change a • βE p ρbar c (σ • m) = σ • (a • βE p ρbar c m)
      rw [βE_smul, galAction_smul, galAction_smul, map_smul]
    have hu := HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
      p hp2 H hrankH' e' he'_add he'_act H₁ hrank₁' e₁ he₁_add he₁_act' φ hφ
    refine hu.unique (fun f => ?_) (fun f => ?_)
    · change e₁ (pre p ((θH a).comp j) f) = a • βE p ρbar c (e' f)
      rw [pre_comp, pre_def, hj', pre_def, hθH', Prod.smul_fst, βE_apply, he'_apply,
        LinearEquiv.symm_apply_apply]
    · change e₁ (pre p (j.comp (θ a)) f) = a • βE p ρbar c (e' f)
      rw [pre_comp, pre_def, hθ, pre_def, hj', βE_apply, he'_apply, LinearEquiv.symm_apply_apply]
  exact ⟨θH, π, j, hθH', hθH_mul, hθH_one, hθH_add, hθH_zero, hπ', hj', hπs, hji, hrange, hθπ, hθj⟩

section Dieudonne

variable {H₁ H : Type} [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [CommRing H] [HopfAlgebra ℤ_[p] H]
  (θ : k → (H₁ →ₐc[ℤ_[p]] H₁)) (θH : k → (H →ₐc[ℤ_[p]] H)) (π : H →ₐc[ℤ_[p]] H₁) (j : H₁ →ₐc[ℤ_[p]] H)
  {D E : Type} [AddCommGroup D] [Module k D] [AddCommGroup E] [Module k E]
  (𝓗 : Deformation.HondaSystem (0 : k) D) (𝓔 : Deformation.HondaSystem (0 : k) E)
  (ι : D ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁))
  (ιE : E ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H))

theorem exists_i
    (hιsmul : ∀ (a : k) (x : D), ι (a • x) = Deformation.DieudonneModule.map (ZMod p) p (bc p (θ a)) (ι x))
    (hEsmul : ∀ (a : k) (z : E), ιE (a • z) = Deformation.DieudonneModule.map (ZMod p) p (bc p (θH a)) (ιE z))
    (hθj : ∀ a : k, (θH a).comp j = j.comp (θ a)) :
    ∃ i : D →ₗ[k] E, ∀ x, ιE (i x) = Deformation.DieudonneModule.map (ZMod p) p (bc p j) (ι x) :=
  exists_linearMap_of_addEquiv ι ιE (Deformation.DieudonneModule.map (ZMod p) p (bc p j))
    (fun a m => Deformation.DieudonneModule.map (ZMod p) p (bc p (θ a)) m)
    (fun a m => Deformation.DieudonneModule.map (ZMod p) p (bc p (θH a)) m) hιsmul hEsmul
    (fun a m => by beta_reduce; rw [← dmap_comp_apply, ← dmap_comp_apply, hθj])

theorem exists_q
    (hιsmul : ∀ (a : k) (x : D), ι (a • x) = Deformation.DieudonneModule.map (ZMod p) p (bc p (θ a)) (ι x))
    (hEsmul : ∀ (a : k) (z : E), ιE (a • z) = Deformation.DieudonneModule.map (ZMod p) p (bc p (θH a)) (ιE z))
    (hθπ : ∀ a : k, (θ a).comp π = π.comp (θH a)) :
    ∃ q : E →ₗ[k] D, ∀ z, ι (q z) = Deformation.DieudonneModule.map (ZMod p) p (bc p π) (ιE z) :=
  exists_linearMap_of_addEquiv ιE ι (Deformation.DieudonneModule.map (ZMod p) p (bc p π))
    (fun a m => Deformation.DieudonneModule.map (ZMod p) p (bc p (θH a)) m)
    (fun a m => Deformation.DieudonneModule.map (ZMod p) p (bc p (θ a)) m) hEsmul hιsmul
    (fun a m => by beta_reduce; rw [← dmap_comp_apply, ← dmap_comp_apply, hθπ])

variable (i : D →ₗ[k] E) (q : E →ₗ[k] D)
  (hi : ∀ x, ιE (i x) = Deformation.DieudonneModule.map (ZMod p) p (bc p j) (ι x))
  (hq : ∀ z, ι (q z) = Deformation.DieudonneModule.map (ZMod p) p (bc p π) (ιE z))

include hq in
theorem q_surjective (hM : Function.Surjective (Deformation.DieudonneModule.map (ZMod p) p (bc p π))) :
    Function.Surjective q := by
  intro x
  obtain ⟨w, hw⟩ := hM (ι x)
  refine ⟨ιE.symm w, ι.injective ?_⟩
  rw [hq, AddEquiv.apply_symm_apply, hw]

include hi in
theorem i_injective (hM : Function.Injective (Deformation.DieudonneModule.map (ZMod p) p (bc p j))) :
    Function.Injective i := by
  intro x y hxy
  apply ι.injective
  apply hM
  rw [← hi, ← hi, hxy]

include hi hq in
theorem q_i (hM : ∀ x, Deformation.DieudonneModule.map (ZMod p) p (bc p π)
    (Deformation.DieudonneModule.map (ZMod p) p (bc p j) x) = 0) (x : D) : q (i x) = 0 := by
  apply ι.injective
  rw [hq, hi, hM, map_zero]

variable [CharP k p]

include hi in
theorem i_F (hιF : ∀ x, ι (𝓗.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p _ (ι x))
    (hEF : ∀ z, ιE (𝓔.F z) = Deformation.DieudonneModule.frobenius (ZMod p) p _ (ιE z)) (x : D) :
    i (𝓗.F x) = 𝓔.F (i x) := by
  apply ιE.injective
  rw [hi, hιF, Deformation.DieudonneModule.map_frobenius, ← hi, hEF]

omit [CharP k p] in
include hi in
theorem i_V (hιV : ∀ x, ι (𝓗.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p _ (ι x))
    (hEV : ∀ z, ιE (𝓔.V z) = Deformation.DieudonneModule.verschiebung (ZMod p) p _ (ιE z)) (x : D) :
    i (𝓗.V x) = 𝓔.V (i x) := by
  apply ιE.injective
  rw [hi, hιV, Deformation.DieudonneModule.map_verschiebung, ← hi, hEV]

include hq in
theorem q_F (hιF : ∀ x, ι (𝓗.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p _ (ι x))
    (hEF : ∀ z, ιE (𝓔.F z) = Deformation.DieudonneModule.frobenius (ZMod p) p _ (ιE z)) (z : E) :
    q (𝓔.F z) = 𝓗.F (q z) := by
  apply ι.injective
  rw [hq, hEF, Deformation.DieudonneModule.map_frobenius, ← hq, hιF]

omit [CharP k p] in
include hq in
theorem q_V (hιV : ∀ x, ι (𝓗.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p _ (ι x))
    (hEV : ∀ z, ιE (𝓔.V z) = Deformation.DieudonneModule.verschiebung (ZMod p) p _ (ιE z)) (z : E) :
    q (𝓔.V z) = 𝓗.V (q z) := by
  apply ι.injective
  rw [hq, hEV, Deformation.DieudonneModule.map_verschiebung, ← hq, hιV]

omit [CharP k p]

variable
  (hιL : ∀ x, x ∈ 𝓗.L ↔ ι x ∈ Deformation.fontaineHodge (ZMod p) p
    (Algebra.TensorProduct.includeRight : H₁ →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H₁).toRingHom)
  (hEL : ∀ z, z ∈ 𝓔.L ↔ ιE z ∈ Deformation.fontaineHodge (ZMod p) p
    (Algebra.TensorProduct.includeRight : H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H).toRingHom)

include hi hιL hEL in
theorem i_L₁ (x : D) (hx : x ∈ 𝓗.L) : i x ∈ 𝓔.L := by
  rw [hEL, hi]
  exact map_mem_fontaineHodge p j ((hιL x).1 hx)

include hi hιL hEL in
theorem i_L₂
    (hLpure : ∀ x, Deformation.DieudonneModule.map (ZMod p) p (bc p j) x ∈
      Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H).toRingHom →
      x ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : H₁ →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H₁).toRingHom)
    (x : D) (hx : i x ∈ 𝓔.L) : x ∈ 𝓗.L := by
  rw [hEL, hi] at hx
  exact (hιL x).2 (hLpure (ι x) hx)

include hq hιL hEL in
theorem q_L₃ (z : E) (hz : z ∈ 𝓔.L) : q z ∈ 𝓗.L := by
  rw [hιL, hq]
  exact map_mem_fontaineHodge p π ((hEL z).1 hz)

include hq hιL hEL in
theorem q_L₄
    (hLonto : ∀ z ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : H₁ →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H₁).toRingHom,
      ∃ y ∈ Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight : H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H).toRingHom,
        Deformation.DieudonneModule.map (ZMod p) p (bc p π) y = z) :
    𝓗.L ≤ (𝓔.L).map q := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hLonto (ι x) ((hιL x).1 hx)
  refine ⟨ιE.symm y, (hEL _).2 (by rwa [AddEquiv.apply_symm_apply]), ι.injective ?_⟩
  rw [hq, AddEquiv.apply_symm_apply, hyx]

end Dieudonne

theorem main [Finite k] (hp2 : p ≠ 2) [CharP k p]
    (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
    [Coalgebra.IsCocomm ℤ_[p] H₁] (hrank₁ : Module.finrank ℤ_[p] H₁ = Nat.card k ^ 2)
    (e₁ : Pts p H₁ ≃ ρbar.V)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : Pts p H₁),
      (∀ h : H₁, g h = ResidualGaloisRep.localAut p σ (f h)) →
        e₁ g = ρbar.ρ (primeLocalToGlobal (pPrime p) σ) (e₁ f))
    (θ : k → (H₁ →ₐc[ℤ_[p]] H₁))
    (hθ : ∀ (a : k) (f : Pts p H₁),
      e₁ (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H₁ →ₐ[ℤ_[p]] H₁))) = a • e₁ f)
    (D : Type) [AddCommGroup D] [Module k D] [FiniteDimensional k D] (𝓗 : Deformation.HondaSystem (0 : k) D)
    (ι : D ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁))
    (hιF : ∀ x, ι (𝓗.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁) (ι x))
    (hιV : ∀ x, ι (𝓗.V x) =
      Deformation.DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁) (ι x))
    (hιL : ∀ x, x ∈ 𝓗.L ↔ ι x ∈ Deformation.fontaineHodge (ZMod p) p
      (Algebra.TensorProduct.includeRight : H₁ →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H₁).toRingHom)
    (hιsmul : ∀ (a : k) (x : D), ι (a • x) = Deformation.DieudonneModule.map (ZMod p) p (bc p (θ a)) (ι x))
    (hD : Module.finrank k D = 2)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (hunipH : IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H)))
    (e : Pts p H ≃ ρbar.V × ρbar.V)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : Pts p H),
      (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) → e g = ρbar.dualLiftModuleActAd p c σ (e f)) :
    ∃ (θH : k → (H →ₐc[ℤ_[p]] H)) (π : H →ₐc[ℤ_[p]] H₁) (j : H₁ →ₐc[ℤ_[p]] H)
      (E : Type) (_ : AddCommGroup E) (_ : Module k E) (_ : FiniteDimensional k E)
      (𝓔 : Deformation.HondaSystem (0 : k) E)
      (ιE : E ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H))
      (i : D →ₗ[k] E) (q : E →ₗ[k] D)
      (XY : Module.End k D × Module.End k D) (Ψ : E ≃ₗ[k] D × D),
      (∃ a : ℕ, Module.finrank ℤ_[p] H = p ^ a) ∧
      (∀ (a : k) (f : Pts p H),
        e (WithConv.toConv ((WithConv.ofConv f).comp (θH a : H →ₐ[ℤ_[p]] H))) = a • e f) ∧
      (∀ f : Pts p H₁, e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[ℤ_[p]] H₁))) = (0, e₁ f)) ∧
      (∀ f : Pts p H, e₁ (WithConv.toConv ((WithConv.ofConv f).comp (j : H₁ →ₐ[ℤ_[p]] H))) = (e f).1) ∧
      (∀ z, ιE (𝓔.F z) =
        Deformation.DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) (ιE z)) ∧
      (∀ z, ιE (𝓔.V z) =
        Deformation.DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) (ιE z)) ∧
      (∀ z, z ∈ 𝓔.L ↔ ιE z ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H).toRingHom) ∧
      (∀ (a : k) (z : E), ιE (a • z) = Deformation.DieudonneModule.map (ZMod p) p (bc p (θH a)) (ιE z)) ∧
      (∀ x : D, ιE (i x) = Deformation.DieudonneModule.map (ZMod p) p (bc p j) (ι x)) ∧
      (∀ z : E, ι (q z) = Deformation.DieudonneModule.map (ZMod p) p (bc p π) (ιE z)) ∧
      XY ∈ 𝓗.extPairs ∧
      (∀ x, Ψ (i x) = (x, 0)) ∧ (∀ z, (Ψ z).2 = q z) ∧
      (∀ z, Ψ (𝓔.F z) = (𝓗.F (Ψ z).1 + XY.1 (Ψ z).2, 𝓗.F (Ψ z).2)) ∧
      (∀ z, Ψ (𝓔.V z) = (𝓗.V (Ψ z).1 + XY.2 (Ψ z).2, 𝓗.V (Ψ z).2)) ∧
      (∀ z, z ∈ 𝓔.L ↔ ((Ψ z).1 ∈ 𝓗.L ∧ (Ψ z).2 ∈ 𝓗.L)) := by
  classical

  have hp0 : (p : ℤ_[p]) ∈ nonZeroDivisors ℤ_[p] :=
    mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card k = p ^ n := by
    haveI := Fintype.ofFinite k
    obtain ⟨n, -, hn⟩ := FiniteField.card k p
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hrank₁' : ∃ a : ℕ, Module.finrank ℤ_[p] H₁ = p ^ a := ⟨n * 2, by rw [hrank₁, hn, pow_mul]⟩
  have hrankH : Module.finrank ℤ_[p] H = Nat.card k ^ 4 := by
    rw [← natCard_pts_eq_finrank p H, Nat.card_congr e, Nat.card_prod, natCard_V]
    ring
  have hrankH' : ∃ a : ℕ, Module.finrank ℤ_[p] H = p ^ a := ⟨n * 4, by rw [hrankH, hn, pow_mul]⟩

  obtain ⟨θH, π, j, hθH, hθH_mul, hθH_one, hθH_add, hθH_zero, hπ, hj, hπs, hji, hrange, hθπ, hθj⟩ :=
    galois_part p hp2 ρbar H₁ hrank₁' e₁ he₁_add he₁_act θ hθ c H hrankH' e he_add he_act

  obtain ⟨E, _, _, _, 𝓔, ιE, hEF, hEV, hEL, hEsmul, hEdim⟩ :=
    Deformation.DieudonneModule.exists_hondaSystem_addEquiv_smul_eq_map_of_isLocalRing_cartierDual
      p k hker H hunipH 4 hrankH θH hθH_mul hθH_one hθH_add hθH_zero

  obtain ⟨i, hi⟩ := exists_i p θ θH j ι ιE hιsmul hEsmul hθj
  obtain ⟨q, hq⟩ := exists_q p θ θH π ι ιE hιsmul hEsmul hθπ

  obtain ⟨hMsurj, hMinj, hM0, hLonto, hLpure⟩ :=
    Deformation.DieudonneModule.map_baseChange_surjective_injective_fontaineHodge_of_range_eq_hopfKer
      p hp0 hker H hrankH' hunipH H₁ hrank₁' H₁ π hπs j hji hrange
  have hqs : Function.Surjective q := q_surjective p π ι ιE q hq hMsurj
  have hii : Function.Injective i := i_injective p j ι ιE i hi hMinj
  have hqi : ∀ x, q (i x) = 0 := q_i p π j ι ιE i q hi hq hM0
  have hexact : LinearMap.range i = LinearMap.ker q :=
    range_eq_ker_of_finrank i q hii hqs hqi (by rw [hEdim, hD])
  have hFV : 𝓔.F ∘ₗ 𝓔.V = 0 := by rw [𝓔.fv, zero_smul]
  have hVF : 𝓔.V ∘ₗ 𝓔.F = 0 := by rw [𝓔.vf, zero_smul]

  obtain ⟨XY, Ψ, hXY, hΨi, hΨq, hΨF, hΨV, hΨL⟩ :=
    exists_extPairs_blockIso 𝓗 𝓔.F 𝓔.V hFV hVF 𝓔.L i q hii hqs hexact
      (i_F p j 𝓗 𝓔 ι ιE i hi hιF hEF) (i_V p j 𝓗 𝓔 ι ιE i hi hιV hEV)
      (q_F p π 𝓗 𝓔 ι ιE q hq hιF hEF) (q_V p π 𝓗 𝓔 ι ιE q hq hιV hEV)
      (i_L₁ p j 𝓗 𝓔 ι ιE i hi hιL hEL) (i_L₂ p j 𝓗 𝓔 ι ιE i hi hιL hEL hLpure)
      (q_L₃ p π 𝓗 𝓔 ι ιE q hq hιL hEL) (q_L₄ p π 𝓗 𝓔 ι ιE q hq hιL hEL hLonto)
  exact ⟨θH, π, j, E, inferInstance, inferInstance, inferInstance, 𝓔, ιE, i, q, XY, Ψ, hrankH', hθH, hπ,
    hj, hEF, hEV, hEL, hEsmul, hi, hq, hXY, hΨi, hΨq, hΨF, hΨV, hΨL⟩

theorem main' [Finite k] (hp2 : p ≠ 2) [CharP k p]
    (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
    [Coalgebra.IsCocomm ℤ_[p] H₁] (hrank₁ : Module.finrank ℤ_[p] H₁ = Nat.card k ^ 2)
    (e₁ : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ h : H₁, g h = ResidualGaloisRep.localAut p σ (f h)) →
        e₁ g = ρbar.ρ (primeLocalToGlobal (pPrime p) σ) (e₁ f))
    (θ : k → (H₁ →ₐc[ℤ_[p]] H₁))
    (hθ : ∀ (a : k) (f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
      e₁ (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H₁ →ₐ[ℤ_[p]] H₁))) = a • e₁ f)
    (D : Type) [AddCommGroup D] [Module k D] [FiniteDimensional k D] (𝓗 : Deformation.HondaSystem (0 : k) D)
    (ι : D ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁))
    (hιF : ∀ x, ι (𝓗.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁) (ι x))
    (hιV : ∀ x, ι (𝓗.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁) (ι x))
    (hιL : ∀ x, x ∈ 𝓗.L ↔ ι x ∈ Deformation.fontaineHodge (ZMod p) p
      (Algebra.TensorProduct.includeRight : H₁ →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H₁).toRingHom)
    (hιsmul : ∀ (a : k) (x : D), ι (a • x) = Deformation.DieudonneModule.map (ZMod p) p
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θ a)) (ι x))
    (hD : Module.finrank k D = 2)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (hunipH : IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H)))
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) → e g = ρbar.dualLiftModuleActAd p c σ (e f)) :
    ∃ (θH : k → (H →ₐc[ℤ_[p]] H)) (π : H →ₐc[ℤ_[p]] H₁) (j : H₁ →ₐc[ℤ_[p]] H)
      (E : Type) (_ : AddCommGroup E) (_ : Module k E) (_ : FiniteDimensional k E)
      (𝓔 : Deformation.HondaSystem (0 : k) E)
      (ιE : E ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H))
      (i : D →ₗ[k] E) (q : E →ₗ[k] D)
      (XY : Module.End k D × Module.End k D) (Ψ : E ≃ₗ[k] D × D),
      (∃ a : ℕ, Module.finrank ℤ_[p] H = p ^ a) ∧
      IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H)) ∧
      (∀ f g, e (f * g) = e f + e g) ∧
      (∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
          e g = ρbar.dualLiftModuleActAd p c σ (e f)) ∧
      (∀ (a : k) (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        e (WithConv.toConv ((WithConv.ofConv f).comp (θH a : H →ₐ[ℤ_[p]] H))) = a • e f) ∧
      (∀ f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p),
        e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[ℤ_[p]] H₁))) = (0, e₁ f)) ∧
      (∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
        e₁ (WithConv.toConv ((WithConv.ofConv f).comp (j : H₁ →ₐ[ℤ_[p]] H))) = (e f).1) ∧
      (∀ z, ιE (𝓔.F z) =
        Deformation.DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) (ιE z)) ∧
      (∀ z, ιE (𝓔.V z) =
        Deformation.DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) (ιE z)) ∧
      (∀ z, z ∈ 𝓔.L ↔ ιE z ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H).toRingHom) ∧
      (∀ (a : k) (z : E), ιE (a • z) = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θH a)) (ιE z)) ∧
      (∀ x : D, ιE (i x) = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) j) (ι x)) ∧
      (∀ z : E, ι (q z) = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π) (ιE z)) ∧
      XY ∈ 𝓗.extPairs ∧
      (∀ x, Ψ (i x) = (x, 0)) ∧ (∀ z, (Ψ z).2 = q z) ∧
      (∀ z, Ψ (𝓔.F z) = (𝓗.F (Ψ z).1 + XY.1 (Ψ z).2, 𝓗.F (Ψ z).2)) ∧
      (∀ z, Ψ (𝓔.V z) = (𝓗.V (Ψ z).1 + XY.2 (Ψ z).2, 𝓗.V (Ψ z).2)) ∧
      (∀ z, z ∈ 𝓔.L ↔ ((Ψ z).1 ∈ 𝓗.L ∧ (Ψ z).2 ∈ 𝓗.L)) := by
  obtain ⟨θH, π, j, E, _, _, _, 𝓔, ιE, i, q, XY, Ψ, hrank, hθH, hπ, hj, hEF, hEV, hEL, hEsmul, hi, hq, hXY,
    hΨi, hΨq, hΨF, hΨV, hΨL⟩ :=
    main p hp2 hker ρbar H₁ hrank₁ e₁ he₁_add he₁_act θ hθ D 𝓗 ι hιF hιV hιL hιsmul hD c H hunipH e
      he_add he_act
  exact ⟨θH, π, j, E, inferInstance, inferInstance, inferInstance, 𝓔, ιE, i, q, XY, Ψ, hrank, hunipH, he_add,
    he_act, hθH, hπ, hj, hEF, hEV, hEL, hEsmul, hi, hq, hXY, hΨi, hΨq, hΨF, hΨV, hΨL⟩

end Construction

set_option maxHeartbeats 1600000 in
theorem main''
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (hunip : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H)) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f))
    (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
    [Coalgebra.IsCocomm ℤ_[p] H₁] (hrank₁ : Module.finrank ℤ_[p] H₁ = Nat.card k ^ 2)
    (hunip₁ : IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H₁)))
    (e₁ : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ h : H₁, g h = ResidualGaloisRep.localAut p σ (f h)) →
        e₁ g = ρbar.ρ (primeLocalToGlobal (pPrime p) σ) (e₁ f))
    (θ : k → (H₁ →ₐc[ℤ_[p]] H₁))
    (hθ : ∀ (a : k) (f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
      e₁ (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H₁ →ₐ[ℤ_[p]] H₁))) = a • e₁ f)
    (hθ_mul : ∀ a b : k, θ (a * b) = (θ a).comp (θ b)) (hθ_one : θ 1 = BialgHom.id ℤ_[p] H₁)
    (hθ_add : ∀ a b : k, WithConv.toConv (θ (a + b) : H₁ →ₐ[ℤ_[p]] H₁) =
      WithConv.toConv (θ a : H₁ →ₐ[ℤ_[p]] H₁) * WithConv.toConv (θ b : H₁ →ₐ[ℤ_[p]] H₁))
    (hθ_zero : WithConv.toConv (θ 0 : H₁ →ₐ[ℤ_[p]] H₁) = 1)
    (D : Type) [AddCommGroup D] [Module k D] [FiniteDimensional k D] (𝓗 : Deformation.HondaSystem (0 : k) D)
    (ι : D ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁))
    (hιF : ∀ x, ι (𝓗.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁) (ι x))
    (hιV : ∀ x, ι (𝓗.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁) (ι x))
    (hιL : ∀ x, x ∈ 𝓗.L ↔ ι x ∈ Deformation.fontaineHodge (ZMod p) p
      (Algebra.TensorProduct.includeRight : H₁ →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H₁).toRingHom)
    (hιsmul : ∀ (a : k) (x : D), ι (a • x) = Deformation.DieudonneModule.map (ZMod p) p
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θ a)) (ι x))
    (hD : Module.finrank k D = 2)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (hc : ρbar.IsLocallyFlatCocycleAd p c) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H) (_ : Module.Finite ℤ_[p] H)
      (_ : Module.Free ℤ_[p] H) (_ : Coalgebra.IsCocomm ℤ_[p] H)
      (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V)
      (θH : k → (H →ₐc[ℤ_[p]] H)) (π : H →ₐc[ℤ_[p]] H₁) (j : H₁ →ₐc[ℤ_[p]] H)
      (E : Type) (_ : AddCommGroup E) (_ : Module k E) (_ : FiniteDimensional k E)
      (𝓔 : Deformation.HondaSystem (0 : k) E)
      (ιE : E ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H))
      (i : D →ₗ[k] E) (q : E →ₗ[k] D)
      (XY : Module.End k D × Module.End k D) (Ψ : E ≃ₗ[k] D × D),
      (∃ a : ℕ, Module.finrank ℤ_[p] H = p ^ a) ∧
      IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H)) ∧
      (∀ f g, e (f * g) = e f + e g) ∧
      (∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
          e g = ρbar.dualLiftModuleActAd p c σ (e f)) ∧
      (∀ (a : k) (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        e (WithConv.toConv ((WithConv.ofConv f).comp (θH a : H →ₐ[ℤ_[p]] H))) = a • e f) ∧
      (∀ f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p),
        e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[ℤ_[p]] H₁))) = (0, e₁ f)) ∧
      (∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
        e₁ (WithConv.toConv ((WithConv.ofConv f).comp (j : H₁ →ₐ[ℤ_[p]] H))) = (e f).1) ∧
      (∀ z, ιE (𝓔.F z) =
        Deformation.DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) (ιE z)) ∧
      (∀ z, ιE (𝓔.V z) =
        Deformation.DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) (ιE z)) ∧
      (∀ z, z ∈ 𝓔.L ↔ ιE z ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H).toRingHom) ∧
      (∀ (a : k) (z : E), ιE (a • z) = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θH a)) (ιE z)) ∧
      (∀ x : D, ιE (i x) = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) j) (ι x)) ∧
      (∀ z : E, ι (q z) = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π) (ιE z)) ∧
      XY ∈ 𝓗.extPairs ∧
      (∀ x, Ψ (i x) = (x, 0)) ∧ (∀ z, (Ψ z).2 = q z) ∧
      (∀ z, Ψ (𝓔.F z) = (𝓗.F (Ψ z).1 + XY.1 (Ψ z).2, 𝓗.F (Ψ z).2)) ∧
      (∀ z, Ψ (𝓔.V z) = (𝓗.V (Ψ z).1 + XY.2 (Ψ z).2, 𝓗.V (Ψ z).2)) ∧
      (∀ z, z ∈ 𝓔.L ↔ ((Ψ z).1 ∈ 𝓗.L ∧ (Ψ z).2 ∈ 𝓗.L)) := by
  classical

  obtain ⟨H, _, _, hfin, hflat, hcoc, hunipH, e, he_add, he_act⟩ :=
    ResidualGaloisRep.exists_unipotent_model_of_isLocallyFlatCocycleAd_of_isLocalRing_cartierDual
      p hp2 hker ρbar hunip c hc
  haveI := hfin
  haveI := hflat
  haveI := hcoc
  haveI : Module.Free ℤ_[p] H := Module.free_of_flat_of_isLocalRing

  have hunipH' : IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H)) := hunipH
  obtain ⟨θH, π, j, E, i1, i2, i3, 𝓔, ιE, i, q, XY, Ψ, hh⟩ :=
    main' p hp2 hker ρbar H₁ hrank₁ e₁ he₁_add he₁_act θ hθ D 𝓗 ι hιF hιV hιL hιsmul hD c H hunipH' e
      he_add he_act
  exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, e, θH, π, j, E, i1, i2, i3,
    𝓔, ιE, i, q, XY, Ψ, hh⟩

end P2PresB
p2m_reactivate "P2MW.S_ResidualGaloisRep_exists_fontaineConradPresentation_of_isLocallyFlatCocycleAd.P2PresB"

open P2PresB in
theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (hunip : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H)) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f))
    (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
    [Coalgebra.IsCocomm ℤ_[p] H₁] (hrank₁ : Module.finrank ℤ_[p] H₁ = Nat.card k ^ 2)
    (hunip₁ : IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H₁)))
    (e₁ : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ h : H₁, g h = ResidualGaloisRep.localAut p σ (f h)) →
        e₁ g = ρbar.ρ (primeLocalToGlobal (pPrime p) σ) (e₁ f))
    (θ : k → (H₁ →ₐc[ℤ_[p]] H₁))
    (hθ : ∀ (a : k) (f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
      e₁ (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H₁ →ₐ[ℤ_[p]] H₁))) = a • e₁ f)
    (hθ_mul : ∀ a b : k, θ (a * b) = (θ a).comp (θ b)) (hθ_one : θ 1 = BialgHom.id ℤ_[p] H₁)
    (hθ_add : ∀ a b : k, WithConv.toConv (θ (a + b) : H₁ →ₐ[ℤ_[p]] H₁) =
      WithConv.toConv (θ a : H₁ →ₐ[ℤ_[p]] H₁) * WithConv.toConv (θ b : H₁ →ₐ[ℤ_[p]] H₁))
    (hθ_zero : WithConv.toConv (θ 0 : H₁ →ₐ[ℤ_[p]] H₁) = 1)
    (D : Type) [AddCommGroup D] [Module k D] [FiniteDimensional k D] (𝓗 : Deformation.HondaSystem (0 : k) D)
    (ι : D ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁))
    (hιF : ∀ x, ι (𝓗.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁) (ι x))
    (hιV : ∀ x, ι (𝓗.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁) (ι x))
    (hιL : ∀ x, x ∈ 𝓗.L ↔ ι x ∈ Deformation.fontaineHodge (ZMod p) p
      (Algebra.TensorProduct.includeRight : H₁ →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H₁).toRingHom)
    (hιsmul : ∀ (a : k) (x : D), ι (a • x) = Deformation.DieudonneModule.map (ZMod p) p
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θ a)) (ι x))
    (hD : Module.finrank k D = 2)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (hc : ρbar.IsLocallyFlatCocycleAd p c) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H) (_ : Module.Finite ℤ_[p] H)
      (_ : Module.Free ℤ_[p] H) (_ : Coalgebra.IsCocomm ℤ_[p] H)
      (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V)
      (θH : k → (H →ₐc[ℤ_[p]] H)) (π : H →ₐc[ℤ_[p]] H₁) (j : H₁ →ₐc[ℤ_[p]] H)
      (E : Type) (_ : AddCommGroup E) (_ : Module k E) (_ : FiniteDimensional k E)
      (𝓔 : Deformation.HondaSystem (0 : k) E)
      (ιE : E ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H))
      (i : D →ₗ[k] E) (q : E →ₗ[k] D)
      (XY : Module.End k D × Module.End k D) (Ψ : E ≃ₗ[k] D × D),
      (∃ a : ℕ, Module.finrank ℤ_[p] H = p ^ a) ∧
      IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H)) ∧
      (∀ f g, e (f * g) = e f + e g) ∧
      (∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
          e g = ρbar.dualLiftModuleActAd p c σ (e f)) ∧
      (∀ (a : k) (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        e (WithConv.toConv ((WithConv.ofConv f).comp (θH a : H →ₐ[ℤ_[p]] H))) = a • e f) ∧
      (∀ f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p),
        e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[ℤ_[p]] H₁))) = (0, e₁ f)) ∧
      (∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
        e₁ (WithConv.toConv ((WithConv.ofConv f).comp (j : H₁ →ₐ[ℤ_[p]] H))) = (e f).1) ∧
      (∀ z, ιE (𝓔.F z) =
        Deformation.DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) (ιE z)) ∧
      (∀ z, ιE (𝓔.V z) =
        Deformation.DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) (ιE z)) ∧
      (∀ z, z ∈ 𝓔.L ↔ ιE z ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H).toRingHom) ∧
      (∀ (a : k) (z : E), ιE (a • z) = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θH a)) (ιE z)) ∧
      (∀ x : D, ιE (i x) = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) j) (ι x)) ∧
      (∀ z : E, ι (q z) = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π) (ιE z)) ∧
      XY ∈ 𝓗.extPairs ∧
      (∀ x, Ψ (i x) = (x, 0)) ∧ (∀ z, (Ψ z).2 = q z) ∧
      (∀ z, Ψ (𝓔.F z) = (𝓗.F (Ψ z).1 + XY.1 (Ψ z).2, 𝓗.F (Ψ z).2)) ∧
      (∀ z, Ψ (𝓔.V z) = (𝓗.V (Ψ z).1 + XY.2 (Ψ z).2, 𝓗.V (Ψ z).2)) ∧
      (∀ z, z ∈ 𝓔.L ↔ ((Ψ z).1 ∈ 𝓗.L ∧ (Ψ z).2 ∈ 𝓗.L)) :=
  main'' p hp2 hker ρbar hunip H₁ hrank₁ hunip₁ e₁ he₁_add he₁_act θ hθ hθ_mul hθ_one hθ_add hθ_zero D 𝓗 ι hιF hιV
    hιL hιsmul hD c hc

end S_ResidualGaloisRep_exists_fontaineConradPresentation_of_isLocallyFlatCocycleAd
end P2MW
export P2MW.S_ResidualGaloisRep_exists_fontaineConradPresentation_of_isLocallyFlatCocycleAd (solution)

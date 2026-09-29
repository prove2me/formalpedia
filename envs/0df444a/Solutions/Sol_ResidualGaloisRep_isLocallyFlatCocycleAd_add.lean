-- Prove2me | solution 1 for ResidualGaloisRep.isLocallyFlatCocycleAd_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1e275705-660c-5910-a10e-a74d13d0a33f

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_model_prod
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_surjective_points_eq_of_galoisStable_addSubgroup
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_quotient_of_equivariant_surjection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_isLocallyFlatCocycleAd_add
p2m_attr_erase "instance" "instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation
open scoped PadicInt

namespace RpFlatAdd

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)

local notation "Γp" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
local notation "Z1" => cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of (ResidualGaloisRep.adRep ρbar)))

def DL (_c : Z1) : Type := ρbar.V × ρbar.V

variable {p ρbar}

def toDL (c : Z1) (x : ρbar.V × ρbar.V) : DL p ρbar c := x
def ofDL {c : Z1} (x : DL p ρbar c) : ρbar.V × ρbar.V := x

scoped instance (c : Z1) : AddCommGroup (DL p ρbar c) := inferInstanceAs (AddCommGroup (ρbar.V × ρbar.V))

@[scoped simp] theorem ofDL_toDL (c : Z1) (x : ρbar.V × ρbar.V) : ofDL (toDL c x) = x := rfl
@[scoped simp] theorem toDL_ofDL {c : Z1} (x : DL p ρbar c) : toDL c (ofDL x) = x := rfl
@[scoped simp] theorem ofDL_add {c : Z1} (x y : DL p ρbar c) : ofDL (x + y) = ofDL x + ofDL y := rfl
@[scoped simp] theorem ofDL_zero {c : Z1} : ofDL (0 : DL p ρbar c) = 0 := rfl
@[scoped simp] theorem ofDL_neg {c : Z1} (x : DL p ρbar c) : ofDL (-x) = -ofDL x := rfl
theorem ofDL_injective {c : Z1} : Function.Injective (ofDL : DL p ρbar c → ρbar.V × ρbar.V) :=
  fun _ _ h => h

noncomputable def A : Γp →* Module.End k ρbar.V :=
  show Γp →* Module.End k ρbar.V from ρbar.ρ.comp (primeLocalToGlobal (pPrime p))

theorem A_apply (σ : Γp) : A (p := p) (ρbar := ρbar) σ = ρbar.ρ (primeLocalToGlobal (pPrime p) σ) := rfl

theorem A_inv_mul_apply (σ : Γp) (v : ρbar.V) :
    ρbar.ρ (primeLocalToGlobal (pPrime p) σ)⁻¹ (A σ v) = v := by
  rw [A_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem cocycle_mul (c : Z1) (σ τ : Γp) :
    (c : Γp → Module.End k ρbar.V) (σ * τ) =
      A σ * (c : Γp → Module.End k ρbar.V) τ * ρbar.ρ (primeLocalToGlobal (pPrime p) σ)⁻¹ +
        (c : Γp → Module.End k ρbar.V) σ :=
  (mem_cocycles₁_iff (c : Γp → Module.End k ρbar.V)).mp c.2 σ τ

theorem cocycle_one (c : Z1) : (c : Γp → Module.End k ρbar.V) 1 = 0 :=
  cocycles₁_map_one c

theorem act_def (c : Z1) (σ : Γp) (x : ρbar.V × ρbar.V) :
    ρbar.dualLiftModuleActAd p c σ x =
      (A σ x.1, (c : Γp → Module.End k ρbar.V) σ (A σ x.1) + A σ x.2) := rfl

noncomputable scoped instance instAct (c : Z1) : DistribMulAction Γp (DL p ρbar c) where
  smul σ x := toDL c (ρbar.dualLiftModuleActAd p c σ (ofDL x))
  one_smul x := by
    apply ofDL_injective
    show ρbar.dualLiftModuleActAd p c (1 : Γp) (ofDL x) = ofDL x
    have h0 : (c : Γp → Module.End k ρbar.V) (1 : Γp) = 0 := cocycles₁_map_one c
    have h1 : A (p := p) (ρbar := ρbar) (1 : Γp) = 1 := map_one _
    rw [act_def, h0, h1]
    simp
  mul_smul σ τ x := by
    apply ofDL_injective
    show ρbar.dualLiftModuleActAd p c (σ * τ) (ofDL x) =
      ρbar.dualLiftModuleActAd p c σ (ρbar.dualLiftModuleActAd p c τ (ofDL x))
    rw [act_def, act_def, act_def, cocycle_mul, map_mul]
    refine Prod.ext rfl ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, map_add, A_inv_mul_apply]
    abel
  smul_zero σ := by
    apply ofDL_injective
    show ρbar.dualLiftModuleActAd p c σ (ofDL 0) = ofDL 0
    rw [act_def, ofDL_zero]
    simp
  smul_add σ x y := by
    apply ofDL_injective
    show ρbar.dualLiftModuleActAd p c σ (ofDL (x + y)) =
      ofDL (toDL c (ρbar.dualLiftModuleActAd p c σ (ofDL x)) + toDL c (ρbar.dualLiftModuleActAd p c σ (ofDL y)))
    rw [ofDL_add, ofDL_add, ofDL_toDL, ofDL_toDL, act_def, act_def, act_def]
    refine Prod.ext ?_ ?_
    · simp [map_add]
    · simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]
      abel

theorem smul_def (c : Z1) (σ : Γp) (x : DL p ρbar c) :
    σ • x = toDL c (ρbar.dualLiftModuleActAd p c σ (ofDL x)) := rfl

theorem ofDL_smul (c : Z1) (σ : Γp) (x : DL p ρbar c) :
    ofDL (σ • x) = ρbar.dualLiftModuleActAd p c σ (ofDL x) := rfl

variable (p ρbar)

theorem model_of_flat (c : Z1) (hc : ρbar.IsLocallyFlatCocycleAd p c) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ DL p ρbar c,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : Γp) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ x : H, g x = σ • (f x)) → e g = σ • (e f) := by
  obtain ⟨H, i1, i2, hfin, hfl, hco, e, he_add, he_act⟩ := hc
  exact ⟨H, i1, i2, hfin, hfl, hco, e, he_add, fun σ f g h => he_act σ f g h⟩

theorem main (c c' : Z1)
    (hc : ρbar.IsLocallyFlatCocycleAd p c) (hc' : ρbar.IsLocallyFlatCocycleAd p c') :
    ρbar.IsLocallyFlatCocycleAd p (c + c') := by
  classical
  obtain ⟨H₁, _, _, hfin₁, hfl₁, hco₁, e₁, he₁_add, he₁_act⟩ := model_of_flat p ρbar c hc
  obtain ⟨H₂, _, _, hfin₂, hfl₂, hco₂, e₂, he₂_add, he₂_act⟩ := model_of_flat p ρbar c' hc'
  haveI := hfin₁; haveI := hfl₁; haveI := hco₁; haveI := hfin₂; haveI := hfl₂; haveI := hco₂

  obtain ⟨P, _, _, hfinP, hflP, hcoP, eP, heP_add, heP_act⟩ :=
    HopfAlgebra.exists_finiteFlat_model_prod (R := ℤ_[p]) (L := PadicAlgCl p) (Γ := Γp)
      H₁ e₁ he₁_add he₁_act H₂ e₂ he₂_add he₂_act
  haveI := hfinP; haveI := hflP; haveI := hcoP

  let N : AddSubgroup (DL p ρbar c × DL p ρbar c') :=
    { carrier := {x | (ofDL x.1).1 = (ofDL x.2).1}
      add_mem' := fun {x y} hx hy => by
        show (ofDL (x.1 + y.1)).1 = (ofDL (x.2 + y.2)).1
        rw [ofDL_add, ofDL_add, Prod.fst_add, Prod.fst_add, hx, hy]
      zero_mem' := by show (ofDL (0 : DL p ρbar c)).1 = (ofDL (0 : DL p ρbar c')).1; rw [ofDL_zero, ofDL_zero]
      neg_mem' := fun {x} hx => by
        show (ofDL (-x.1)).1 = (ofDL (-x.2)).1
        rw [ofDL_neg, ofDL_neg, Prod.fst_neg, Prod.fst_neg, hx] }
  have hmemN : ∀ x, x ∈ N ↔ (ofDL x.1).1 = (ofDL x.2).1 := fun _ => Iff.rfl
  have hN : ∀ (σ : Γp) (m : DL p ρbar c × DL p ρbar c'), m ∈ N → σ • m ∈ N := by
    intro σ m hm
    rw [hmemN] at hm ⊢
    rw [Prod.smul_fst, Prod.smul_snd, ofDL_smul, ofDL_smul, act_def, act_def]
    show A σ (ofDL m.1).1 = A σ (ofDL m.2).1
    rw [hm]

  obtain ⟨HF, _, _, hfinF, hflF, hcoF, ϖ, -, hpts, huniq, haddF⟩ :=
    HopfAlgebra.exists_finiteFlat_padicInt_surjective_points_eq_of_galoisStable_addSubgroup
      p P eP heP_add heP_act N hN
  haveI := hfinF; haveI := hflF; haveI := hcoF

  letI instN : DistribMulAction Γp ↥N :=
    { smul := fun σ x => ⟨σ • (x : DL p ρbar c × DL p ρbar c'), hN σ x x.2⟩
      one_smul := fun x => Subtype.ext (one_smul _ _)
      mul_smul := fun σ τ x => Subtype.ext (mul_smul _ _ _)
      smul_zero := fun σ => Subtype.ext (smul_zero _)
      smul_add := fun σ x y => Subtype.ext (smul_add _ _ _) }
  have hsmulN : ∀ (σ : Γp) (x : ↥N), ((σ • x : ↥N) : DL p ρbar c × DL p ρbar c') = σ • (x : _) :=
    fun _ _ => rfl
  let val : WithConv (HF →ₐ[ℤ_[p]] PadicAlgCl p) → DL p ρbar c × DL p ρbar c' :=
    fun h => eP (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : P →ₐ[ℤ_[p]] HF)))
  have hval : ∀ h, val h = eP (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : P →ₐ[ℤ_[p]] HF))) :=
    fun _ => rfl
  have hbij : Function.Bijective (fun h => (⟨val h, hpts h⟩ : ↥N)) := by
    constructor
    · intro h h' hh
      have hv : val h = val h' := congrArg Subtype.val hh
      obtain ⟨h₀, -, huq⟩ := huniq (val h) (hpts h)
      exact (huq h rfl).trans (huq h' hv.symm).symm
    · intro m
      obtain ⟨h, hh, -⟩ := huniq m.1 m.2
      exact ⟨h, Subtype.ext hh⟩
  let eF : WithConv (HF →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ↥N := Equiv.ofBijective _ hbij
  have heF : ∀ h, ((eF h : ↥N) : DL p ρbar c × DL p ρbar c') = val h := fun _ => rfl
  have heF_add : ∀ f g, eF (f * g) = eF f + eF g := by
    intro f g
    apply Subtype.ext
    rw [heF, AddSubgroup.coe_add, heF, heF]
    exact haddF f g
  have heF_act : ∀ (σ : Γp) (f g : WithConv (HF →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ x : HF, g x = σ (f x)) → eF g = σ • (eF f) := by
    intro σ f g hfg
    apply Subtype.ext
    rw [heF, hsmulN, heF, hval, hval]
    apply heP_act σ
    intro y
    exact hfg (ϖ y)

  let π : ↥N →+ DL p ρbar (c + c') :=
    { toFun := fun x => toDL (c + c')
        ((ofDL (x : DL p ρbar c × DL p ρbar c').1).1,
          (ofDL (x : DL p ρbar c × DL p ρbar c').1).2 + (ofDL (x : DL p ρbar c × DL p ρbar c').2).2)
      map_zero' := by
        apply ofDL_injective
        simp only [ofDL_toDL, AddSubgroup.coe_zero, Prod.fst_zero, Prod.snd_zero, ofDL_zero, add_zero]
        rfl
      map_add' := fun x y => by
        apply ofDL_injective
        simp only [ofDL_toDL, ofDL_add, AddSubgroup.coe_add, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
        refine Prod.ext rfl ?_
        show _ = _
        abel }
  have hπ_apply : ∀ x : ↥N, ofDL (π x) =
      ((ofDL (x : DL p ρbar c × DL p ρbar c').1).1,
        (ofDL (x : DL p ρbar c × DL p ρbar c').1).2 + (ofDL (x : DL p ρbar c × DL p ρbar c').2).2) :=
    fun _ => rfl
  have hπ : Function.Surjective π := by
    intro z
    refine ⟨⟨(toDL c (ofDL z), toDL c' ((ofDL z).1, 0)), ?_⟩, ?_⟩
    · show (ofDL (toDL c (ofDL z))).1 = (ofDL (toDL c' ((ofDL z).1, 0))).1
      rw [ofDL_toDL, ofDL_toDL]
    · apply ofDL_injective
      rw [hπ_apply]
      simp only [ofDL_toDL, add_zero, Prod.mk.eta]
  have hπ_eq : ∀ (σ : Γp) (m : ↥N), π (σ • m) = σ • (π m) := by
    intro σ m
    have hm : (ofDL (m : DL p ρbar c × DL p ρbar c').1).1 = (ofDL (m : DL p ρbar c × DL p ρbar c').2).1 :=
      (hmemN _).mp m.2
    apply ofDL_injective
    rw [hπ_apply, ofDL_smul, act_def, hπ_apply, hsmulN, Prod.smul_fst, Prod.smul_snd, ofDL_smul, ofDL_smul,
      act_def, act_def, ← hm]
    refine Prod.ext rfl ?_
    have hadd : ∀ w, ((c + c' : Z1) : Γp → Module.End k ρbar.V) σ w =
        (c : Γp → Module.End k ρbar.V) σ w + (c' : Γp → Module.End k ρbar.V) σ w := fun _ => rfl
    simp only [hadd, LinearMap.add_apply, map_add]
    abel

  obtain ⟨H, iH1, iH2, hfinH, hflH, hcoH, e', he'_add, he'_act⟩ :=
    HopfAlgebra.exists_finiteFlat_padicInt_quotient_of_equivariant_surjection
      p HF eF heF_add heF_act π hπ hπ_eq
  exact ⟨H, iH1, iH2, hfinH, hflH, hcoH, e', he'_add, fun σ f g h => he'_act σ f g h⟩

end RpFlatAdd
p2m_reactivate "P2MW.S_ResidualGaloisRep_isLocallyFlatCocycleAd_add.RpFlatAdd"

theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (c c' : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (hc : ρbar.IsLocallyFlatCocycleAd p c) (hc' : ρbar.IsLocallyFlatCocycleAd p c') :
    ρbar.IsLocallyFlatCocycleAd p (c + c') :=
  RpFlatAdd.main p ρbar c c' hc hc'

end S_ResidualGaloisRep_isLocallyFlatCocycleAd_add
end P2MW
export P2MW.S_ResidualGaloisRep_isLocallyFlatCocycleAd_add (solution)

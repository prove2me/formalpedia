-- Prove2me | solution 1 for WeierstrassCurve.exists_H1_bot_ne_zero_parabolic_diamondRaw_eq_heckeT_eq_smul_of_isEigensystemH1_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8b0980dd-9241-5147-b991-eb48af7a5eaf

import Mathlib
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
import Theorems.Thm_WeierstrassCurve_not_forall_apOfModel_eq_two_of_modRepIsIrreducible
import Theorems.Thm_CohCarrier_heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_heckeT_top_apply_eq_heckeOperatorHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_H1_bot_ne_zero_parabolic_diamondRaw_eq_heckeT_eq_smul_of_isEigensystemH1_one
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy FrobeniusDensity.isMaximal_ratPrimeIdeal AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CongruenceSubgroup

namespace Ws23K4a

open CongruenceSubgroup HeckeEis
open scoped MatrixGroups

section Bridge

variable (N : ℕ) (κ : Type) [CommRing κ]

noncomputable abbrev triv : Representation κ (Gamma0 N) κ := 1

theorem coeffCoboundaries_triv_eq_bot : coeffCoboundaries (triv N κ) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun z hz => ?_
  obtain ⟨v, rfl⟩ := (mem_coeffCoboundaries_iff _ _).mp hz
  funext g
  simp [triv]

theorem mem_coeffCocycles_triv_iff (z : Gamma0 N → κ) :
    z ∈ coeffCocycles (triv N κ) ↔ ∀ g h : Gamma0 N, z (g * h) = z g + z h := by
  rw [mem_coeffCocycles_iff]
  simp [triv]

variable {N κ}

def homOfCocycle (z : ↥(coeffCocycles (triv N κ))) : Additive (Gamma0 N) →+ κ where
  toFun g := (z : Gamma0 N → κ) (Additive.toMul g)
  map_zero' := by
    have h := (mem_coeffCocycles_triv_iff N κ z).mp z.2 1 1
    rw [mul_one] at h
    have h' : (z : Gamma0 N → κ) 1 + (z : Gamma0 N → κ) 1 = (z : Gamma0 N → κ) 1 + 0 := by
      rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  map_add' g h := (mem_coeffCocycles_triv_iff N κ z).mp z.2 (Additive.toMul g) (Additive.toMul h)

@[scoped simp] theorem homOfCocycle_apply (z : ↥(coeffCocycles (triv N κ))) (g : Gamma0 N) :
    homOfCocycle z (Additive.ofMul g) = (z : Gamma0 N → κ) g := rfl

def cocycleOfHom (f : Additive (Gamma0 N) →+ κ) : ↥(coeffCocycles (triv N κ)) :=
  ⟨fun g => f (Additive.ofMul g), (mem_coeffCocycles_triv_iff N κ _).mpr fun g h => by
    rw [ofMul_mul, map_add]⟩

@[scoped simp] theorem coe_cocycleOfHom (f : Additive (Gamma0 N) →+ κ) (g : Gamma0 N) :
    (cocycleOfHom f : Gamma0 N → κ) g = f (Additive.ofMul g) := rfl

@[scoped simp] theorem homOfCocycle_cocycleOfHom (f : Additive (Gamma0 N) →+ κ) :
    homOfCocycle (cocycleOfHom f) = f := AddMonoidHom.ext fun _ => rfl

variable (N κ)

def cocycleEquiv : ↥(coeffCocycles (triv N κ)) ≃ₗ[κ] (Additive (Gamma0 N) →+ κ) where
  toFun := homOfCocycle
  invFun := cocycleOfHom
  map_add' _ _ := AddMonoidHom.ext fun _ => rfl
  map_smul' _ _ := AddMonoidHom.ext fun _ => rfl
  left_inv _ := Subtype.ext (funext fun _ => rfl)
  right_inv _ := AddMonoidHom.ext fun _ => rfl

noncomputable def H1equiv : coeffH1 (triv N κ) ≃ₗ[κ] (Additive (Gamma0 N) →+ κ) :=
  (Submodule.quotEquivOfEqBot _ (by
      rw [coeffCoboundaries_triv_eq_bot, Submodule.comap_bot, Submodule.ker_subtype])).trans
    (cocycleEquiv N κ)

theorem H1equiv_mk (z : ↥(coeffCocycles (triv N κ))) :
    H1equiv N κ (coeffH1Mk _ z) = homOfCocycle z := rfl

end Bridge

section Carrier

variable (N : ℕ)

def topEquiv : ↥(CohCarrier.GammaH N ⊤) ≃* Gamma0 N :=
  MulEquiv.subgroupCongr CohCarrier.GammaH_top

@[scoped simp] theorem coe_topEquiv (γ : ↥(CohCarrier.GammaH N ⊤)) :
    ((topEquiv N γ : Gamma0 N) : SL(2, ℤ)) = (γ : SL(2, ℤ)) := rfl

variable (κ : Type) [CommRing κ]

def carrierEquiv : (Additive (Gamma0 N) →+ κ) ≃ₗ[κ] CohCarrier.H1 N ⊤ κ where
  toFun f := f.comp (MonoidHom.toAdditive (topEquiv N).toMonoidHom)
  invFun F := F.comp (MonoidHom.toAdditive (topEquiv N).symm.toMonoidHom)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    refine AddMonoidHom.ext fun g => ?_
    show f _ = f g
    congr 1
  right_inv F := by
    refine AddMonoidHom.ext fun g => ?_
    show F _ = F g
    congr 1

theorem carrierEquiv_apply (f : Additive (Gamma0 N) →+ κ) (γ : ↥(CohCarrier.GammaH N ⊤)) :
    carrierEquiv N κ f (Additive.ofMul γ) =
      f (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) := rfl

theorem heckeT_carrierEquiv (ℓ : ℕ) [NeZero ℓ] (f : Additive (Gamma0 N) →+ κ) :
    CohCarrier.heckeT N ⊤ ℓ κ (carrierEquiv N κ f) = carrierEquiv N κ (heckeOperatorHom N ℓ κ f) := by
  refine AddMonoidHom.ext fun g => ?_
  have h := CohCarrier.heckeT_top_apply_eq_heckeOperatorHom N ℓ κ (carrierEquiv N κ f) f
    (fun γ => rfl) (Additive.toMul g)
  have h__ := h
  try simp [carrierEquiv_apply] at h__
  try simp [carrierEquiv_apply]
  exact h__

end Carrier

section Forward

variable (N : ℕ) (κ : Type) [Field κ]

theorem exists_heckeT_top_eigen (S₀ : Set ℕ) (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N (1 : Representation κ (Gamma0 N) κ)
      (fun _ => LinearMap.id) S₀ lam) :
    ∃ v : CohCarrier.H1 N ⊤ κ, v ≠ 0 ∧
      ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
        CohCarrier.heckeT N ⊤ ℓ κ v = lam ℓ • v := by
  classical
  obtain ⟨x, hx0, hx⟩ := hocc
  refine ⟨carrierEquiv N κ (H1equiv N κ x), ?_, ?_⟩
  · intro h
    apply hx0
    have h1 : H1equiv N κ x = 0 := (carrierEquiv N κ).map_eq_zero_iff.mp h
    exact (H1equiv N κ).map_eq_zero_iff.mp h1
  · intro ℓ _ hℓ hℓN hℓS
    obtain ⟨T, hT, hTx⟩ := hx ℓ hℓ hℓN hℓS

    obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
    obtain ⟨w, hw, hTz⟩ := hT z

    have hw' : homOfCocycle w = heckeOperatorHom N ℓ κ (homOfCocycle z) := by
      refine AddMonoidHom.ext fun g' => ?_
      obtain ⟨g, rfl⟩ := Additive.ofMul.surjective g'
      rw [homOfCocycle_apply, hw]
      have hz : (z : Gamma0 N → κ) = fun h => homOfCocycle z (Additive.ofMul h) :=
        funext fun _ => rfl
      rw [hz]
      exact coeffHeckeFun_trivial N ℓ (homOfCocycle z) g
    have hf : heckeOperatorHom N ℓ κ (H1equiv N κ (coeffH1Mk _ z)) =
        lam ℓ • H1equiv N κ (coeffH1Mk _ z) := by
      calc heckeOperatorHom N ℓ κ (H1equiv N κ (coeffH1Mk _ z))
          = homOfCocycle w := by rw [H1equiv_mk, hw']
        _ = H1equiv N κ (T (coeffH1Mk _ z)) := by rw [hTz, H1equiv_mk]
        _ = lam ℓ • H1equiv N κ (coeffH1Mk _ z) := by rw [hTx, map_smul]
    rw [heckeT_carrierEquiv, hf, map_smul]

end Forward

section Restrict

variable (N : ℕ) [NeZero N]

theorem levelLE_top_bot : CohCarrier.LevelLE N N (⊤ : Subgroup (ZMod N)ˣ) (⊥ : Subgroup (ZMod N)ˣ) 1 :=
  ⟨dvd_rfl, one_dvd _, fun _ _ => Subgroup.mem_top _⟩

theorem coe_iotaDeg_one (γ : ↥(CohCarrier.GammaH N ⊥)) :
    ((CohCarrier.iotaDeg N N ⊤ ⊥ 1 (levelLE_top_bot N) γ : ↥(CohCarrier.GammaH N ⊤)) : SL(2, ℤ)) =
      (γ : SL(2, ℤ)) := by
  show CohCarrier.conjLowerMat 1 (γ : SL(2, ℤ)) ((levelLE_top_bot N).dvd_entry γ) = _
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [CohCarrier.conjLowerMat]

theorem GammaH_bot_le_top : CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ) ≤ CohCarrier.GammaH N ⊤ := by
  intro A hA
  rw [CohCarrier.GammaH_top]
  exact CohCarrier.GammaH_le_Gamma0 _ hA

variable (κ : Type) [AddCommGroup κ]

def res (φ₀ : CohCarrier.H1 N ⊤ κ) : CohCarrier.H1 N ⊥ κ :=
  CohCarrier.iDeg' N N ⊤ ⊥ 1 κ (levelLE_top_bot N) φ₀

theorem res_apply (φ₀ : CohCarrier.H1 N ⊤ κ) (γ : ↥(CohCarrier.GammaH N ⊥)) :
    res N κ φ₀ (Additive.ofMul γ) = φ₀ (Additive.ofMul ⟨(γ : SL(2, ℤ)), GammaH_bot_le_top N γ.2⟩) := by
  show φ₀ (Additive.ofMul (CohCarrier.iotaDeg N N ⊤ ⊥ 1 (levelLE_top_bot N) γ)) = _
  exact congrArg (fun t : ↥(CohCarrier.GammaH N ⊤) => φ₀ (Additive.ofMul t))
    (Subtype.ext (coe_iotaDeg_one N γ))

end Restrict

section Main

theorem main
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N : ℕ) [NeZero N] (M : ℕ) [NeZero M] (S₀ : Set ℕ)
    (hS₀ : ∀ ℓ ∈ S₀, ¬ W.IsGoodPrimeFor ℓ ∨ ℓ ∣ M ∨ ℓ = p)
    (κ : Type) [Field κ] [CharP κ p]
    (hocc : HeckeEis.IsEigensystemH1 N (1 : Representation κ (Gamma0 N) κ) (fun _ => LinearMap.id) S₀
      (fun ℓ => ((W.apOfModel ℓ : ℤ) : κ))) :
    ∃ φ : CohCarrier.H1 N ⊥ κ, φ ≠ 0 ∧
      φ ∈ ModularCurve.Period.parabolicHoms κ (CohCarrier.GammaH N ⊥) κ ∧
      (∀ σ : Gamma0 N, CohCarrier.diamondRaw N ⊥ κ σ φ = φ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ¬ ℓ ∣ N → ℓ ≠ p →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT N ⊥ ℓ κ φ = ((W.apOfModel ℓ : ℤ) : κ) • φ) := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨φ₀, hφ₀0, heig⟩ := exists_heckeT_top_eigen N κ S₀ (fun ℓ => ((W.apOfModel ℓ : ℤ) : κ)) hocc

  let ι : ZMod p →+* κ := ZMod.castHom (dvd_refl p) κ
  have hι : Function.Injective ι := ι.injective
  have hcast : ∀ a : ℤ, ((a : ZMod p) = 2 ↔ ((a : κ) = 2)) := fun a => by
    rw [← hι.eq_iff, map_intCast, map_ofNat]

  set S : Set ℕ := {q | q.Prime ∧ q ∣ M} with hS
  have hSfin : S.Finite := by
    refine (Set.finite_le_nat M).subset ?_
    rintro q ⟨-, hq⟩
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hq

  have harith : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ℓ ≡ 1 [MOD p * N] → W.IsGoodPrimeFor ℓ →
      ¬ ℓ ∣ N ∧ ℓ ∉ S₀ ∧ ℓ ≡ 1 [MOD N] ∧ ((ℓ : κ) + 1 = 2) := by
    intro ℓ hℓ hℓS hℓ1 hgood
    have h1N : ℓ ≡ 1 [MOD N] := hℓ1.of_mul_left p
    have h1p : ℓ ≡ 1 [MOD p] := hℓ1.of_mul_right N
    have hℓM : ¬ ℓ ∣ M := fun h => hℓS ⟨hℓ, h⟩
    have hself : ¬ ℓ ≡ 1 [MOD ℓ] := by
      intro h
      have h' : ℓ % ℓ = 1 % ℓ := h
      rw [Nat.mod_self, Nat.mod_eq_of_lt hℓ.one_lt] at h'
      exact absurd h' (by norm_num)
    have hℓN : ¬ ℓ ∣ N := fun h => hself (h1N.of_dvd h)
    have hℓp : ℓ ≠ p := by
      rintro rfl
      exact hself h1p
    have hℓS₀ : ℓ ∉ S₀ := fun h => by
      rcases hS₀ ℓ h with h' | h' | h'
      · exact h' hgood
      · exact hℓM h'
      · exact hℓp h'
    refine ⟨hℓN, hℓS₀, h1N, ?_⟩
    have : (ℓ : κ) = ((1 : ℕ) : κ) := CharP.natCast_eq_natCast' κ p h1p
    rw [this]
    norm_num

  have hpar0 : ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH N ⊤) φ₀ := by
    have h627 := WeierstrassCurve.not_forall_apOfModel_eq_two_of_modRepIsIrreducible
      p hp2 W hΔ hirr N S hSfin
    push Not at h627
    obtain ⟨ℓ, hℓ, hℓS, hℓ1, hgood, hne⟩ := h627
    obtain ⟨hℓN, hℓS₀, h1N, h2⟩ := harith ℓ hℓ hℓS hℓ1 hgood
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hmem := CohCarrier.heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
      N ⊤ κ φ₀ ℓ hℓ hℓN h1N
    rw [heig ℓ hℓ hℓN hℓS₀, ← Nat.cast_smul_eq_nsmul κ, Nat.cast_succ, h2, ← sub_smul,
      ModularCurve.Period.mem_parabolicHoms_iff] at hmem
    have hne' : ((W.apOfModel ℓ : ℤ) : κ) - 2 ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => hne ((hcast _).mpr h)
    have : φ₀ = (((W.apOfModel ℓ : ℤ) : κ) - 2)⁻¹ • ((((W.apOfModel ℓ : ℤ) : κ) - 2) • φ₀) := by
      rw [smul_smul, inv_mul_cancel₀ hne', one_smul]
    rw [this]
    exact (ModularCurve.Period.parabolicHoms κ (CohCarrier.GammaH N ⊤) κ).smul_mem _ hmem

  refine ⟨res N κ φ₀, ?_, ?_, ?_, ?_⟩
  ·
    intro hres
    have hvan : ∀ γ : ↥(CohCarrier.GammaH N ⊤), (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma N →
        φ₀ (Additive.ofMul γ) = 0 := by
      intro γ hγ
      have hγ1 : (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ) := by
        rw [CohCarrier.mem_GammaH_iff]
        obtain ⟨-, -, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
        refine ⟨CongruenceSubgroup.Gamma0_mem.mpr h10, ?_⟩
        rw [Subgroup.mem_bot]
        apply Units.ext
        rw [CohCarrier.val_gamma0Units, Units.val_one]
        exact h11
      have h := res_apply N κ φ₀ ⟨(γ : SL(2, ℤ)), hγ1⟩
      rw [hres, AddMonoidHom.zero_apply] at h
      exact h.symm
    have heis : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N →
        CohCarrier.heckeT N ⊤ ℓ κ φ₀ = (ℓ + 1) • φ₀ := fun ℓ _ hℓ hℓN =>
      CohCarrier.heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero N κ φ₀
        ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), hvan⟩ ℓ hℓ hℓN
    refine WeierstrassCurve.not_forall_apOfModel_eq_two_of_modRepIsIrreducible
      p hp2 W hΔ hirr N S hSfin ?_
    intro ℓ hℓ hℓS hℓ1 hgood
    obtain ⟨hℓN, hℓS₀, -, h2⟩ := harith ℓ hℓ hℓS hℓ1 hgood
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have h := heis ℓ hℓ hℓN
    rw [heig ℓ hℓ hℓN hℓS₀, ← Nat.cast_smul_eq_nsmul κ, Nat.cast_succ, h2, ← sub_eq_zero,
      ← sub_smul] at h
    by_contra hne
    have hne' : ((W.apOfModel ℓ : ℤ) : κ) - 2 ≠ 0 :=
      sub_ne_zero.mpr fun e => hne ((hcast _).mpr e)
    exact hφ₀0 (by rw [← one_smul κ φ₀, ← inv_mul_cancel₀ hne', mul_smul, h, smul_zero])
  ·
    rw [ModularCurve.Period.mem_parabolicHoms_iff]
    intro γ hγ
    rw [res_apply]
    exact hpar0 _ hγ
  ·
    intro σ
    refine AddMonoidHom.ext fun g => ?_
    obtain ⟨γ, rfl⟩ := Additive.ofMul.surjective g
    show res N κ φ₀ (Additive.ofMul (CohCarrier.conjHom N ⊥ σ γ)) = res N κ φ₀ (Additive.ofMul γ)
    rw [res_apply, res_apply]
    have hσ : (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH N ⊤ := by
      rw [CohCarrier.GammaH_top]; exact σ.2
    have key : (⟨((CohCarrier.conjHom N ⊥ σ γ : ↥(CohCarrier.GammaH N ⊥)) : SL(2, ℤ)),
          GammaH_bot_le_top N (CohCarrier.conjHom N ⊥ σ γ).2⟩ : ↥(CohCarrier.GammaH N ⊤)) =
        (⟨(σ : SL(2, ℤ)), hσ⟩ : ↥(CohCarrier.GammaH N ⊤)) *
          ⟨(γ : SL(2, ℤ)), GammaH_bot_le_top N γ.2⟩ * (⟨(σ : SL(2, ℤ)), hσ⟩)⁻¹ :=
      Subtype.ext rfl
    rw [key, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
    abel
  ·
    intro ℓ hℓ hgood hℓM hℓN hℓp
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓS₀ : ℓ ∉ S₀ := fun h => by
      rcases hS₀ ℓ h with h' | h' | h'
      · exact h' hgood
      · exact hℓM h'
      · exact hℓp h'
    have hc := CohCarrier.iDeg_heckeT_comm_of_coprime (A := κ) (levelLE_top_bot N)
      (Nat.coprime_one_right ℓ) hℓ hℓN φ₀
    show CohCarrier.heckeT N ⊥ ℓ κ (CohCarrier.iDeg' N N ⊤ ⊥ 1 κ (levelLE_top_bot N) φ₀) = _
    rw [← hc, heig ℓ hℓ hℓN hℓS₀]
    exact AddMonoidHom.ext fun _ => rfl

end Main

end Ws23K4a
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_H1_bot_ne_zero_parabolic_diamondRaw_eq_heckeT_eq_smul_of_isEigensystemH1_one.Ws23K4a"

open CongruenceSubgroup in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N : ℕ) [NeZero N] (M : ℕ) [NeZero M] (S₀ : Set ℕ)
    (hS₀ : ∀ ℓ ∈ S₀, ¬ W.IsGoodPrimeFor ℓ ∨ ℓ ∣ M ∨ ℓ = p)
    (κ : Type) [Field κ] [CharP κ p]
    (hocc : HeckeEis.IsEigensystemH1 N (1 : Representation κ (Gamma0 N) κ) (fun _ => LinearMap.id) S₀
      (fun ℓ => ((W.apOfModel ℓ : ℤ) : κ))) :
    ∃ φ : CohCarrier.H1 N ⊥ κ, φ ≠ 0 ∧
      φ ∈ ModularCurve.Period.parabolicHoms κ (CohCarrier.GammaH N ⊥) κ ∧
      (∀ σ : Gamma0 N, CohCarrier.diamondRaw N ⊥ κ σ φ = φ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ¬ ℓ ∣ N → ℓ ≠ p →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT N ⊥ ℓ κ φ = ((W.apOfModel ℓ : ℤ) : κ) • φ) :=
  Ws23K4a.main p hp2 W hΔ hirr N M S₀ hS₀ κ hocc

end S_WeierstrassCurve_exists_H1_bot_ne_zero_parabolic_diamondRaw_eq_heckeT_eq_smul_of_isEigensystemH1_one
end P2MW
export P2MW.S_WeierstrassCurve_exists_H1_bot_ne_zero_parabolic_diamondRaw_eq_heckeT_eq_smul_of_isEigensystemH1_one (solution)

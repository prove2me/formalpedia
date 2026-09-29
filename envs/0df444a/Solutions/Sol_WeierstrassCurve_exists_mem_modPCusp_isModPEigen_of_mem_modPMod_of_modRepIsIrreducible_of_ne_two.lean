-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_modPCusp_isModPEigen_of_mem_modPMod_of_modRepIsIrreducible_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1e0be50f-ab04-5d92-94b3-2e65cbfe0b10

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Theorems.Thm_ModularForm_exists_cuspForm_coeffHeckeT_eq_of_modEq_one
import Theorems.Thm_WeierstrassCurve_not_forall_apOfModel_eq_two_of_modRepIsIrreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_modPCusp_isModPEigen_of_mem_modPMod_of_modRepIsIrreducible_of_ne_two
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy FrobeniusDensity.isMaximal_ratPrimeIdeal AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"
set_option autoImplicit false

open ModPForms

namespace CuspidalLowPoint

section Eis

variable {F : Type} [Field F]

private theorem coeff_heckePS (k : ℤ) (ℓ : ℕ) (φ : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff n (heckePS k ℓ φ) =
      PowerSeries.coeff (n * ℓ) φ + if ℓ ∣ n then (ℓ : F) ^ (k - 1) * PowerSeries.coeff (n / ℓ) φ else 0 := by
  simp only [heckePS, PowerSeries.coeff_mk]

private theorem heckePS_add (k : ℤ) (ℓ : ℕ) (φ ψ : PowerSeries F) :
    heckePS k ℓ (φ + ψ) = heckePS k ℓ φ + heckePS k ℓ ψ := by
  ext n
  simp only [coeff_heckePS, map_add]
  split_ifs <;> ring

private theorem heckePS_smul (k : ℤ) (ℓ : ℕ) (c : F) (φ : PowerSeries F) :
    heckePS k ℓ (c • φ) = c • heckePS k ℓ φ := by
  ext n
  simp only [coeff_heckePS, PowerSeries.coeff_smul, smul_eq_mul]
  split_ifs <;> ring

private noncomputable def heckeMinus (k : ℤ) (ℓ : ℕ) : PowerSeries F →ₗ[F] PowerSeries F where
  toFun φ := heckePS k ℓ φ - (1 + (ℓ : F) ^ (k - 1)) • φ
  map_add' φ ψ := by rw [heckePS_add, smul_add]; abel
  map_smul' c φ := by rw [heckePS_smul, RingHom.id_apply, smul_sub, smul_comm]

private theorem heckeMinus_apply (k : ℤ) (ℓ : ℕ) (φ : PowerSeries F) :
    heckeMinus k ℓ φ = heckePS k ℓ φ - (1 + (ℓ : F) ^ (k - 1)) • φ := rfl

private theorem heckeMinus_generator_mem (N' : ℕ) [NeZero N'] (k : ℤ) (hk : 1 ≤ k) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓ1 : ℓ ≡ 1 [MOD N']) (f : ModularForm (CongruenceSubgroup.Gamma0 N') k) (a : ℕ → ℤ)
    (ha : ∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    heckeMinus k ℓ (PowerSeries.mk fun n => ((a n : ℤ) : F)) ∈ modPCusp N' k F := by
  obtain ⟨g, hg⟩ := ModularForm.exists_cuspForm_coeffHeckeT_eq_of_modEq_one N' k f ℓ hℓ hℓ1
  obtain ⟨e, he⟩ : ∃ e : ℕ, k - 1 = e := ⟨(k - 1).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩

  set d : ℕ → ℤ := fun n =>
    (a (n * ℓ) + if ℓ ∣ n then ((ℓ ^ e : ℕ) : ℤ) * a (n / ℓ) else 0) - (1 + ((ℓ ^ e : ℕ) : ℤ)) * a n with hd
  have hgcoeff : ∀ n, ModularFormClass.qCoeff g n = (d n : ℂ) := by
    intro n
    have h := hg n
    rw [ModularForm.coeffHeckeT, ha, ha, he, zpow_natCast, ha] at h
    have h' : ModularFormClass.qCoeff g n =
        ((a (n * ℓ) : ℂ) + if ℓ ∣ n then (ℓ : ℂ) ^ e * (a (n / ℓ) : ℂ) else 0) - (1 + (ℓ : ℂ) ^ e) * (a n : ℂ) := by
      linear_combination -h
    rw [h', hd]
    simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_one, Nat.cast_pow]
    split_ifs <;> simp
  have hL : heckeMinus k ℓ (PowerSeries.mk fun n => ((a n : ℤ) : F)) = PowerSeries.mk fun n => ((d n : ℤ) : F) := by
    ext n
    rw [heckeMinus_apply, map_sub, coeff_heckePS, PowerSeries.coeff_smul, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk, smul_eq_mul, he, zpow_natCast, hd]
    simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_one, Nat.cast_pow]
    split_ifs <;> simp
  rw [hL]
  exact Submodule.subset_span ⟨g, d, hgcoeff, rfl⟩

private theorem heckeMinus_mem (N' : ℕ) [NeZero N'] (k : ℤ) (hk : 1 ≤ k) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓ1 : ℓ ≡ 1 [MOD N']) (ψ : PowerSeries F) (hψ : ψ ∈ modPMod N' k F) :
    heckeMinus k ℓ ψ ∈ modPCusp N' k F := by
  have hle : modPMod N' k F ≤ (modPCusp N' k F).comap (heckeMinus (F := F) k ℓ) := by
    refine Submodule.span_le.mpr ?_
    rintro φ ⟨f, a, ha, rfl⟩
    exact heckeMinus_generator_mem N' k hk ℓ hℓ hℓ1 f a ha
  exact hle hψ

end Eis

private theorem eq_two_of_isModPEigen_of_not_mem_modPCusp
    (p : ℕ) [Fact p.Prime] (N' : ℕ) [NeZero N'] (k : ℤ) (hk : 1 ≤ k) (S₀ : Set ℕ)
    (F : Type) [Field F] [CharP F p] (ψ : PowerSeries F) (mu : ℕ → F)
    (hψ : ψ ∈ modPMod N' k F) (heig : IsModPEigen N' S₀ k ψ mu) (hcusp : ψ ∉ modPCusp N' k F)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓ1 : ℓ ≡ 1 [MOD p * N']) : mu ℓ = 2 := by
  have hℓN : ℓ ≡ 1 [MOD N'] := Nat.ModEq.of_mul_left p hℓ1
  have hℓp : ℓ ≡ 1 [MOD p] := Nat.ModEq.of_mul_right N' hℓ1
  have hℓndvd : ¬ ℓ ∣ N' := by
    intro hdvd
    have hg : Nat.gcd ℓ N' = Nat.gcd 1 N' := hℓN.gcd_eq
    rw [Nat.gcd_eq_left hdvd, Nat.gcd_one_left] at hg
    exact hℓ.one_lt.ne' hg
  obtain ⟨hψ0, heq⟩ := heig
  have hT : heckePS k ℓ ψ = mu ℓ • ψ := heq ℓ hℓ hℓndvd hℓS
  have hmem := heckeMinus_mem N' k hk ℓ hℓ hℓN ψ hψ
  rw [heckeMinus_apply, hT, ← sub_smul] at hmem

  have hℓF : (ℓ : F) = 1 := by
    have := (CharP.natCast_eq_natCast F p).mpr hℓp
    simpa using this
  rw [hℓF, one_zpow] at hmem
  by_contra hne
  have hunit : mu ℓ - (1 + 1) ≠ 0 := by
    intro h
    apply hne
    have : mu ℓ = 1 + 1 := sub_eq_zero.mp h
    rw [this]; norm_num
  exact hcusp ((Submodule.smul_mem_iff _ hunit).mp hmem)

private theorem not_dvd_of_modEq_one' {ℓ N' : ℕ} (hℓ : ℓ.Prime) (hℓN : ℓ ≡ 1 [MOD N']) : ¬ ℓ ∣ N' := by
  intro hdvd
  have hg : Nat.gcd ℓ N' = Nat.gcd 1 N' := hℓN.gcd_eq
  rw [Nat.gcd_eq_left hdvd, Nat.gcd_one_left] at hg
  exact hℓ.one_lt.ne' hg

private theorem main (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N') (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀)
    (k' : ℤ) (hk' : 2 ≤ k') (j : ℕ)
    (ψ : PowerSeries (AlgebraicClosure (ZMod p))) (mu : ℕ → AlgebraicClosure (ZMod p))
    (hψ : ψ ∈ modPMod N' k' (AlgebraicClosure (ZMod p))) (heig : IsModPEigen N' S₀ k' ψ mu)
    (hmu : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
      mu ℓ = ((ℓ ^ j * W.apOfModel ℓ : ℤ) : AlgebraicClosure (ZMod p))) :
    ∃ (ψ' : PowerSeries (AlgebraicClosure (ZMod p))) (mu' : ℕ → AlgebraicClosure (ZMod p)),
      ψ' ∈ modPCusp N' k' (AlgebraicClosure (ZMod p)) ∧ IsModPEigen N' S₀ k' ψ' mu' ∧
        ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
          mu' ℓ = ((ℓ ^ j * W.apOfModel ℓ : ℤ) : AlgebraicClosure (ZMod p)) := by
  have _ := hpN'
  have _ := hS₀p
  haveI hchar : CharP (AlgebraicClosure (ZMod p)) p := inferInstance
  refine ⟨ψ, mu, ?_, heig, hmu⟩
  by_contra hcusp
  have hk1 : 1 ≤ k' := by omega
  apply WeierstrassCurve.not_forall_apOfModel_eq_two_of_modRepIsIrreducible p hp2 W hΔ hirr N' S₀ hS₀fin
  intro ℓ hℓ hℓS hℓ1 hgood
  have h2 : mu ℓ = 2 :=
    eq_two_of_isModPEigen_of_not_mem_modPCusp p N' k' hk1 S₀ (AlgebraicClosure (ZMod p)) ψ mu hψ heig hcusp ℓ hℓ hℓS hℓ1
  have hℓN : ¬ ℓ ∣ N' := not_dvd_of_modEq_one' hℓ (Nat.ModEq.of_mul_left p hℓ1)
  have hℓp : ℓ ≡ 1 [MOD p] := Nat.ModEq.of_mul_right N' hℓ1
  have hℓF : (ℓ : AlgebraicClosure (ZMod p)) = 1 := by
    have := (CharP.natCast_eq_natCast (AlgebraicClosure (ZMod p)) p).mpr hℓp
    simpa using this
  have hm : ((ℓ ^ j * W.apOfModel ℓ : ℤ) : AlgebraicClosure (ZMod p)) = 2 := by rw [← hmu ℓ hℓ hℓS hℓN hgood, h2]
  have ha : ((W.apOfModel ℓ : ℤ) : AlgebraicClosure (ZMod p)) = 2 := by
    have hm' : ((ℓ : AlgebraicClosure (ZMod p)) ^ j) * ((W.apOfModel ℓ : ℤ) : AlgebraicClosure (ZMod p)) = 2 := by
      have := hm
      push_cast at this
      exact this
    rwa [hℓF, one_pow, one_mul] at hm'
  apply (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective
  rw [map_intCast, map_ofNat]
  exact ha

end CuspidalLowPoint

theorem solution (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N') (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀)
    (k' : ℤ) (hk' : 2 ≤ k') (j : ℕ)
    (ψ : PowerSeries (AlgebraicClosure (ZMod p))) (mu : ℕ → AlgebraicClosure (ZMod p))
    (hψ : ψ ∈ modPMod N' k' (AlgebraicClosure (ZMod p))) (heig : IsModPEigen N' S₀ k' ψ mu)
    (hmu : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
      mu ℓ = ((ℓ ^ j * W.apOfModel ℓ : ℤ) : AlgebraicClosure (ZMod p))) :
    ∃ (ψ' : PowerSeries (AlgebraicClosure (ZMod p))) (mu' : ℕ → AlgebraicClosure (ZMod p)),
      ψ' ∈ modPCusp N' k' (AlgebraicClosure (ZMod p)) ∧ IsModPEigen N' S₀ k' ψ' mu' ∧
        ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
          mu' ℓ = ((ℓ ^ j * W.apOfModel ℓ : ℤ) : AlgebraicClosure (ZMod p)) :=
  CuspidalLowPoint.main p hp2 W hΔ hirr N' hpN' S₀ hS₀fin hS₀p k' hk' j ψ mu hψ heig hmu

end S_WeierstrassCurve_exists_mem_modPCusp_isModPEigen_of_mem_modPMod_of_modRepIsIrreducible_of_ne_two
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_modPCusp_isModPEigen_of_mem_modPMod_of_modRepIsIrreducible_of_ne_two (solution)

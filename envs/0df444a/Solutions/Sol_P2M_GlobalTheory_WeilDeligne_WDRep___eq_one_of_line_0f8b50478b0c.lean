-- Prove2me | solution 1 for P2M_GlobalTheory_WeilDeligne_WDRep___eq_one_of_line_0f8b50478b0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:48:19.726335+00:00
-- url     : https://prove2.me/submissions/ee55e378-d70a-439f-9f8c-aac2559dec05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LpCharCompatibilities
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_exists_eq_zpow_mul
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' V'' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']
open GlobalTheory.WeilDeligne.WDRep
namespace GlobalTheory.WeilDeligne.WDRep
theorem _root_.solution (c : WDRep h V') (hu : c.Unr) (hd : finrank ℂ V' = 1)
    (hroot : (c.ρ (frob h)).charpoly.IsRoot 1) (σ : Weil h) : c.ρ σ = 1 := by
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot).exists_hasEigenvector
  have hv1 : c.ρ (frob h) v = v := by simpa using hv.apply_eq_smul
  have hspan := (finrank_eq_one_iff_of_nonzero' v hv.2).mp hd
  have hF : c.ρ (frob h) = 1 := LinearMap.ext fun u => by
    obtain ⟨t, rfl⟩ := hspan u
    simp [hv1]
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  have hz : ∀ n : ℤ, c.ρ (frob h ^ n) = 1 := fun n => by
    have h1 : c.ρ.toHomUnits (frob h) = 1 := Units.ext hF
    have h2 : c.ρ.toHomUnits (frob h ^ n) = 1 := by rw [map_zpow, h1, one_zpow]
    exact congrArg Units.val h2
  rw [hτ, map_mul, hz, hu.2 τ, one_mul]
end GlobalTheory.WeilDeligne.WDRep

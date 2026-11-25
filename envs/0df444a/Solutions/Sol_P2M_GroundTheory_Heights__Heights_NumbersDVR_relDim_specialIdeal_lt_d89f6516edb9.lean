-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_relDim_specialIdeal_lt_d89f6516edb9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:48:45.837271+00:00
-- url     : https://prove2.me/submissions/108dd60f-d583-4688-a90c-86541095a775

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagProjSpecialDimSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagProjSpecialDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_specialIdeal_dim_add_one_le_e4698d282d3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} (P : Ideal (MRing ι O)) [P.IsPrime]
    (hPC : P.comap (C : O →+* MRing ι O) = ⊥) (n : ℕ)
    (hdim : ringKrullDim (MRing ι O ⧸ P) ≤ ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim (specialIdeal P) < ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have h := (specialIdeal_dim_add_one_le hϖ P hPC).trans hdim
  unfold FieldNumbers.relDim specialIdeal
  generalize ringKrullDim (MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) ⧸
    P.map (MvPolynomial.map (IsLocalRing.residue O))) = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) ≤ ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      have h'' : m + 1 ≤ n + Fintype.card K := by exact_mod_cast h'
      have hlt : (m : ℤ) - Fintype.card K < n := by omega
      change (((((m : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) < (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      exact_mod_cast hlt
end GroundTheory.Heights₂.Heights.NumbersDVR

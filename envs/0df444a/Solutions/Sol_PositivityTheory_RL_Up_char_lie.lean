-- Prove2me | solution 1 for PositivityTheory.RL.Up.char_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:33:38.419011+00:00
-- url     : https://prove2.me/submissions/bfadf7eb-5f16-4860-99ab-1538d648112b

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieC
import Theorems.Thm_PositivityTheory_RL_Up_exp_mul_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_GroupGeneratedByExp_trotter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace PositivityTheory.RL.Up
theorem _root_.solution [FiniteDimensional ℝ 𝔸] (S : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (hS : ∀ Z ∈ 𝔤, expU Z ∈ S)
    (hAd : ∀ Z ∈ 𝔤, ∀ Y ∈ 𝔤, NormedSpace.exp Z * Y * NormedSpace.exp (-Z) ∈ 𝔤) (χ : S →* ℂ) (hc : ContinuousAt χ 1)
    (hz : ∀ Z (h : Z ∈ 𝔤), ∃ z : ℂ, ∀ t : ℝ, χ ⟨expU (t • Z), hS _ (𝔤.smul_mem t h)⟩ = cexp (z * t)) :
    ∃ ζ : 𝔸 →ₗ[ℝ] ℂ, (∀ Z (h : Z ∈ 𝔤), ∀ t : ℝ, χ ⟨expU (t • Z), hS _ (𝔤.smul_mem t h)⟩ = cexp (ζ Z * t)) ∧
      ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, ζ (X * Y - Y * X) = 0 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  let ex : 𝔤 → S := fun Z => ⟨expU Z.1, hS _ Z.2⟩
  choose z hz using hz
  have hz' : ∀ (Z : 𝔤) (t : ℝ), χ (ex (t • Z)) = cexp (z Z.1 Z.2 * t) := fun Z t => hz Z.1 Z.2 t
  have hsm : ∀ (r : ℝ) (Z : 𝔤), z (r • Z).1 (r • Z).2 = r • z Z.1 Z.2 := fun r Z => exp_mul_inj fun t => by
    rw [← hz', smul_smul, hz', real_smul]
    congr 1
    push_cast
    ring
  have hex : ∀ X Y : 𝔤, χ (ex (X + Y)) = χ (ex X) * χ (ex Y) := fun X Y => by
    have h1 : Tendsto (fun n : ℕ => (ex (((n : ℝ)⁻¹) • X) * ex (((n : ℝ)⁻¹) • Y)) ^ n) atTop (𝓝 (ex (X + Y))) := by
      rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff, Units.isOpenEmbedding_val.isInducing.tendsto_nhds_iff]
      exact Formalism.FourierDecayAlt.P.GroupGeneratedByExp.trotter X.1 Y.1
    have h2 : Tendsto (fun n : ℕ => (ex (((n : ℝ)⁻¹) • X) * ex (((n : ℝ)⁻¹) • Y)) ^ n * (ex (X + Y))⁻¹) atTop (𝓝 1) := by
      simpa using h1.mul_const (ex (X + Y))⁻¹
    have h3 := (hc.tendsto.comp h2).mul_const (χ (ex (X + Y)))
    rw [map_one, one_mul] at h3
    refine tendsto_nhds_unique h3 (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have e : ∀ Z : 𝔤, χ (ex (((n : ℝ)⁻¹) • Z)) ^ n = χ (ex Z) := fun Z => by
      have := hz' Z 1
      rw [one_smul] at this
      rw [hz', this, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    rw [Function.comp_apply, ← map_mul χ (_ * _), inv_mul_cancel_right, map_pow, map_mul, mul_pow, e, e]
  let ζ0 : 𝔤 →ₗ[ℝ] ℂ :=
    { toFun := fun Z => z Z.1 Z.2
      map_smul' := hsm
      map_add' := fun X Y => exp_mul_inj fun t => by rw [← hz', smul_add, hex, hz', hz', ← Complex.exp_add, add_mul] }
  obtain ⟨ζ, hζ⟩ := ζ0.exists_extend
  have hζ' : ∀ Z (h : Z ∈ 𝔤), ζ Z = z Z h := fun Z h => LinearMap.congr_fun hζ ⟨Z, h⟩
  refine ⟨ζ, fun Z h t => by rw [hζ' Z h, hz], fun X hX Y hY => ?_⟩
  have hA : ∀ s : ℝ, ζ (NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • -X)) = ζ Y := fun s => by
    have hm := hAd _ (𝔤.smul_mem s hX) Y hY
    rw [smul_neg, hζ' _ hm, hζ' _ hY]
    refine exp_mul_inj fun t => ?_
    rw [← hz, ← hz]
    let g : S := ex (s • ⟨X, hX⟩)
    have e : (⟨expU (t • (NormedSpace.exp (s • X) * Y * NormedSpace.exp (-(s • X)))), hS _ (𝔤.smul_mem t hm)⟩ : S) =
        g * ⟨expU (t • Y), hS _ (𝔤.smul_mem t hY)⟩ * g⁻¹ := by
      refine Subtype.ext (Units.ext ?_)
      have := NormedSpace.exp_units_conj (expU (s • X)) (t • Y)
      rw [mul_smul_comm, smul_mul_assoc] at this
      exact this
    rw [e, map_mul, map_mul, mul_right_comm, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have h1 := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0).mul_const Y).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0)
  have h2 := ζ.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 : HasDerivAt (fun s : ℝ => ζ (NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • -X))) 0 0 := by
    simp only [hA]
    exact hasDerivAt_const _ _
  have := h2.unique h3
  simpa [sub_eq_add_neg] using this
end PositivityTheory.RL.Up

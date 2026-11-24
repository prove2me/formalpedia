-- Prove2me | solution 1 for PI.VolStabSW.quadCoord_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:42.315485+00:00
-- url     : https://prove2.me/submissions/9dc62558-5e92-4727-b5e1-6a366785f6ac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfCo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
open PI.AdicCompletionValuation
namespace PI.VolStabSW
theorem _root_.solution : QuadCoord := by
  intro V H _ _ _ _ n m eV eH Q β hV hH hβc hβa hβs hQ
  have hVs : ∀ y z, eV.symm (y + z) = eV.symm y + eV.symm z := by
    intro y z; apply eV.injective; rw [hV]; simp
  let b : (Fin n → ℝ) → (Fin n → ℝ) → (Fin m → ℝ) := fun y z => eH (β (eV.symm y) (eV.symm z))
  have hb1 : ∀ y y' z, b y z + b y' z = b (y + y') z := by
    intro y y' z; simp only [b, hVs, hβa, hH]
  have hb2 : ∀ y z z', b y (z + z') = b y z + b y z' := by
    intro y z z'; simp only [b, hVs]
    rw [hβs, hβa, hH, hβs (eV.symm z), hβs (eV.symm z')]
  have hbc : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => b p.1 p.2) :=
    eH.continuous.comp (hβc.comp ((eV.symm.continuous.comp continuous_fst).prodMk
      (eV.symm.continuous.comp continuous_snd)))
  let L1 : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) := fun y =>
    AddMonoidHom.toRealLinearMap (AddMonoidHom.mk' (b y) (hb2 y))
      (hbc.comp (continuous_const.prodMk continuous_id))
  have hL1 : ∀ y z, L1 y z = b y z := fun _ _ => rfl
  have hsm1 : ∀ (c : ℝ) y z, b (c • y) z = c • b y z := by
    intro c y z
    have : b (c • y) z = c • b y z := (AddMonoidHom.toRealLinearMap (AddMonoidHom.mk' (fun y => b y z)
      (fun y y' => (hb1 y y' z).symm)) (hbc.comp (continuous_id.prodMk continuous_const))).map_smul c y
    exact this
  let Bl : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
    { toFun := L1
      map_add' := fun y y' => by ext1 z; simp only [add_apply, hL1, hb1]
      map_smul' := fun c y => by
        ext1 z; simp only [smul_apply, hL1, hsm1, RingHom.id_apply] }
  let B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) := LinearMap.toContinuousLinearMap Bl
  have hB : ∀ y z, B y z = b y z := fun _ _ => rfl
  have hf : ∀ y, eH (Q (eV.symm y)) = (1/2 : ℝ) • B y y := by
    intro y
    rw [hB]
    simp only [b, hQ, hH]
    rw [← two_smul ℝ (eH (Q (eV.symm y))), smul_smul]
    norm_num
  have hfe : (fun y => eH (Q (eV.symm y))) = fun y => (1/2 : ℝ) • B y y := funext hf
  have hd : ∀ y, HasFDerivAt (fun y => (1/2 : ℝ) • B y y)
      ((1/2 : ℝ) • (B.precompR (Fin n → ℝ) y (ContinuousLinearMap.id ℝ _) +
        B.precompL (Fin n → ℝ) (ContinuousLinearMap.id ℝ _) y)) y :=
    fun y => by
      have h := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)).const_smul
        (1/2 : ℝ)
      exact h
  refine ⟨?_, fun x y => ?_⟩
  · rw [hfe]
    exact (B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)).const_smul
      (1/2 : ℝ)
  · rw [hfe, (hd _).fderiv]
    show (1/2 : ℝ) • (B (eV x) (eV y) + B (eV y) (eV x)) = eH (β x y)
    rw [hB, hB]
    simp only [b, Homeomorph.symm_apply_apply]
    rw [hβs y x, ← two_smul ℝ (eH (β x y)), smul_smul]
    norm_num
end PI.VolStabSW

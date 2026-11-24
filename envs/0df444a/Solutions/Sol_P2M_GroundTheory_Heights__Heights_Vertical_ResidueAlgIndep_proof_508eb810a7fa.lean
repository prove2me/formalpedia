-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ResidueAlgIndep_proof_508eb810a7fa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:58.97466+00:00
-- url     : https://prove2.me/submissions/aa737e86-7ec8-4552-8c82-6de32bfca669

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PResidueAlgIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace ResidueAlgIndep
theorem _root_.solution : ResidueAlgIndep.Statement := by
  intro K _ _ e n v
  have : v.asIdeal.IsMaximal := v.isMaximal
  let R := ParDVR e n v
  let E := (IsLocalRing.maximalIdeal R).ResidueField
  let k := v.asIdeal.ResidueField
  let _ : Algebra k E := (resToKappa e n v).toAlgebra
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective v.asIdeal) p

  have hext : (eval₂Hom ((algebraMap k E).comp (algebraMap (𝓞 K) k)) (parYκ e n v)) =
      (algebraMap R E).comp (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]
      rw [← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) R]
      exact Ideal.ResidueField.map_algebraMap _ _ _ _ a
    · simp [parYκ, parY, R, E]
  have key : aeval (parYκ e n v) (MvPolynomial.map (algebraMap (𝓞 K) k) q) =
      algebraMap R E (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R q) := by
    rw [aeval_def, eval₂_map]
    exact congrArg (fun φ => φ q) hext
  rw [key, Ideal.algebraMap_residueField_eq_zero] at hp
  have hq : q ∈ parPrime e n v := by
    have h2 : (IsLocalRing.maximalIdeal R).comap (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R) =
        parPrime e n v :=
      Localization.AtPrime.under_maximalIdeal
    rw [← h2]
    exact hp
  rw [parPrime, MvPolynomial.mem_map_C_iff] at hq
  ext m
  rw [coeff_map, coeff_zero]
  exact Ideal.algebraMap_residueField_eq_zero.mpr (hq m)
end ResidueAlgIndep
end GroundTheory.Heights₂.Heights.Vertical

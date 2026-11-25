-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_point_d98209b0a482
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:00:57.385843+00:00
-- url     : https://prove2.me/submissions/869a523a-f0ec-4b37-89f5-6a4f07909d36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualCurvePoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_eq_zero_of_mem_3ac1f31f332f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_eval__ratio_eq_zero_of_le_870ab3fe7cbc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_eq_c5bae4ee8eec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_smul_86362b669f83
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_single_46d578258d2e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_dualLatticeCoord_eq_d4438b97a002
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_eval_eq_080797a46129
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_X_mem_of_eq_zero_e9e44dbdbf54


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualCurvePointAlt
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} [Fintype T]
  [DecidableEq T]
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.DualCurvePointAlt
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice F)) {L : Type} [Field L] [CharZero L]
    (z : (Σ _ : Unit, T) → L) (t0 : T) (hz : z ⟨(), t0⟩ = 1) (hle : dualIdeal b ≤ mCoordIdeal z) :
    ∃ (_ : Algebra K L) (v : Fin i → L), v ≠ 0 ∧ dualPointCoord b v = z := by
  have hu : dualLatticeCoord b ⟨(), t0⟩ ≠ 0 := fun h0 => by
    have hX : (X ⟨(), t0⟩ : MRing (dualBlocks T)) ∈ mCoordIdeal z :=
      hle (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.X_mem_of_eq_zero h0)
    have := aeval_eq_zero_of_mem hX
    rw [eval₂_X, hz] at this
    exact one_ne_zero this
  let ev : MvPolynomial (Σ _ : Unit, T) ℚ →+* ProjField K i :=
    eval₂Hom (Rat.castHom _) fun p => dualLatticeCoord b p / dualLatticeCoord b ⟨(), t0⟩
  let ev2 : MvPolynomial (Σ _ : Unit, T) ℚ →+* L := eval₂Hom (Rat.castHom L) z
  have hker : ∀ g ∈ RingHom.ker ev, ev2 g = 0 := fun g hg => by
    have h := eval₂_ratio_eq_zero_of_le hle (fun _ => t0) (fun _ => hu)
      (fun _ => by rw [hz]; exact one_ne_zero) (RingHom.mem_ker.1 hg)
    have e : (fun p : Σ _ : Unit, T => z p / z ⟨p.1, (fun _ : Unit => t0) p.1⟩) = z := by
      funext ⟨⟨⟩, t⟩
      show z ⟨(), t⟩ / z ⟨(), t0⟩ = z ⟨(), t⟩
      rw [hz, div_one]
    show eval₂ (Rat.castHom L) z g = 0
    rw [← e]
    exact h
  let ψ : ev.range →+* L :=
    (Ideal.Quotient.lift (RingHom.ker ev) ev2 hker).comp ev.quotientKerEquivRange.symm.toRingHom
  have hψ : ∀ g, ψ ⟨ev g, g, rfl⟩ = ev2 g := fun g => by
    show Ideal.Quotient.lift _ ev2 hker (ev.quotientKerEquivRange.symm ⟨ev g, g, rfl⟩) = ev2 g
    rw [show ev.quotientKerEquivRange.symm ⟨ev g, g, rfl⟩ = Ideal.Quotient.mk _ g from
      (RingEquiv.symm_apply_eq _).2 rfl]
    rfl
  have hmem : ∀ w, linVal w / dualLatticeCoord b ⟨(), t0⟩ ∈ ev.range := fun w => by
    obtain ⟨g, hg⟩ := exists_eval_eq b t0 w
    exact ⟨g, hg⟩
  have hκ : ∀ a, constK K i a ∈ ev.range := fun a => by
    have h := hmem (a • (b t0 : Fin i → K))
    rwa [linVal_smul, ← dualLatticeCoord_eq, mul_div_assoc, div_self hu, mul_one] at h
  let lam : K →+* L := ψ.comp ((constK K i).codRestrict ev.range hκ)
  let _ : Algebra K L := lam.toAlgebra
  let v : Fin i → L := fun j => ψ ⟨linVal (Pi.single j 1) / dualLatticeCoord b ⟨(), t0⟩, hmem _⟩
  have hv : dualPointCoord b v = z := by
    funext p
    obtain ⟨⟨⟩, t⟩ := p
    have e : (∑ j, (constK K i).codRestrict ev.range hκ ((b t : Fin i → K) j) *
        (⟨linVal (Pi.single j 1) / dualLatticeCoord b ⟨(), t0⟩, hmem _⟩ : ev.range)) =
          ⟨ev (X ⟨(), t⟩), X ⟨(), t⟩, rfl⟩ := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, RingHom.codRestrict_apply]
      rw [show ev (X ⟨(), t⟩) = dualLatticeCoord b ⟨(), t⟩ / dualLatticeCoord b ⟨(), t0⟩ from eval₂_X _ _ _,
        dualLatticeCoord_eq b t, linVal_eq (b t : Fin i → K), Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [linVal_single, mul_div_assoc]
    have h2 := congrArg ψ e
    rw [map_sum, hψ] at h2
    simp only [map_mul] at h2
    rw [show ev2 (X ⟨(), t⟩) = z ⟨(), t⟩ from eval₂_X _ _ _] at h2
    rw [← h2]
    rfl
  refine ⟨lam.toAlgebra, v, fun h0 => ?_, hv⟩
  have := congrFun hv ⟨(), t0⟩
  rw [h0, hz] at this
  simp [dualPointCoord] at this
end GroundTheory.Heights₂.Heights.DualCurvePointAlt

-- Prove2me | solution 1 for PI.OddDualWeyl.twistedWeylStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:31:13.371145+00:00
-- url     : https://prove2.me/submissions/dcc42a93-94ec-4cae-92c5-b4d96c7fabe5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Theorems.Thm_PI_OddDualWeyl_Red_rowAct_rowAct
import Theorems.Thm_PI_OddDualWeyl_Red_rowAct_one
import Theorems.Thm_PI_OddDualWeyl_Red_rowAct_homog
import Theorems.Thm_PI_OddDualWeyl_Red_map_dualSub
import Theorems.Thm_PI_OddDualWeyl_Red_map_det_genM
import Theorems.Thm_PI_OddDualWeyl_Red_det_inv_eq
import Theorems.Thm_PI_OddDualWeyl_Red_relK
import Theorems.Thm_PI_OddDualWeyl_Red_zp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Matrix
noncomputable section
namespace PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
section Field
variable {K : Type*} [Field K] {k : ℕ}
end Field
end PI.OddDualWeyl.Red
namespace PI.OddDualWeyl
open Red
private theorem mem_twisted_weyl_det_iff {O K : Type*} [CommRing O] [Field K] [Algebra O K] (m : ℕ)
    (lam : Fin (m + 1) → ℤ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    F ∈ deltaLTw O K m lam g ↔ ∃ F0 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K,
      (∃ f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam),
        MvPolynomial.map (algebraMap O K) f = rowAct K g F0) ∧ g.det ^ (-(lam (Fin.last m))) • F0 = F := by
  unfold deltaLTw deltaL
  simp only [Submodule.mem_map, Submodule.mem_comap]
  first
  | rfl
  | (simp only [LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, LinearMap.lsmul_apply,
      MvPolynomial.mapAlgHom_apply]; rfl)
  | exact Iff.rfl
end PI.OddDualWeyl
end
end

set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open Red
namespace PI.OddDualWeyl
theorem _root_.solution : GStep := by
  unfold GStep
  intro O K _ _ _ m lam g hg hbal hhom hdual F hF
  have hd : g.det ≠ 0 := hg.ne_zero
  obtain ⟨F0, ⟨f, hf, hfF⟩, rfl⟩ := (mem_twisted_weyl_det_iff m lam g F).mp hF
  obtain ⟨f', hf', hrel⟩ := hdual f hf
  have hrelK : Rel K (m + 1) (expM lam) (MvPolynomial.map (algebraMap O K) f)
      (MvPolynomial.map (algebraMap O K) f') := by
    have h0 : dualSub O (m + 1) f' = (genM O (m + 1)).det ^ expM lam * f := hrel
    show dualSub K (m + 1) (MvPolynomial.map (algebraMap O K) f') =
      (genM K (m + 1)).det ^ expM lam * MvPolynomial.map (algebraMap O K) f
    rw [← PI.OddDualWeyl.Red.map_dualSub, h0, _root_.map_mul, _root_.map_pow,
      PI.OddDualWeyl.Red.map_det_genM]
  have hhomK : (MvPolynomial.map (algebraMap O K) f').IsHomogeneous
      (degW (nuOf (lamStar lam))) := by
    first
    | exact (hhom f' hf').map _
    | (intro d hd0; apply hhom f' hf'; intro h0; apply hd0; rw [coeff_map, h0, _root_.map_zero])
  have hF0 : rowAct K g⁻¹ (MvPolynomial.map (algebraMap O K) f) = F0 := by
    rw [hfF, PI.OddDualWeyl.Red.rowAct_rowAct, Matrix.mul_nonsing_inv g hg, PI.OddDualWeyl.Red.rowAct_one]
  have hT : gᵀ * (g⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul g hg, Matrix.transpose_one]
  have hdetT : ((g⁻¹)ᵀ).det = (g.det)⁻¹ := by
    rw [Matrix.det_transpose, PI.OddDualWeyl.Red.det_inv_eq]
  refine ⟨((g⁻¹)ᵀ.det ^ (-(lamStar lam (Fin.last m)))) •
    rowAct K gᵀ (MvPolynomial.map (algebraMap O K) f'), ?_, ?_, ?_⟩
  · rw [mem_twisted_weyl_det_iff]
    refine ⟨rowAct K gᵀ (MvPolynomial.map (algebraMap O K) f'), ⟨f', hf', ?_⟩, rfl⟩
    rw [PI.OddDualWeyl.Red.rowAct_rowAct, hT, PI.OddDualWeyl.Red.rowAct_one]
  · show dualSub K (m + 1) _ = (genM K (m + 1)).det ^ expM lam * _
    rw [← hF0]
    apply PI.OddDualWeyl.Red.relK g hd hrelK hhomK
    rw [hdetT]
    exact PI.OddDualWeyl.Red.zp g.det hd _ _ _ _ hbal
  · have hC : IsHomogeneous (C ((g⁻¹)ᵀ.det ^ (-(lamStar lam (Fin.last m)))) :
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) 0 := by
      first | exact isHomogeneous_C _ _ | exact isHomogeneous_C _
    have h1 := hC.mul (PI.OddDualWeyl.Red.rowAct_homog gᵀ hhomK)
    rw [zero_add] at h1
    rw [MvPolynomial.smul_eq_C_mul]
    exact h1
end PI.OddDualWeyl

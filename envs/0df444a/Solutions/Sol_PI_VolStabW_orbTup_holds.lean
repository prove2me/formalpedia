-- Prove2me | solution 1 for PI.VolStabW.orbTup_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:10.52631+00:00
-- url     : https://prove2.me/submissions/7f4f5893-6b4d-4949-bbf3-7c95751715fd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_OrbRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HformSmulLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_InclRAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_LocalSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StFix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_ExistsOrthogonalFamily
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_OrbTupFin
import Theorems.Thm_PI_VolStabW_cm_fixed
import Theorems.Thm_Formalism_UG_P_hform_eq_dot
import Theorems.Thm_PIW_AdelicOrbitU_hform_conj
import Theorems.Thm_PIW_AdelicOrbitU_hform_eq_dot
import Theorems.Thm_PIW_AdelicOrbitU_hform_smul_right
import Theorems.Thm_PIW_AdelicOrbitU_inclR_algebraMap
import Theorems.Thm_PIW_AdelicOrbitU_isHerm_JR
import Theorems.Thm_PIW_AdelicOrbitU_isUnit_det_JR
import Theorems.Thm_PIW_AdelicOrbitU_sigR_inclR
import Theorems.Thm_PIW_AdelicOrbitU_stFix
import Theorems.Thm_PIW_AdelicOrbitU_stLam
import Theorems.Thm_PIW_AdelicOrbitU_stP
import Theorems.Thm_PI_UnitaryGroupMassFormula_HermConj_exists_orthogonal_family
import Theorems.Thm_PI_VolStabW_OrbR_gram_mul
import Theorems.Thm_PI_VolStabW_OrbR_gram_tM
import Theorems.Thm_PI_VolStabW_OrbR_orb_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix Formalism.UG PI.VolStabW.OrbR
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution : OrbTup := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet y hy
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hfix := cm_fixed σ hCM
  set T := gramE σ J X0 with hTdef
  let sE : E →+* E := σ
  have hTH : IsHerm sE T := by
    ext i j; exact hT i j
  have hh : PI.UnitaryGroupMassFormula.HermConj.IsHermForm sE (hform sE T) :=
    { add := fun x y z => by
        rw [PIW.AdelicOrbitU.hform_eq_dot, PIW.AdelicOrbitU.hform_eq_dot,
          PIW.AdelicOrbitU.hform_eq_dot, mulVec_add, dotProduct_add]
      smul := fun x c y => PIW.AdelicOrbitU.hform_smul_right sE T c x y
      herm := fun x y => (PIW.AdelicOrbitU.hform_conj sE T hinv hTH x y).symm }
  obtain ⟨v, hvli, hvo⟩ := PI.UnitaryGroupMassFormula.HermConj.exists_orthogonal_family sE a (Fin a → E)
    (by simp) (hform sE T) hh
  set P : Matrix (Fin a) (Fin a) E := tM v with hP
  have hPu : IsUnit P.det := by
    have h1 : IsUnit (Matrix.of v) := Matrix.linearIndependent_rows_iff_isUnit.mp hvli
    have h2 : P = (Matrix.of v)ᵀ := rfl
    rw [h2, det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp h1
  set D := cT sE P * T * P with hD
  have hDv : ∀ j k, hform sE T (v j) (v k) = D j k := fun j k => gram_tM sE T v j k
  have hDoff : ∀ j k, j ≠ k → D j k = 0 := fun j k hjk => by rw [← hDv]; exact hvo j k hjk
  have hDdiag : D = Matrix.diagonal fun j => D j j := by
    ext j k
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [hDoff j k hjk, Matrix.diagonal_apply_ne _ hjk]
  have hDdet : D.det ≠ 0 := by
    have hc : (cT sE P).det = sE P.det := by
      rw [cT, det_transpose, RingHom.map_det]; rfl
    rw [hD, det_mul, det_mul, hc]
    refine mul_ne_zero (mul_ne_zero ?_ hdet) hPu.ne_zero
    exact (map_ne_zero sE).mpr hPu.ne_zero
  have hDne : ∀ j, D j j ≠ 0 := by
    intro j
    rw [hDdiag, det_diagonal] at hDdet
    exact Finset.prod_ne_zero_iff.mp hDdet j (Finset.mem_univ j)
  have hDfix : ∀ j, σ (D j j) = D j j := fun j => by
    rw [← hDv]; exact PIW.AdelicOrbitU.hform_conj sE T hinv hTH _ _

  let R := AF F
  let sS := sigR R σ
  let JS := JR (F := F) R J
  have hsS : ∀ z, sS (sS z) = z := (PIW.AdelicOrbitU.stFix F E σ h2 hfix R).1
  have hJS : IsHerm sS JS := PIW.AdelicOrbitU.isHerm_JR R σ J hJ.1
  have hJSd : IsUnit JS.det := PIW.AdelicOrbitU.isUnit_det_JR (F := F) R J hJ.2
  have hcTmap : ∀ {p q : ℕ} (N : Matrix (Fin p) (Fin q) E),
      cT sS (N.map (inclR (F := F) R)) = (cT sE N).map (inclR (F := F) R) := by
    intro p q N; ext i j
    simp only [cT, Matrix.map_apply, Matrix.transpose_apply]
    exact PIW.AdelicOrbitU.sigR_inclR (F := F) R σ _
  set Xm : Matrix (Fin M) (Fin a) (R ⊗[F] E) := (tM X0).map (inclR (F := F) R) with hXm
  set Pm : Matrix (Fin a) (Fin a) (R ⊗[F] E) := P.map (inclR (F := F) R) with hPm
  have hTg : cT sE (tM X0) * J * tM X0 = T := by
    ext i j; rw [← gram_tM]; rfl
  have hyg : cT sS (tM y) * JS * tM y = T.map (inclR (F := F) R) := by
    ext i j; rw [← gram_tM]; exact congrFun (congrFun hy i) j
  let x' : Fin a → Fin M → R ⊗[F] E := fun j r => (Xm * Pm) r j
  let y' : Fin a → Fin M → R ⊗[F] E := fun j r => (tM y * Pm) r j
  have hGx : ∀ j k, hform sS JS (x' j) (x' k) = inclR (F := F) R (D j k) := by
    intro j k
    rw [gram_tM]
    have e : tM x' = Xm * Pm := rfl
    rw [e, gram_mul, hXm, hPm, hcTmap, hcTmap]
    show ((cT sE P).map (inclR (F := F) R) * ((cT sE (tM X0)).map (inclR (F := F) R) * J.map (inclR (F := F) R) *
      (tM X0).map (inclR (F := F) R)) * P.map (inclR (F := F) R)) j k = _
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hTg]
    rfl
  have hGy : ∀ j k, hform sS JS (y' j) (y' k) = inclR (F := F) R (D j k) := by
    intro j k
    rw [gram_tM]
    have e : tM y' = tM y * Pm := rfl
    rw [e, gram_mul, hyg, hPm, hcTmap, ← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  obtain ⟨g, hgU, hgx⟩ := orb_orth sS JS hsS hJS hJSd a x' y'
    (fun j k hjk => by rw [hGx, hDoff j k hjk, map_zero])
    (fun j k => by rw [hGx, hGy])
    (fun j => by rw [hGx]; exact (isUnit_iff_ne_zero.mpr (hDne j)).map _)
    (fun j t => by
      obtain ⟨β, hβ⟩ := (hfix _).mp (hDfix j)
      have hβ0 : β ≠ 0 := by
        rintro rfl; exact hDne j (by rw [← hβ, map_zero])
      obtain ⟨lam, hlam, hu⟩ := PIW.AdelicOrbitU.stLam F E σ h2 hfix R (PIW.AdelicOrbitU.stP F) t β hβ0
      refine ⟨lam, hlam, ?_⟩
      rw [hGx, ← hβ, PIW.AdelicOrbitU.inclR_algebraMap]
      exact hu)
  have hmat : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm * Pm = tM y * Pm := by
    ext r j
    rw [Matrix.mul_assoc]
    have := congrFun (hgx j) r
    simpa [x', y', Matrix.mul_apply, mulVec, dotProduct] using this
  have hPmu : IsUnit Pm.det := by
    show IsUnit ((inclR (F := F) R).mapMatrix P).det
    rw [← RingHom.map_det]; exact hPu.map _
  have hmat2 : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm = tM y := by
    have := congrArg (fun N => N * Pm⁻¹) hmat
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hPmu] using this
  refine ⟨(⟨g, hgU⟩ : HR (AF F) σ J), ?_⟩
  funext i
  funext r
  show ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ ratTup (AF F) X0 i) r = y i r
  have := congrFun (congrFun hmat2 r) i
  simpa [Xm, tM, ratTup, Matrix.mul_apply, mulVec, dotProduct] using this
end PI.VolStabW

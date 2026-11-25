-- Prove2me | solution 1 for PI.WGL.LTA.rowGen_gmin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:35:48.050493+00:00
-- url     : https://prove2.me/submissions/5d536c46-5ad5-423f-a699-7271e9cd6682

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
import Theorems.Thm_PI_WGL_LTA_rowGen_Xz
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTA
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL.LTA
theorem _root_.solution {r c m : ℕ} (a b : Fin r) (ρ : Fin m → Fin r) (κ : Fin m → Fin c) :
    rowGen ℤ a b (gmin ρ κ) =
      ∑ S : Finset (Fin m), if (∀ p ∈ S, ρ p = b) then
        Polynomial.X ^ S.card * Polynomial.C (gmin (upd ρ S a) κ) else 0 := by
  classical
  set A : Equiv.Perm (Fin m) → Fin m → Polynomial (MvPolynomial (Fin r × Fin c) ℤ) :=
    fun σ i => Polynomial.C (X (ρ i, κ (σ i))) with hA
  set B : Equiv.Perm (Fin m) → Fin m → Polynomial (MvPolynomial (Fin r × Fin c) ℤ) :=
    fun σ i => if ρ i = b then Polynomial.X * Polynomial.C (X (a, κ (σ i))) else 0 with hB
  have h1 : rowGen ℤ a b (gmin ρ κ) =
      ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ • ∏ i, (B σ i + A σ i) := by
    unfold gmin
    rw [AlgHom.map_det, ← Matrix.det_transpose, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Matrix.transpose_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowGen_Xz,
      hA, hB]
    ring
  have h2 : ∀ S : Finset (Fin m), gmin (upd ρ S a) κ =
      ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ •
        ∏ i, (X (upd ρ S a i, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ) := by
    intro S
    unfold gmin
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  rw [h1]
  simp only [Finset.prod_add, Finset.smul_sum]
  rw [Finset.sum_comm, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs with hS
  · rw [h2, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hBS : ∏ i ∈ S, B σ i =
        Polynomial.X ^ S.card * Polynomial.C (∏ i ∈ S, (X (a, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ)) := by
      rw [Finset.prod_congr rfl (fun i hi => show B σ i = Polynomial.X * Polynomial.C (X (a, κ (σ i))) by
        simp [hB, hS i hi])]
      rw [Finset.prod_mul_distrib, Finset.prod_const, map_prod]
    have hAS : ∏ i ∈ Finset.univ \ S, A σ i =
        Polynomial.C (∏ i ∈ Finset.univ \ S, (X (ρ i, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ)) := by
      rw [map_prod]
    have hprod : (∏ i ∈ Finset.univ \ S, (X (ρ i, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ)) *
        (∏ i ∈ S, (X (a, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ)) =
        ∏ i, (X (upd ρ S a i, κ (σ i)) : MvPolynomial (Fin r × Fin c) ℤ) := by
      rw [← Finset.prod_sdiff (Finset.subset_univ S)]
      congr 1
      · refine Finset.prod_congr rfl fun i hi => ?_
        simp [upd, (Finset.mem_sdiff.mp hi).2]
      · refine Finset.prod_congr rfl fun i hi => ?_
        simp [upd, hi]
    rw [hBS, hAS, ← hprod, Units.smul_def, Units.smul_def, map_zsmul, map_mul]
    simp only [zsmul_eq_mul]
    ring
  · push_neg at hS
    obtain ⟨p, hp, hpb⟩ := hS
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [Finset.prod_eq_zero hp (by simp [hB, hpb]), zero_mul, smul_zero]
end PI.WGL.LTA

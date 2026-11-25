-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.rational_points_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:20.940973+00:00
-- url     : https://prove2.me/submissions/855efb07-63cf-4a00-bf56-9c2976b27e0a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_single_tmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_nsmul_tmul_F
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UJClassFin_mulVec_single__bf9be0aca3c7
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_latHat_smul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_single_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_Oh_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_approx
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_den
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_intAf_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_low_nat
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_tmul_mem_Oh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution : RatDense := by
  intro F E _ _ _ _ _ σ M J L _h4 h5 h y
  classical
  obtain ⟨k, hk, hkL⟩ := low_nat L h5
  set g' := finMat σ J h⁻¹ with hg'
  have hden : ∃ m : ℕ, 0 < m ∧ ∀ l j, m • g' l j ∈ Oh F E := by
    choose mf hmf hmO using fun p : Fin M × Fin M => den (g' p.1 p.2)
    refine ⟨∏ p, mf p, Finset.prod_pos (fun p _ => hmf p), fun l j => ?_⟩
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem mf (Finset.mem_univ (l, j))
    rw [hq, mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ (hmO (l, j)) _
  obtain ⟨m, hm, hmO⟩ := hden
  have K1 : ∀ o ∈ Oh F E, ∀ j, g'.mulVec (Pi.single j ((k * m) • o)) ∈ latHat F E L := by
    intro o ho j
    rw [mulVec_single']
    have : (fun l => g' l j * ((k * m) • o)) = ∑ l, Pi.single l (k • ((m • g' l j) * o)) := by
      rw [Finset.univ_sum_single (fun l => k • ((m • g' l j) * o))]
      funext l
      rw [mul_smul_comm, smul_mul_assoc, smul_smul]
    rw [this]
    exact AddSubgroup.sum_mem _ (fun l _ => single_mem L hkL (Oh_mul (hmO l j) ho) l)
  have SL : ∀ p ∈ Oh F E, ∀ j, Pi.single j ((k * m) • p) ∈ latHat F E (abelian₂ σ J L h) := by
    intro p hp j
    induction hp using AddSubgroup.closure_induction with
    | mem p hp =>
      obtain ⟨a, ha, e, he, rfl⟩ := hp
      rw [nsmul_tmul_F, single_tmul]
      refine AddSubgroup.subset_closure ⟨a, ha, _, ?_, rfl⟩
      show g'.mulVec (vinc (Pi.single j (((k * m : ℕ) : F) • e))) ∈ latHat F E L
      have hv : vinc (F := F) (Pi.single j (((k * m : ℕ) : F) • e)) = Pi.single j ((k * m) • ((1 : Af F) ⊗ₜ[F] e)) := by
        rw [nsmul_tmul_F, single_tmul]
        rfl
      rw [hv]
      exact K1 _ (tmul_mem_Oh intAf_one he) j
    | zero => rw [smul_zero, Pi.single_zero]; exact zero_mem _
    | add p q _ _ h1 h2 => rw [smul_add, Pi.single_add]; exact add_mem h1 h2
    | neg p _ h1 => rw [smul_neg, Pi.single_neg]; exact neg_mem h1
  constructor
  · intro hy
    choose e o ho hyo using fun j => approx (F := F) (k * m) (Nat.mul_pos hk hm) (y j)
    have hyw : y = vinc (F := F) e + ∑ j, Pi.single j ((k * m) • o j) := by
      rw [Finset.univ_sum_single (fun j => (k * m) • o j)]
      funext j
      exact hyo j
    have hwsum : g'.mulVec (∑ j, Pi.single j ((k * m) • o j)) ∈ latHat F E L := by
      rw [Matrix.mulVec_sum]
      exact AddSubgroup.sum_mem _ (fun j _ => K1 _ (ho j) j)
    have he : e ∈ abelian₂ σ J L h := by
      show g'.mulVec (vinc e) ∈ latHat F E L
      have : vinc (F := F) e = y - ∑ j, Pi.single j ((k * m) • o j) := by
        conv_rhs => rw [hyw]
        abel
      rw [this, Matrix.mulVec_sub]
      exact sub_mem hy hwsum
    rw [hyw]
    refine add_mem (AddSubgroup.subset_closure ⟨1, intAf_one, e, he, rfl⟩) ?_
    exact AddSubgroup.sum_mem _ (fun j _ => SL _ (ho j) j)
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have hx' : g'.mulVec (vinc x) ∈ latHat F E L := hx
      have : (fun i => a ⊗ₜ[F] x i) = (a ⊗ₜ[F] (1 : E)) • vinc (F := F) x := by
        funext i
        simp [vinc, inclR, Algebra.TensorProduct.tmul_mul_tmul]
      rw [this, Matrix.mulVec_smul]
      exact latHat_smul L ha hx'
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [Matrix.mulVec_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [Matrix.mulVec_neg]; exact neg_mem h1
end PI.UnitaryGroupMassFormula.UJClassFin

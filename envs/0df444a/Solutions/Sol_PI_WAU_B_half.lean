-- Prove2me | solution 1 for PI.WAU.B.half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:09.036923+00:00
-- url     : https://prove2.me/submissions/3c66280b-5039-4039-afa5-cd0fa98cef0b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB
import Theorems.Thm_PI_WAU_B_nsmul_cancel
import Theorems.Thm_PI_WAU_B_fmat_inv_mul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WAU_B_cls_eq
import Theorems.Thm_PI_WAU_B_incA_mem
import Theorems.Thm_PI_WAU_B_ivec_mem
import Theorems.Thm_PI_WAU_B_lam_sub_alt
import Theorems.Thm_PI_WAU_B_mulVec_lam
import Theorems.Thm_PI_WAU_B_smulO_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Formalism.UG Matrix PI.WAU.B
open scoped TensorProduct
variable (I : AutInst) {k : ℕ} (m : Fin k → Fin I.n → I.E)
namespace PI.WAU.B
theorem _root_.solution (hm : ∀ i, m i ∈ I.L) (hgen : ∀ l ∈ I.L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    {N : ℕ} {x y : I.Gf} (hx : PN I m N x) (hy : PN I m N y) (he : fN I m N x = fN I m N y)
    (j : Fin k) : (I.fmat y⁻¹ * I.fmat x) *ᵥ ivec (F := I.F) (m j) ∈ I.Lf := by
  classical
  obtain ⟨hN, hxj⟩ := hx
  obtain ⟨_, hyj⟩ := hy
  have hTx : N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ Tset (F := I.F) m :=
    lam_sub_alt hm hgen (hxj j).1
  have hTy : N • (I.fmat y *ᵥ ivec (F := I.F) (m j)) ∈ Tset (F := I.F) m :=
    lam_sub_alt hm hgen (hyj j).1
  have hej := congrFun he j
  simp only [fN, dif_pos hTx, dif_pos hTy] at hej
  obtain ⟨haI, haE⟩ := hTx.choose_spec
  obtain ⟨ha'I, ha'E⟩ := hTy.choose_spec

  have hb : ∀ i, ∃ b : Af I.F, (∀ v, b v ∈ v.adicCompletionIntegers I.F) ∧
      hTx.choose i - hTy.choose i = ((N * N : ℕ) : Af I.F) * b := fun i =>
    cls_eq (Nat.mul_pos hN hN) (haI i) (ha'I i) (congrFun hej i)
  choose b hbI hbE using hb
  set w : Fin I.n → I.E ⊗[I.F] Af I.F := ∑ i, incA I.F I.E (b i) • ivec (F := I.F) (m i) with hwdef
  have hw : w ∈ I.Lf :=
    Submodule.sum_mem _ fun i _ => smulO_mem (incA_mem (hbI i)) (ivec_mem (hm i))
  have hdiff : N • (I.fmat x *ᵥ ivec (F := I.F) (m j) - I.fmat y *ᵥ ivec (F := I.F) (m j)) =
      N • (N • w) := by
    rw [smul_sub, haE, ha'E, ← Finset.sum_sub_distrib, hwdef, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, ← map_sub, hbE i, map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul,
      smul_smul]
  have hd : I.fmat x *ᵥ ivec (F := I.F) (m j) - I.fmat y *ᵥ ivec (F := I.F) (m j) = N • w :=
    nsmul_cancel (K := I.F) hN hdiff
  have hxu : I.fmat x *ᵥ ivec (F := I.F) (m j) = I.fmat y *ᵥ ivec (F := I.F) (m j) + N • w := by
    rw [← hd]
    abel
  rw [← Matrix.mulVec_mulVec, hxu, Matrix.mulVec_add, Matrix.mulVec_mulVec, fmat_inv_mul I y,
    Matrix.one_mulVec]
  refine Submodule.add_mem _ (ivec_mem (hm j)) ?_
  have hP : ∀ i, (N • I.fmat y⁻¹) *ᵥ ivec (F := I.F) (m i) ∈ I.Lf := fun i => by
    rw [Matrix.smul_mulVec]
    exact (hyj i).2
  have h2 := mulVec_lam hm hgen (N • I.fmat y⁻¹) hP hw
  rwa [Matrix.smul_mulVec, ← Matrix.mulVec_smul] at h2
end PI.WAU.B

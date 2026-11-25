-- Prove2me | solution 1 for PIW.AdelClassFin.mGen_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:44.29017+00:00
-- url     : https://prove2.me/submissions/106ff061-e0a9-43ff-95b6-cdae5a2d2cca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
import Theorems.Thm_PIW_AdelClassFin_DictGen_lf_eq
import Theorems.Thm_PIW_AdelClassFin_DictGen_iv_nsmul
import Theorems.Thm_PIW_AdelClassFin_DictGen_natCast_cancel
import Theorems.Thm_PIW_AdelClassFin_DictGen_fmat_inv_mul
import Theorems.Thm_PIW_AdelClassFin_DictGen_exists_denominator_fmat
import Theorems.Thm_PIW_AdelClassFin_DictGen_nL_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (hD : LDenom) (hDen : LDense) : MGen := by
  intro I x y hy
  obtain ⟨N, hN, hN'⟩ := DictGen.exists_denominator_fmat I hD x
  have hNE : (N : I.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNL : ∀ u ∈ I.Lf, (N : (I.E ⊗[I.F] Af I.F)) • u ∈
      Submodule.span (IntAf I.F I.E) (Set.range fun v : abelian₂ I x => iv I (v : Fin I.n → I.E)) := by
    intro u hu
    rw [DictGen.lf_eq] at hu
    induction hu using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨l, hl⟩, rfl⟩ := hz
      show (N : (I.E ⊗[I.F] Af I.F)) • iv I l ∈ _
      rw [← DictGen.iv_nsmul]
      exact Submodule.subset_span ⟨⟨N • l, DictGen.nL_sub I x N hN' hl⟩, rfl⟩
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact Submodule.add_mem _ ha hb
    | smul s a _ ha =>
      have e : (N : (I.E ⊗[I.F] Af I.F)) • (s • a) = s • ((N : (I.E ⊗[I.F] Af I.F)) • a) := by
        show (N : (I.E ⊗[I.F] Af I.F)) • ((s : (I.E ⊗[I.F] Af I.F)) • a) = (s : (I.E ⊗[I.F] Af I.F)) • ((N : (I.E ⊗[I.F] Af I.F)) • a)
        rw [smul_smul, smul_smul, mul_comm]
      rw [e]
      exact Submodule.smul_mem _ s ha
  obtain ⟨l, hl, y', hy', hw⟩ := hDen I (N * N) (Nat.mul_pos hN hN) _ (hN' y hy).1
  obtain ⟨v, hv⟩ : ∃ v : Fin I.n → I.E, v = (N : I.E)⁻¹ • l := ⟨_, rfl⟩
  have hNv : N • v = l := by
    rw [hv, ← Nat.cast_smul_eq_nsmul I.E, smul_smul, mul_inv_cancel₀ hNE, one_smul]
  have hz : I.fmat x *ᵥ y = iv I v + (N : (I.E ⊗[I.F] Af I.F)) • y' := by
    apply DictGen.natCast_cancel I N hN
    rw [smul_add, ← DictGen.iv_nsmul, hNv, hw, smul_smul, Nat.cast_mul]
  have hvL : v ∈ abelian₂ I x := by
    show I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf
    have e : iv I v = I.fmat x *ᵥ y - (N : (I.E ⊗[I.F] Af I.F)) • y' := by
      first
        | rw [hz, add_sub_cancel_right]
        | (rw [hz]; abel)
    rw [e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, DictGen.fmat_inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_smul]
    exact I.Lf.sub_mem hy (hN' y' hy').2
  rw [hz]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨⟨v, hvL⟩, rfl⟩) (hNL y' hy')
end PIW.AdelClassFin

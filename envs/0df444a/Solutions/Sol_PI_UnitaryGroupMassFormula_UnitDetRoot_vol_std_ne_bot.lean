-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.vol_std_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:50.700031+00:00
-- url     : https://prove2.me/submissions/7c06c56f-7fbb-4798-b5b2-6784983f4978

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobVol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] :
    vol (KF b d) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ ⊥ := by
  unfold vol volSet UnitDetRootDefs.stdLat
  rw [Submodule.ne_bot_iff]
  refine ⟨(Matrix.of fun (j i : m) => if i = j then lam * (a : ℂ) else 0).det,
    Submodule.subset_span ⟨_, fun j => ?_, rfl⟩, ?_⟩
  · refine fun i _ => ?_
    show (if i = j then lam * (a : ℂ) else 0) ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice
    have hω : lam * (a : ℂ) ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice := by
      simp only [PeriodPair.lattice, UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair,
        UnitDetRootDefs.cmPair]
      exact Submodule.subset_span (Set.mem_insert _ _)
    by_cases h : i = j
    · rw [if_pos h]
      exact hω
    · rw [if_neg h]
      exact zero_mem _
  · have hD : (Matrix.of fun (j i : m) => if i = j then lam * (a : ℂ) else 0) =
        Matrix.diagonal (fun _ => lam * (a : ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, eq_comm]
    rw [hD, Matrix.det_diagonal, Finset.prod_const]
    exact pow_ne_zero _ (mul_ne_zero hlam (by exact_mod_cast ha.ne'))
end PI.UnitaryGroupMassFormula.UnitDetRoot

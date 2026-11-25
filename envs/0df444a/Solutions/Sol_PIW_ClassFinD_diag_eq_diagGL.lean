-- Prove2me | solution 1 for PIW.ClassFinD.diag_eq_diagGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:27:08.060802+00:00
-- url     : https://prove2.me/submissions/bf650dc7-2321-4155-b9e1-e1ec74501e60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
import Theorems.Thm_PIW_ClassFinD_diagGL_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD
open NumberField IsDedekindDomain
namespace PIW.ClassFinD
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (t : GL (Fin n) R) (ht : IsDiagM t.val) :
    ∃ τ : Fin n → Rˣ, t = diagGL n τ := by
  have hunit : ∀ i, IsUnit (t.val i i) := by
    intro i
    have h : (t⁻¹.val * t.val) i i = (1 : Matrix (Fin n) (Fin n) R) i i := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_apply, Matrix.one_apply_eq,
      Finset.sum_eq_single i (fun k _ hki => by rw [ht k i hki, mul_zero]) (by simp)] at h
    exact ⟨⟨t.val i i, t⁻¹.val i i, (mul_comm _ _).trans h, h⟩, rfl⟩
  refine ⟨fun i => (hunit i).unit, Units.ext ?_⟩
  rw [diagGL_val]
  ext i j
  simp only [Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    exact (IsUnit.unit_spec _).symm
  · exact ht i j hij
end PIW.ClassFinD

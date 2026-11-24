-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.rk_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:45.027953+00:00
-- url     : https://prove2.me/submissions/69dd2763-80c5-4534-bc16-1b0d89c0cb5a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiB
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.ColumnAntisymmetry
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.ColumnAntisymmetry
theorem _root_.solution {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (I : Fin m → Fin n)
    (hI : ColInj col I) (p : Fin m) : rk col I p ≤ (top : ℕ) - I p := by
  unfold rk
  have h1 : (Finset.univ.filter fun q => col q = col p ∧ I p < I q).card ≤ (Finset.Ioi (I p)).card := by
    apply Finset.card_le_card_of_injOn I
    · intro q hq
      simp at hq ⊢
      exact hq.2
    · intro q hq q' hq' hqq
      simp at hq hq'
      exact hI q q' (hq.1.trans hq'.1.symm) hqq
  rw [Fin.card_Ioi] at h1
  omega
end PositivityTheory.Rg.Cz.ColumnAntisymmetry

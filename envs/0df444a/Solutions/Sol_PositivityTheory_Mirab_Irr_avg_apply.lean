-- Prove2me | solution 1 for PositivityTheory.Mirab.Irr.avg_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:39:32.120803+00:00
-- url     : https://prove2.me/submissions/bd125363-c552-41d6-a36e-870c31930cdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndIrr
import Theorems.Thm_GlobalTheory_FiniteGL_mirabInduced_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FiniteGL.mirabInduced_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open PositivityTheory PositivityTheory.Mirab PositivityTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
namespace PositivityTheory.Mirab.Irr
theorem _root_.solution [Fintype (uniSub k n)] (ψ₀ : AddChar k ℂ) (f : MirabInducedSpace n ψ₀) (x : mirabSub k n) :
    ((∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) • mirabInduced n ψ₀ (u : mirabSub k n) f :
        MirabInducedSpace n ψ₀) : mirabSub k n → ℂ) x =
      ∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * (f : mirabSub k n → ℂ) (x * u) := by
  rw [Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Submodule.coe_smul, Pi.smul_apply, mirabInduced_apply, smul_eq_mul]
end PositivityTheory.Mirab.Irr

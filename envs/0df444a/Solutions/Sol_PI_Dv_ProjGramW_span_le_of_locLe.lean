-- Prove2me | solution 1 for PI.Dv.ProjGramW.span_le_of_locLe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:57.324553+00:00
-- url     : https://prove2.me/submissions/56d69014-f735-45a2-8d13-c50eb7dcd11d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Theorems.Thm_PI_Dv_ProjGramW_locLe_zero_iff
import Theorems.Thm_PI_Dv_ProjGramW_algebraMap_ne_zero_of_not_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {X Y : Submodule (𝓞 K) V} (h : LocLe w 0 X Y) :
    Submodule.span K (X : Set V) ≤ Submodule.span K (Y : Set V) := by
  rw [Submodule.span_le]
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (locLe_zero_iff w X Y).mp h x hx
  have hs0 := algebraMap_ne_zero_of_not_mem w hs
  have h1 : (algebraMap (𝓞 K) K s) • x ∈ Submodule.span K (Y : Set V) := by
    rw [algebraMap_smul]
    exact Submodule.subset_span hsx
  have h2 := Submodule.smul_mem (Submodule.span K (Y : Set V)) (algebraMap (𝓞 K) K s)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at h2
end PI.Dv.ProjGramW

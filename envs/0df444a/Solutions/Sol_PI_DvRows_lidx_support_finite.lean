-- Prove2me | solution 1 for PI.DvRows.lidx_support_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:23:38.652633+00:00
-- url     : https://prove2.me/submissions/00913cba-6957-4d6a-9fc5-6dc213865338

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_log_covolume_slope_mu
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
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv
variable {K : Type} [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
namespace PI.DvRows
theorem _root_.solution (A : HLat K) (hG : A.Good) (M : Submodule (𝓞 K) A.V) (hM : M.FG) {j : ℕ}
    (y : Fin j → A.V) (hy : LinearIndependent K y)
    (hsp : Submodule.span K (M : Set A.V) = Submodule.span K (Set.range y)) :
    (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      Formalism.HermitianLatticesTheory.lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range y)) M).Finite := by
  by_cases h0 : M = ⊥
  · subst h0
    have hj : j = 0 := by
      by_contra hj
      have hmem : y ⟨0, by omega⟩ ∈ Submodule.span K (Set.range y) := Submodule.subset_span ⟨_, rfl⟩
      rw [← hsp] at hmem
      simp at hmem
      exact hy.ne_zero _ hmem
    subst hj
    simp [Formalism.HermitianLatticesTheory.lidx]
  · obtain ⟨-, -, -, hfin, -⟩ := log_covolume_slope_mu K A.V A.ι A.b A.X hG.1 j y M hy hM h0 hsp
    refine (hfin.preimage (hosEquiv (K := K)).injective.injOn).subset ?_
    intro w hw
    exact hw
end PI.DvRows

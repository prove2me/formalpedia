-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.natCast_mem_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:55:25.286199+00:00
-- url     : https://prove2.me/submissions/0adf27fb-6418-4d7e-93ad-29fd949e1e2f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_val_natCast_lt_one
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g : ℕ)
    (hg : (g : 𝓞 F) ∈ v.asIdeal) :
    (g : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h1 := val_natCast_lt_one F v g hg
  have h2 : Valued.v ((w : v.adicCompletion F)) ≤ 1 := w.2
  have h3 : (g : v.adicCompletion F) * (w : v.adicCompletion F) = 1 := by
    have := congrArg Subtype.val hw
    simpa using this
  have h4 := congrArg Valued.v h3
  rw [map_mul, map_one] at h4
  have h5 : Valued.v ((g : v.adicCompletion F)) * Valued.v ((w : v.adicCompletion F)) < 1 :=
    calc Valued.v ((g : v.adicCompletion F)) * Valued.v ((w : v.adicCompletion F))
        ≤ Valued.v ((g : v.adicCompletion F)) * 1 := by gcongr
      _ = Valued.v ((g : v.adicCompletion F)) := mul_one _
      _ < 1 := h1
  exact (ne_of_lt h5) h4
end PI.UnitaryGroupMassFormula.ScXuExists

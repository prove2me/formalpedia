-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.Gl.finite_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:19.52007+00:00
-- url     : https://prove2.me/submissions/889be8a2-fb7c-49fd-9fe7-4fe7068f2cef

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.Gl
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists PI.UnitaryGroupMassFormula.AdIndexEq
namespace PI.UnitaryGroupMassFormula.ScXuExists.Gl
theorem _root_.solution (F : Type) [Field F] [NumberField F] {g : ℕ} (hg : 1 ≤ g) :
    {v : HeightOneSpectrum (𝓞 F) | (g : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have hg0 : (g : 𝓞 F) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have h0 : Ideal.span {(g : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hg0
  exact (Ideal.finite_factors h0).subset (fun v hv => Ideal.dvd_span_singleton.2 hv)
end PI.UnitaryGroupMassFormula.ScXuExists.Gl

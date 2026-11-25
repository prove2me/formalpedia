-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.Phi_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:35.265007+00:00
-- url     : https://prove2.me/submissions/993698c7-bb95-4e38-80aa-d255581045ff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_sgl_int
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Phi_tmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_Phi_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_Oh_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_tmul_mem_Oh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct RestrictedProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {s : E ⊗[F] Fv F v}
    (hs : s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (Fv F v) (PI.UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers F).toSubring) :
    Phi v s ∈ Oh F E := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · obtain ⟨o, rfl⟩ := he
      rw [Phi_tmul]
      exact tmul_mem_Oh (sgl_int v (one_mem _)) o.isIntegral_coe
    · rw [Phi_tmul]
      exact tmul_mem_Oh (sgl_int v hy) isIntegral_one
  | zero => rw [map_zero]; exact zero_mem _
  | one =>
    rw [show (1 : E ⊗[F] Fv F v) = (1 : E) ⊗ₜ[F] (1 : Fv F v) from rfl, Phi_tmul]
    exact tmul_mem_Oh (sgl_int v (one_mem _)) isIntegral_one
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg x _ h1 => rw [map_neg]; exact neg_mem h1
  | mul x y _ _ h1 h2 => rw [Phi_mul]; exact Oh_mul h1 h2
end PI.UnitaryGroupMassFormula.UJClassMass

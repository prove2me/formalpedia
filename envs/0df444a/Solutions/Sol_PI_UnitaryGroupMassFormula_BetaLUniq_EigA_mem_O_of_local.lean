-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BetaLUniq.EigA.mem_O_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:10.754107+00:00
-- url     : https://prove2.me/submissions/ec387634-2a25-43ca-8a9e-429e421fea99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BetaUniqueness_EqZeroOfNormLtOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BetaLUniq PI.UnitaryGroupMassFormula.BetaLUniq.EigA
variable {E : Type} [Field E] [NumberField E]
namespace PI.UnitaryGroupMassFormula.BetaLUniq.EigA
theorem _root_.solution (ν : E)
    (h : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ s : 𝓞 E, s ∉ P ∧ InO (algebraMap (𝓞 E) E s * ν)) :
    InO ν := by
  let J : Ideal (𝓞 E) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 E) E ν)
    (LinearMap.range (Algebra.linearMap (𝓞 E) E))
  have hmem : ∀ s, s ∈ J ↔ InO (algebraMap (𝓞 E) E s * ν) := by
    intro s
    simp only [J, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, LinearMap.mem_range,
      Algebra.linearMap_apply, Algebra.smul_def, InO]
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨s, hsM, hs⟩ := h M hM
    exact hsM (hJM ((hmem s).mpr hs))
  have h1 := (hmem 1).mp (hJ ▸ Submodule.mem_top)
  rwa [map_one, one_mul] at h1
end PI.UnitaryGroupMassFormula.BetaLUniq.EigA

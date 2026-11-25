-- Prove2me | solution 1 for PI.VolStabSW.exFDStab_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:30.959795+00:00
-- url     : https://prove2.me/submissions/694d173b-367f-4229-aaf9-308cdded75f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_FundamentalDomainExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExFDStab
import Theorems.Thm_PI_VolSemiDirect_W_exists_fd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (h1 : SCHA) (h2 : DiscHF) : ExFDStab := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' _hμ'
  have i1 : SecondCountableTopology (HA (AF F) σ J) := h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  have i2 : DiscreteTopology (HFinIn (AF F) σ J) := h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  have i3 : SecondCountableTopology (stabT (AF F) σ J X0) :=
    TopologicalSpace.Subtype.secondCountableTopology (stabT (AF F) σ J X0 : Set (HA (AF F) σ J))
  let f : ratIn F E σ M J (stabT (AF F) σ J X0) → HFinIn (AF F) σ J := fun x =>
    ⟨((x : stabT (AF F) σ J X0) : HA (AF F) σ J), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_subtype_val :
      Continuous fun x : ratIn F E σ M J (stabT (AF F) σ J X0) => ((x : stabT (AF F) σ J X0) : HA (AF F) σ J))).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext e)
  have : DiscreteTopology (ratIn F E σ M J (stabT (AF F) σ J X0)) := DiscreteTopology.of_continuous_injective hf hinj
  obtain ⟨𝓕, -, h𝓕⟩ := PI.VolSemiDirect.W.exists_fd (G := stabT (AF F) σ J X0) (ratIn F E σ M J (stabT (AF F) σ J X0))
  exact ⟨𝓕, h𝓕 μ'⟩
end PI.VolStabSW

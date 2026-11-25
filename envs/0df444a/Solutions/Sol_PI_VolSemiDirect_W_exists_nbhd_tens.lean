-- Prove2me | solution 1 for PI.VolSemiDirect.W.exists_nbhd_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:14:43.418155+00:00
-- url     : https://prove2.me/submissions/3b186a47-1b31-4a24-8512-f8c4b5ed8a85

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA
import Theorems.Thm_PI_VolSemiDirect_W_isOpen_nbhdA
import Theorems.Thm_PI_VolSemiDirect_W_eq_zero_of_mem_nbhdA
import Theorems.Thm_PI_VolSemiDirect_W_zero_mem_nbhdA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct Matrix
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [Module.Finite F E]
namespace PI.VolSemiDirect.W
theorem _root_.solution : ∃ U : Set (AF F ⊗[F] E), IsOpen U ∧ (0 : AF F ⊗[F] E) ∈ U ∧
    ∀ e : E, inclR (F := F) (AF F) e ∈ U → e = 0 := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  refine ⟨⋂ i, (B.coord i) ⁻¹' nbhdA F, ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun i =>
      (isOpen_nbhdA F).preimage (IsModuleTopology.continuous_of_linearMap (B.coord i))
  · simp only [Set.mem_iInter, Set.mem_preimage, map_zero]
    exact fun _ => zero_mem_nbhdA F
  · intro e he
    simp only [Set.mem_iInter, Set.mem_preimage] at he
    have hc : ∀ i, b.repr e i = 0 := by
      intro i
      apply eq_zero_of_mem_nbhdA F
      have := he i
      have hco : B.coord i (inclR (F := F) (AF F) e) = algebraMap F (AF F) (b.repr e i) := by
        simp [B, inclR, Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul]
      rwa [hco] at this
    have : b.repr e = 0 := Finsupp.ext hc
    simpa using this
end PI.VolSemiDirect.W

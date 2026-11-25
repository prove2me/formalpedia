-- Prove2me | solution 1 for PI.DvRows.lidx_map_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:53:02.805675+00:00
-- url     : https://prove2.me/submissions/29caed43-4279-44cc-9814-c6a33258b911

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_PI_DvRows_localization_map_of_injective
import Theorems.Thm_PI_DvRows_length_map_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
open Formalism.HermitianLatticesTheory
variable {R : Type*} [CommRing R] {W W' : Type*} [AddCommGroup W] [Module R W]
  [AddCommGroup W'] [Module R W']
namespace PI.DvRows
theorem _root_.solution (p : Ideal R) [p.IsPrime] (f : W →ₗ[R] W') (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f →
      y ∈ LinearMap.range f)
    (A B : Submodule R W) : lidx p (A.map f) (B.map f) = lidx p A B := by
  unfold lidx locLen
  rw [← Submodule.map_inf f hf, localization_map_of_injective p f hf hsat, localization_map_of_injective p f hf hsat,
    localization_map_of_injective p f hf hsat, length_map_inj f hf, length_map_inj f hf]
end PI.DvRows

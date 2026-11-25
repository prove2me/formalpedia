-- Prove2me | solution 1 for PI.Dv.TIW.intEl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:03.12988+00:00
-- url     : https://prove2.me/submissions/26052591-7d6d-471e-99f7-0daf1540a83d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution (ρ : Representation K G V) (L : Submodule (𝓞 K) V) (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L)
    (z : MonoidAlgebra K G) (hz : IntEl z) : ∀ x ∈ L, ρ.asAlgebraHom z x ∈ L := by
  intro x hx
  rw [← MonoidAlgebra.sum_single z]
  rw [Finsupp.sum, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun g _ => ?_
  obtain ⟨o, ho⟩ := hz g
  rw [Representation.asAlgebraHom_single, LinearMap.smul_apply, ← ho, algebraMap_smul]
  exact L.smul_mem o (hL g x hx)
end PI.Dv.TIW

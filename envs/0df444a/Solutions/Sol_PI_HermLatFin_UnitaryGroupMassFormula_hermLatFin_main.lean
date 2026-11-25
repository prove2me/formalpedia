-- Prove2me | solution 1 for PI.HermLatFin.UnitaryGroupMassFormula.hermLatFin_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:00.197749+00:00
-- url     : https://prove2.me/submissions/bd39c87a-09cd-43f5-9646-9fa9a824a735

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HformTracePos
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ShortVectors
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomOfTrace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HermLatFinMain
import Theorems.Thm_PI_HermLatFin_UnitaryGroupMassFormula_covol_le
import Theorems.Thm_Formalism_FN_LowerVolumeBound_covol_le
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetFinite_core
import Theorems.Thm_Formalism_HermitianLatticesTheory_finIntermediate
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomOfTrace
import Theorems.Thm_Formalism_HermitianLatticesTheory_shortVectors
import Theorems.Thm_Formalism_HermitianLatticesTheory_traceReal
import Theorems.Thm_PI_HermLatFin_UnitaryGroupMassFormula_herm_hermitian
import Theorems.Thm_PI_HermLatFin_UnitaryGroupMassFormula_hform_eq_herm
import Theorems.Thm_PI_HermLatFin_UnitaryGroupMassFormula_hform_isSymm
import Theorems.Thm_PI_HermLatFin_UnitaryGroupMassFormula_hform_trace_pos
import Theorems.Thm_PI_HermLatFin_UnitaryGroupMassFormula_isUJ_of_isom
import Theorems.Thm_PI_HermLatFin_UnitaryGroupMassFormula_sigma_invol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexOrder
noncomputable section
open PI PI.HermLatFin PI.HermLatFin.UnitaryGroupMassFormula
variable {E : Type} [Field E] [NumberField E]
namespace PI.HermLatFin.UnitaryGroupMassFormula
theorem _root_.solution : HermLatFin := by
  intro E _ _ n σ J T hσ hJ hT
  classical
  letI : StarRing E := starOf σ (sigma_invol σ hσ)
  have hst : ∀ a : E, star a = σ a := fun _ => rfl
  have hJs : ∀ i j, star (J i j) = J j i := fun i j => herm_hermitian σ hσ J hJ i j
  have hs := hform_isSymm J hJs
  have hpos : ∀ x : Fin n → E, x ≠ 0 → 0 < Algebra.trace ℚ E (hform J x x) :=
    hform_trace_pos σ hst hσ J hJ
  obtain ⟨N, ι, hι, hmul, hlat⟩ := Formalism.HermitianLatticesTheory.traceReal E (Fin n → E) (hform J) hs hpos
  obtain ⟨s, -, hsall⟩ := Formalism.HermitianLatticesTheory.classSetFinite_core Formalism.HermitianLatticesTheory.shortVectors
    Formalism.HermitianLatticesTheory.finIntermediate Formalism.HermitianLatticesTheory.isomOfTrace (hform J) hpos N ι hι hmul 1 one_pos _
    {L | admitted σ J T L}
    (fun M hM x hx y hy => by
      rw [Nat.cast_one, one_mul, hform_eq_herm σ hst]
      exact Submodule.mem_one.mpr ⟨⟨_, hM.2.1 x hx y hy⟩, rfl⟩)
    (fun M hM => hlat M ⟨hM.1.1, hM.1.2⟩)
    (fun M hM _ _ => covol_le σ hst J T N ι hι M hM hT)
  refine ⟨(s : Set _), s.finite_toSet, fun L hL => ?_⟩
  obtain ⟨N', hN', g, hg, hgN⟩ := hsall L hL
  refine ⟨N', hN', LinearMap.toMatrix' (g : (Fin n → E) →ₗ[E] (Fin n → E)),
    isUJ_of_isom σ hst J _ (fun x y => hg x y), ?_⟩
  rw [← hgN, Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe]
  congr 1
  funext x
  exact LinearMap.toMatrix'_mulVec _ x
end PI.HermLatFin.UnitaryGroupMassFormula

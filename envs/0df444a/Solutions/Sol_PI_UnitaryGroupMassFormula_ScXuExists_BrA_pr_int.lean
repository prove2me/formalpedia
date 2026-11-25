-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrA.pr_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:27.396255+00:00
-- url     : https://prove2.me/submissions/6eab073a-3f86-456a-be67-3d68fd617cd6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_gp_int
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_pr_vec
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_hl_ratV
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_pr_span_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_pr_span_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_first_coordinate_vector_mem_span
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_second_coordinate_vector_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrA
open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrA
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) : ∀ β ∈ Lam2 I v p1, ∀ x ∈ Lam1 I v p1, pr (Pm I v p1) β x ∈ OV I v := by

  have h0 : ∀ l ∈ (I.L : Set (Fin I.n → I.E)), ∀ l' ∈ (I.L : Set (Fin I.n → I.E)),
      pr (Pm I v p1) (vec2 p1 (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l))
        (vec1 p1 (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l')) ∈ OV I v := by
    intro l hl l' hl'
    rw [pr_vec, hl_ratV]
    exact gp_int I v ε p1 hp _ ((I.L_dual l').1 hl' l hl)
  have h1 : ∀ β ∈ Submodule.span (OV I v)
      ((fun l => vec2 p1 (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l)) '' (I.L : Set _)),
      ∀ x ∈ Submodule.span (OV I v)
      ((fun l => vec1 p1 (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l)) '' (I.L : Set _)),
      pr (Pm I v p1) β x ∈ OV I v := by
    intro β hβ x hx
    refine pr_span_left (OV I v) (Pm I v p1) (fun β' hβ' => ?_) β hβ
    obtain ⟨l, hl, rfl⟩ := hβ'
    refine pr_span_right (OV I v) (Pm I v p1) (fun x' hx' => ?_) x hx
    obtain ⟨l', hl', rfl⟩ := hx'
    exact h0 l hl l' hl'
  intro β hβ x hx
  refine pr_span_left (OV I v) (Pm I v p1) (fun β' hβ' => ?_) β hβ
  obtain ⟨X, hX, rfl⟩ := hβ'
  refine pr_span_right (OV I v) (Pm I v p1) (fun x' hx' => ?_) x hx
  obtain ⟨Y, hY, rfl⟩ := hx'
  exact h1 _ (second_coordinate_vector_mem_span I v p1 hp.1 X hX) _ (first_coordinate_vector_mem_span I v p1 hp.1 Y hY)
end PI.UnitaryGroupMassFormula.ScXuExists.BrA

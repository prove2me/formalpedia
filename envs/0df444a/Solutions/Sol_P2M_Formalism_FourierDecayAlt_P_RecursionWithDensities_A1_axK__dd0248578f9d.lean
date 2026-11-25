-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_axK__dd0248578f9d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:11.072812+00:00
-- url     : https://prove2.me/submissions/3b152dcc-4ddc-4ae4-8000-fb161856ae37

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_restr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
section gen
variable {α : Type}
variable {E : Type} [AddCommGroup E]
end gen
section ta
variable {E : Type} [Field E] [DecidableEq E]
private theorem isPt_of_mem_pt (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) :
    ∀ n, ∀ h ∈ PT Sg n, IsPt n h := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h hh
    cases n with
    | zero =>
      simp only [PT, Finset.mem_singleton] at hh
      subst hh
      simp [TA.IsPt, TA.lvl]
    | succ n =>
      simp only [PT, Finset.mem_biUnion, Finset.mem_attach, true_and, Finset.mem_image] at hh
      obtain ⟨a, h0, hh0, t, ht, he⟩ := hh
      subst he
      have hm := Finset.mem_range.mp a.2
      obtain ⟨hl, hb⟩ := ih a.1 hm h0 hh0
      unfold TA.IsPt
      refine ⟨?_, ?_⟩
      · simp [TA.ext, TA.lvl] at hl ⊢
        omega
      · intro b hbm
        simp only [TA.ext, List.mem_append, List.mem_singleton] at hbm
        rcases hbm with hbm | rfl
        · exact hb b hbm
        · refine ⟨?_, hNZ _ _ t ht⟩
          show 1 ≤ n + 1 - a.1
          omega
end ta
section main
variable {E : Type} [Field E] [DecidableEq E]
end main
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism.FourierDecayAlt.P.BudgetLiftBounds Formalism.FourierDecayAlt.TC
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.P.OneLevelCoefficients Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexOrder ComplexConjugate
end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
namespace Formalism.FourierDecayAlt.P
open RecursionWithDensities
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {E : Type} [Field E] [DecidableEq E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
theorem _root_.solution (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (hNZ : NZSg Sg) (hK : AxK D) :
    AxK (D' D Sg Th) := by
  obtain ⟨hK1, hK2⟩ := hK
  unfold TA.AxK
  refine ⟨?_, fun i hi P hP => ?_⟩
  · show restr (PT Sg 0) (D.K 0) [] [] = 1
    have h0 : ([] : Pt E) ∈ PT Sg 0 := by simp [PT]
    unfold restr
    rw [if_pos ⟨h0, h0⟩]
    exact hK1
  · show PSDOn P (restr (PT Sg i) (D.K i))
    exact psd_restr (PT Sg i) P (hK2 i hi _ (isPt_of_mem_pt Sg hNZ i))
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1

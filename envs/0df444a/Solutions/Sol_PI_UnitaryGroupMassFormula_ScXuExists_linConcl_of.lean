-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.linConcl_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:24.099323+00:00
-- url     : https://prove2.me/submissions/6b743c07-abdd-4c01-bf72-aa34e0208111

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (hL : LocLin) (K : Type) [Field K] (O : ValuationSubring K) (n r : ℕ)
    (P : Matrix (Fin n) (Fin n) K) (g : K) (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
    (u φ u0 φ0 : Fin n → K) (t : K) (h : LinHyp K O n r P g Λ1 Λ2 a a' α α' u φ u0 φ0 t) :
    ∃ T : GL (Fin n) K, LinConcl K O n r P g Λ1 Λ2 a a' α α' u φ u0 φ0 T := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact hL K O n r P g Λ1 Λ2 a a' α α' u φ u0 φ0 t h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
end PI.UnitaryGroupMassFormula.ScXuExists

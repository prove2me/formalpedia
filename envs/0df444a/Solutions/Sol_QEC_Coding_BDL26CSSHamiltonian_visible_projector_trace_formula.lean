-- Prove2me | solution 1 for QEC.Coding.BDL26CSSHamiltonian.visible_projector_trace_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:58:49.89461+00:00
-- url     : https://prove2.me/submissions/251b66c2-eba6-47d5-831b-f139c17000a0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_visible_sector_finrank_two
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_invisible_sector_finrank_zero
import Theorems.Thm_QEC_Coding_CSSGibbs_trace_projector
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_e0d1cb1e0b_118
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_e0d1cb1e0b_119
namespace QEC.Coding.BDL26CSSHamiltonian
theorem _root_.solution
    (s : Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n))) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n)) (projector S n s) =
      if s ∈ visibleRealizable S n then (2 : ℂ) else 0 := by
  calc
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n)) (projector S n s) =
        (Module.finrank ℂ (sector S n s) : ℂ) :=
      CSSGibbs.trace_projector (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n) s
    _ = if s ∈ visibleRealizable S n then (2 : ℂ) else 0 := by
      by_cases hs : s ∈ visibleRealizable S n
      · have hr := visible_sector_finrank_two S n s hs
        calc
          (Module.finrank ℂ (sector S n s) : ℂ) = (2 : ℂ) := by exact_mod_cast hr
          _ = if s ∈ visibleRealizable S n then (2 : ℂ) else 0 := (if_pos hs).symm
      · have hr := invisible_sector_finrank_zero S n s hs
        calc
          (Module.finrank ℂ (sector S n s) : ℂ) = (0 : ℂ) := by exact_mod_cast hr
          _ = if s ∈ visibleRealizable S n then (2 : ℂ) else 0 := (if_neg hs).symm
end QEC.Coding.BDL26CSSHamiltonian

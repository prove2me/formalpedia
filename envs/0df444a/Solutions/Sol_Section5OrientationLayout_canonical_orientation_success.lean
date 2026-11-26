-- Prove2me | solution 1 for Section5OrientationLayout.canonical_orientation_success
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T21:09:19.473475+00:00
-- url     : https://prove2.me/submissions/562bead5-3f33-4c37-ba0c-4a6d7b85ca6e

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5OrientationLayout
import Definitions.Def_Section5Verified_Section5ReindexedQEXLaw
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
import Theorems.Thm_Section5OrientationLayout_canonical_orientation_circuit
import Theorems.Thm_section5_raw_orientation_success
import Theorems.Thm_section5_reindexed_three_qex_probability
import Theorems.Thm_section5_reversible_circuit_permutation
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_ket_injective {ι : Type*} [DecidableEq ι] :
    Function.Injective (ket : ι → EuclideanSpace ℂ ι) := by
  intro a b hab
  by_contra h
  have hc := congrArg (fun v : EuclideanSpace ℂ ι => v a) hab
  simp [ket,PiLp.single_apply,h,Ne.symm h] at hc







end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example
namespace Section5OrientationLayout
end Section5OrientationLayout
open Section5OrientationLayout
open Classical in
theorem solution (n q a f : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) :
    ∃ c : Circuit gatesRev (Section5OrientationLayout.width n q a),
      c.size ≤ (128*(n+a+34)^4+1)*3+3+19*(a+2)*n ∧
      ∀ x : Fin n → Qubits (a+1), ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖=1 →
        Section5OrientationLayout.estimateVector f x ≠ 0 → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ flip : Bool,
        ‖(if flip then -NormedSpace.normalize (Section5OrientationLayout.estimateVector f x)
          else NormedSpace.normalize (Section5OrientationLayout.estimateVector f x))-w‖ ≤ ε/6 →
        probEvent (act c.unitary (section5_reindex_state (Section5OrientationLayout.split n q a)
          (tensorVec (ket (Section5OrientationLayout.estimateBits x)) (section5_three_qex_state (q:=q) w))))
          (fun z => Section5OrientationLayout.readout f z ≠ 0 ∧ ‖NormedSpace.normalize (Section5OrientationLayout.readout f z)-w‖ ≤ ε) ≥ 27/32 := by
  obtain ⟨c,hc,hact⟩ := Section5OrientationLayout.canonical_orientation_circuit n q a f hn hgrid
  obtain ⟨F,hF⟩ := section5_reversible_circuit_permutation c
  refine ⟨c,hc,?_⟩
  intro x w hw hr ε hε hε' flip hclose
  have hread (s : Qubits (n*q) × Qubits (n*q) × Qubits (n*q)) :
      Section5OrientationLayout.readout f (F ((Section5OrientationLayout.split n q a).symm (Section5OrientationLayout.estimateBits x,section5_labelled_three_qex_outcome w s)))=
        section5_oriented_direction w (Section5OrientationLayout.estimateVector f x) s := by
    obtain ⟨z',hz',hout⟩ := hact x w s
    have heq := section5_ket_injective
      ((hF ((Section5OrientationLayout.split n q a).symm (Section5OrientationLayout.estimateBits x,section5_labelled_three_qex_outcome w s))).symm.trans hz')
    rw [heq]
    exact hout
  rw [section5_reindexed_three_qex_probability (Section5OrientationLayout.split n q a) w (Section5OrientationLayout.estimateBits x) c.unitary F hF]
  simp only [hread]
  exact section5_raw_orientation_success n q hn hgrid w (Section5OrientationLayout.estimateVector f x) hw hr ε hε hε' flip hclose

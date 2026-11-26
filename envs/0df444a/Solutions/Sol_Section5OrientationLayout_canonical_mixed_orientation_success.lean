-- Prove2me | solution 1 for Section5OrientationLayout.canonical_mixed_orientation_success
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T21:12:24.960168+00:00
-- url     : https://prove2.me/submissions/58a0cb9f-cd6c-4dc4-a094-2841705673e4

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
import Definitions.Def_Section5Verified_Section5MixedOrientationSuccess
import Definitions.Def_Section5Verified_Section5MixedQEXMeasurement
import Definitions.Def_Section5Verified_Section5OrientationAmplification
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5OrientationLayout
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
import Theorems.Thm_Section5OrientationLayout_canonical_orientation_circuit
import Theorems.Thm_section5_finite_conditioned_success
import Theorems.Thm_section5_mixed_three_qex_probability
import Theorems.Thm_section5_raw_orientation_success
import Theorems.Thm_section5_reversible_circuit_permutation
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Three finite-QEX votes amplify orientation success, for either sign. -/



theorem section5_qex_distribution_nonneg (n q : ℕ) (z : Qubits (n*q)) :
    0 ≤ section5_qex_distribution n q z := by
  exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun x _ => (Real.exp_pos _).le))









end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! The actual majority decision outputs a direction close to w, rather than merely
bounding an abstract error predicate. -/













theorem section5_three_qex_weight_nonneg (n q : ℕ)
    (z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q)) : 0 ≤ section5_three_qex_weight n q z := by
  exact mul_nonneg (mul_nonneg (section5_qex_distribution_nonneg n q z.1)
    (section5_qex_distribution_nonneg n q z.2.1)) (section5_qex_distribution_nonneg n q z.2.2)







end
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
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement QuantumLTF.Example
namespace Section5OrientationLayout
end Section5OrientationLayout
open Section5OrientationLayout
open Classical in
theorem solution (n q a f : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) :
    ∃ c : Circuit gatesRev (Section5OrientationLayout.width n q a),
      c.size ≤ (128*(n+a+34)^4+1)*3+3+19*(a+2)*n ∧
      ∀ σ : Matrix (Section5OrientationLayout.DataWire n a → Bool) (Section5OrientationLayout.DataWire n a → Bool) ℂ,
        (∀ d, 0 ≤ (σ d d).re) → ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖=1 →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        (∑ d, if Section5OrientationLayout.GoodEstimate f ε w d then (σ d d).re else 0) ≥ 11/12 →
        probMixed c.unitary (section5_mixed_qex_density (Section5OrientationLayout.split n q a) σ w)
          (fun z => Section5OrientationLayout.readout f z ≠ 0 ∧ ‖NormedSpace.normalize (Section5OrientationLayout.readout f z)-w‖ ≤ ε) ≥ 73/96 := by
  obtain ⟨c,hc,hact⟩ := Section5OrientationLayout.canonical_orientation_circuit n q a f hn hgrid
  obtain ⟨F,hF⟩ := section5_reversible_circuit_permutation c
  refine ⟨c,hc,?_⟩
  intro σ hp w hw ε hε hε' hgood
  let p : (Section5OrientationLayout.DataWire n a → Bool) → ℝ := fun d => (σ d d).re
  let G : (Section5OrientationLayout.DataWire n a → Bool) → Prop := Section5OrientationLayout.GoodEstimate f ε w
  let A := fun (d : Section5OrientationLayout.DataWire n a → Bool) (s : Qubits (n*q) × Qubits (n*q) × Qubits (n*q)) =>
    Section5OrientationLayout.readout f (F ((Section5OrientationLayout.split n q a).symm (d,section5_labelled_three_qex_outcome w s))) ≠ 0 ∧
      ‖NormedSpace.normalize (Section5OrientationLayout.readout f (F ((Section5OrientationLayout.split n q a).symm (d,section5_labelled_three_qex_outcome w s))))-w‖ ≤ ε
  letI : DecidablePred G := fun d => inferInstanceAs (Decidable (Section5OrientationLayout.GoodEstimate f ε w d))
  letI : ∀ d, DecidablePred (A d) := fun d s => inferInstanceAs (Decidable
    (Section5OrientationLayout.readout f (F ((Section5OrientationLayout.split n q a).symm (d,section5_labelled_three_qex_outcome w s))) ≠ 0 ∧
      ‖NormedSpace.normalize (Section5OrientationLayout.readout f (F ((Section5OrientationLayout.split n q a).symm (d,section5_labelled_three_qex_outcome w s))))-w‖ ≤ ε))
  have hconditional (d : Section5OrientationLayout.DataWire n a → Bool) (hd : G d) :
      (∑ s, if A d s then section5_three_qex_weight n q s else 0) ≥ 27/32 := by
    obtain ⟨x,hd,hr,⟨flip,hclose⟩⟩ := hd
    subst d
    have hread (s : Qubits (n*q) × Qubits (n*q) × Qubits (n*q)) :
        Section5OrientationLayout.readout f (F ((Section5OrientationLayout.split n q a).symm (Section5OrientationLayout.estimateBits x,section5_labelled_three_qex_outcome w s)))=
          section5_oriented_direction w (Section5OrientationLayout.estimateVector f x) s := by
      obtain ⟨z',hz',hout⟩ := hact x w s
      have heq := section5_ket_injective
        ((hF ((Section5OrientationLayout.split n q a).symm (Section5OrientationLayout.estimateBits x,section5_labelled_three_qex_outcome w s))).symm.trans hz')
      rw [heq]
      exact hout
    simpa only [A,hread] using
      section5_raw_orientation_success n q hn hgrid w (Section5OrientationLayout.estimateVector f x) hw hr ε hε hε' flip hclose
  have hcombined := section5_finite_conditioned_success p (section5_three_qex_weight n q)
    hp (section5_three_qex_weight_nonneg n q) G A (27/32) (11/12) (by norm_num) hgood hconditional
  rw [section5_mixed_three_qex_probability (Section5OrientationLayout.split n q a) σ w c.unitary F hF]
  exact (show (73/96:ℝ) ≤ (27/32)*(11/12) by norm_num).trans hcombined

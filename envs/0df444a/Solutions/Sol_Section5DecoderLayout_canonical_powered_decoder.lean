-- Prove2me | solution 1 for Section5DecoderLayout.canonical_powered_decoder
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:40:16.356169+00:00
-- url     : https://prove2.me/submissions/5b4c3318-e895-4d00-85d5-c3aa5e74534a

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
import Definitions.Def_Section5Verified_Section5CanonicalPoweredDecoder
import Definitions.Def_Section5Verified_Section5DecoderLayout
import Definitions.Def_Section5Verified_Section5DecoderLayoutLaws
import Definitions.Def_Section5Verified_Section5ExactMatrixPowerCircuit
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5PoweredMatrixDecoder
import Definitions.Def_Section5Verified_Section5ScoredColumnMatrix
import Mathlib
import Theorems.Thm_Section5DecoderLayout_record_matrix_read
import Theorems.Thm_Section5DecoderLayout_records_columnLabel
import Theorems.Thm_Section5DecoderLayout_records_disjoint
import Theorems.Thm_section5_powered_matrix_decoder_circuit
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

namespace Section5DecoderLayout

@[simp] theorem records_score {N K b f : ℕ} (j : Fin (N+1)) (i : Fin (scoreWidth N b)) :
    records (K:=K) (b:=b) (f:=f) j (scoreField N b i)=scores j i := by
  change records j (Fin.castAdd _ i)=_
  exact combineEmb_castAdd _ _ _ i

@[simp] theorem records_real {N K b f : ℕ} (j : Fin (N+1)) (i : Fin (payloadWidth N b)) :
    records (K:=K) (b:=b) (f:=f) j (realField N b i)=part false j i := by
  change records j (Fin.natAdd _ (Fin.castAdd _ i))=_
  unfold records
  rw [combineEmb_natAdd,combineEmb_castAdd]

@[simp] theorem records_imag {N K b f : ℕ} (j : Fin (N+1)) (i : Fin (payloadWidth N b)) :
    records (K:=K) (b:=b) (f:=f) j (imagField N b i)=part true j i := by
  change records j (Fin.natAdd _ (Fin.natAdd _ i))=_
  unfold records
  rw [combineEmb_natAdd,combineEmb_natAdd]







theorem not_in_records {N K b f : ℕ} (w : Wire N K b f) (hw : columnLabel w=none)
    (j : Fin (N+1)) : code N K b f w ∉ Set.range (records j) := by
  rintro ⟨e,he⟩
  have hh := records_columnLabel (K:=K) (b:=b) (f:=f) j e
  rw [he,Equiv.symm_apply_apply,hw] at hh
  cases hh

theorem fresh_workspace {N K b f : ℕ} (w : Wire N K b f) (hw : columnLabel w=none)
    (hc : ∀ i, w ≠ Wire.scanControl i) :
    section5_outside_column_records records (scanControl N K b f) (code N K b f w) := by
  refine ⟨not_in_records w hw,?_⟩
  rintro ⟨i,hi⟩
  have hh := (code N K b f).injective hi
  exact hc i hh.symm



end Section5DecoderLayout

end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace

namespace Section5DecoderLayout





theorem fields_disjoint (N b : ℕ) :
    (∀ i e, realField N b i ≠ scoreField N b e) ∧
    (∀ i e, imagField N b i ≠ scoreField N b e) ∧
    (∀ i j, realField N b i ≠ imagField N b j) := by
  constructor
  · intro i e h
    have hh := congrArg (records (K:=0) (f:=0) (0 : Fin (N+1))) h
    rw [records_real,records_score] at hh
    exact scores_parts_disjoint _ _ false e i hh.symm
  constructor
  · intro i e h
    have hh := congrArg (records (K:=0) (f:=0) (0 : Fin (N+1))) h
    rw [records_imag,records_score] at hh
    exact scores_parts_disjoint _ _ true e i hh.symm
  · intro i j h
    have hh := congrArg (records (K:=0) (f:=0) (0 : Fin (N+1))) h
    rw [records_real,records_imag] at hh
    exact parts_disjoint false true _ _ (Or.inl Bool.false_ne_true) i j hh



end Section5DecoderLayout

end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout
theorem solution (N K b f q : ℕ)
    (hf : f ≤ (q+1)*(K+1)) (hfit : (q+1)*(K+1)+2 ≤ b+1) :
    ∃ c : Circuit gatesRev (Section5DecoderLayout.width N K b f),
      c.size ≤
        (((16*(2*(N+1)+b+b+1)+6)*(((N+1)+(N+1))*(b+1)*(b+1)))*(N+1)+
          (16*(2*(N+1)+b+b+1)+1+7*(Section5DecoderLayout.recordWidth N b))*N)+
        ((16*((N+1)+b+b+1+1)+6)*(((N+1)+(N+1))*(b+1)*(b+1))+
          7*((N+1)*(b+1))+2*(f+2)*(N+1)) ∧
      ∀ z : Qubits (Section5DecoderLayout.width N K b f), Section5DecoderLayout.Clean z →
      ∀ M : Section5IntegerMatrix (N+1), IsSelfAdjoint (M.dyadicOperator q) →
        section5_signed_matrix_read (Section5DecoderLayout.matrix (f:=f) (Fin.last K)) z=M.power (K+1) →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        800*((N+1:ℕ):ℝ)/ε ≤ (2:ℝ)^(K+1) →
        144*((N+1:ℕ):ℝ)^2*(4:ℝ)^(K+1)/ε ≤ (2:ℝ)^f →
      ∀ w : EuclideanSpace ℝ (Fin (N+1)), ‖w‖=1 →
        ‖M.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/2000 →
        ∃ z' : Qubits (Section5DecoderLayout.width N K b f), act c.unitary (ket z)=ket z' ∧
          let v : EuclideanSpace ℝ (Fin (N+1)) := WithLp.toLp 2 fun i => readFp
            (⟨fun e => Section5DecoderLayout.output N K b f i e.rev,
              fun _ _ h => Fin.rev_injective ((Section5DecoderLayout.output N K b f i).injective h)⟩) f z'
          v ≠ 0 ∧ (‖NormedSpace.normalize v-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize v+w‖ ≤ ε/6) := by
  obtain ⟨hre,him,hri⟩ := Section5DecoderLayout.fields_disjoint N b
  have hpa : ∀ i e j, Section5DecoderLayout.records (K:=K) (b:=b) (f:=f) i e ≠ Section5DecoderLayout.scoreAnc N K b f j := by
    intro i e j h
    exact Section5DecoderLayout.not_in_records (Wire.scoreAnc j) rfl i ⟨e,h⟩
  have hpt : ∀ i e, Section5DecoderLayout.records (K:=K) (b:=b) (f:=f) i e ≠ Section5DecoderLayout.code N K b f Wire.scoreScratch := by
    intro i e h
    exact Section5DecoderLayout.not_in_records Wire.scoreScratch rfl i ⟨e,h⟩
  have hta : ∀ j, Section5DecoderLayout.code N K b f Wire.scoreScratch ≠ Section5DecoderLayout.scoreAnc N K b f j := by
    intro j h
    have hh := (Section5DecoderLayout.code N K b f).injective h
    cases hh
  have hctrl : ∀ i j e, Section5DecoderLayout.scanControl N K b f i ≠ Section5DecoderLayout.records j e := by
    intro i j e h
    exact Section5DecoderLayout.not_in_records (Wire.scanControl i) rfl j ⟨e,h.symm⟩
  have hscan : ∀ i e j, Section5DecoderLayout.records (K:=K) (b:=b) (f:=f) i e ≠ Section5DecoderLayout.scanCarry N K b f j := by
    intro i e j h
    exact Section5DecoderLayout.not_in_records Wire.scanCarry rfl i ⟨e,h⟩
  have hca : ∀ i j, Section5DecoderLayout.scanControl N K b f i ≠ Section5DecoderLayout.scanCarry N K b f j := by
    intro i j h
    have hh := (Section5DecoderLayout.code N K b f).injective h
    cases hh
  have hnpa : ∀ i j, Section5DecoderLayout.normAccumulator N K b f i ≠ Section5DecoderLayout.normAnc N K b f j := by
    intro i j h
    have hh := (Section5DecoderLayout.code N K b f).injective h
    cases hh
  have hntp : Section5DecoderLayout.code N K b f Wire.normScratch ∉ Set.range (Section5DecoderLayout.normAccumulator N K b f) := by
    rintro ⟨i,hi⟩
    have hh := (Section5DecoderLayout.code N K b f).injective hi
    cases hh
  have hnta : ∀ j, Section5DecoderLayout.code N K b f Wire.normScratch ≠ Section5DecoderLayout.normAnc N K b f j := by
    intro j h
    have hh := (Section5DecoderLayout.code N K b f).injective h
    cases hh
  have hdst : ∀ i j, i ≠ j → ∀ e g, Section5DecoderLayout.output N K b f i e ≠ Section5DecoderLayout.output N K b f j g := by
    intro i j hij e g h
    have hh := (Section5DecoderLayout.code N K b f).injective h
    exact hij (Section5DecoderLayout.Wire.output.inj hh).1
  have hndst : ∀ i j e, Section5DecoderLayout.normAccumulator N K b f j ≠ Section5DecoderLayout.output N K b f i e := by
    intro i j e h
    have hh := (Section5DecoderLayout.code N K b f).injective h
    cases hh
  have hnpf : ∀ e, section5_outside_column_records Section5DecoderLayout.records (Section5DecoderLayout.scanControl N K b f)
      (Section5DecoderLayout.normAccumulator N K b f e) := by
    intro e
    exact Section5DecoderLayout.fresh_workspace (Wire.normAccumulator e) rfl (by intro i h; cases h)
  have hnaf : ∀ e, section5_outside_column_records Section5DecoderLayout.records (Section5DecoderLayout.scanControl N K b f)
      (Section5DecoderLayout.normAnc N K b f e) := by
    intro e
    exact Section5DecoderLayout.fresh_workspace (Wire.normAnc e) rfl (by intro i h; cases h)
  have hntf : section5_outside_column_records Section5DecoderLayout.records (Section5DecoderLayout.scanControl N K b f)
      (Section5DecoderLayout.code N K b f Wire.normScratch) :=
    Section5DecoderLayout.fresh_workspace Wire.normScratch rfl (by intro i h; cases h)
  have hdf : ∀ i e, section5_outside_column_records Section5DecoderLayout.records (Section5DecoderLayout.scanControl N K b f)
      (Section5DecoderLayout.output N K b f i e) := by
    intro i e
    exact Section5DecoderLayout.fresh_workspace (Wire.output i e) rfl (by intro j h; cases h)
  obtain ⟨c,hc,hact⟩ := section5_powered_matrix_decoder_circuit (Section5DecoderLayout.scoreField N b) Section5DecoderLayout.records
    (Section5DecoderLayout.realField N b) (Section5DecoderLayout.imagField N b) (Section5DecoderLayout.scoreAnc N K b f) (Section5DecoderLayout.code N K b f Wire.scoreScratch)
    (Section5DecoderLayout.scanControl N K b f) (Section5DecoderLayout.scanCarry N K b f) (Section5DecoderLayout.normAccumulator N K b f) (Section5DecoderLayout.normAnc N K b f)
    (Section5DecoderLayout.code N K b f Wire.normScratch) (Section5DecoderLayout.output N K b f) hf hfit Section5DecoderLayout.records_disjoint
    hre him hri hpa hpt hta hctrl hscan hca hnpa hntp hnta hdst hndst hnpf hnaf hntf hdf
  refine ⟨c,hc,?_⟩
  intro z hz M hM hpower ε hε hε' hiter hbits w hw herror
  have hmatrix : section5_record_integer_matrix Section5DecoderLayout.records (Section5DecoderLayout.realField N b) (Section5DecoderLayout.imagField N b) z=
      M.power (K+1) := (Section5DecoderLayout.record_matrix_read z).trans hpower
  apply hact z (hz _ rfl) (fun j => hz _ rfl) ?_ (fun i => hz _ rfl) (fun j => hz _ rfl)
    (hz _ rfl) (fun j => hz _ rfl) (fun e => hz _ rfl) (fun i e => hz _ rfl)
    M hM hmatrix ε hε hε' hiter hbits w hw herror
  intro i e
  rw [Section5DecoderLayout.records_score]
  exact hz _ rfl

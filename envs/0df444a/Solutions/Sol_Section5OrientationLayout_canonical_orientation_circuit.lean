-- Prove2me | solution 1 for Section5OrientationLayout.canonical_orientation_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:50:34.492841+00:00
-- url     : https://prove2.me/submissions/79e90e88-83af-4195-be49-57ac0d1578f1

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
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Definitions.Def_Section5Verified_Section5FixedPointOutputCircuit
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5OrientationLayout
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
import Theorems.Thm_section5_orientation_postprocessor
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

namespace Section5OrientationLayout





























@[simp] theorem split_symm_data (n q a : ℕ) (d : DataWire n a → Bool)
    (s : Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)) (w : DataWire n a) :
    (split n q a).symm (d,s) (code n q a (.inl w))=d w := by
  change (match (code n q a).symm (code n q a (.inl w)) with
    | .inl v => d v | .inr (i,e) => ![s.1,s.2.1,s.2.2] i e)=_
  rw [Equiv.symm_apply_apply]

@[simp] theorem split_symm_sample (n q a : ℕ) (d : DataWire n a → Bool)
    (s : Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)) (i : Fin 3) (e : Fin (n*q+1)) :
    (split n q a).symm (d,s) (code n q a (.inr (i,e)))= ![s.1,s.2.1,s.2.2] i e := by
  change (match (code n q a).symm (code n q a (.inr (i,e))) with
    | .inl v => d v | .inr (j,b) => ![s.1,s.2.1,s.2.2] j b)=_
  rw [Equiv.symm_apply_apply]







end Section5OrientationLayout

end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example
namespace Section5OrientationLayout
end Section5OrientationLayout
open Section5OrientationLayout
theorem solution (n q a f : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) :
    ∃ c : Circuit gatesRev (Section5OrientationLayout.width n q a),
      c.size ≤ (128*(n+a+34)^4+1)*3+3+19*(a+2)*n ∧
      ∀ x : Fin n → Qubits (a+1), ∀ w : EuclideanSpace ℝ (Fin n),
      ∀ s : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
        ∃ z' : Qubits (Section5OrientationLayout.width n q a),
          act c.unitary (ket ((Section5OrientationLayout.split n q a).symm (Section5OrientationLayout.estimateBits x,section5_labelled_three_qex_outcome w s)))=
            ket z' ∧ Section5OrientationLayout.readout f z'=section5_oriented_direction w (Section5OrientationLayout.estimateVector f x) s := by
  have hpair : ∀ i j, i ≠ j → ∀ e b,
      Section5OrientationLayout.comparator (n:=n) (q:=q) (a:=a) i e ≠ Section5OrientationLayout.comparator j b := by
    intro i j hij e b h
    have he := Sum.inl.inj ((Section5OrientationLayout.code n q a).injective h)
    exact hij (Section5OrientationLayout.DataWire.comparator.inj he).1
  have hpa : ∀ i e j, Section5OrientationLayout.comparator (n:=n) (q:=q) (a:=a) i e ≠ Section5OrientationLayout.comparisonAnc n q a j := by
    intro i e j h
    have he := (Section5OrientationLayout.code n q a).injective h
    cases he
  have htp : ∀ i, Section5OrientationLayout.code n q a (.inl .scratch) ∉ Set.range (Section5OrientationLayout.comparator i) := by
    rintro i ⟨e,he⟩
    have h := (Section5OrientationLayout.code n q a).injective he
    cases h
  have hta : ∀ j, Section5OrientationLayout.code n q a (.inl .scratch) ≠ Section5OrientationLayout.comparisonAnc n q a j := by
    intro j h
    have he := (Section5OrientationLayout.code n q a).injective h
    cases he
  have hut : ∀ i e, Section5OrientationLayout.input (n:=n) (q:=q) (a:=a) i e ≠ Section5OrientationLayout.code n q a (.inl .scratch) := by
    intro i e h
    have he := (Section5OrientationLayout.code n q a).injective h
    cases he
  have hxt : ∀ i e, Section5OrientationLayout.examples (n:=n) (q:=q) (a:=a) i e ≠ Section5OrientationLayout.code n q a (.inl .scratch) := by
    intro i e h
    have he := (Section5OrientationLayout.code n q a).injective h
    cases he
  have hup : ∀ i e j, Section5OrientationLayout.input (n:=n) (q:=q) (a:=a) i e ∉ Set.range (Section5OrientationLayout.comparator j) := by
    rintro i e j ⟨b,hb⟩
    have he := (Section5OrientationLayout.code n q a).injective hb
    cases he
  have hxp : ∀ i e j, Section5OrientationLayout.examples (n:=n) (q:=q) (a:=a) i e ∉ Set.range (Section5OrientationLayout.comparator j) := by
    rintro i e j ⟨b,hb⟩
    have he := (Section5OrientationLayout.code n q a).injective hb
    cases he
  have hxa : ∀ i e j, Section5OrientationLayout.examples (n:=n) (q:=q) (a:=a) i e ≠ Section5OrientationLayout.comparisonAnc n q a j := by
    intro i e j h
    have he := (Section5OrientationLayout.code n q a).injective h
    cases he
  have hlp : ∀ i j, Section5OrientationLayout.labels n q a i ∉ Set.range (Section5OrientationLayout.comparator j) := by
    rintro i j ⟨b,hb⟩
    have he := (Section5OrientationLayout.code n q a).injective hb
    cases he
  have hcp : ∀ j, Section5OrientationLayout.code n q a (.inl .flip) ∉ Set.range (Section5OrientationLayout.comparator j) := by
    rintro j ⟨b,hb⟩
    have he := (Section5OrientationLayout.code n q a).injective hb
    cases he
  have hsap : ∀ e j, Section5OrientationLayout.signAnc n q a e ∉ Set.range (Section5OrientationLayout.comparator j) := by
    rintro e j ⟨b,hb⟩
    have he := (Section5OrientationLayout.code n q a).injective hb
    cases he
  have hop : ∀ i e j, Section5OrientationLayout.output (n:=n) (q:=q) (a:=a) i e ∉ Set.range (Section5OrientationLayout.comparator j) := by
    rintro i e j ⟨b,hb⟩
    have he := (Section5OrientationLayout.code n q a).injective hb
    cases he
  have hopair : ∀ i j, i ≠ j → ∀ e b,
      Section5OrientationLayout.output (n:=n) (q:=q) (a:=a) i e ≠ Section5OrientationLayout.output j b := by
    intro i j hij e b h
    have he := Sum.inl.inj ((Section5OrientationLayout.code n q a).injective h)
    exact hij (Section5OrientationLayout.DataWire.output.inj he).1
  have hio : ∀ i j e b, Section5OrientationLayout.input (n:=n) (q:=q) (a:=a) i e ≠ Section5OrientationLayout.output j b := by
    intro i j e b h
    have he := (Section5OrientationLayout.code n q a).injective h
    cases he
  have hco : ∀ i e, Section5OrientationLayout.code n q a (.inl .flip) ≠ Section5OrientationLayout.output i e := by
    intro i e h
    have he := (Section5OrientationLayout.code n q a).injective h
    cases he
  have hcsa : ∀ e, Section5OrientationLayout.code n q a (.inl .flip) ≠ Section5OrientationLayout.signAnc n q a e := by
    intro e h
    have he := (Section5OrientationLayout.code n q a).injective h
    cases he
  have hosa : ∀ i e b, Section5OrientationLayout.output (n:=n) (q:=q) (a:=a) i e ≠ Section5OrientationLayout.signAnc n q a b := by
    intro i e b h
    have he := (Section5OrientationLayout.code n q a).injective h
    cases he
  have hic : ∀ i e, Section5OrientationLayout.input (n:=n) (q:=q) (a:=a) i e ≠ Section5OrientationLayout.code n q a (.inl .flip) := by
    intro i e h
    have he := (Section5OrientationLayout.code n q a).injective h
    cases he
  obtain ⟨c,hc,hact⟩ := section5_orientation_postprocessor hn hgrid f Section5OrientationLayout.input Section5OrientationLayout.output Section5OrientationLayout.examples (Section5OrientationLayout.labels n q a)
    Section5OrientationLayout.comparator (Section5OrientationLayout.comparisonAnc n q a) (Section5OrientationLayout.code n q a (.inl .scratch)) (Section5OrientationLayout.signAnc n q a)
    (Section5OrientationLayout.code n q a (.inl .flip)) hpair hpa htp hta hut hxt hup hxp hxa hlp hcp hsap hop hopair hio hco hcsa hosa hic
  refine ⟨c,hc,?_⟩
  intro x w s
  let z := (Section5OrientationLayout.split n q a).symm (Section5OrientationLayout.estimateBits x,section5_labelled_three_qex_outcome w s)
  have hdata (d : Section5OrientationLayout.DataWire n a) : z (Section5OrientationLayout.code n q a (.inl d))=Section5OrientationLayout.estimateBits x d := Section5OrientationLayout.split_symm_data _ _ _ _ _ d
  have hzero (d : Section5OrientationLayout.DataWire n a) (hd : Section5OrientationLayout.estimateBits x d=false) : z (Section5OrientationLayout.code n q a (.inl d))=false :=
    (hdata d).trans hd
  have hsample (i : Fin 3) (e : Fin (n*q+1)) : z (Section5OrientationLayout.code n q a (.inr (i,e)))=
      ![(section5_labelled_three_qex_outcome w s).1,(section5_labelled_three_qex_outcome w s).2.1,
        (section5_labelled_three_qex_outcome w s).2.2] i e := Section5OrientationLayout.split_symm_sample _ _ _ _ _ i e
  have hex (i : Fin 3) : z ∘ Section5OrientationLayout.examples (n:=n) (q:=q) (a:=a) i= ![s.1,s.2.1,s.2.2] i := by
    funext e
    change z (Section5OrientationLayout.code n q a (.inr (i,e.castSucc)))=_
    rw [hsample]
    fin_cases i <;> simp [section5_labelled_three_qex_outcome,section5_labelled_qex_outcome]
  have hlabels : ∀ i, z (Section5OrientationLayout.labels n q a i)=decide (ltf w 0 (gridPoint (z ∘ Section5OrientationLayout.examples i))= -1) := by
    intro i
    change z (Section5OrientationLayout.code n q a (.inr (i,Fin.last (n*q))))=_
    rw [hsample,hex i]
    fin_cases i <;> simp [section5_labelled_three_qex_outcome,section5_labelled_qex_outcome]
    all_goals exact decide_eq_decide.mpr Iff.rfl
  have hvector : (WithLp.toLp 2 fun i => readFp (section5_msb_register (Section5OrientationLayout.input i)) f z)=Section5OrientationLayout.estimateVector f x := by
    ext i
    change fpVal (a+1) f (fun e => z (Section5OrientationLayout.code n q a (.inl (.estimate i e.rev))))=
      fpVal (a+1) f (section5_lsb_to_msb (x i))
    congr 1
    funext e
    exact hdata (.estimate i e.rev)
  obtain ⟨z',hz',hoff,hread⟩ := hact z (hzero .scratch rfl) (fun e => hzero (.comparisonAnc e) rfl)
    (fun i e => hzero (.comparator i e) rfl) (hzero .flip rfl)
    (fun e => hzero (.signAnc e) rfl) (fun i e => hzero (.output i e) rfl)
  refine ⟨z',hz',?_⟩
  have hh := hread w hlabels
  rw [hvector,hex 0,hex 1,hex 2] at hh
  exact hh

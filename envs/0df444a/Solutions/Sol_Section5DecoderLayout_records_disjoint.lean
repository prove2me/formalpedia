-- Prove2me | solution 1 for Section5DecoderLayout.records_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:18.178466+00:00
-- url     : https://prove2.me/submissions/d75bd9cf-5578-4891-90a4-088d4d2d7755

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
import Definitions.Def_Section5Verified_Section5DecoderLayout
import Definitions.Def_Section5Verified_Section5DecoderLayoutLaws
import Mathlib
import Theorems.Thm_Section5DecoderLayout_records_columnLabel
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout
theorem solution {N K b f : ℕ} (i j : Fin (N+1)) (hij : i ≠ j) :
    ∀ e g, Section5DecoderLayout.records (K:=K) (b:=b) (f:=f) i e ≠ Section5DecoderLayout.records j g := by
  intro e g h
  have hh := congrArg (fun v => Section5DecoderLayout.columnLabel ((Section5DecoderLayout.code N K b f).symm v)) h
  rw [Section5DecoderLayout.records_columnLabel,Section5DecoderLayout.records_columnLabel] at hh
  exact hij (Option.some.inj hh)

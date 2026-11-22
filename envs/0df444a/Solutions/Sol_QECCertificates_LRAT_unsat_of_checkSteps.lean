-- Prove2me | solution 1 for QECCertificates.LRAT.unsat_of_checkSteps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:29.510298+00:00
-- url     : https://prove2.me/submissions/c4173783-d13d-4144-af64-1bce5a340dbc

module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Lemmas
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Theorems.Thm_QECCertificates_LRAT_checkSteps_sound

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {F : CNF} {steps : List LStep}
    (h : checkSteps F steps = true) : ¬ Satisfiable F := checkSteps_sound h
end QECCertificates.LRAT

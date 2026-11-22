-- Prove2me | solution 1 for QECCertificates.LRAT.checkSteps_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:01.55615+00:00
-- url     : https://prove2.me/submissions/a332fe37-2fa3-4ae2-b253-68cab802c968

module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Lemmas
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Theorems.Thm_QECCertificates_LRAT_checkAux_sound

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {F : CNF} {steps : List LStep}
    (h : checkSteps F steps = true) : ¬ Satisfiable F := by
  rintro ⟨σ, hσ⟩
  exact checkAux_sound ClauseDB.array (ClauseDB.array.ofCNF F) steps
    (fun C hC => hσ C (ClauseDB.array.ofCNF_mem hC)) h
end QECCertificates.LRAT

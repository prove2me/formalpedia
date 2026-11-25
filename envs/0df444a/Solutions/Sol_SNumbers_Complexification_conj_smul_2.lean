-- Prove2me | solution 2 for SNumbers.Complexification.conj_smul
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T04:33:23.98894+00:00
-- url     : https://prove2.me/submissions/ccd480b5-697c-47e5-9845-d2006ef98789

module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Module
public import Definitions.Def_BasicResults_Spectral_Complexification
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open RCLike Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
open SNumbers
open SNumbers.Complexification

/-- Conjugation on the complexification is conjugate-linear: it intertwines `c •` with
`star c •`. -/
theorem solution (c : ℂ) (u : Complexification H) :
    conj (c • u) = (starRingEnd ℂ c) • conj u := by
  apply Prod.ext <;>
    simp only [conj_fst, conj_snd, smul_fst, smul_snd, Complex.conj_re, Complex.conj_im] <;>
    module

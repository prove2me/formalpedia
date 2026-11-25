-- Prove2me | solution 1 for SNumbers.Complexification.conj_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:23:32.90698+00:00
-- url     : https://prove2.me/submissions/7d0e6fc5-2ed7-4796-b89c-10620e4794d5

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
namespace SNumbers.Complexification
theorem _root_.solution (c : ℂ) (u : Complexification H) :
    conj (c • u) = (starRingEnd ℂ c) • conj u := by
  apply Prod.ext <;>
    simp only [conj_fst, conj_snd, smul_fst, smul_snd, Complex.conj_re, Complex.conj_im] <;> module
end SNumbers.Complexification

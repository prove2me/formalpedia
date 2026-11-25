-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.NullPf.exists_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:49:04.514532+00:00
-- url     : https://prove2.me/submissions/c07686d8-fa10-4fd7-b691-ed8695958d9f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetEqZeroOfRankLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Module
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.SP.NullPf
variable {K : Type*} [Field K]
namespace PositivityTheory.Rg.Sw.SP.NullPf
theorem _root_.solution {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] (M : Matrix m n K) {k : ℕ} (hk : k ≤ M.rank) :
    ∃ I : Fin k ↪ m, LinearIndependent K (fun p => M (I p)) := by
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent K (Set.range M.row)
  have hfin : b.Finite := (Set.finite_range _).subset hbs
  have : Fintype b := hfin.fintype
  have hcard : M.rank = b.toFinset.card := by
    rw [M.rank_eq_finrank_span_row, ← hspan]
    exact finrank_span_set_eq_card hli
  have hkb : k ≤ Fintype.card b := by rw [← Set.toFinset_card]; omega
  let e : Fin k ↪ b := (Fin.castLEEmb hkb).trans (Fintype.equivFin b).symm.toEmbedding
  let sec : b → m := fun v => (hbs v.2).choose
  have hsec : ∀ v : b, M.row (sec v) = v := fun v => (hbs v.2).choose_spec
  have hinj : Function.Injective sec := by
    intro v w h
    apply Subtype.ext
    rw [← hsec v, ← hsec w, h]
  refine ⟨e.trans ⟨sec, hinj⟩, ?_⟩
  have h2 : (fun p => M ((e.trans ⟨sec, hinj⟩) p)) = (fun v : b => (v : n → K)) ∘ e := by
    funext p
    simp only [Function.comp_apply, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
    exact hsec (e p)
  rw [h2]
  exact hli.comp e e.injective
end PositivityTheory.Rg.Sw.SP.NullPf

-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.hamiltonian_commute_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:39:13.847695+00:00
-- url     : https://prove2.me/submissions/e747f5fa-e437-4a1e-af4f-cf77d02bd661

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_commute_selected
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_syndrome_resolution


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_807a85e857_19
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_807a85e857_20
namespace QEC.Coding.CSSGibbs
theorem _root_.solution (A : Finset (Realizable P Q)) :
    Commute (hamiltonian P Q) (selectedProjector P Q horth A) := by
  rw [hamiltonian_syndrome_resolution P Q horth]
  apply Commute.sum_left
  intro s _
  exact (projector_commute_selected P Q horth s A).smul_left _
end QEC.Coding.CSSGibbs

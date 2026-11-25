-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_add_index_le_of_strictAnti_2e47e0a48638
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:24:13.925211+00:00
-- url     : https://prove2.me/submissions/a8b0fa4e-7858-4c3c-92a6-e8710c7d65f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombSortShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset Equiv
open GroundTheory.Heights₂.Heights.RestTerms.Comb
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
theorem _root_.solution {m : ℕ} {f : Fin m → ℕ} (hf : StrictAnti f) (a b : Fin m)
    (hab : a ≤ b) : f b + (b : ℕ) ≤ f a + (a : ℕ) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have h1 := ih (by omega)
    have h2 : f ⟨n + 1, hb⟩ < f ⟨n, by omega⟩ := hf (by simp [Fin.lt_def])
    simp only at h1 ⊢
    omega
end GroundTheory.Heights₂.Heights.RestTerms.Comb

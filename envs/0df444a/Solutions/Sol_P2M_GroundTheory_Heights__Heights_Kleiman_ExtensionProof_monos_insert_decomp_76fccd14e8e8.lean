-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_monos_insert_decomp_76fccd14e8e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:01:21.6978+00:00
-- url     : https://prove2.me/submissions/00a5faff-f4a1-4dbc-ba3f-97e1d92140d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
theorem _root_.solution {i : Fin (N + 1)} {J : Finset (Fin (N + 1))} {s : Poly S N}
    (hs : s ∈ monos (insert i J)) : ∃ (p : ℕ) (t : Poly S N), t ∈ monos J ∧ s = X i ^ p * t := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨k, hk, rfl⟩ := ha
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hk) with rfl | hk'
    · exact ⟨1, 1, one_mem _, by ring⟩
    · exact ⟨0, X k, X_mem_monos hk', by ring⟩
  | one => exact ⟨0, 1, one_mem _, by ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨p, t, ht, rfl⟩ := ha
    obtain ⟨p', t', ht', rfl⟩ := hb
    exact ⟨p + p', t * t', mul_mem ht ht', by ring⟩
end GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof

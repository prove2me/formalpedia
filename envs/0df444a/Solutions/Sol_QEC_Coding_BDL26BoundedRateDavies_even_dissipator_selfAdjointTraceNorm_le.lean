-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.even_dissipator_selfAdjointTraceNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:24:44.386304+00:00
-- url     : https://prove2.me/submissions/fabbd29c-aff8-4213-99be-78ab9b02f1bc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_dissipator_selfAdjointTraceNorm_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26BoundedRateDavies
theorem _root_.solution (k : Nat)
    (rate : CouplingIndex S (2*k) → BDL26CSSDaviesLocality.Frequency S (2*k) → ℝ) (hmax : ℝ)
    (hm : 0 ≤ hmax) (hn : ∀ qa ω, 0 ≤ rate qa ω) (hu : ∀ qa ω, rate qa ω ≤ hmax) :
    selfAdjointTraceNormOneToOne (dissipator S (2*k) rate) ≤
      6 * Fintype.card (Physical S (2*k)) * hmax :=
  dissipator_selfAdjointTraceNorm_le S (2*k) rate hmax hm hn hu
end QEC.Coding.BDL26BoundedRateDavies

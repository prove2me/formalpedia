-- Prove2me | solution 1 for QEC.QLDPC.QuantumCodeFamily.boundedLocality_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:28:49.331946+00:00
-- url     : https://prove2.me/submissions/66797d55-f01b-4df0-aeff-26be45de9573

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily

set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC.QuantumCodeFamily
theorem _root_.solution (F : QuantumCodeFamily A ι κ) (a : A) (bound : Nat) :
    Coding.BoundedLocality (F.localityProfile a) bound ↔
      F.maxCheckWeight a ≤ bound ∧ F.maxVariableDegree a ≤ bound :=
  Iff.rfl
end QEC.QLDPC.QuantumCodeFamily

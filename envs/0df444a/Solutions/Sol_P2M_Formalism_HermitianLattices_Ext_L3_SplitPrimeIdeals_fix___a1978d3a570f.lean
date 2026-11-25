-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_fix___a1978d3a570f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:31.531386+00:00
-- url     : https://prove2.me/submissions/4b1a8e72-244f-4854-b84e-be0abe087ca4

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondVariant_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NotIsPrimeMapOfSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
variable {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} {σ : B →+* B}
namespace Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
theorem _root_.solution (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι) (a : A) : σ (ι a) = ι a :=
  (hfix _).2 ⟨a, rfl⟩
end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals

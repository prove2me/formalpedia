-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap___comap_ebbf3c779431
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:53:00.253151+00:00
-- url     : https://prove2.me/submissions/5cd0c543-e4c8-47d5-ad92-7963529bbffb

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondVariant_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NotIsPrimeMapOfSplit
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_fix___a1978d3a570f

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
theorem _root_.solution (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι) (P : Ideal B) :
    (P.comap σ).comap ι = P.comap ι := by
  ext a
  simp only [Ideal.mem_comap, fix_ι hfix]
end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals

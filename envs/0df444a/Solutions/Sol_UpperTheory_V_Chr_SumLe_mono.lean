-- Prove2me | solution 1 for UpperTheory.V.Chr.SumLe.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:45.040889+00:00
-- url     : https://prove2.me/submissions/c26f3cef-3949-451a-b47d-620e4626d53e

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CharacterLevelBounds_ShaFamMono
import Theorems.Thm_UpperTheory_V_Chr_nrm_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base
open UpperTheory UpperTheory.V UpperTheory.V.Chr
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ) [Fact l.Prime]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O]
namespace UpperTheory.V.Chr
namespace SumLe
theorem _root_.solution {f g : ℕ → ℕ∞} {t : ℕ} {B : ℝ} (h : SumLe l O g t B) (hf : ∀ e, 0 < e → e < t → f e ≤ g e) :
    SumLe l O f t B := by
  refine ⟨fun e h1 h2 => ne_top_of_le_ne_top (h.1 e h1 h2) (hf e h1 h2), le_trans ?_ h.2⟩
  refine Finset.sum_le_sum fun e he => ?_
  rw [Finset.mem_Ico] at he
  exact nrm_mono l (hf e he.1 he.2) (h.1 e he.1 he.2)
end SumLe
end UpperTheory.V.Chr

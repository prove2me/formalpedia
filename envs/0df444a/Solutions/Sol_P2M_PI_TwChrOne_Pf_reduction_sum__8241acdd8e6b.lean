-- Prove2me | solution 1 for P2M_PI_TwChrOne_Pf_reduction_sum__8241acdd8e6b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:28.403202+00:00
-- url     : https://prove2.me/submissions/e965b84d-443c-4878-8350-83c69bfcc81f

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwChrOne.Pf
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  have h1 : ((∑ i ∈ s, (⟨f i, hf i⟩ : intS P) : intS P) : E) = ∑ i ∈ s, f i := by simp
  rw [← h1]
  exact map_sum (redH P) (fun i => (⟨f i, hf i⟩ : intS P)) s
end PI.TwChrOne.Pf

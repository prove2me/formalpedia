-- Prove2me | solution 1 for UpperTheory.Ram.not_dvd_condN_of_unram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:27.635532+00:00
-- url     : https://prove2.me/submissions/1dde5e04-44b7-416b-865e-ad38c6eb0080

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_CondSq
import Theorems.Thm_UpperTheory_Ram_mem_sq_of_dvd_condN
import Theorems.Thm_UpperTheory_Ram_exists_place_over

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open UpperTheory UpperTheory.Ram
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
namespace UpperTheory.Ram
theorem _root_.solution {p : ℕ} (hp : p.Prime)
    (h : ∀ w : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ w.asIdeal → (p : 𝓞 H.E) ∉ w.asIdeal ^ 2) :
    ¬ p ∣ H.QS * H.q * H.d := fun hd => by
  obtain ⟨w, hw⟩ := exists_place_over H.E hp
  exact h w hw (mem_sq_of_dvd_condN H hp hd w.asIdeal w.isPrime hw)
end UpperTheory.Ram

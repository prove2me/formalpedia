-- Prove2me | solution 1 for PI.charpoly_int_of_powers_in_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:51.101928+00:00
-- url     : https://prove2.me/submissions/a20bab83-2439-429f-9dfa-1e1e5ba6c858

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicFiniteOrder_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI
open NumberField IsDedekindDomain TensorProduct Matrix
namespace PI
theorem _root_.solution (hT : TensCpctDen) (hP : PowBddInt)
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ)
    (γ : Matrix (Fin k) (Fin k) E) :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ C : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F), IsCompact C →
    (∀ (n : ℕ) (i j : Fin k), inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) ((γ ^ n) i j) ∈ C) →
    ∀ i, IsIntegral ℤ (γ.charpoly.coeff i) := by
  let _ := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  intro C hC hmem
  obtain ⟨N, hN, hNC⟩ := hT F E C hC
  exact hP E k γ N hN (fun n i j => hNC _ (hmem n i j))
end PI

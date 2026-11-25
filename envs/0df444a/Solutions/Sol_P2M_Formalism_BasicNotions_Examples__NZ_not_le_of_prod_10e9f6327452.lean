-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_not_le_of_prod_10e9f6327452
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:32:15.024065+00:00
-- url     : https://prove2.me/submissions/00ae9703-746e-42fb-bd6a-aa69b805e6de

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZColB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open IsDedekindDomain
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {V : Type*} [AddCommGroup V] [Module R V]
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {S : Finset (HeightOneSpectrum R)} (m : HeightOneSpectrum R → ℕ) (w : HeightOneSpectrum R)
    (hw : w ∉ S) : ¬ (∏ v ∈ S, v.asIdeal ^ m v) ≤ w.asIdeal := by
  intro h
  obtain ⟨v, hv, hle⟩ := (w.isPrime.prod_le).mp h
  have h2 : v.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le hle
  have h3 : v.asIdeal = w.asIdeal := (v.isMaximal).eq_of_le w.isPrime.ne_top h2
  exact hw (HeightOneSpectrum.ext h3 ▸ hv)
end Formalism.BasicNotions.Examples₂.NZ

-- Prove2me | solution 1 for P2M_PI_ClassNumImQ_ZetaNonvanishing__cnt_eq_one_of_71a563f7a539
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:02:38.490641+00:00
-- url     : https://prove2.me/submissions/fdfc645a-65d9-49f8-8033-dae140880965

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_SpanNatCastSupEqTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_GenBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.ClassNumImQ PI.ClassNumImQ.ZetaNonvanishing₂
variable {K : Type} [Field K] [NumberField K]
theorem _root_.solution {n : ℕ} (X : Ideal (𝓞 K)) (hX : Ideal.absNorm X = n)
    (h : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n → I = X) : cnt K n = 1 := by
  show Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} = 1
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext ((h _ a.2).trans (h _ b.2).symm)⟩, ⟨⟨X, hX⟩⟩⟩




-- Prove2me | solution 1 for PI.LocCartanPair.pair_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:15:51.583813+00:00
-- url     : https://prove2.me/submissions/fdda7938-695e-47cc-9d37-de1036b9a0f1

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag
import Theorems.Thm_PI_LocCartanPair_lag_exists
import Theorems.Thm_PI_LocCartanPair_pair_base_of_lag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocCartanPair
open Matrix IsLocalRing
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
  [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
namespace PI.LocCartanPair
theorem _root_.solution (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ))
    {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Even (Fintype.card ι)) (A : Matrix ι ι R)
    (hA : Aᴴ = A) (hdet : IsUnit A.det) (h h₁ : Matrix ι ι R) (c : R)
    (hh : h = c • h₁) (hh₁ : IsUnit h₁.det) :
    ∃ e f : Matrix ι ι R, e * e = e ∧ eᴴ * A = A * (1 - e) ∧ e * h = h * f := by
  obtain ⟨e, he, heA⟩ := lag_exists hR₀ hθ hι A hA hdet
  exact pair_base_of_lag A e h h₁ c hh hh₁ he heA
end PI.LocCartanPair

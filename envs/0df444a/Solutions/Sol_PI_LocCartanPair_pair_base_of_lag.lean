-- Prove2me | solution 1 for PI.LocCartanPair.pair_base_of_lag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:17.196838+00:00
-- url     : https://prove2.me/submissions/d704db48-b24a-4df3-b3af-05753d36b796

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (A e h h₁ : Matrix ι ι R) (c : R)
    (hh : h = c • h₁) (hh₁ : IsUnit h₁.det) (he : e * e = e) (heA : eᴴ * A = A * (1 - e)) :
    ∃ e f : Matrix ι ι R, e * e = e ∧ eᴴ * A = A * (1 - e) ∧ e * h = h * f := by
  refine ⟨e, h₁⁻¹ * e * h₁, he, heA, ?_⟩
  rw [hh, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    mul_nonsing_inv h₁ hh₁, Matrix.one_mul]
end PI.LocCartanPair

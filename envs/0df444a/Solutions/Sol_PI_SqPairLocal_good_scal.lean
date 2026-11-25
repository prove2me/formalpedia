-- Prove2me | solution 1 for PI.SqPairLocal.good_scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:39.596217+00:00
-- url     : https://prove2.me/submissions/f764a11b-93c1-4b4b-b400-ecf78d5fd1f3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SplitPlaceOf
import Theorems.Thm_PI_SqPairLocal_scal_sq
import Theorems.Thm_PI_SqPairLocal_scal_adj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField Matrix
namespace PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
private lemma smallAt_smul_one_of_dv {Q : Ideal (𝓞 E)} {c a : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}
    (h : Dv Q c a) : SmallAt Q c L (((a : 𝓞 E) : E) • (1 : Matrix (Fin N) (Fin N) E)) := by
  unfold Dv at h
  unfold SmallAt
  intro y hy
  obtain ⟨s, hs, w, hw⟩ := h
  refine ⟨s, hs, w • y, L.smul_mem w hy, ?_⟩
  have key : ∀ (r : 𝓞 E) (z : Fin N → E), r • z = (r : E) • z := fun r z => rfl
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, key, smul_smul]
  congr 1
  exact_mod_cast hw
end PI.SqPairLocal
end
end

set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution {Q : Ideal (𝓞 E)} [Q.IsPrime] {c : 𝓞 E} {L' L'' : Submodule (𝓞 E) (Fin N → E)}
    {ε : 𝓞 E} (h1 : Dv Q c (ε * (ε - 1))) (h2 : Dv Q c (ε + cj E ε - 1)) :
    Good Q c L' L'' ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) := by
  unfold Good
  rw [scal_sq, scal_adj]
  repeat' constructor
  all_goals first | exact smallAt_smul_one_of_dv h1 | exact smallAt_smul_one_of_dv h2
end PI.SqPairLocal

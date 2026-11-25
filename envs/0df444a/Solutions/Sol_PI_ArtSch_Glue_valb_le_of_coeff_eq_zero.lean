-- Prove2me | solution 1 for PI.ArtSch.Glue.valb_le_of_coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:11.825187+00:00
-- url     : https://prove2.me/submissions/c6109e3e-ff0a-4860-bfd2-cee940141ed1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationGluing_ValbLeOfCoeffEqZero
import Theorems.Thm_PI_ArtSch_Glue_coeff_add_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.Glue
open scoped NNReal
noncomputable section
variable {l : ℕ} [hl : Fact l.Prime]
namespace PI.ArtSch.Glue
theorem _root_.solution (r : OCb l) (n : ℕ) (hr : PreTilt.coeff n r = 0) :
    valb l r ≤ (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l) ^ (l ^ n) := by
  by_cases h0 : r = 0
  · rw [h0, map_zero]; exact zero_le
  have hex : ∃ m, PreTilt.coeff m r ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact h0 (Perfection.ext fun m => (hall m).trans (map_zero _).symm)
  obtain ⟨N, hM⟩ : ∃ N, PreTilt.coeff (N + n) r ≠ 0 :=
    ⟨_, PreTilt.coeff_nat_find_add_ne_zero (h := hex) n⟩
  have hk : PreTilt.coeff (N + n) r ^ (l ^ N) = 0 := by
    have h1 := coeff_add_pow r n (N)
    rw [hr, Nat.add_comm] at h1
    exact h1
  show PreTilt.valAux (PadicComplex l) (PadicComplex.valued l).v (OC l) l r ≤ _
  rw [PreTilt.valAux_eq (PadicComplexInt.integers l) hM]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff (N + n) r)
  rw [← hy, ModP.preVal_mk (PadicComplexInt.integers l) (by rw [hy]; exact hM)]
  have hdiv : ((l : ℕ) : OC l) ∣ y ^ (l ^ N) := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_pow, hy]
    exact hk
  have hle := (PadicComplexInt.integers l).le_of_dvd hdiv
  rw [map_pow, map_pow, map_natCast] at hle
  rw [pow_add, pow_mul]
  exact pow_le_pow_left₀ zero_le hle _
end PI.ArtSch.Glue

-- Prove2me | solution 1 for PI.TwChrOne.Pf.Mb_mul_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:36.606226+00:00
-- url     : https://prove2.me/submissions/d59f1da4-8839-4559-b071-a6509f60e30a

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
import Theorems.Thm_PI_TwChrOne_Pf_reduction_mul
import Theorems.Thm_P2M_PI_TwChrOne_Pf_reduction_sum__8241acdd8e6b
import Theorems.Thm_PI_TwChrOne_Pf_apply_eq_sum
import Theorems.Thm_PI_TwChrOne_Pf_dI_inj
import Theorems.Thm_PI_TwChrOne_Pf_atN_dI

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
variable {n : ℕ}
variable {kj N c : ℕ}
namespace PI.TwChrOne.Pf
theorem _root_.solution {r g h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)}
    (hDA : ∀ i : Fin (N + c), kj ≤ i.1 → i.1 < N → ∀ j : Fin (N + c), ¬(kj ≤ j.1 ∧ j.1 < N) →
      redP P (r (Loc.eN E (N + c) j.1) i) = 0)
    (hrI : ∀ (j : ℕ) i, IntAt P (r (Loc.eN E (N + c) j) i))
    (hgI : ∀ (j : ℕ) i, IntAt P (g (Loc.eN E (N + c) j) i))
    (hh : ∀ t : Fin (N - kj), h (Loc.eN E (N + c) (kj + t.1)) = r (g (Loc.eN E (N + c) (kj + t.1)))) :
    Mb P kj N c h = Mb P kj N c r * Mb P kj N c g := by
  ext s t
  have key : ∀ m : Fin (N + c), ¬(kj ≤ m.1 ∧ m.1 < N) →
      redP P (r (Loc.eN E (N + c) m.1) (dI kj N c s)) = 0 :=
    fun m hm => hDA (dI kj N c s) (show kj ≤ kj + s.1 by omega) (show kj + s.1 < N by have := s.2; omega) m hm
  simp only [Mb, Ment, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, atN_dI]
  conv_lhs => rw [hh t, apply_eq_sum r, reduction_sum₂ P _ _ fun m => (intS P).mul_mem (hgI _ m) (hrI _ _)]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨dI kj N c, dI_inj⟩)) ?_, Finset.sum_map]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [reduction_mul P (hgI _ _) (hrI _ _)]
    exact mul_comm _ _
  · intro m _ hm
    have hD : ¬(kj ≤ m.1 ∧ m.1 < N) := by
      rintro ⟨h1, h2⟩
      exact hm (Finset.mem_map.2 ⟨⟨m.1 - kj, by omega⟩, Finset.mem_univ _,
        Fin.ext (show kj + (m.1 - kj) = m.1 by omega)⟩)
    rw [reduction_mul P (hgI _ _) (hrI _ _), key m hD, mul_zero]
end PI.TwChrOne.Pf

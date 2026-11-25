-- Prove2me | solution 1 for P2M_Formalism_HermitianLatticeCounting_P_coveringO__of_transference_9aab640b96fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:43:40.875417+00:00
-- url     : https://prove2.me/submissions/1f3dd0d8-1040-4594-bb10-7b0960b8a66a

import Definitions.Def_Formalism_FlagUnipotentLattices_SubmoduleGeneratorsBound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SumComplexEmbeddingsEqSumInfinitePlace
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumTupleOfLatticeSumTuple
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_four_mul_card_le_norm_sq_mul_discr
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5bLat_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open NumberField
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hT : Transference) : CoveringO' := by
  intro E _ _ hc x
  classical
  set f := Fintype.card (InfinitePlace E) with hf'
  have hf0 : 0 < f := Fintype.card_pos
  have hfR : (0:ℝ) < f := by exact_mod_cast hf0
  have hn : finrank ℚ E = 2 * f := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have h2 : InfinitePlace.nrRealPlaces E = 0 := by
      have : IsEmpty {w : InfinitePlace E // w.IsReal} :=
        ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (hc w.1)) w.2⟩
      exact Fintype.card_eq_zero
    have h3 : InfinitePlace.nrComplexPlaces E = f :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv hc)
    rw [h2, h3] at h1; omega
  set D : ℝ := |(discr E : ℝ)| with hD
  have hD0 : 0 < D := by
    rw [hD]; exact abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
  set r : ℝ := D ^ (1 / (finrank ℚ E : ℝ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hD0 _
  have hr2 : r ^ 2 = D ^ (1 / (f : ℝ)) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le, hn]
    congr 1; push_cast; field_simp
  set lam : ℝ := 2 * Real.sqrt f / r with hlam
  have hlam0 : 0 < lam := by positivity
  have hdim : finrank ℝ (s5bV E) = 2 * f := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (s5bV E), Complex.finrank_real_complex, finrank_euclideanSpace]
  obtain ⟨l, hl, hle⟩ := hT (s5bV E) (integerEmbeddingLattice hc) lam hlam0 (by
    intro y hy hint
    have hb := four_mul_card_le_norm_sq_mul_discr hc y hy hint
    rw [← hf', ← hr2] at hb
    have h1 : lam ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [hlam, div_pow, mul_pow, Real.sq_sqrt hfR.le, div_le_iff₀ (by positivity)]
      linarith
    exact (pow_le_pow_iff_left₀ hlam0.le (norm_nonneg _) (by norm_num)).mp h1)
    (WithLp.toLp 2 x)
  obtain ⟨a, rfl⟩ := (s5bLat_mem hc l).1 hl
  refine ⟨a, fun w => ?_⟩
  rw [hdim] at hle
  have h1 : ‖(WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)‖ ≤ Real.sqrt f * r / 2 := by
    have h2 : ‖(WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)‖ ≤ ((2 * f : ℕ) : ℝ) / 2 / lam := by
      rw [le_div_iff₀ hlam0]; exact hle
    refine h2.trans (le_of_eq ?_)
    rw [hlam]; push_cast
    have hs : Real.sqrt f * Real.sqrt f = f := Real.mul_self_sqrt hfR.le
    have hs0 : 0 < Real.sqrt f := Real.sqrt_pos.mpr hfR
    field_simp
    nlinarith
  have h3 : ‖x w - w.embedding (a : E)‖ ≤ ‖(WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)‖ :=
    PiLp.norm_apply_le ((WithLp.toLp 2 x : s5bV E) - complexEmbeddingVector (a : E)) w
  refine h3.trans (h1.trans (le_of_eq ?_))
  have h4 : (finrank ℚ E : ℝ) / 2 = f := by rw [hn]; push_cast; ring
  rw [h4]; ring
end Formalism.HermitianLatticeCounting.P

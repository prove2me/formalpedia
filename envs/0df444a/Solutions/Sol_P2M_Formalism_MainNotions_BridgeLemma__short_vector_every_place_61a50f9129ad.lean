-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__short_vector_every_place_61a50f9129ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:45:16.874822+00:00
-- url     : https://prove2.me/submissions/04fe77cc-3013-4b84-8804-0e25821e6812

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__norm_embedding_le_trace_44957880a079
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__conj_inner_self_nonneg_326874735826
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__trace_inner_pos_of_orthonormal_pair_2c4d27f0bf2f
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__covolume_trace_lattice_48d268a15504
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__minkowski_discriminant_ineq_412dc0b620e6
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__exists_short_vector_minkowski_88a123bac9a8
import Theorems.Thm_Formalism_HermitianLatticesTheory_final_genusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_final_traceReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Module Formalism.HermitianLatticesTheory
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) :
    ShortVectorEveryPlace K (2 * (finrank ℚ K : ℝ) * rootDiscriminant K) := by
  intro V _ _ _ _ h L hsymm hL M hM
  obtain ⟨e, hli, hsp, rfl, he⟩ := hL
  haveI : FiniteDimensional K V := Module.Finite.of_basis (Module.Basis.mk hli hsp.ge)
  have hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := fun x hx => trace_inner_pos_of_orthonormal_pair hK h e hli hsp he x hx
  obtain ⟨N, ι, hι, -, hlat⟩ := Formalism.HermitianLatticesTheory.final_traceReal K V h hsymm hpos
  have hLlat : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range e)) :=
    ⟨Submodule.fg_span (Set.finite_range e), by rw [Submodule.span_span_of_tower]; exact hsp⟩
  obtain ⟨iL1, iL2⟩ := hlat _ hLlat
  obtain ⟨familyMassRatio, familyMassSecondLine⟩ := hlat M hM.1
  have hcov := Formalism.HermitianLatticesTheory.final_genusCovol K V h hsymm hpos N ι hι _ M hLlat hM
  obtain ⟨hcL, hN⟩ := covolume_trace_lattice hK h e hli hsp he N ι hι
  set n := Module.finrank ℚ K with hn_def
  subst hN
  have hn : 1 ≤ n := Module.finrank_pos
  have hΔ : 0 < |(discr K : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero K))
  have hrd0 : 0 < rootDiscriminant K := Real.rpow_pos_of_pos hΔ _
  have hrdn : rootDiscriminant K ^ n = |(discr K : ℝ)| := by
    rw [rootDiscriminant, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), ← hn_def, one_div,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (by omega)), Real.rpow_one]
  have hB0 : 0 ≤ 2 * (n : ℝ) * rootDiscriminant K := mul_nonneg (by positivity) hrd0.le
  obtain ⟨v, hvM, hv0, hvR⟩ := exists_short_vector_minkowski (2 * n) (by omega) (zmap ι M) (Real.sqrt (2 * n * rootDiscriminant K))
    (Real.sqrt_nonneg _) (by rw [hcov, hcL]; exact minkowski_discriminant_ineq n hn _ _ hΔ hrdn hrd0)
  obtain ⟨x, hxM, rfl⟩ := hvM
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hv0 (map_zero ι)
  refine ⟨x, hxM, hx0, fun φ => ?_⟩
  have h1 := norm_embedding_le_trace (h x x) (conj_inner_self_nonneg hK h e hli hsp he x) φ
  have h2 : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ‖ι x‖ ^ 2 := by
    rw [← hι x x, real_inner_self_eq_norm_sq]
  have h3 : ‖ι x‖ ^ 2 < 2 * n * rootDiscriminant K := by
    have := pow_lt_pow_left₀ hvR (norm_nonneg _) two_ne_zero
    rwa [Real.sq_sqrt hB0] at this
  linarith
end Formalism.MainNotions.BridgeLemma₂

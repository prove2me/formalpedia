-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__inner_self_ne_zero_of_orthonormal_5dc73cdd2eeb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:21.663564+00:00
-- url     : https://prove2.me/submissions/3ebf4c69-10c2-4194-83a1-5b80e39ac03e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__eq_sum_coords_orthonormal_pair_0215a3f94e35
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_eq_coords_orthonormal_pair_1a25b2c19c4f

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
open NumberField NumberField.mixedEmbedding Formalism.HermitianLatticesTheory
open scoped nonZeroDivisors NNReal ENNReal
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V)
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (hcm : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V) (hx : x ≠ 0) : h x x ≠ 0 := by
  intro h0
  apply hx
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hpar := inner_eq_coords_orthonormal_pair h e hspan ho x x
  rw [h0] at hpar
  have h1 := congrArg φ hpar
  simp only [map_zero, map_add, map_mul, hcm] at h1
  have e0 : ((Complex.normSq (φ (h (e 0) x)) + Complex.normSq (φ (h (e 1) x)) : ℝ) : ℂ) = 0 := by
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    exact h1.symm
  have e0' := Complex.ofReal_eq_zero.1 e0
  have n0 := Complex.normSq_nonneg (φ (h (e 0) x))
  have n1 := Complex.normSq_nonneg (φ (h (e 1) x))
  have hb0 : φ (h (e 0) x) = 0 := Complex.normSq_eq_zero.1 (by linarith)
  have hb1 : φ (h (e 1) x) = 0 := Complex.normSq_eq_zero.1 (by linarith)
  have hb0' : h (e 0) x = 0 := (map_eq_zero_iff φ φ.injective).1 hb0
  have hb1' : h (e 1) x = 0 := (map_eq_zero_iff φ φ.injective).1 hb1
  rw [eq_sum_coords_orthonormal_pair h e hspan ho x, hb0', hb1', zero_smul, zero_smul, add_zero]
end Formalism.MainNotions.BridgeLemma₂

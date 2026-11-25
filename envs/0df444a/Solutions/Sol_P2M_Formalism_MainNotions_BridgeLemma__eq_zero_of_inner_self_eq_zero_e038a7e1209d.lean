-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__eq_zero_of_inner_self_eq_zero_e038a7e1209d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:09.143969+00:00
-- url     : https://prove2.me/submissions/a6d053f7-650e-4235-b8ad-2de05afb6326

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_comb_orthogonal_pair_4a851b395e83

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
open NumberField Formalism.HermitianLatticesTheory Module
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K)
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (hK : IsCMUnram K) (L : Submodule (𝓞 K) V) (hL : IsOrthoLattice h L 2) (v : V)
    (hv : h v v = 0) : v = 0 := by
  obtain ⟨e, hli, hsp, -, horth⟩ := hL
  have hv' : v ∈ Submodule.span K (Set.range e) := by rw [hsp]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv'
  rw [Fin.sum_univ_two] at hv ⊢
  have h01 : h (e 0) (e 1) = 0 := by rw [horth]; simp
  have h10 : h (e 1) (e 0) = 0 := by rw [horth]; simp
  rw [inner_comb_orthogonal_pair h _ _ h01 h10, horth, horth] at hv
  simp only [if_true, mul_one] at hv
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have h2 := congrArg φ hv
  rw [map_add, map_mul, map_mul, hK.2.1, hK.2.1, map_zero] at h2
  have h3 : ((Complex.normSq (φ (c 0)) + Complex.normSq (φ (c 1)) : ℝ) : ℂ) = 0 := by
    push_cast; rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]; exact h2
  have h4 : Complex.normSq (φ (c 0)) + Complex.normSq (φ (c 1)) = 0 := by exact_mod_cast h3
  have h5 := Complex.normSq_nonneg (φ (c 0))
  have h6 := Complex.normSq_nonneg (φ (c 1))
  have h7 : Complex.normSq (φ (c 0)) = 0 := by linarith
  have h8 : Complex.normSq (φ (c 1)) = 0 := by linarith
  have c0 : c 0 = 0 := (map_eq_zero φ).1 (Complex.normSq_eq_zero.1 h7)
  have c1 : c 1 = 0 := (map_eq_zero φ).1 (Complex.normSq_eq_zero.1 h8)
  simp [c0, c1]
end Formalism.MainNotions.BridgeLemma₂

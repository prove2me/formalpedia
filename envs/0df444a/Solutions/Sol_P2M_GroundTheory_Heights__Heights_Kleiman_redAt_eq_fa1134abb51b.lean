-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_redAt_eq_fa1134abb51b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:01:40.022394+00:00
-- url     : https://prove2.me/submissions/5e6bbbd1-2300-429b-a713-07beca282adf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_aeval_ne_zero_of_primeOf_le_25245e7237d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K')
variable {k x y}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
include hsp
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {f s : Poly k N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s.IsHomogeneous e)
    (h : aeval y s ≠ 0) : redAt k x y (aeval x f / aeval x s) = aeval y f / aeval y s := by
  have hex : ∃ (p : Poly k N × Poly k N) (e : ℕ), p.1.IsHomogeneous e ∧ p.2.IsHomogeneous e ∧
      aeval y p.2 ≠ 0 ∧ aeval x f / aeval x s = aeval x p.1 / aeval x p.2 :=
    ⟨(f, s), e, hf, hs, h, rfl⟩
  rw [redAt, dif_pos hex]
  obtain ⟨e', hf', hs', h', heq⟩ := hex.choose_spec
  have hx := aeval_ne_zero_of_primeOf_le hsp hs h
  have hx' := aeval_ne_zero_of_primeOf_le hsp hs' h'
  rw [div_eq_div_iff hx hx'] at heq
  have hhom : (f * hex.choose.2 - hex.choose.1 * s).IsHomogeneous (e + e') := by
    refine (hf.mul hs').sub ?_
    rw [add_comm e e']; exact hf'.mul hs
  have hmem : f * hex.choose.2 - hex.choose.1 * s ∈ primeOf (S := k) x := by
    rw [mem_primeOf_of_isHomogeneous x hhom]
    simp only [map_sub, map_mul, heq, sub_self]
  have hy := (mem_primeOf_of_isHomogeneous y hhom).mp (hsp hmem)
  simp only [map_sub, map_mul] at hy
  rw [div_eq_div_iff h' h]
  linear_combination -hy
end GroundTheory.Heights₂.Heights.Kleiman

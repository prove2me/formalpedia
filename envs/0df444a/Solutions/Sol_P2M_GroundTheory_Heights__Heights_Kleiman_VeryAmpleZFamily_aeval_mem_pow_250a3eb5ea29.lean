-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_aeval_mem_pow_250a3eb5ea29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:12:23.558372+00:00
-- url     : https://prove2.me/submissions/76b17142-1a7b-4d0a-9189-02a064840bc8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_pow_mem_pow_9418c8e10619


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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ} {h : Fin (r + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
theorem _root_.solution {I : Chart x} {Q : Submodule (chartRing S x I) Ω} (hQ : ∀ l, h l ∈ Q)
    {f : MvPolynomial (Fin (r + 1)) S} {e : ℕ} (hf : f.IsHomogeneous e) : aeval h f ∈ Q ^ e := by
  have hmon : ∀ (d : Fin (r + 1) →₀ ℕ) (t : Finset (Fin (r + 1))),
      ∏ j ∈ t, h j ^ d j ∈ Q ^ (∑ j ∈ t, d j) := by
    intro d t
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, pow_zero]
      exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    | insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, pow_add]
      exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hQ j) _) ih
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [aeval_monomial]
  have hdeg : ∑ j ∈ d.support, d j = e := by
    have := hf (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have hm := hmon d d.support
  rw [hdeg] at hm
  have := Submodule.smul_mem (Q ^ e)
    (⟨algebraMap S Ω (coeff d f), Subalgebra.algebraMap_mem _ _⟩ : chartRing S x I) hm
  rw [chartRing_smul_def] at this
  exact this
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily

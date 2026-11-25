-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRingI_equiv_6c221ab935ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:28.067902+00:00
-- url     : https://prove2.me/submissions/19dcf05e-60af-489a-9d3c-8725e696a788

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_div_mem_chartRingI_68ce525af692

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable (S : Type) [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace chartRingI
theorem _root_.solution (x : Fin (N + 1) → Ω) (I : Kleiman.Chart x) :
    IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 = Kleiman.chartRing S x I := by
  apply le_antisymm
  · rw [IndefiniteRowSideFullHecke.Kleiman.chartRingI, Algebra.adjoin_le_iff]
    rintro _ ⟨i, hi, j, rfl⟩
    exact ⟨X j, X i, 1, Kleiman.X_mem_monos hi, isHomogeneous_X S j, isHomogeneous_X S i, by simp⟩
  · rintro _ ⟨f, s, e, hs, hf, hse, rfl⟩
    obtain ⟨i₀, hi₀⟩ := I.2.1
    have hx₀ : x i₀ ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi₀)
    have hs0 : aeval x s ≠ 0 := Kleiman.eval_ne_zero_of_mem_monos I hs
    have hsne : s ≠ 0 := fun h => hs0 (by rw [h, map_zero])
    obtain ⟨e', hse', hmem⟩ := pow_div_mem_chartRingI S x I i₀ hs
    have hee : e = e' := hse.inj_right hse' hsne
    subst hee
    have hall : ∀ g : Poly S N, aeval (fun l => x l / x i₀) g ∈ IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => rw [aeval_C]; exact Subalgebra.algebraMap_mem _ a
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | mul_X p i hp =>
        rw [map_mul, aeval_X]
        exact mul_mem hp (Algebra.subset_adjoin ⟨i₀, hi₀, i, rfl⟩)
    have hf' : aeval x f / x i₀ ^ e ∈ IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 := by
      rw [← Kleiman.aeval_div_of_isHomogeneous hf i₀]
      exact hall f
    have heq : aeval x f / aeval x s = (aeval x f / x i₀ ^ e) * (x i₀ ^ e / aeval x s) := by
      field_simp
    rw [heq]
    exact mul_mem hf' hmem
end chartRingI
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

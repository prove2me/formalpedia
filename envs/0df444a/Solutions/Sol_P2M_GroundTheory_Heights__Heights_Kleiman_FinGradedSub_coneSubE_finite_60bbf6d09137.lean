-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_coneSubE_finite_60bbf6d09137
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:20:20.629055+00:00
-- url     : https://prove2.me/submissions/5fe19999-d63d-4177-b8f1-65070bcd2ed0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_smul_singleE_6f24e5511d10

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FinGradedSub
theorem _root_.solution : Module.Finite (Poly S N) M.coneSubE := by
  obtain ⟨n, deg, gen, hgen, hspan⟩ := M.fg
  have heq : M.coneSubE = Submodule.span (Poly S N) (Set.range fun j => singleE S x E (deg j) (gen j)) := by
    refine le_antisymm (fun w hw => ?_) (Submodule.span_le.mpr ?_)
    · rw [← sum_singleE w]
      refine Submodule.sum_mem _ fun c _ => ?_
      have hv := hspan c (hw c)
      refine Submodule.span_induction (p := fun v _ => singleE S x E c v ∈
        Submodule.span (Poly S N) (Set.range fun j => singleE S x E (deg j) (gen j))) ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨j, f, e, hf, hej, rfl⟩
        have : singleE S x E c (aeval x f • gen j) = f • singleE S x E (deg j) (gen j) := by
          rw [smul_singleE hf, show deg j + (e : ℤ) = c by omega]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · rw [map_zero]; exact zero_mem _
      · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
      · intro s a _ ha; rw [map_smul]; exact Submodule.smul_of_tower_mem _ s ha
    · rintro _ ⟨j, rfl⟩
      exact M.singleE_mem_coneSubE (hgen j)
  rw [Module.Finite.iff_fg, heq]
  exact Submodule.fg_span (Set.finite_range _)
end FinGradedSub
end GroundTheory.Heights₂.Heights.Kleiman

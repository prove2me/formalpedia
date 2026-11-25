-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_coneSub_finite_e7769f5bc1e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:25.784065+00:00
-- url     : https://prove2.me/submissions/464d9596-54e9-4d40-b7ee-c976fb699158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_smul_coneSingle_4b1ab4277a3e

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FinGradedSub
theorem _root_.solution : Module.Finite (Poly S N) M.coneSub := by
  obtain ⟨n, deg, gen, hgen, hspan⟩ := M.fg
  have heq : M.coneSub = Submodule.span (Poly S N) (Set.range fun j => coneSingle S x (deg j) (gen j)) := by
    refine le_antisymm (fun w hw => ?_) (Submodule.span_le.mpr ?_)
    · rw [← sum_coneSingle w]
      refine Submodule.sum_mem _ fun c _ => ?_
      have hv := hspan c (hw c)
      refine Submodule.span_induction (p := fun v _ => coneSingle S x c v ∈
        Submodule.span (Poly S N) (Set.range fun j => coneSingle S x (deg j) (gen j))) ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨j, f, e, hf, hej, rfl⟩
        have : coneSingle S x c (aeval x f • gen j) = f • coneSingle S x (deg j) (gen j) := by
          rw [smul_coneSingle hf, smul_eq_mul, show deg j + (e : ℤ) = c by omega]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · rw [map_zero]; exact zero_mem _
      · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
      · intro s a _ ha; rw [map_smul]; exact Submodule.smul_of_tower_mem _ s ha
    · rintro _ ⟨j, rfl⟩
      exact M.coneSingle_mem_coneSub (hgen j)
  rw [Module.Finite.iff_fg, heq]
  exact Submodule.fg_span (Set.finite_range _)
end FinGradedSub
end GroundTheory.Heights₂.Heights.Kleiman

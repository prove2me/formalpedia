-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_redSys_sub_eq_span_6c3d9f7436b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:45:10.120469+00:00
-- url     : https://prove2.me/submissions/0cf20bb5-b15a-4c73-bfcc-7e6f772c2141

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LineBundleRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLineBundleRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_add_75c3baa8859e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_zero_68297b898f07


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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp
variable {γ : Ω} {Q : LineBundle k x}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hg : RedGood hxy Q.toSubSystem γ) (I : Chart y) {s : Set Ω}
    (hs : Submodule.span (chartRing k x (liftChart hxy I)) s = Q.sub (liftChart hxy I)) :
    (redSys hxy Q.toSubSystem γ).sub I =
      Submodule.span (chartRing k y I) ((fun q => redAt k x y (q / γ)) '' s) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    have hq' : q ∈ Submodule.span (chartRing k x (liftChart hxy I)) s := by rw [hs]; exact hq
    refine Submodule.span_induction (p := fun q _ => redAt k x y (q / γ) ∈
      Submodule.span (chartRing k y I) ((fun q => redAt k x y (q / γ)) '' s)) ?_ ?_ ?_ ?_ hq'
    · intro q hq; exact Submodule.subset_span ⟨q, hq, rfl⟩
    · rw [zero_div, (locAt_zero hsp).2]; exact Submodule.zero_mem _
    · intro u v hu hv ihu ihv
      rw [add_div, (locAt_add hsp (hg I u (hs ▸ hu)) (hg I v (hs ▸ hv))).2]
      exact Submodule.add_mem _ ihu ihv
    · intro c u hu ihu
      rw [chartRing_smul_def, mul_div_assoc,
        (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 (hg I u (hs ▸ hu))).2]
      have := Submodule.smul_mem _ (⟨_, (chartRing_sub_locAt hsp hxy I c.2).2⟩ : chartRing k y I) ihu
      rwa [chartRing_smul_def] at this
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    have hq' : q ∈ Q.sub (liftChart hxy I) := by rw [← hs]; exact Submodule.subset_span hq
    exact Submodule.subset_span ⟨q, hq', rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman

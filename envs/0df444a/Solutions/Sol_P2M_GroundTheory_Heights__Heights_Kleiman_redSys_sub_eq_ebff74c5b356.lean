-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_redSys_sub_eq_ebff74c5b356
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:52:02.424803+00:00
-- url     : https://prove2.me/submissions/2941c16d-e784-41f5-ab3b-1f99805007c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_sub_of_isVeryAmpleBy_4e23af4f9328
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
  (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
  {Nb : LineBundle k x} {r : ℕ} {h : Fin (r + 1) → Ω}
include hsp
variable {g : Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hV : IsVeryAmpleBy Nb.toSubSystem h) (hg : RedGood hxy Nb.toSubSystem g)
    (I : Chart y) : (redSys hxy Nb.toSubSystem g).sub I =
      Submodule.span (chartRing k y I) (Set.range fun l => redAt k x y (h l / g)) := by
  have hgen := hV.generates (liftChart hxy I)
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    have hq' := hq
    rw [← hgen] at hq'
    refine Submodule.span_induction (p := fun q _ => redAt k x y (q / g) ∈
      Submodule.span (chartRing k y I) (Set.range fun l => redAt k x y (h l / g))) ?_ ?_ ?_ ?_ hq'
    · rintro _ ⟨l, rfl⟩; exact Submodule.subset_span ⟨l, rfl⟩
    · rw [zero_div, (locAt_zero hsp).2]; exact Submodule.zero_mem _
    · intro u v hu hv ihu ihv
      rw [add_div, (locAt_add hsp (hg I u (hgen ▸ hu)) (hg I v (hgen ▸ hv))).2]
      exact Submodule.add_mem _ ihu ihv
    · intro c u hu ihu
      rw [chartRing_smul_def, mul_div_assoc,
        (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 (hg I u (hgen ▸ hu))).2]
      have := Submodule.smul_mem _ (⟨_, (chartRing_sub_locAt hsp hxy I c.2).2⟩ : chartRing k y I) ihu
      rwa [chartRing_smul_def] at this
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, rfl⟩
    exact Submodule.subset_span ⟨h l, mem_sub_of_isVeryAmpleBy hV l _, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman

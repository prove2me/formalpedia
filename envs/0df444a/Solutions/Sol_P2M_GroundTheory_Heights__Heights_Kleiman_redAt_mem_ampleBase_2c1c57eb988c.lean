-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_redAt_mem_ampleBase_2c1c57eb988c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:02.713788+00:00
-- url     : https://prove2.me/submissions/7a306679-a7b7-467c-bd87-51efd0a13fe7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_add_75c3baa8859e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_algebraMap_ad6f57dcffae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_div_084462a2e36e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9


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
variable {σ : Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hg0 : g ≠ 0) (hgl : ∀ l, h l / g ∈ locAt k x y) {j : Fin (r + 1)}
    (hr : redAt k x y (h j / g) ≠ 0) {z : Ω} (hz : z ∈ ampleBase (S := k) h j) :
    z ∈ locAt k x y ∧
      redAt k x y z ∈ ampleBase (S := k) (fun l => redAt k x y (h l / g)) j := by
  refine Algebra.adjoin_induction (p := fun z _ => z ∈ locAt k x y ∧
    redAt k x y z ∈ ampleBase (S := k) (fun l => redAt k x y (h l / g)) j) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨l, rfl⟩
    dsimp only
    rw [← div_div_div_cancel_right₀ hg0 (h l) (h j)]
    obtain ⟨h1, h2⟩ := locAt_div hsp (hgl l) (hgl j) hr
    exact ⟨h1, by rw [h2]; exact Algebra.subset_adjoin ⟨l, rfl⟩⟩
  · intro c
    obtain ⟨h1, h2⟩ := locAt_algebraMap hsp c
    exact ⟨h1, by rw [h2]; exact Subalgebra.algebraMap_mem _ c⟩
  · intro u v _ _ hu hv
    obtain ⟨h1, h2⟩ := locAt_add hsp hu.1 hv.1
    exact ⟨h1, by rw [h2]; exact add_mem hu.2 hv.2⟩
  · intro u v _ _ hu hv
    obtain ⟨h1, h2⟩ := locAt_mul hsp hu.1 hv.1
    exact ⟨h1, by rw [h2]; exact mul_mem hu.2 hv.2⟩
end GroundTheory.Heights₂.Heights.Kleiman

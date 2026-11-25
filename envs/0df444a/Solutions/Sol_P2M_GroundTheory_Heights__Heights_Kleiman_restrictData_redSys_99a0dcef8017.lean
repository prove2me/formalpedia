-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_restrictData_redSys_99a0dcef8017
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:28:00.927808+00:00
-- url     : https://prove2.me/submissions/f79d10c6-ff60-4edf-85d9-9803a8930728

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_add_75c3baa8859e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_locAt_48cfe111c0a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redAt_eq_fa1134abb51b


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
theorem _root_.solution (hg : RedGood hxy Nb.toSubSystem g) (Q' : LineBundle k y)
    (hQ : Q'.toSubSystem = redSys hxy Nb.toSubSystem g) :
    RestrictData Nb.toSubSystem hxy Q'.toSubSystem (fun q => redAt k x y (q / g)) := by
  rw [hQ]
  exact
    { mem := fun I q hq => Submodule.subset_span ⟨q, hq, rfl⟩
      add := fun I q hq q' hq' => by
        rw [add_div]; exact (locAt_add hsp (hg I q hq) (hg I q' hq')).2
      smul := fun I q hq f s e hs hf hse => by
        have hsy : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos I hs
        rw [mul_div_assoc, (locAt_mul hsp (mem_locAt hf hse hsy) (hg I q hq)).2,
          redAt_eq hsp hf hse hsy]
      span := fun I => rfl }
end GroundTheory.Heights₂.Heights.Kleiman

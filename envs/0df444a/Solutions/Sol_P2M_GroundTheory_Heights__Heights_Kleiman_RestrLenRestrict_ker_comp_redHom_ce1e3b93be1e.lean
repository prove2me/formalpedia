-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_ker_comp_redHom_ce1e3b93be1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:18:02.706963+00:00
-- url     : https://prove2.me/submissions/59eefaf7-0850-42b4-a652-6efb074d9011

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartPrime_iff_8a48624344f9
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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
theorem _root_.solution (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    {j : Fin (N + 1)} (hyj : y j ≠ 0) (pp : Ideal (Poly k N)) [pp.IsPrime]
    (hle : primeOf (S := k) y ≤ pp) (hX : (X j : Poly k N) ∉ pp) {K'' : Type w} [Field K'']
    [Algebra k K''] (ψ : chartRing k y (singleChart hyj) →ₐ[k] K'')
    (hker : RingHom.ker ψ = chartPrime pp hyj) :
    RingHom.ker (ψ.comp (redHom hsp hxy hyj)) = chartPrime pp (hxy j hyj) := by
  ext a
  obtain ⟨f, s, e, hs, hf, hse, ha⟩ := a.2
  have hsy : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hyj) hs
  have hred : ((redHom hsp hxy hyj a : chartRing k y (singleChart hyj)) : K') =
      aeval y f / aeval y s := by
    show redAt k x y (a : Ω) = _
    rw [ha]
    exact redAt_eq hsp hf hse hsy
  rw [RingHom.mem_ker, AlgHom.comp_apply, ← RingHom.mem_ker (f := ψ), hker,
    mem_chartPrime_iff hyj hle hX hf hs hse hred,
    mem_chartPrime_iff (hxy j hyj) (hsp.trans hle) hX hf hs hse ha]
end GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict

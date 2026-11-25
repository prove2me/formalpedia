-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_sub_le_twist_sup_span_d1f50341dc77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:31:49.716263+00:00
-- url     : https://prove2.me/submissions/4dc38014-3402-4419-830a-127b4f6b1413

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutNonempty
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_mem_idealMod_2810c4e8df36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_mul_mem_span_1d57a849979c

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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {pp : Ideal (Poly k N)}
    (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) (L : LineBundle k x) (s : Ω)
    (hmin : ∀ qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes, ∀ i, (X i : Poly k N) ∈ qq)
    (j : Fin (N + 1)) (hj : x j ≠ 0) :
    L.sub (singleChart hj) ≤ (L.twist (idealSys x pp)).sub (singleChart hj) ⊔
      Submodule.span (chartRing k x (singleChart hj)) {s} := by
  have hrad : (X j : Poly k N) ∈ (pp ⊔ zeroIdeal L.toSubSystem s).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.mpr fun qq hq => hmin qq hq j
  obtain ⟨m, hm⟩ := hrad
  obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hm
  intro ℓ hℓ
  have h1 : ((aeval (ratio (S := k) hj) ((X j : Poly k N) ^ m) : chartRing k x (singleChart hj)) : Ω) = 1 := by
    rw [map_pow, aeval_X, SubmonoidClass.coe_pow]
    change (x j / x j) ^ m = 1
    rw [div_self hj, one_pow]
  have hsplit : ℓ = ((aeval (ratio (S := k) hj) p : chartRing k x (singleChart hj)) : Ω) * ℓ +
      ((aeval (ratio (S := k) hj) z : chartRing k x (singleChart hj)) : Ω) * ℓ := by
    rw [← add_mul, ← Subalgebra.coe_add, ← map_add, hpz, h1, one_mul]
  rw [hsplit]
  refine Submodule.add_mem_sup (Submodule.subset_span ?_) (coe_aeval_ratio_mul_mem_span hj hz hℓ)
  exact ⟨_, coe_aeval_ratio_mem_idealMod hh hj hp, ℓ, hℓ, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman

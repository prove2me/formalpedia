-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_twist_idealSys_of_algebraMap_mul_mem_7c334198a913
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:24.590976+00:00
-- url     : https://prove2.me/submissions/9c2902fd-e73d-497f-b860-0d41c2d300e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreRestrKer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_idealMod_of_algebraMap_mul_mem_d6a9246660b6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


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
open scoped Pointwise nonZeroDivisors
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {qq : Ideal (Poly S N)} [hq : qq.IsPrime]
    (hle : primeOf (S := S) x ≤ qq) (hconst : ∀ s : S, (C s : Poly S N) ∈ qq → s = 0)
    (Q : LineBundle S x) (I : Chart x) {s₀ : S} (hs₀ : s₀ ≠ 0) {v : Ω} (hv : v ∈ Q.sub I)
    (hsv : algebraMap S Ω s₀ * v ∈ (Q.twist (idealSys x qq)).sub I) :
    v ∈ (Q.twist (idealSys x qq)).sub I := by
  rw [SubSystem.twist_sub_eq_mul_of_line] at hsv ⊢
  obtain ⟨Q', hQ'⟩ := Q.invertible I
  have key : ∀ q' ∈ Q', v * q' ∈ (idealSys x qq).sub I := by
    intro q' hq'
    have hA : v * q' ∈ (1 : Submodule (chartRing S x I) Ω) := by
      rw [← hQ']
      exact Submodule.mul_mem_mul hv hq'
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp hA
    have hmemA : v * q' ∈ chartRing S x I := by
      rw [← hb]
      exact b.2
    refine mem_idealMod_of_algebraMap_mul_mem hq (fun p d hp hp0 => hle ((mem_primeOf_of_isHomogeneous x hp).mpr hp0))
      I (fun h => hs₀ (hconst s₀ h)) hmemA ?_
    have : algebraMap S Ω s₀ * v * q' ∈ (idealSys x qq).sub I * Q.sub I * Q' :=
      Submodule.mul_mem_mul hsv hq'
    rw [mul_assoc ((idealSys x qq).sub I), hQ', mul_one, mul_assoc] at this
    exact this
  have h1 : (1 : Ω) ∈ Q.sub I * Q' := by
    rw [hQ']
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hall : ∀ y ∈ Q.sub I * Q', v * y ∈ (idealSys x qq).sub I * Q.sub I := by
    intro y hy
    refine Submodule.mul_induction_on (C := fun y => v * y ∈ (idealSys x qq).sub I * Q.sub I) hy ?_ ?_
    · intro g hg q' hq'
      rw [show v * (g * q') = (v * q') * g by ring]
      exact Submodule.mul_mem_mul (key q' hq') hg
    · intro a b ha hb
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
  simpa using hall 1 h1
end GroundTheory.Heights₂.Heights.Kleiman

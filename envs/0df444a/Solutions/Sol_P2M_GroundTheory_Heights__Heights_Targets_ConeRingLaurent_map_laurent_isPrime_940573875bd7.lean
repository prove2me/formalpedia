-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_map_laurent_isPrime_940573875bd7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:44:17.561915+00:00
-- url     : https://prove2.me/submissions/ae990cbb-d205-4551-b340-8b1681f6dc54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeRingLaurent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PConeRingLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_map_C_isPrime_0d7c90a25962

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.Targets.ConeRingLaurent
variable {K : Type} [Fintype K] {ι : K → Type} (i : (k : K) → ι k)
namespace GroundTheory.Heights₂.Heights.Targets.ConeRingLaurent
theorem _root_.solution (𝔮 : Ideal (DehomRing i)) [𝔮.IsPrime] :
    (𝔮.map (algebraMap (DehomRing i) (Laurent i))).IsPrime := by
  rw [IsScalarTower.algebraMap_eq (DehomRing i) (MvPolynomial K (DehomRing i)) (Laurent i), ← Ideal.map_map,
    MvPolynomial.algebraMap_eq]
  apply IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (tProd i)) (Laurent i) _ (map_C_isPrime 𝔮)
  rw [Set.disjoint_left]
  intro x hx hmem
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hx
  have hle : 𝔮.map (C : DehomRing i →+* MvPolynomial K (DehomRing i)) ≤
      RingHom.ker (eval₂Hom (Ideal.Quotient.mk 𝔮) fun _ : K => (1 : DehomRing i ⧸ 𝔮)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hy]
  have h0 := hle hmem
  rw [RingHom.mem_ker] at h0
  simp [tProd] at h0
  rw [← map_one (Ideal.Quotient.mk 𝔮), Ideal.Quotient.eq_zero_iff_mem] at h0
  exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h0)
end GroundTheory.Heights₂.Heights.Targets.ConeRingLaurent

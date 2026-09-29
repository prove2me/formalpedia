-- Prove2me | solution 1 for WeierstrassCurve.smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/08c88441-bdff-5896-9fda-bff230ffb11b

import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn
import Theorems.Thm_WeierstrassCurve_mem_valuationSubring_of_nsmul_eq_zero_of_liesOverPrime
import Theorems.Thm_WeierstrassCurve_exists_reduction_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map reduction toAffine Affine.Point Δ c₄ InZeroComponentAt inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn mem_valuationSubring_of_nsmul_eq_zero_of_liesOverPrime exists_reduction_inZeroComponentAt inZeroComponentAt_sub inZeroComponentAt_smul"
namespace D5Sol
p2m_open "WeierstrassCurve"

theorem nsmul_algEquiv_smul_sub_eq_zero {F S : Type} [Field F] [CommRing S] [Algebra S F]
    [DecidableEq F] {W : WeierstrassCurve S} (g : F ≃ₐ[S] F) {n : ℕ} {R : (W.toAffine⁄F).Point}
    (hR : n • R = 0) : n • (g • R - R) = 0 := by
  rw [nsmul_sub, hR, sub_zero, algEquiv_smul_def, ← map_nsmul, hR, _root_.map_zero]

end WeierstrassCurve.D5Sol

namespace ValuationSubring
p2m_export "ValuationSubring" "decompositionSubgroup LiesOverPrime inertiaSubgroupIn"
namespace D5Sol
p2m_open "ValuationSubring"

theorem mem_decompositionSubgroup_of_mem_inertiaSubgroupIn {K L : Type} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K) :
    σ ∈ A.decompositionSubgroup K := by
  obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.mp hσ
  exact g.2

end ValuationSubring.D5Sol

theorem solution
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0) (hqΔ : (q : ℤ) ∣ W.Δ)
    (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {n : ℕ} (hn : ¬ q ∣ n) {σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hP : n • P = 0) :
    τ • (σ • P - P) = σ • P - P := by
  classical
  set Q := σ • P - P with hQdef

  have hQn : n • Q = 0 := WeierstrassCurve.D5Sol.nsmul_algEquiv_smul_sub_eq_zero σ hP
  have hQ0 : W.InZeroComponentAt A Q :=
    W.inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn hq hΔ hqΔ hqc₄ A hA σ hσ P
  have hRn : n • (τ • Q - Q) = 0 := WeierstrassCurve.D5Sol.nsmul_algEquiv_smul_sub_eq_zero τ hQn
  have hR0 : W.InZeroComponentAt A (τ • Q - Q) :=
    W.inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn hq hΔ hqΔ hqc₄ A hA τ hτ Q

  have hτQ0 : W.InZeroComponentAt A (τ • Q) :=
    W.inZeroComponentAt_smul A
      (ValuationSubring.D5Sol.mem_decompositionSubgroup_of_mem_inertiaSubgroupIn A hτ) hQ0
  have hnegQ0 : W.InZeroComponentAt A (-Q) := by
    have h := W.inZeroComponentAt_sub A (P := 0) (Or.inl rfl) hQ0
    rwa [zero_sub] at h

  obtain ⟨red, hred0, hadd, -, -, hker, hinert⟩ := W.exists_reduction_inZeroComponentAt A
  have hredneg : red (-Q) = -red Q := by
    have h := hadd Q (-Q) hQ0 hnegQ0
    rw [add_neg_cancel, hred0] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  have hredR : red (τ • Q - Q) = 0 := by
    rw [sub_eq_add_neg, hadd _ _ hτQ0 hnegQ0, hinert τ hτ Q, hredneg, add_neg_cancel]

  rcases hker _ hR0 hredR with hR | ⟨x, y, h, hRxy, hx⟩
  · exact sub_eq_zero.mp hR
  · rw [hRxy] at hRn
    exact absurd (W.mem_valuationSubring_of_nsmul_eq_zero_of_liesOverPrime A hq hA hn h hRn) hx

end S_WeierstrassCurve_smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction
end P2MW
export P2MW.S_WeierstrassCurve_smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction (solution)

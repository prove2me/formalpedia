-- Prove2me | solution 1 for PI.PolynomialProperness.coreInst_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:03:06.655138+00:00
-- url     : https://prove2.me/submissions/1819fd6a-773e-4eaf-abec-94b49c8843b4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_CoreInst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness
namespace PI.PolynomialProperness
theorem _root_.solution (hC : IsoCore) (hI : HpkInvol) (hN : GNFacts) (h1 : Formalism.FourierDecayAlt.C2.GramIndependentSignature) :
    CoreInst := by
  intro k r z z' γ hstd hpos
  obtain ⟨_, ⟨Q, _, hQG⟩, hpd, _⟩ := h1 k r z z' γ hstd hpos
  obtain ⟨hH1, hH2⟩ := hI k r
  have hG : gramOf (Hpk k r) (gramVec k r z z' γ) = gramM k r z z' γ := by
    ext i j
    rfl
  have hunit : IsUnit (gramOf (Hpk k r) (gramVec k r z z' γ)).det := by
    rw [hG]
    set M0 : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
      Matrix.fromBlocks 1 0 0 (-1) with hM0
    have hsq : M0 * M0 = 1 := by
      rw [hM0, Matrix.fromBlocks_multiply]
      simp [Matrix.fromBlocks_one]
    have hM0u : IsUnit M0.det :=
      IsUnit.of_mul_eq_one (b := M0.det) (by rw [← Matrix.det_mul, hsq, Matrix.det_one])
    rw [← hQG, Matrix.det_mul, Matrix.det_mul] at hM0u
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hM0u)
  have hcond : ∀ x, (∀ i, herm (Hpk k r) x (gramVec k r z z' γ i) = 0) →
      0 ≤ (herm (Hpk k r) x x).re := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      simp [herm]
    · have hxU : x ∈ Uperp k r z z' γ := by
        rw [Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
        ext i
        have h2 := hx i
        simp only [herm] at h2
        simpa [Matrix.mulVec, dotProduct] using h2
      exact (hpd x hxU hx0).le
  obtain ⟨C0, hC0⟩ := hC _ (Hpk k r) _ (gramVec k r z z' γ) hH1 hH2 hunit hcond
  obtain ⟨_, _, _, hgn⟩ := hN k r
  refine ⟨C0 * ∑ j : Fin (2 * r + k + 1), nsq (bvec j : Fin (2 * r + k + 1) → ℂ), fun s hs K hK hsm => ?_⟩
  rw [hgn s]
  calc ∑ j, nsq (s *ᵥ bvec j) ≤ ∑ j : Fin (2 * r + k + 1), C0 * (1 + K) ^ 2 * nsq (bvec j : Fin (2 * r + k + 1) → ℂ) :=
        Finset.sum_le_sum fun j _ => hC0 s hs K hK hsm (bvec j)
    _ = C0 * (∑ j : Fin (2 * r + k + 1), nsq (bvec j : Fin (2 * r + k + 1) → ℂ)) * (1 + K) ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
end PI.PolynomialProperness

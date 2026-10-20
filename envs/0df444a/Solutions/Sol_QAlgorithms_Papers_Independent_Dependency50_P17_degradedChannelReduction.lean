-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P17.degradedChannelReduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:43:03.916062+00:00
-- url     : https://prove2.me/submissions/5cf02b62-825b-4553-98b7-4746669504df

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P17

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P17

open QAlgorithms.Papers.Independent.Information100.P56 (productOutput)

/-- PDF pp.12–13, Appendix C.A, (38): the constructed affine encoders induce
exactly the degraded product channel, after averaging the hidden seed and the
uniform first message conditional on their sum. No channel-simulation hypothesis
is assumed. The fixed extension and affine shift precede every message and seed.
The printed q^(-n) is corrected to p^(-n)=|F|^(-n), as required by its summation set. -/
theorem solution {F I : Type*} [Field F] [Fintype F]
    (W : CQMAC F I) {ell k : ℕ}
    (L : ((Fin ell → F) × (Fin k → F)) ≃ₗ[F] (Fin (ell + k) → F))
    (e : Fin (ell + k) → F) :
    (∀ (a b : Fin ell → F) (z : Fin k → F),
      aliceEncoder L z a + bobEncoder L e z b = sumEncoder L e (a + b)) ∧
    (∀ (m : Fin ell → F) (i j : Fin (ell + k) → I),
      conditionalSumOutput W L e m i j =
        degradedProduct W (sumEncoder L e m) i j) := by
  have hsub : ∀ (m a : Fin ell → F) (z : Fin k → F),
      L (m - a, -z) = L (m, 0) - L (a, z) := by
    intro m a z
    rw [← map_sub]
    congr 1
    ext <;> simp
  refine ⟨fun a b z => ?_, fun m i j => ?_⟩
  · simp only [aliceEncoder, bobEncoder, sumEncoder]
    rw [← add_assoc, ← map_add]
    congr 2
    ext <;> simp
  · simp only [conditionalSumOutput, degradedProduct, degradedOutput, productOutput]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      inv_pow, Fintype.prod_sum]
    congr 1
    let g : (Fin (ell + k) → F) → ℂ := fun c =>
      ∏ t, W.output (c t) (sumEncoder L e m t - c t) (i t) (j t)
    have hterm : ∀ (a : Fin ell → F) (z : Fin k → F),
        (∏ t, W.output (aliceEncoder L z a t) (bobEncoder L e z (m - a) t) (i t) (j t))
          = g (L (a, z)) := by
      intro a z
      refine Finset.prod_congr rfl fun t _ => ?_
      congr 1
      simp only [bobEncoder, sumEncoder, hsub, Pi.add_apply, Pi.sub_apply]
      ring
    simp only [hterm]
    rw [← Fintype.sum_prod_type' (fun a z => g (L (a, z)))]
    exact Equiv.sum_comp L.toEquiv g


end


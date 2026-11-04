-- Prove2me | solution 1 for ThreeSum.TernaryPairedTensorScaled.scaled_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:05:58.291852+00:00
-- url     : https://prove2.me/submissions/bebfb69d-6528-48b8-b2cf-e97c12292a3d

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatch
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensorScaled
import Theorems.Thm_ThreeSum_TernaryPairedTensorScaled_scaled_potential

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedTensorScaled
open LightTernaryPairedPolynomial LightTernaryPairedPotential
open TernaryPairedTensor TernaryPairedColumnEnumeration
open scoped BigOperators
namespace ThreeSum.TernaryPairedTensorScaled
theorem _root_.solution {H : ℕ} {P : Fin H→Type*} [∀ i, Fintype (P i)]
    (K base Λ : ℕ) (μ : ℕ→ℤ) (L R : ∀ i, P i→Fin Λ→ℤ) (s : ℤ)
    (hTensor : ∀ (i : Fin H) (a b c d : Fin Λ),
      μ (base+i.val*Λ^4+tensorIndex Λ a.val b.val c.val d.val)=s*tensor (L i) (R i) a b c d) :
    LightTernaryPairedPotentialBatch.total K base Λ μ H=s^K*
      ((∑ i : Fin H, ∑ e : Fin K→P i, TernaryPairedPotential.rowWeight
        (Sum.elim (fun j => L i (e j)) (fun j => R i (e j)))) : ℤ) := by
  have heach (i : Fin H) : LightTernaryPairedPotentialBatch.term K base Λ μ i.val=s^K*
      ((∑ e : Fin K→P i, TernaryPairedPotential.rowWeight
        (Sum.elim (fun j => L i (e j)) (fun j => R i (e j)))) : ℤ) :=
    scaled_potential K (base+i.val*Λ^4) Λ μ (L i) (R i) s (hTensor i)
  unfold LightTernaryPairedPotentialBatch.total
  rw [←Fin.sum_univ_eq_sum_range]
  simp_rw [heach]
  rw [←Finset.mul_sum]
end ThreeSum.TernaryPairedTensorScaled

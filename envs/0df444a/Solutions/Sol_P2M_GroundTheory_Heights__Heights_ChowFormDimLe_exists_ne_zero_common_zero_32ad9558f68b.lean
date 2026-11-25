-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormDimLe_exists_ne_zero_common_zero_32ad9558f68b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:29:35.54472+00:00
-- url     : https://prove2.me/submissions/0b62d8ac-0bbf-4081-99ef-5812a3be0022

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormDim
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormDimLe
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_height_add_ringKrullDim_quotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChowFormDimLe
namespace GroundTheory.Heights₂.Heights.ChowFormDimLe
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] {n k : ℕ}
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime] (hPQ : P ≤ RingHom.ker (eval (0 : Fin n → K)))
    (hdim : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) K ⧸ P))
    (u : Fin k × Fin n → K) :
    ∃ x : Fin n → K, x ≠ 0 ∧ (∀ g ∈ P, eval x g = 0) ∧ ∀ i, ∑ j, u (i, j) * x j = 0 := by
  classical
  set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K)) with hQdef
  have : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)
  let mk := Ideal.Quotient.mk P
  let ℓ : Fin k → MvPolynomial (Fin n) K := fun i => ∑ j, C (u (i, j)) * X j
  have hℓQ : ∀ i, ℓ i ∈ Q := by
    intro i
    simp [Q, ℓ, RingHom.mem_ker]
  set Mb : Ideal (MvPolynomial (Fin n) K ⧸ P) := Q.map mk
  have : Mb.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hPQ)
  let s : Finset (MvPolynomial (Fin n) K ⧸ P) := Finset.univ.image (fun i => mk (ℓ i))
  have hsM : Ideal.span (s : Set (MvPolynomial (Fin n) K ⧸ P)) ≤ Mb := by
    rw [Ideal.span_le]
    intro y hy
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    exact Ideal.mem_map_of_mem _ (hℓQ i)
  obtain ⟨q, hqmin, hqM⟩ := Ideal.exists_minimalPrimes_le hsM
  have : q.IsPrime := hqmin.1.1
  have hqht : q.height ≤ k := by
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hqmin).trans ?_
    exact_mod_cast Finset.card_image_le.trans (by simp)
  have hMht : (Mb.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin n) K ⧸ P) := by
    have h := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient K Mb
    have hF : IsField ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient Mb).mp inferInstance
    have h0 : ringKrullDim ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) = 0 := by
      have h00 := ringKrullDim_eq_zero_of_isField (F := (MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) hF
      convert h00 using 2
    rwa [h0, add_zero] at h
  have hqne : q ≠ Mb := by
    intro hq
    rw [hq] at hqht
    have h1 : ((Mb.height : ℕ∞) : WithBot ℕ∞) ≤ ((k : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hqht
    rw [hMht] at h1
    exact absurd h1 (not_le.mpr (by exact_mod_cast hdim))
  set Q' := q.comap mk
  have : Q'.IsPrime := Ideal.comap_isPrime mk q
  have hQQ' : ¬ Q ≤ Q' := by
    intro h
    apply hqne
    refine le_antisymm hqM ?_
    calc Mb = Q.map mk := rfl
      _ ≤ Q'.map mk := Ideal.map_mono h
      _ = q := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q
  have hnull := MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) Q'
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ zeroLocus K Q', x ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    apply hQQ'
    intro g hg
    rw [← hnull, mem_vanishingIdeal_iff]
    intro x hx
    rw [hcon x hx]
    simpa [Q, RingHom.mem_ker] using hg
  refine ⟨x, hx0, fun g hg => ?_, fun i => ?_⟩
  · have hgQ' : g ∈ Q' := by
      show mk g ∈ q
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg]
      exact q.zero_mem
    simpa using (mem_zeroLocus_iff.mp hx) g hgQ'
  · have hmem : ℓ i ∈ Q' := by
      show mk (ℓ i) ∈ q
      exact hqmin.1.2 (Ideal.subset_span (by simp [s]))
    simpa [ℓ] using (mem_zeroLocus_iff.mp hx) _ hmem
end GroundTheory.Heights₂.Heights.ChowFormDimLe

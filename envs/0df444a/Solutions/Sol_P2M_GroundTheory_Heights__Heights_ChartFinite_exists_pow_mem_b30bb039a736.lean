-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFinite_exists_pow_mem_b30bb039a736
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:18.542412+00:00
-- url     : https://prove2.me/submissions/49e50b1b-326f-480b-abee-645a113ae957

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PFGNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormMultiHomog_proof_0a9ffdd46c66
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FGNullstellensatz_proof_bfbcefa7fcd9


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
open GroundTheory.Heights₂.Heights.ChartFinite
variable {F : Type} [Field F] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartFinite
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin (e + 1) × Fin n) F)
    (t : Fin n → F) (hf : IsChowForm I (e + 1) f) (m : Fin n) :
    ∃ N : ℕ, (Polynomial.eval₂RingHom (rename (R := F) (Sum.inr : Fin e × Fin n → Fin n ⊕ Fin e × Fin n)).toRingHom
      (X (Sum.inl m)) (linePoly f t m)) ^ N ∈ chartIncIdeal I t e := by
  classical
  set J := chartIncIdeal I t e
  set ψ := Polynomial.eval₂RingHom (rename (R := F) (Sum.inr : Fin e × Fin n → Fin n ⊕ Fin e × Fin n)).toRingHom
      (X (Sum.inl m))
  have : IsReduced (MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ J.radical) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical J)
  suffices h0 : Ideal.Quotient.mk J.radical (ψ (linePoly f t m)) = 0 from
    Ideal.Quotient.eq_zero_iff_mem.mp h0
  refine FGNullstellensatz.proof F _ _ fun φ => ?_
  set Φ := φ.comp (Ideal.Quotient.mkₐ F J.radical)
  set pt : Fin n ⊕ Fin e × Fin n → AlgebraicClosure F := fun v => Φ (X v) with hpt
  have hΦ : Φ = aeval pt := aeval_unique Φ
  have hJ : ∀ g ∈ J, aeval pt g = 0 := by
    intro g hg
    rw [← hΦ]
    change φ (Ideal.Quotient.mk _ g) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.le_radical hg), map_zero]
  set x : Fin n → AlgebraicClosure F := fun j => pt (Sum.inl j) with hx
  have hI : ∀ g ∈ I, aeval x g = 0 := by
    intro g hg
    have := hJ (rename Sum.inl g)
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hg)))
    rwa [aeval_rename] at this
  have hlin : ∑ j, algebraMap F _ (t j) * x j = 1 := by
    have := hJ (rename Sum.inl (linForm t - 1))
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))))
    rw [aeval_rename] at this
    simpa [linForm, sub_eq_zero] using this
  have hU : ∀ i : Fin e, ∑ j, pt (Sum.inr (i, j)) * x j = 0 := by
    intro i
    have := hJ _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    simpa using this
  set V : Fin (e + 1) × Fin n → AlgebraicClosure F := fun ij =>
    Fin.cases (motive := fun _ => AlgebraicClosure F)
      (algebraMap F _ (t ij.2) * x m - algebraMap F _ (if ij.2 = m then 1 else 0))
      (fun i => pt (Sum.inr (i, ij.2))) ij.1 with hV
  have hVmem : V ∈ incidence I (e + 1) := by
    refine ⟨x, ?_, hI, ?_⟩
    · intro h0
      rw [h0] at hlin
      simp at hlin
    · intro i
      cases i using Fin.cases with
      | zero =>
        calc ∑ j, V (0, j) * x j
            = x m * ∑ j, algebraMap F _ (t j) * x j - ∑ j, algebraMap F _ (if j = m then 1 else 0) * x j := by
              simp only [hV, Fin.cases_zero, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
              congr 1
              exact Finset.sum_congr rfl fun j _ => by ring
          _ = 0 := by simp [hlin]
      | succ i => simpa [hV] using hU i
  have hfV : aeval V f = 0 := (hf.2 f).mpr dvd_rfl V hVmem
  have hk1 : ((aeval pt).toRingHom.comp ψ).comp
      (algebraMap F (Polynomial (MvPolynomial (Fin e × Fin n) F))) = algebraMap F (AlgebraicClosure F) := by
    ext a
    simp [ψ, Polynomial.algebraMap_apply]
  have hk2 : ((aeval pt).toRingHom.comp ψ) ∘ lineVar t m = V := by
    funext ⟨i, j⟩
    cases i using Fin.cases with
    | zero => by_cases h : j = m <;> simp [lineVar, hV, ψ, hx, h]
    | succ i => simp [lineVar, hV, ψ]
  change Φ (ψ (linePoly f t m)) = 0
  rw [hΦ]
  change ((aeval pt).toRingHom.comp ψ) (linePoly f t m) = 0
  rw [linePoly, aeval_def, MvPolynomial.eval₂_comp_left, hk1, hk2, ← aeval_def, hfV]
end GroundTheory.Heights₂.Heights.ChartFinite

-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartz_withSeminorms_P3
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T04:14:56.370493+00:00
-- url     : https://prove2.me/submissions/ac8de59e-1aad-4b64-853b-e6df8184da55

-- New proof of an upstream statement, with the coefficient sum written over its support.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L471-L478
import Theorems.Thm_RiemannMasullo_elementarySchwartz_polynomial_operator_continuous_seminorm
import Theorems.Thm_RiemannMasullo_elementarySchwartz_withSeminorms_P2
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ENNReal
theorem solution :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        (MvPolynomial (Fin m ⊕ Fin r) ℂ × MvPolynomial (Fin m ⊕ Fin n) ℂ),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          (‖MvPolynomial.eval (Sum.elim (fun k ↦ (xt.1 k : ℂ)) (fun k ↦ (a k : ℂ))) i.1 *
            (∑ d ∈ i.2.support, i.2.coeff d * elementaryPartial f
              (fun k ↦ d (.inl k)) (fun k ↦ d (.inr k)) xt a b)‖₊ : ℝ≥0∞) := by
  classical
  let I := MvPolynomial (Fin m ⊕ Fin r) ℂ × MvPolynomial (Fin m ⊕ Fin n) ℂ
  choose Q hc hv using (fun i : I => elementarySchwartz_polynomial_operator_continuous_seminorm (F:=F) i.1 i.2)
  refine ⟨Q, ?_, hv⟩
  obtain ⟨P,hp,hP⟩ := elementarySchwartz_withSeminorms_P2 (m:=m) (n:=n) (r:=r) (F:=F)
  have cover (i : (Fin m → ℕ) × (Fin n → ℕ) × MvPolynomial (Fin m ⊕ Fin r) ℂ) : ∃ j : I, P i = Q j := by
    let d : (Fin m ⊕ Fin n) →₀ ℕ := Finsupp.equivFunOnFinite.symm (Sum.elim i.1 i.2.1)
    let j : I := (i.2.2,MvPolynomial.monomial d 1)
    refine ⟨j, ?_⟩
    ext f
    have he : ENNReal.ofReal (P i f) = ENNReal.ofReal (Q j f) := by
      rw [hP,hv]
      apply iSup_congr
      intro x
      apply iSup_congr
      intro a
      apply iSup_congr
      intro b
      dsimp only [j]
      simp only [MvPolynomial.support_monomial,one_ne_zero,if_false,Finset.sum_singleton,MvPolynomial.coeff_monomial,if_pos rfl,one_mul,←norm_mul,ofReal_norm_eq_enorm]
      simp only [if_true,one_mul]
      rfl
    simpa only [ENNReal.toReal_ofReal (apply_nonneg _ _)] using congrArg ENNReal.toReal he
  apply (SeminormFamily.withSeminorms_iff_nhds_eq_iInf Q).mpr
  apply le_antisymm
  · apply le_iInf
    intro j
    apply Filter.tendsto_iff_comap.mp
    exact (hc j).tendsto' 0 0 (map_zero _)
  · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf P).mp hp]
    apply le_iInf
    intro i
    obtain ⟨j,hij⟩ := cover i
    rw [hij]
    exact iInf_le _ j

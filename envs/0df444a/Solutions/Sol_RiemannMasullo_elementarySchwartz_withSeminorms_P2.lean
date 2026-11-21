-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartz_withSeminorms_P2
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:38:35.298183+00:00
-- url     : https://prove2.me/submissions/95feffbd-e68c-4d9d-9ead-6d50f53f5f04

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L460-L467
import Theorems.Thm_RiemannMasullo_elementarySchwartz_polynomial_weight_continuous_seminorm
import Theorems.Thm_RiemannMasullo_elementarySchwartz_withSeminorms
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ENNReal
theorem solution :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        ((Fin m → ℕ) × (Fin n → ℕ) × MvPolynomial (Fin m ⊕ Fin r) ℂ),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          ENNReal.ofReal
            (‖MvPolynomial.eval (Sum.elim (fun k ↦ (xt.1 k : ℂ)) (fun k ↦ (a k : ℂ))) i.2.2‖ *
              ‖elementaryPartial f i.1 i.2.1 xt a b‖) := by
  classical
  let I := (Fin m → ℕ) × (Fin n → ℕ) × MvPolynomial (Fin m ⊕ Fin r) ℂ
  choose Q hc hv using (fun i : I => elementarySchwartz_polynomial_weight_continuous_seminorm (F:=F) i.2.2 i.1 i.2.1)
  refine ⟨Q, ?_, hv⟩
  let P : SeminormFamily ℂ (ElementarySchwartz m n r F) _ := elementarySchwartzSeminorm
  have hp : WithSeminorms P := elementarySchwartz_withSeminorms
  have cover (i : ElementarySchwartzIndex m n r) : ∃ j : I, P i = Q j := by
    let d : (Fin m ⊕ Fin r) →₀ ℕ := Finsupp.equivFunOnFinite.symm (Sum.elim i.1 i.2.2.2)
    let j : I := (i.2.1,i.2.2.1,MvPolynomial.monomial d 1)
    refine ⟨j, ?_⟩
    ext f
    have he : ENNReal.ofReal (Q j f) = elementarySchwartzBound f.val i := by
      rw [hv]
      unfold elementarySchwartzBound
      apply iSup_congr
      intro x
      apply iSup_congr
      intro a
      apply iSup_congr
      intro b
      dsimp only [j]
      rw [MvPolynomial.eval_monomial,d.prod_fintype _ (fun _ => pow_zero _),Fintype.prod_sum_type,one_mul,←norm_mul,ofReal_norm_eq_enorm]
      rfl
    change (elementarySchwartzBound f.val i).toReal = Q j f
    rw [←he,ENNReal.toReal_ofReal (apply_nonneg _ _)]
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

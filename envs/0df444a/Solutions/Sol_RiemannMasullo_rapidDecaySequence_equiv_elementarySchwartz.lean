-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequence_equiv_elementarySchwartz
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:21:54.61925+00:00
-- url     : https://prove2.me/submissions/d8006d7b-8a7e-4b99-9e3e-4036d80be6cd

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L604-L606
import Theorems.Thm_RiemannMasullo_lattice_weighted_sum_le_finite_monomial_seminorms
import Theorems.Thm_RiemannMasullo_rapidDecaySequence_to_elementarySchwartz
import Theorems.Thm_RiemannMasullo_elementarySchwartz_withSeminorms
import Theorems.Thm_RiemannMasullo_rapidDecaySequence_withSeminorms
import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
import Mathlib
open RiemannMasullo
open scoped NNReal ENNReal
variable {r : ℕ}
theorem solution :
    ∃ e : RapidDecaySequence r ≃L[ℂ] ElementarySchwartz 0 0 r PUnit,
      ∀ s (g : ElementaryLieGroup 0 0 r PUnit), e s g = s g.2.2.1 := by
  classical
  obtain ⟨L,hinj,hL⟩ := rapidDecaySequence_to_elementarySchwartz r
  let E := ElementarySchwartz 0 0 r PUnit
  let v (f : E) := fun a : Fin r → ℤ => f (0,0,a,PUnit.unit)
  have hmem (f : E) : v f ∈ rapidDecaySequenceSubmodule r := by
    intro j
    obtain ⟨C,hC,h⟩ := lattice_weighted_sum_le_finite_monomial_seminorms r j
    exact (h f).trans_lt ENNReal.ofReal_lt_top
  let T : E →ₗ[ℂ] RapidDecaySequence r :=
    { toFun := fun f => (⟨v f,hmem f⟩ : rapidDecaySequenceSubmodule r)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hc : Continuous T := by
    apply WithSeminorms.continuous_of_continuous_comp rapidDecaySequence_withSeminorms T
    intro j
    obtain ⟨C,hC,h⟩ := lattice_weighted_sum_le_finite_monomial_seminorms r j
    let p (U : Finset (Fin r)) : Seminorm ℂ E := elementarySchwartzSeminorm
      (0,0,0,fun i => if i ∈ U then j+2 else 0)
    let Q : Seminorm ℂ E := ∑ U,p U
    have hQ : Continuous Q := Seminorm.continuous_finsetSum (fun U _ =>
      elementarySchwartz_withSeminorms.continuous_seminorm _)
    let c : ℝ≥0 := ⟨C,hC⟩
    have hcQ : Continuous (c • Q : Seminorm ℂ E) := hQ.const_smul c
    apply Seminorm.continuous_of_le hcQ
    intro f
    have hsum : Q f = ∑ U,p U f := by
      change FunLike.coeAddMonoidHom _ _ _ (∑ U,p U) f = _
      rw [map_sum,Finset.sum_apply]
      rfl
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h f)
    change (rapidDecaySequenceBound j (v f)).toReal ≤ C * Q f
    rw [hsum]
    have hn : 0 ≤ C * ∑ U,p U f := mul_nonneg hC (Finset.sum_nonneg fun U _ => apply_nonneg _ _)
    exact hh.trans_eq (ENNReal.toReal_ofReal hn)
  let e : RapidDecaySequence r ≃ₗ[ℂ] E :=
    { L.toLinearMap with
      invFun := T
      left_inv := fun s => by
        apply Subtype.ext
        funext a
        exact hL s (0,0,a,PUnit.unit)
      right_inv := fun f => by
        apply Subtype.ext
        funext g
        change L (T f) g = f g
        rw [hL]
        change f (0,0,g.2.2.1,PUnit.unit) = f g
        apply congrArg (fun x => f x)
        rcases g with ⟨x,y,a,b⟩
        have hx : (0 : EuclideanSpace ℝ (Fin 0)) = x := Subsingleton.elim _ _
        have hy : (0 : Fin 0 → AddCircle (1:ℝ)) = y := Subsingleton.elim _ _
        have hb : PUnit.unit = b := Subsingleton.elim _ _
        simp [hx,hy,hb] }
  exact ⟨{ e with continuous_toFun := L.continuous, continuous_invFun := hc },hL⟩

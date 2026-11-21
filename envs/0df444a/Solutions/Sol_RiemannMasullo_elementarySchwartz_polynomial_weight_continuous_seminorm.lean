-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartz_polynomial_weight_continuous_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:36:52.877429+00:00
-- url     : https://prove2.me/submissions/2f322c5f-f2d4-4a50-9126-8bfbed4ef4ea

-- New supporting theorem for the polynomial generating family of Appendix D.
import Theorems.Thm_RiemannMasullo_elementaryPartial_evaluation_continuousLinear
import Theorems.Thm_RiemannMasullo_elementarySchwartz_polynomial_weight_le_monomial_sum
import Theorems.Thm_RiemannMasullo_elementarySchwartz_withSeminorms
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ENNReal

theorem solution (p : MvPolynomial (Fin m ⊕ Fin r) ℂ) (β : Fin m → ℕ) (γ : Fin n → ℕ) :
    ∃ q : Seminorm ℂ (ElementarySchwartz m n r F), Continuous q ∧ ∀ f, ENNReal.ofReal (q f) =
      ⨆ (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
        ENNReal.ofReal (‖MvPolynomial.eval (Sum.elim (fun k => (x.1 k : ℂ)) (fun k => (a k : ℂ))) p‖ *
          ‖elementaryPartial f β γ x a b‖) := by
  classical
  let E := ElementarySchwartz m n r F
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let J := X × (Fin r → ℤ) × F
  choose L hL using (elementaryPartial_evaluation_continuousLinear (F:=F) β γ)
  let c (u : J) := MvPolynomial.eval (Sum.elim (fun k => (u.1.1 k:ℂ)) (fun k => (u.2.1 k:ℂ))) p
  let t (u : J) : Seminorm ℂ E := ‖c u‖₊ • (normSeminorm ℂ ℂ).comp (L u.1 u.2.1 u.2.2).toLinearMap
  let d (v : (Fin m ⊕ Fin r) →₀ ℕ) : ElementarySchwartzIndex m n r :=
    (fun k => v (Sum.inl k),β,γ,fun k => v (Sum.inr k))
  let s (v : (Fin m ⊕ Fin r) →₀ ℕ) : Seminorm ℂ E :=
    ‖p.coeff v‖₊ • elementarySchwartzSeminorm (d v)
  let Q : Seminorm ℂ E := ∑ v ∈ p.support,s v
  have hQ : Continuous Q := Seminorm.continuous_finsetSum (fun v _ =>
    (elementarySchwartz_withSeminorms.continuous_seminorm (d v)).const_smul ‖p.coeff v‖₊)
  have htv (u : J) (f : E) : t u f = ‖c u‖*‖elementaryPartial f β γ u.1 u.2.1 u.2.2‖ := by
    change ‖c u‖ * ‖L u.1 u.2.1 u.2.2 f‖ = _
    rw [hL]
  have hdom (u : J) : t u ≤ Q := by
    intro f
    rw [htv]
    have he : Q f = ∑ v ∈ p.support,s v f := by
      change FunLike.coeAddMonoidHom _ _ _ (∑ v ∈ p.support,s v) f = _
      rw [map_sum,Finset.sum_apply]; rfl
    rw [he]
    exact elementarySchwartz_polynomial_weight_le_monomial_sum p f β γ u.1 u.2.1 u.2.2
  have hbd : BddAbove (Set.range t) := ⟨Q,by rintro _ ⟨u,rfl⟩; exact hdom u⟩
  let q := ⨆ u : J,t u
  refine ⟨q,Seminorm.continuous_of_le hQ (ciSup_le hdom),?_⟩
  intro f
  let U := ⨆ (x : X) (a : Fin r → ℤ) (b : F), ENNReal.ofReal (t (x,a,b) f)
  have hU : U < ⊤ := by
    apply lt_of_le_of_lt _ (ENNReal.ofReal_lt_top (r:=Q f))
    exact iSup_le fun x => iSup_le fun a => iSup_le fun b => ENNReal.ofReal_le_ofReal (hdom (x,a,b) f)
  have eq : ENNReal.ofReal (q f) = U := by
    apply le_antisymm
    · rw [←ENNReal.ofReal_toReal hU.ne]
      apply ENNReal.ofReal_le_ofReal
      rw [show q f = ⨆ u : J,t u f from Seminorm.iSup_apply hbd]
      apply ciSup_le
      rintro ⟨x,a,b⟩
      have h : ENNReal.ofReal (t (x,a,b) f) ≤ U :=
        le_iSup_of_le x (le_iSup_of_le a (le_iSup_of_le b le_rfl))
      simpa only [ENNReal.toReal_ofReal (apply_nonneg _ _)] using ENNReal.toReal_mono hU.ne h
    · apply iSup_le
      intro x; apply iSup_le; intro a; apply iSup_le; intro b
      exact ENNReal.ofReal_le_ofReal (le_ciSup hbd (x,a,b) f)
  rw [eq]
  simp only [U,htv,c]
  rfl

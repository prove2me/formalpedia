-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartz_polynomial_operator_continuous_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:59:22.60775+00:00
-- url     : https://prove2.me/submissions/5aaad2fd-71c4-4c59-a813-8774d6e497e0

-- New supporting theorem for polynomial differential operators in Appendix D.
import Theorems.Thm_RiemannMasullo_elementaryPartial_evaluation_continuousLinear
import Theorems.Thm_RiemannMasullo_elementarySchwartz_polynomial_weight_continuous_seminorm
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ENNReal

theorem solution (p : MvPolynomial (Fin m ⊕ Fin r) ℂ) (D : MvPolynomial (Fin m ⊕ Fin n) ℂ) :
    ∃ q : Seminorm ℂ (ElementarySchwartz m n r F), Continuous q ∧ ∀ f, ENNReal.ofReal (q f) =
      ⨆ (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
        (‖MvPolynomial.eval (Sum.elim (fun k => (x.1 k : ℂ)) (fun k => (a k : ℂ))) p *
          (∑ d ∈ D.support, D.coeff d * elementaryPartial f (fun k => d (.inl k)) (fun k => d (.inr k)) x a b)‖₊ : ℝ≥0∞) := by
  classical
  let E := ElementarySchwartz m n r F
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let J := X × (Fin r → ℤ) × F
  let V := (Fin m ⊕ Fin n) →₀ ℕ
  let β (v : V) := fun k : Fin m => v (.inl k)
  let γ (v : V) := fun k : Fin n => v (.inr k)
  choose L hL using (fun v : V => elementaryPartial_evaluation_continuousLinear (F:=F) (β v) (γ v))
  choose P hP hval using (fun v : V => elementarySchwartz_polynomial_weight_continuous_seminorm (F:=F) p (β v) (γ v))
  let c (u : J) := MvPolynomial.eval (Sum.elim (fun k => (u.1.1 k:ℂ)) (fun k => (u.2.1 k:ℂ))) p
  let A (u : J) : E →ₗ[ℂ] ℂ := ∑ v ∈ D.support, D.coeff v • (L v u.1 u.2.1 u.2.2).toLinearMap
  let t (u : J) : Seminorm ℂ E := ‖c u‖₊ • (normSeminorm ℂ ℂ).comp (A u)
  let s (v : V) : Seminorm ℂ E := ‖D.coeff v‖₊ • P v
  let Q : Seminorm ℂ E := ∑ v ∈ D.support,s v
  have hQ : Continuous Q := Seminorm.continuous_finsetSum (fun v _ => (hP v).const_smul ‖D.coeff v‖₊)
  have htv (u : J) (f : E) : t u f = ‖c u * (∑ v ∈ D.support, D.coeff v *
      elementaryPartial f (β v) (γ v) u.1 u.2.1 u.2.2)‖ := by
    change ‖c u‖ * ‖A u f‖ = _
    simp only [A,LinearMap.sum_apply,LinearMap.smul_apply,ContinuousLinearMap.coe_coe,smul_eq_mul,hL,norm_mul]
  have hdom (u : J) : t u ≤ Q := by
    intro f
    have he : Q f = ∑ v ∈ D.support,s v f := by
      change FunLike.coeAddMonoidHom _ _ _ (∑ v ∈ D.support,s v) f = _
      rw [map_sum,Finset.sum_apply]; rfl
    rw [he,htv,Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro v _
    have h : ENNReal.ofReal (‖c u‖*‖elementaryPartial f (β v) (γ v) u.1 u.2.1 u.2.2‖) ≤ ENNReal.ofReal (P v f) := by
      rw [hval]
      exact le_iSup_of_le u.1 (le_iSup_of_le u.2.1 (le_iSup_of_le u.2.2 le_rfl))
    have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal (apply_nonneg _ _)] at h'
    change _ ≤ ‖D.coeff v‖ * P v f
    simp only [norm_mul]
    nlinarith only [mul_le_mul_of_nonneg_left h' (norm_nonneg (D.coeff v))]
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
  simp only [U,htv,c,ofReal_norm_eq_enorm]
  rfl

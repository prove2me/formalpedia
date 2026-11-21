-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartz_radial_weight_continuous_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T04:34:43.010675+00:00
-- url     : https://prove2.me/submissions/ced04829-a73e-4e8c-921b-b8eb0f5aa470

-- New supporting theorem for the radial generating family of Appendix D.
import Theorems.Thm_RiemannMasullo_elementarySchwartz_polynomial_weight_continuous_seminorm
import Theorems.Thm_RiemannMasullo_elementarySchwartz_even_radial_weight_polynomial
import Theorems.Thm_RiemannMasullo_elementaryPartial_evaluation_continuousLinear
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ENNReal NNReal

theorem solution (k l : ℕ) (β : Fin m → ℕ) (γ : Fin n → ℕ) :
    ∃ q : Seminorm ℂ (ElementarySchwartz m n r F), Continuous q ∧ ∀ f, ENNReal.ofReal (q f) =
      ⨆ (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
        ENNReal.ofReal ((1+‖x.1‖^k)*(1+‖(WithLp.toLp 2 (fun j => (a j : ℝ)) :
          EuclideanSpace ℝ (Fin r))‖^l)*‖elementaryPartial f β γ x a b‖) := by
  classical
  let E := ElementarySchwartz m n r F
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let J := X × (Fin r → ℤ) × F
  choose L hL using (elementaryPartial_evaluation_continuousLinear (F:=F) β γ)
  let y (a : Fin r → ℤ) : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun j => (a j:ℝ))
  let c (u : J) : ℝ≥0 := ⟨(1+‖u.1.1‖^k)*(1+‖y u.2.1‖^l), by positivity⟩
  let t (u : J) : Seminorm ℂ E := c u • (normSeminorm ℂ ℂ).comp (L u.1 u.2.1 u.2.2).toLinearMap
  obtain ⟨p,hp⟩ := elementarySchwartz_even_radial_weight_polynomial (m:=m) (r:=r) k l
  obtain ⟨P,hP,hval⟩ := elementarySchwartz_polynomial_weight_continuous_seminorm (F:=F) p β γ
  let Q : Seminorm ℂ E := (4:ℝ≥0) • P
  have hQ : Continuous Q := hP.const_smul (4:ℝ≥0)
  have htv (u : J) (f : E) : t u f = (c u:ℝ)*‖elementaryPartial f β γ u.1 u.2.1 u.2.2‖ := by
    change (c u:ℝ)*‖L u.1 u.2.1 u.2.2 f‖ = _
    rw [hL]
  have hdom (u : J) : t u ≤ Q := by
    intro f
    let R := (1+‖u.1.1‖^(2*k))*(1+‖y u.2.1‖^(2*l))
    let V := ‖elementaryPartial f β γ u.1 u.2.1 u.2.2‖
    have hev : MvPolynomial.eval (Sum.elim (fun i => (u.1.1 i:ℂ)) (fun j => (u.2.1 j:ℂ))) p = (R:ℂ) := by
      simpa [y,R] using hp u.1.1 (y u.2.1)
    have hm : ENNReal.ofReal (‖MvPolynomial.eval (Sum.elim (fun i => (u.1.1 i:ℂ)) (fun j => (u.2.1 j:ℂ))) p‖*V) ≤ ENNReal.ofReal (P f) := by
      rw [hval]
      exact le_iSup_of_le u.1 (le_iSup_of_le u.2.1 (le_iSup_of_le u.2.2 le_rfl))
    have hR : 0 ≤ R := by dsimp [R]; positivity
    rw [hev,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR] at hm
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    rw [ENNReal.toReal_ofReal (mul_nonneg hR (norm_nonneg _)),ENNReal.toReal_ofReal (apply_nonneg _ _)] at hb
    have hh (v : ℝ) (n : ℕ) : 1+v^n ≤ 2*(1+v^(2*n)) := by
      rw [mul_comm 2 n,pow_mul]; nlinarith [sq_nonneg (v^n-1)]
    have hfac := mul_le_mul (hh ‖u.1.1‖ k) (hh ‖y u.2.1‖ l) (by positivity) (by positivity)
    have hc : (c u:ℝ) ≤ 4*R := by
      change (1+‖u.1.1‖^k)*(1+‖y u.2.1‖^l) ≤ 4*((1+‖u.1.1‖^(2*k))*(1+‖y u.2.1‖^(2*l)))
      linarith only [hfac]
    rw [htv]
    change (c u:ℝ)*V ≤ 4*P f
    change R*V ≤ P f at hb
    linarith only [mul_le_mul_of_nonneg_right hc (show 0 ≤ V from norm_nonneg _),hb]
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
  simp only [U,htv,c,y]
  try rfl

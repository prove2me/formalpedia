-- Prove2me | solution 1 for WeierstrassEllipticZeta.exponentialPreimage_finite_entire_equations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-25T03:25:21.518996+00:00
-- url     : https://prove2.me/submissions/e3e710d6-8e1e-40bf-bbf5-4ea5faeb0f0a

import Definitions.Def_WeierstrassEllipticZeta_ExponentialPreimage
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity

noncomputable section
open MvPolynomial
namespace WeierstrassEllipticZeta
open PhilipponApplication
theorem exponentialCoordinates_polynomial_entire
    (S : Fin 5 → ℂ → ℂ) (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (Q : MvPolynomial (Fin 7) ℂ) :
    AnalyticOnNhd ℂ (fun v : Fin 3 → ℂ => eval (exponentialCoordinates S v) Q) Set.univ := by
  intro v _
  have hc (i : Fin 3) : AnalyticAt ℂ (fun w : Fin 3 → ℂ => w i) v :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) i).analyticAt _
  have hs (j : Fin 5) : AnalyticAt ℂ (fun w : Fin 3 → ℂ => S j (w 1)) v :=
    (hS j (v 1) trivial).comp (f := fun w : Fin 3 → ℂ => w 1) (x := v) (hc 1)
  apply AnalyticAt.aeval_mvPolynomial
  intro i
  fin_cases i
  · exact analyticAt_const
  · exact hc 0
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · exact (hs 3).add ((hc 2).mul (hs 0))
  · exact (hs 4).add ((hc 2).mul (hs 2))

theorem exponentialPreimage_finite_entire_equations
    (S : Fin 5 → ℂ → ℂ) (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (M : Model S) (H : AlgebraicSubgroup M.group) :
    ∃ F : Finset ((Fin 3 → ℂ) → ℂ),
      (∀ f ∈ F, AnalyticOnNhd ℂ f Set.univ) ∧
      ∀ v, v ∈ M.exponentialPreimage H ↔ ∀ f ∈ F, f v = 0 := by
  classical
  let equations : Set (MvPolynomial (Fin 7) ℂ) :=
    {Q | ∃ m n, Bihomogeneous Q m n ∧
      ∀ g ∈ H.carrier, M.group.ambient.eval (M.polynomial Q) (M.group.embedding g) = 0}
  obtain ⟨polys, hpolys, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset equations).mp
      (IsNoetherian.noetherian (Ideal.span equations))
  change Ideal.span equations = Ideal.span (polys : Set (MvPolynomial (Fin 7) ℂ)) at hspan
  let pull : MvPolynomial (Fin 7) ℂ → (Fin 3 → ℂ) → ℂ :=
    fun Q v => eval (exponentialCoordinates S v) Q
  refine ⟨polys.image pull, ?_, fun v => ⟨?_, ?_⟩⟩
  · intro f hf
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hf
    exact exponentialCoordinates_polynomial_entire S hS Q
  · intro hv f hf
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨m, n, hhom, hzero⟩ := hpolys hQ
    exact hv Q m n hhom hzero
  · intro hv Q m n hhom hzero
    have hmem : Q ∈ Ideal.span equations := Ideal.subset_span ⟨m, n, hhom, hzero⟩
    have hker : Ideal.span (polys : Set (MvPolynomial (Fin 7) ℂ)) ≤
        RingHom.ker (eval (exponentialCoordinates S v)) :=
      Ideal.span_le.mpr (fun P hP => hv _ (Finset.mem_image.mpr ⟨P, hP, rfl⟩))
    rw [hspan] at hmem
    exact hker hmem

end WeierstrassEllipticZeta
end
theorem solution
    (S : Fin 5 → ℂ → ℂ) (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (M : Model S) (H : AlgebraicSubgroup M.group) :
    ∃ F : Finset ((Fin 3 → ℂ) → ℂ),
      (∀ f ∈ F, AnalyticOnNhd ℂ f Set.univ) ∧
      ∀ v, v ∈ M.exponentialPreimage H ↔ ∀ f ∈ F, f v = 0 := by
  exact WeierstrassEllipticZeta.exponentialPreimage_finite_entire_equations S hS M H
#print axioms solution

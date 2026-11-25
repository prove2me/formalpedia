-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.exists_monic_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:36:15.029498+00:00
-- url     : https://prove2.me/submissions/e37aad32-b821-443f-ae6e-aa7f7ab65f47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_rel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
set_option maxHeartbeats 1600000
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (P : Ideal (MRing ι)) (hPh : IsMultiHomogIdeal P) (hΨ : IsGoodProj P Ψ)
    (F : MvPolynomial ((k : K) → ι k) ℂ) :
    ∃ (n : ℕ) (c : ℕ → MvPolynomial (Fin (e + 1)) ℂ), c n = 1 ∧
      ∀ z ∈ mcPts P, ∑ i ∈ Finset.range (n + 1),
        eval (Ψ (segre z)) (c i) * eval (segre z) F ^ i = 0 := by
  classical
  have hrel := fun i => segre_rel hPh Ψ hΨ i
  choose r hr G hG hrelz using hrel
  let R := MvPolynomial (Fin (e + 1)) ℂ
  let Z := ↥(mcPts P)
  let φw : MvPolynomial ((k : K) → ι k) ℂ →+* (Z → ℂ) :=
    Pi.ringHom fun z : Z => MvPolynomial.eval (segre z.1)
  let φy : R →+* (Z → ℂ) := Pi.ringHom fun z : Z => MvPolynomial.eval (Ψ (segre z.1))
  letI : Algebra R (Z → ℂ) := φy.toAlgebra
  have hsmul : ∀ (c : R) (x : Z → ℂ), c • x = φy c * x := fun c x => Algebra.smul_def c x
  let T : Finset (((k : K) → ι k) →₀ ℕ) :=
    (Fintype.piFinset fun i => Finset.range (r i)).image Finsupp.equivFunOnFinite.symm
  have memT : ∀ s : ((k : K) → ι k) →₀ ℕ, (∀ i, s i < r i) → s ∈ T := fun s hs =>
    Finset.mem_image.2 ⟨⇑s, Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (hs i),
      Finsupp.equivFunOnFinite_symm_coe s⟩
  let N : Submodule R (Z → ℂ) :=
    Submodule.span R (↑(T.image fun s => φw (monomial s 1)) : Set (Z → ℂ))
  have hC : ∀ (a : ℂ) (x : Z → ℂ), x ∈ N → φw (C a) * x ∈ N := by
    intro a x hx
    have e1 : φw (C a) = φy (C a) := by
      funext z
      show MvPolynomial.eval (segre z.1) (C a) = MvPolynomial.eval (Ψ (segre z.1)) (C a)
      rw [eval_C, eval_C]
    rw [e1, ← hsmul]
    exact N.smul_mem _ hx
  have hY : ∀ (j : Fin (e + 1)) (x : Z → ℂ), x ∈ N → φy (X j) * x ∈ N := by
    intro j x hx
    rw [← hsmul]
    exact N.smul_mem _ hx
  have key : ∀ d, ∀ f : MvPolynomial ((k : K) → ι k) ℂ, f.totalDegree ≤ d → φw f ∈ N := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro f hf
      rw [f.as_sum, map_sum]
      refine N.sum_mem fun s hs => ?_
      rw [show monomial s (coeff s f) = C (coeff s f) * monomial s 1 by
        rw [C_mul_monomial, mul_one], map_mul]
      apply hC
      have hsdeg : (s.sum fun _ e => e) ≤ d := (le_totalDegree hs).trans hf
      by_cases hall : ∀ i, s i < r i
      · exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (memT s hall)))
      · push_neg at hall
        obtain ⟨i, hi⟩ := hall
        obtain ⟨s', hsplit⟩ : ∃ s', s = s' + Finsupp.single i (r i) :=
          ⟨s - Finsupp.single i (r i), (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hi)).symm⟩
        have hdeg : (s.sum fun _ e => e) = (s'.sum fun _ e => e) + r i := by
          rw [hsplit, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
            Finsupp.sum_single_index rfl]
        have hXr : φw (X i ^ r i) = ∑ j, φy (X j) * φw (G i j) := by
          funext z
          rw [Finset.sum_apply]
          show MvPolynomial.eval (segre z.1) (X i ^ r i) =
            ∑ j, MvPolynomial.eval (Ψ (segre z.1)) (X j) * MvPolynomial.eval (segre z.1) (G i j)
          simp only [map_pow, eval_X]
          exact hrelz i z.1 z.2
        have hri := hr i
        rw [hsplit, monomial_add_single, map_mul, hXr, Finset.mul_sum]
        refine N.sum_mem fun j _ => ?_
        rw [mul_left_comm, ← map_mul φw]
        apply hY
        apply ih ((s.sum fun _ e => e) - 1) (by omega)
        calc (monomial s' 1 * G i j).totalDegree
            ≤ (monomial s' (1 : ℂ)).totalDegree + (G i j).totalDegree := totalDegree_mul _ _
          _ ≤ (s'.sum fun _ e => e) + (r i - 1) := by
            rw [totalDegree_monomial _ one_ne_zero]
            exact Nat.add_le_add_left (hG i j) _
          _ ≤ (s.sum fun _ e => e) - 1 := by omega
  have hFG : (Subalgebra.toSubmodule (Algebra.adjoin R (Set.range φw))).FG := by
    have e2 : Subalgebra.toSubmodule (Algebra.adjoin R (Set.range φw)) = N := by
      apply le_antisymm
      · rw [Algebra.adjoin_eq_span, Submodule.span_le]
        intro x hx
        let Mw : Submonoid (Z → ℂ) :=
          { carrier := Set.range φw
            mul_mem' := by
              rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
              exact ⟨a * b, map_mul _ _ _⟩
            one_mem' := ⟨1, map_one _⟩ }
        have hx' : x ∈ Mw := (Submonoid.closure_le.2 (fun y hy => hy)) hx
        obtain ⟨f, rfl⟩ := hx'
        exact key _ f le_rfl
      · rw [Submodule.span_le]
        intro x hx
        obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact Algebra.subset_adjoin ⟨_, rfl⟩
    rw [e2]
    exact ⟨_, rfl⟩
  have hint : IsIntegral R (φw F) :=
    IsIntegral.of_mem_of_fg (Algebra.adjoin R (Set.range φw)) hFG (φw F)
      (Algebra.subset_adjoin ⟨F, rfl⟩)
  obtain ⟨p, hpm, hp⟩ := hint
  refine ⟨p.natDegree, p.coeff, hpm.coeff_natDegree, fun z hz => ?_⟩
  have h := congrFun hp ⟨z, hz⟩
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_apply] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.Geo

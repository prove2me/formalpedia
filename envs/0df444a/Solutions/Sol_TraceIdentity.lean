-- Prove2me | solution 1 for TraceIdentity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:16:08.532252+00:00
-- url     : https://prove2.me/submissions/c7167cc1-0e9d-4574-ac3c-e4053a4157d3

module
public import Definitions.Def_PHarmonicPoly_MaxPointDerivatives
public import Definitions.Def_PHarmonicPoly_EpOpEvalPoly
public import Definitions.Def_PHarmonicPoly_TraceIdentity
public import Theorems.Thm_EpOpEvalPoly
public import Theorems.Thm_MaxPointDerivatives
public import Theorems.Thm_MvPolyHessian


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n m : ℕ} (hm : 1 ≤ m) {p : ℝ} {P : MvPolynomial (Fin n) ℝ}
    (hhom : P.IsHomogeneous m) {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1)
    (hmax : MvPolynomial.eval (fun i => e i) P = 1)
    (hbd : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 →
      |MvPolynomial.eval (fun i => y i) P| ≤ 1)
    (hE : EpAlg p P = 0)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    {i₀ : Fin n} (hb0 : b i₀ = e) :
    ∑ i ∈ Finset.univ.erase i₀,
        (iteratedFDeriv ℝ 2
            (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
            ![b i, b i] + (m : ℝ) * ((m : ℝ) - 1))
      = ((n : ℝ) - p) * ((m : ℝ) * ((m : ℝ) - 1)) := by
  obtain ⟨hgrad, hhess⟩ := MaxPointDerivatives hm hhom he hmax hbd
  have hm0 : (0:ℝ) < (m:ℝ) := by
    have h : 0 < m := hm
    exact_mod_cast h
  have hgn : ‖gradient (fun x : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun i => x i) P) e‖ ^ 2 = (m:ℝ) ^ 2 := by
    rw [hgrad, norm_smul, he, Real.norm_eq_abs, mul_one, sq_abs]
  have hkey : ∑ i, ∑ j, (e i) * (e j) *
      MvPolynomial.eval (fun k => e k) (pderiv i (pderiv j P))
      = (m:ℝ) * ((m:ℝ) - 1) := by
    rw [← MvPolyHessian P e e e]
    exact hhess
  have hhess3 : iteratedFDeriv ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) =>
        MvPolynomial.eval (fun i => x i) P) e
        ![gradient (fun x : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => x i) P) e,
          gradient (fun x : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => x i) P) e]
      = (m:ℝ) ^ 2 * ((m:ℝ) * ((m:ℝ) - 1)) := by
    rw [hgrad, MvPolyHessian P e ((m:ℝ) • e) ((m:ℝ) • e), ← hkey, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hc : ∀ z : Fin n, (((m:ℝ) • e : EuclideanSpace ℝ (Fin n)) z) = (m:ℝ) * e z :=
      fun z => rfl
    rw [hc, hc]
    ring
  have hlap : Laplacian.laplacian (fun x : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun i => x i) P) e
      = ∑ i, iteratedFDeriv ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) =>
          MvPolynomial.eval (fun i => x i) P) e ![b i, b i] := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  have hsplit : ∑ i, iteratedFDeriv ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) =>
        MvPolynomial.eval (fun i => x i) P) e ![b i, b i]
      = (m:ℝ) * ((m:ℝ) - 1) + ∑ i ∈ Finset.univ.erase i₀,
        iteratedFDeriv ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) =>
          MvPolynomial.eval (fun i => x i) P) e ![b i, b i] := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hb0, hhess]
  have heq : EpOp p (fun y : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun i => y i) P) e = 0 := by
    rw [EpOpEvalPoly p P e, hE]
    simp
  simp only [EpOp] at heq
  rw [hgn, hhess3, hlap, hsplit] at heq
  have hm2 : ((m:ℝ)) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hm0)
  have hfac : (m:ℝ) * ((m:ℝ) - 1)
      + (∑ i ∈ Finset.univ.erase i₀, iteratedFDeriv ℝ 2
          (fun x : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => x i) P) e ![b i, b i])
      + (p - 2) * ((m:ℝ) * ((m:ℝ) - 1)) = 0 := by
    have h1 : ((m:ℝ)) ^ 2 * ((m:ℝ) * ((m:ℝ) - 1)
        + (∑ i ∈ Finset.univ.erase i₀, iteratedFDeriv ℝ 2
            (fun x : EuclideanSpace ℝ (Fin n) =>
              MvPolynomial.eval (fun i => x i) P) e ![b i, b i])
        + (p - 2) * ((m:ℝ) * ((m:ℝ) - 1))) = 0 := by
      linear_combination heq
    exact (mul_eq_zero.mp h1).resolve_left hm2
  rw [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hcast : (((n - 1 : ℕ)) : ℝ) = (n:ℝ) - 1 := by
    have hn : 1 ≤ n := Fin.pos i₀
    push_cast [Nat.cast_sub hn]
    ring
  rw [hcast]
  linear_combination hfac

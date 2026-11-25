-- Prove2me | solution 1 for TotalDegreePDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:35:11.929394+00:00
-- url     : https://prove2.me/submissions/fdfcb371-2e05-47ec-a68a-2f60e250c877

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_TotalDegreePDeriv

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {σ : Type*} (i : σ) (φ : MvPolynomial σ ℝ) :
    (pderiv i φ).totalDegree ≤ φ.totalDegree - 1 := by
  classical
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le ?_
  intro s hs
  have hco : (pderiv i φ).coeff s ≠ 0 := by
    simpa using (MvPolynomial.mem_support_iff).1 hs
  rw [coeff_pderiv] at hco
  have hne : φ.coeff (s + Finsupp.single i 1) ≠ 0 := by
    intro h; rw [h, zero_mul] at hco; exact hco rfl
  have hmem : s + Finsupp.single i 1 ∈ φ.support := MvPolynomial.mem_support_iff.2 hne
  have hle : ((s + Finsupp.single i 1).sum fun _ e => e) ≤ φ.totalDegree :=
    MvPolynomial.le_totalDegree hmem
  have hsum : ((s + Finsupp.single i 1).sum fun _ e => e) = (s.sum fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (by intro a; rfl) (by intro a b₁ b₂; rfl)]
    simp [Finsupp.sum_single_index]
  omega

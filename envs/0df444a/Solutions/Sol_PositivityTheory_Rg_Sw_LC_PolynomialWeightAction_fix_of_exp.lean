-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.fix_of_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:44.538955+00:00
-- url     : https://prove2.me/submissions/a4f327f3-3050-48e7-8462-4ce9ed39731b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
theorem _root_.solution (δ : Derivation ℂ (MvPolynomial (FinalTheorems m n) ℂ) (MvPolynomial (FinalTheorems m n) ℂ))
    (φ : MvPolynomial (FinalTheorems m n) ℂ →ₐ[ℂ] MvPolynomial (FinalTheorems m n) ℂ) (c : ℂ)
    (hφ : ∀ v, φ (X v) = X v + C c * δ (X v))
    (hδ : ∀ v, ∃ (w : FinalTheorems m n) (r : ℂ), δ (X v) = C r * X w ∧ δ (X w) = 0)
    (p : MvPolynomial (FinalTheorems m n) ℂ) (hp : δ p = 0) : φ p = p := by
  classical
  let Φ : MvPolynomial (FinalTheorems m n) ℂ →ₐ[ℂ] Polynomial (MvPolynomial (FinalTheorems m n) ℂ) :=
    aeval (fun v => Polynomial.C (X v) + Polynomial.X * Polynomial.C (C c * δ (X v)))
  have hΦδ : ∀ v, Φ (δ (X v)) = Polynomial.C (δ (X v)) := by
    intro v
    obtain ⟨w, r, h1, h2⟩ := hδ v
    rw [h1]
    simp [Φ, h2, MvPolynomial.algebraMap_eq, Polynomial.C_mul]
  have hC : Φ (C c) = Polynomial.C (C c) := by
    simp [Φ, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]
  have hX : ∀ v, Φ (X v) = Polynomial.C (X v) + Polynomial.X * Polynomial.C (C c * δ (X v)) := by
    intro v; simp [Φ]
  have hder : ∀ q, Polynomial.derivative (Φ q) = Φ (C c * δ q) := by
    intro q
    refine MvPolynomial.induction_on (motive := fun q => Polynomial.derivative (Φ q) = Φ (C c * δ q)) q ?_ ?_ ?_
    · intro a
      simp [Φ, MvPolynomial.derivation_C, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    · intro p q hp hq
      simp only [map_add, Polynomial.derivative_add, hp, hq, mul_add]
    · intro p v hp
      rw [map_mul, Polynomial.derivative_mul, hp, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      simp only [mul_add, map_add, map_mul, hΦδ, hX, hC, Polynomial.derivative_add, Polynomial.derivative_C,
        Polynomial.derivative_mul, Polynomial.derivative_X, zero_add, one_mul, mul_zero, add_zero, Polynomial.C_mul]
      ring
  have hev1 : ∀ q, Polynomial.eval 1 (Φ q) = φ q := by
    intro q
    refine MvPolynomial.induction_on (motive := fun q => Polynomial.eval 1 (Φ q) = φ q) q ?_ ?_ ?_
    · intro a
      simp [Φ, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    · intro p q hp hq
      simp only [map_add, Polynomial.eval_add, hp, hq]
    · intro p v hp
      rw [map_mul, map_mul, Polynomial.eval_mul, hp, hX, hφ]
      simp
  have hev0 : ∀ q, Polynomial.eval 0 (Φ q) = q := by
    intro q
    refine MvPolynomial.induction_on (motive := fun q => Polynomial.eval 0 (Φ q) = q) q ?_ ?_ ?_
    · intro a
      simp [Φ, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    · intro p q hp hq
      simp only [map_add, Polynomial.eval_add, hp, hq]
    · intro p v hp
      rw [map_mul, Polynomial.eval_mul, hp, hX]
      simp
  have h0 : Polynomial.derivative (Φ p) = 0 := by rw [hder, hp, mul_zero, map_zero]
  have hdeg : (Φ p).natDegree = 0 := Polynomial.derivative_eq_zero.mp h0
  calc φ p = Polynomial.eval 1 (Φ p) := (hev1 p).symm
    _ = Polynomial.eval 0 (Φ p) := by rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]; simp
    _ = p := hev0 p
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction

-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.deriv_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:50:33.167495+00:00
-- url     : https://prove2.me/submissions/79dfea7b-874f-4d76-a3ef-a446beb6a9da

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorFormula
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_phi_X

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.SP.Mi
variable {n : ℕ}
set_option maxHeartbeats 2000000
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (p q : Fin ρ) (f : Pm (Polynomial ℂ) ρ) :
    (∑ a : Fin n, ∑ d : Fin n, yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (phi b I J f)) = phi b I J (del p q f) := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    simp [phi, del]
  | add f g hf hg =>
    simp only [map_add, Derivation.leibniz, mul_add, Finset.sum_add_distrib, hf, hg]
  | mul_X f pq hf =>
    have e : phi b I J (f * X pq) = phi b I J f * yv b (J pq.1) (I pq.2) := by rw [map_mul, phi_X]
    have hdx : del p q (X pq : Pm (Polynomial ℂ) ρ) = X (pq.1, p) * X (q, pq.2) := by simp [del, mkDerivation_X]
    rw [e, Derivation.leibniz (del p q), smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, ← hf, hdx, map_mul,
      phi_X, phi_X, phi_X]
    have hsplit : ∀ a d : Fin n, yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (phi b I J f * yv b (J pq.1) (I pq.2)) =
        yv b (J pq.1) (I pq.2) * (yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (phi b I J f)) +
          phi b I J f * (yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (yv b (J pq.1) (I pq.2))) := by
      intro a d
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hpart : (∑ a : Fin n, ∑ d : Fin n, yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (yv b (J pq.1) (I pq.2))) =
        yv b (J pq.1) (I p) * yv b (J q) (I pq.2) := by
      rw [Finset.sum_eq_single (J pq.1), Finset.sum_eq_single (I pq.2)]
      · simp only [yv, pderiv_X, Pi.single_eq_same, mul_one]
      · intro d _ hd
        simp only [yv, pderiv_X]
        rw [Pi.single_eq_of_ne (fun h => hd (congrArg (fun x : Bool × Fin n × Fin n => x.2.2) h).symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro a _ ha
        refine Finset.sum_eq_zero fun d _ => ?_
        simp only [yv, pderiv_X]
        rw [Pi.single_eq_of_ne (fun h => ha (congrArg (fun x : Bool × Fin n × Fin n => x.2.1) h).symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hpart, add_comm]
end PositivityTheory.Rg.Sw.SP

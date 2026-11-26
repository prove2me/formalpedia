-- Prove2me | solution 1 for SemigroupBetti.GenData.spanRank_le_beta1_of_n_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:16:58.720819+00:00
-- url     : https://prove2.me/submissions/0fc92d8f-578a-40e8-b624-bec17639f9b5

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
public import Theorems.Thm_SemigroupBetti_GenData_spanRank_toricKer_le_beta1

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution {n : Fin 4 → ℕ} (hn : G.n = n) :
    (RingHom.ker (MvPolynomial.aeval (R := K)
      (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom).spanRank ≤
      (G.beta1 : Cardinal) := by
  subst hn; exact G.spanRank_toricKer_le_beta1 K
end SemigroupBetti.GenData

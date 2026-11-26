-- Prove2me | solution 1 for SemigroupBetti.GenData.spanRank_toricKer_le_beta1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:15:36.350402+00:00
-- url     : https://prove2.me/submissions/0797d052-99de-48da-9a97-3ac0688b7d89

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
public import Theorems.Thm_SemigroupBetti_GenData_card_binomGens_le
public import Theorems.Thm_SemigroupBetti_GenData_toricKer_eq_span

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution :
    (RingHom.ker (MvPolynomial.aeval (R := K)
      (fun i => (Polynomial.X : Polynomial K) ^ G.n i)).toRingHom).spanRank ≤
      (G.beta1 : Cardinal) := by
  change (G.toricKer K).spanRank ≤ _
  rw [G.toricKer_eq_span K]
  calc (Ideal.span (G.binomGens K : Set (MvPolynomial (Fin 4) K))).spanRank
      ≤ Cardinal.mk (G.binomGens K : Set (MvPolynomial (Fin 4) K)) :=
        Submodule.spanRank_span_le_card _
    _ = (#(G.binomGens K) : Cardinal) := Cardinal.mk_coe_finset
    _ ≤ (G.beta1 : Cardinal) := Nat.cast_le.2 (G.card_binomGens_le K)
end SemigroupBetti.GenData

-- Prove2me | solution 1 for UAVariety.free_ump
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T16:55:32.18722+00:00
-- url     : https://prove2.me/submissions/1eb31557-46f5-4a3e-8deb-cd0699bee041

import Definitions.Def_UAVariety_defs
import Theorems.Thm_UAVariety_term_ump
import Theorems.Thm_UAVariety_quot_lift_hom
import Theorems.Thm_UAVariety_ker_quot_mem_S

universe u₁ v₁

open FirstOrder FirstOrder.Language UAVariety


theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]
    (K : Set (UAVariety.Alg L)) (X : Type u₁) (A : UAVariety.Alg L) (hA : A ∈ K) (v : X → A) :
    ∃! f : UAVariety.freeAlg K X →[L] A, ∀ x, f (UAVariety.freeGen K X x) = v x := by
  obtain ⟨e, he, -⟩ := term_ump (L := L) v
  obtain ⟨φ, hφ, hS⟩ := ker_quot_mem_S K hA e
  obtain ⟨g, hg⟩ := quot_lift_hom (freeCong K X) e
    (fun p q hpq => (hφ p q).1 (hpq φ hS))
  refine ⟨g, fun x => (hg _).trans (he x), fun f hf => ?_⟩
  -- the quotient map T(X) → F_K(X)
  let π : L.Term X →[L] freeAlg K X :=
    ⟨fun p => freeMk K X p, fun f ts => (funMap_quotient_mk' (s := (freeCong K X).toSetoid) f ts).symm,
      fun r => isEmptyElim r⟩
  have h1 : f.comp π = e := (term_ump (L := L) v).unique (fun x => hf x) he
  have h2 : g.comp π = e := (term_ump (L := L) v).unique (fun x => (hg _).trans (he x)) he
  ext a
  induction a using Quotient.ind with
  | _ p => exact congrArg (fun k : L.Term X →[L] A => k p) (h1.trans h2.symm)

-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.theorem_1_1_of_tests_and_compiler
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T18:16:19.000788+00:00
-- url     : https://prove2.me/submissions/1b46012b-311d-416b-83f7-0d28139c9a2f

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Languages

namespace TreeEquivalenceHORS.Equivalence

open Nat.Partrec (Code)
open Nat.Partrec.Code
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- A computable test at each depth semidecides failure by searching for a failing depth. -/
private theorem coCE_of_tests {P : ℕ → Prop} (test : ℕ → ℕ → Bool)
    (hc : Computable₂ test) (hs : ∀ n, P n ↔ ∀ d, test n d = true) : CoCE P := by
  have search := (Partrec.rfind (p := fun n d => Part.some (!(test n d)))
    (Primrec.not.to_comp.comp hc).partrec.to₂).dom_re
  apply search.of_eq
  intro n
  rw [Nat.rfind_dom (p := fun d => Part.some (!(test n d))), hs]
  simp

/-- Nonhalting for a pair consisting of a Mathlib partial-recursive program and its input. -/
def Nonhalts (n : ℕ) : Prop :=
  ¬ (eval (Denumerable.ofNat Code n.unpair.1) n.unpair.2).Dom

private theorem reduces_to_nonhalts {A : ℕ → Prop} (hA : CoCE A) : A ≤₀ Nonhalts := by
  have part : Partrec (fun n => (Part.assert (¬ A n) (fun _ => Part.some ())).map (fun _ => (0 : ℕ))) :=
    hA.map (Computable.const (0 : ℕ)).to₂
  obtain ⟨c, hc⟩ := exists_code.mp (Partrec.nat_iff.mp part)
  refine ⟨fun n => Nat.pair (Encodable.encode c) n, (Primrec₂.natPair.comp (Primrec.const _) Primrec.id).to_comp, ?_⟩
  intro n
  simp [Nonhalts, hc, Part.assert]

private theorem nonhalts_undecidable : ¬ ComputablePred Nonhalts := by
  intro h
  have reduce : (fun c : Code => ¬ (eval c 0).Dom) ≤₀ Nonhalts :=
    ⟨fun c => Nat.pair (Encodable.encode c) 0,
      (Primrec₂.natPair.comp Primrec.encode (Primrec.const 0)).to_comp,
      fun c => by simp [Nonhalts]⟩
  exact ComputablePred.halting_problem_not_re 0
    (ComputablePred.computable_of_manyOneReducible reduce h).to_re

private theorem classify {P : ℕ → Prop} (upper : CoCE P) (lower : Nonhalts ≤₀ P) :
    CoCEComplete P ∧ ¬ ComputablePred P :=
  ⟨⟨upper, fun _ h => (reduces_to_nonhalts h).trans lower⟩,
    fun h => nonhalts_undecidable (ComputablePred.computable_of_manyOneReducible lower h)⟩

/-- The two remaining inputs to the classification are a uniform family of terminating depth
tests and a computable reduction into the common safe, productive, binary fragment. -/

private theorem proved_here
    (tests : ∀ P ∈ [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd],
      ∃ test : ℕ → ℕ → Bool, Computable₂ test ∧ ∀ n, P n ↔ ∀ d, test n d = true)
    (F : ℕ → HORS × HORS) (hF : Computable (fun n => Encodable.encode (F n)))
    (good : ∀ n, ∀ G ∈ [(F n).1, (F n).2],
      G.Valid ∧ G.alphabet = sigma2 ∧ G.order ≤ 4 ∧ G.Prod ∧ G.Safe)
    (correct : ∀ n, (¬ (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n.unpair.1) n.unpair.2).Dom) ↔ (F n).1.BT = (F n).2.BT) :
    (CoCEComplete EqHORS ∧ ¬ ComputablePred EqHORS) ∧
    (CoCEComplete Eq4Sigma2 ∧ ¬ ComputablePred Eq4Sigma2) ∧
    (CoCEComplete Eq4Sigma2Prod ∧ ¬ ComputablePred Eq4Sigma2Prod) ∧
    (CoCEComplete Eq4Sigma2SafeProd ∧ ¬ ComputablePred Eq4Sigma2SafeProd) := by
  have allP (P) (hp : P ∈ [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd]) :
      CoCEComplete P ∧ ¬ ComputablePred P := by
    obtain ⟨test, hc, hs⟩ := tests P hp
    apply classify (coCE_of_tests test hc hs)
    refine ⟨_, hF, fun n => (correct n).trans ?_⟩
    obtain ⟨v₁, a₁, o₁, p₁, s₁⟩ := good n (F n).1 (by simp)
    obtain ⟨v₂, a₂, o₂, p₂, s₂⟩ := good n (F n).2 (by simp)
    rcases hpair : F n with ⟨G, H⟩
    simp only [hpair] at v₁ a₁ o₁ p₁ s₁ v₂ a₂ o₂ p₂ s₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      simp [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd, ValidPair,
        Encodable.encodek, v₁, a₁, o₁, p₁, s₁, v₂, a₂, o₂, p₂, s₂]
  exact ⟨allP _ (by simp), allP _ (by simp), allP _ (by simp), allP _ (by simp)⟩

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution
    (tests : ∀ P ∈ [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd],
      ∃ test : ℕ → ℕ → Bool, Computable₂ test ∧ ∀ n, P n ↔ ∀ d, test n d = true)
    (F : ℕ → HORS × HORS) (hF : Computable (fun n => Encodable.encode (F n)))
    (good : ∀ n, ∀ G ∈ [(F n).1, (F n).2],
      G.Valid ∧ G.alphabet = sigma2 ∧ G.order ≤ 4 ∧ G.Prod ∧ G.Safe)
    (correct : ∀ n, (¬ (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n.unpair.1) n.unpair.2).Dom) ↔ (F n).1.BT = (F n).2.BT) :
    (CoCEComplete EqHORS ∧ ¬ ComputablePred EqHORS) ∧
    (CoCEComplete Eq4Sigma2 ∧ ¬ ComputablePred Eq4Sigma2) ∧
    (CoCEComplete Eq4Sigma2Prod ∧ ¬ ComputablePred Eq4Sigma2Prod) ∧
    (CoCEComplete Eq4Sigma2SafeProd ∧ ¬ ComputablePred Eq4Sigma2SafeProd) := proved_here tests F hF good correct

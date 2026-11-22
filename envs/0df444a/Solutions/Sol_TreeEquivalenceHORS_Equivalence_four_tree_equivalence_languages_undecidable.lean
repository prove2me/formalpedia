-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.four_tree_equivalence_languages_undecidable
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T19:09:33.45736+00:00
-- url     : https://prove2.me/submissions/2e71e456-6f5a-4495-b5f2-495fb39324cd

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Languages
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_universal_zero_start_simulation
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_theorem_5_8
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_9
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_nonhalting_iff_compiled_tree_equality

namespace TreeEquivalenceHORS.Equivalence

private theorem effective_on_actual_codes {α β : Type} [Encodable α] [Encodable β]
    (f : α → β) (hf : Computable (fun n : ℕ => Encodable.encode ((Encodable.decode n : Option α).map f)))
    (g : ℕ → α) (hg : Computable (fun n => Encodable.encode (g n))) :
    Computable (fun n => Encodable.encode (f (g n))) := by
  apply (Primrec.pred.to_comp.comp (hf.comp hg)).of_eq
  intro n
  simp [Encodable.encodek]

theorem compiled_binary_pairs_of_source_simulation
    (U : ℕ → Prop)
    (sim : ∃ m : ℕ → Machine, Computable (fun n => Encodable.encode (m n)) ∧
      ∀ n, U n ↔ ¬ (m n).Halts)
    (hc : Computable (fun n : ℕ => Encodable.encode ((Encodable.decode n : Option Machine).map
      fun M => (compile .L M, compile .R M))))
    (hs : ∀ (M : Machine) (s : Side), (compile s M).Valid ∧ (compile s M).Safe ∧
      (compile s M).Prod ∧ (compile s M).alphabet = sigma0 ∧ (compile s M).order ≤ 4)
    (he : ∀ M : Machine, ¬ M.Halts ↔ (compile .L M).BT = (compile .R M).BT)
    (f : HORS → HORS) (hcomp : Computable (fun n : ℕ => Encodable.encode ((Encodable.decode n : Option HORS).map f)))
    (props : ∀ G : HORS, G.Valid → G.alphabet = sigma0 → G.Prod → (f G).Valid ∧
      (f G).alphabet = sigma2 ∧ (f G).Prod ∧ (f G).order ≤ max 1 G.order ∧
      (f G).BT = encAt G.BT ∧ (G.Safe → (f G).Safe))
    (refl : ∀ G H : HORS, G.Valid → H.Valid → G.alphabet = sigma0 → H.alphabet = sigma0 →
      G.Prod → H.Prod → ((f G).BT = (f H).BT ↔ G.BT = H.BT)) :
    ∃ F : ℕ → HORS × HORS, Computable (fun n => Encodable.encode (F n)) ∧
      (∀ n, ∀ G ∈ [(F n).1, (F n).2], G.Valid ∧ G.alphabet = sigma2 ∧ G.order ≤ 4 ∧ G.Prod ∧ G.Safe) ∧
      ∀ n, U n ↔ (F n).1.BT = (F n).2.BT := by
  obtain ⟨m, cm, hm⟩ := sim
  let L (n : ℕ) := compile .L (m n)
  let R (n : ℕ) := compile .R (m n)
  have cp : Computable (fun n => Encodable.encode (L n,R n)) := effective_on_actual_codes _ hc m cm
  have cl : Computable (fun n => Encodable.encode (L n)) :=
    ((Computable.fst.comp Computable.unpair).comp cp).of_eq (fun n => by simp [Encodable.encode_prod_val])
  have cr : Computable (fun n => Encodable.encode (R n)) :=
    ((Computable.snd.comp Computable.unpair).comp cp).of_eq (fun n => by simp [Encodable.encode_prod_val])
  refine ⟨fun n => (f (L n), f (R n)), ?_, ?_, ?_⟩
  · exact (Primrec₂.natPair.to_comp.comp (effective_on_actual_codes f hcomp L cl)
      (effective_on_actual_codes f hcomp R cr)).of_eq (fun n => rfl)
  · intro n G mem
    have good (s : Side) : (f (compile s (m n))).Valid ∧ (f (compile s (m n))).alphabet = sigma2 ∧
        (f (compile s (m n))).order ≤ 4 ∧ (f (compile s (m n))).Prod ∧ (f (compile s (m n))).Safe := by
      obtain ⟨v,safe,p,a,o⟩ := hs (m n) s
      obtain ⟨v',a',p',o',_,safe'⟩ := props _ v a p
      exact ⟨v',a',o'.trans (max_le (by decide) o),p',safe' safe⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact good .L
    · exact good .R
  · intro n
    obtain ⟨vl,_,pl,al,_⟩ := hs (m n) .L
    obtain ⟨vr,_,pr,ar,_⟩ := hs (m n) .R
    exact (hm n).trans ((he _).trans (refl _ _ vl vr al ar pl pr).symm)

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- A computable test at each depth semidecides failure by searching for a failing depth. -/
theorem coCE_of_tests {P : ℕ → Prop} (test : ℕ → ℕ → Bool)
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

theorem reduces_to_nonhalts {A : ℕ → Prop} (hA : CoCE A) : A ≤₀ Nonhalts := by
  have part : Partrec (fun n => (Part.assert (¬ A n) (fun _ => Part.some ())).map (fun _ => (0 : ℕ))) :=
    hA.map (Computable.const (0 : ℕ)).to₂
  obtain ⟨c, hc⟩ := exists_code.mp (Partrec.nat_iff.mp part)
  refine ⟨fun n => Nat.pair (Encodable.encode c) n, (Primrec₂.natPair.comp (Primrec.const _) Primrec.id).to_comp, ?_⟩
  intro n
  simp [Nonhalts, hc, Part.assert]

theorem nonhalts_undecidable : ¬ ComputablePred Nonhalts := by
  intro h
  have reduce : (fun c : Code => ¬ (eval c 0).Dom) ≤₀ Nonhalts :=
    ⟨fun c => Nat.pair (Encodable.encode c) 0,
      (Primrec₂.natPair.comp Primrec.encode (Primrec.const 0)).to_comp,
      fun c => by simp [Nonhalts]⟩
  exact ComputablePred.halting_problem_not_re 0
    (ComputablePred.computable_of_manyOneReducible reduce h).to_re


/-- One computable map simultaneously reduces nonhalting to all four languages. -/
private theorem shared_reduction :
    ∃ f : ℕ → ℕ, Computable f ∧ ∀ P ∈ [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd],
      ∀ n, Nonhalts n ↔ P (f n) := by
  obtain ⟨b, hb, hprops, hreflect⟩ := lemma_5_9
  obtain ⟨F, hF, good, correct⟩ := compiled_binary_pairs_of_source_simulation
    Nonhalts universal_zero_start_simulation theorem_5_8.1 theorem_5_8.2.1
    nonhalting_iff_compiled_tree_equality b hb hprops hreflect
  refine ⟨fun n => Encodable.encode (F n), hF, ?_⟩
  intro P hp n
  refine (correct n).trans ?_
  obtain ⟨v₁, a₁, o₁, p₁, s₁⟩ := good n (F n).1 (by simp)
  obtain ⟨v₂, a₂, o₂, p₂, s₂⟩ := good n (F n).2 (by simp)
  rcases hpair : F n with ⟨G, H⟩
  simp only [hpair] at v₁ a₁ o₁ p₁ s₁ v₂ a₂ o₂ p₂ s₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    simp [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd, ValidPair,
      Encodable.encodek, hpair, v₁, a₁, o₁, p₁, s₁, v₂, a₂, o₂, p₂, s₂]

/-- Undecidability and co-c.e.-hardness hold even with all the restrictions imposed together. -/

private theorem proved_here :
    ∀ P ∈ [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd],
      (∀ A : ℕ → Prop, CoCE A → A ≤₀ P) ∧ ¬ ComputablePred P := by
  obtain ⟨f, hf, h⟩ := shared_reduction
  intro P hp
  have lower : Nonhalts ≤₀ P := ⟨f, hf, h P hp⟩
  exact ⟨fun _ hA => (reduces_to_nonhalts hA).trans lower,
    fun dec => nonhalts_undecidable (ComputablePred.computable_of_manyOneReducible lower dec)⟩

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution :
    ∀ P ∈ [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd],
      (∀ A : ℕ → Prop, CoCE A → A ≤₀ P) ∧ ¬ ComputablePred P := proved_here

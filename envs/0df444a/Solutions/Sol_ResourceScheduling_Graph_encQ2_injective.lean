-- Prove2me | solution 1 for ResourceScheduling.Graph.encQ2_injective
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T05:55:30.814117+00:00
-- url     : https://prove2.me/submissions/8ea1b7de-114d-4145-896b-6f1b11181b88

import Definitions.Def_ResourceScheduling_Graph_ResDot11
import Theorems.Thm_ResourceScheduling_Graph_unary_codec_correct

set_option autoImplicit false

open ResourceScheduling.Graph

private theorem unary_split {n m : ℕ} {xs ys : List Letter}
    (h : unary n ++ xs = unary m ++ ys) : n = m ∧ xs = ys := by
  have e := congrArg readUnary h
  simpa only [unary_codec_correct.1, Option.some.injEq, Prod.mk.injEq] using e

private theorem table_injective {α : Type} (m n : ℕ) :
    Function.Injective (fun f : Fin m → Fin n → α =>
      (List.finRange m).flatMap fun i => (List.finRange n).map (f i)) := by
  induction m with
  | zero => intro f g _; funext i; exact Fin.elim0 i
  | succ m ih =>
    intro f g h
    simp only [List.finRange_succ, List.flatMap_cons, List.flatMap_map,
      Function.comp_def] at h
    obtain ⟨hzero, hsucc⟩ := List.append_inj h (by simp)
    have hz : f 0 = g 0 := List.ofFn_injective (by simpa [List.ofFn_eq_map] using hzero)
    have hs : (fun i : Fin m => f i.succ) = (fun i => g i.succ) := ih hsucc
    funext i
    refine Fin.cases hz (fun j => congrFun hs j) i

private theorem requirement_encoding {n l : ℕ} (r : Fin l → Fin n → ℕ) :
    (List.finRange l).flatMap (fun h => (List.finRange n).flatMap fun j => unary (r h j)) =
      encNatList ((List.finRange l).flatMap fun h => (List.finRange n).map (r h)) := by
  simp [encNatList, List.flatMap_assoc, List.flatMap_map, Function.comp_def]

private theorem data_injective : Function.Injective ResDot11Data.enc := by
  intro x z h
  rcases x with ⟨n, l, r, hr, y⟩
  rcases z with ⟨n', l', r', hr', y'⟩
  simp only [ResDot11Data.enc, List.append_assoc] at h
  obtain ⟨hn, h⟩ := unary_split h
  subst n'
  obtain ⟨hl, h⟩ := unary_split h
  subst l'
  rw [requirement_encoding, requirement_encoding] at h
  have codes : encNatList (((List.finRange l).flatMap fun i =>
      (List.finRange n).map (r i)) ++ [y]) =
      encNatList (((List.finRange l).flatMap fun i =>
        (List.finRange n).map (r' i)) ++ [y']) := by
    simpa only [encNatList, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] using h
  have fields := unary_codec_correct.2.2 codes
  obtain ⟨hmatrix, hy⟩ := List.append_inj' fields (by simp)
  have heq := table_injective l n hmatrix
  have hy' : y = y' := by simpa using hy
  subst r'
  subst y'
  rfl

/-- The exact original unary encoding uniquely determines both speeds and all instance data. -/
theorem solution : Function.Injective encQ2 := by
  rintro ⟨q, x⟩ ⟨v, z⟩ h
  simp only [encQ2, List.append_assoc] at h
  obtain ⟨h0, h⟩ := unary_split h
  obtain ⟨h1, hdata⟩ := unary_split h
  have hq : q = v := by
    funext i
    fin_cases i
    · exact Subtype.ext h0
    · exact Subtype.ext h1
  exact Prod.ext hq (data_injective hdata)

#print axioms solution

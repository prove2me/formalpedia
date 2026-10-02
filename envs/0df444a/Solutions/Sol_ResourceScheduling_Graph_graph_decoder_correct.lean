-- Prove2me | solution 1 for ResourceScheduling.Graph.graph_decoder_correct
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T06:05:48.341988+00:00
-- url     : https://prove2.me/submissions/fe470e4a-385b-469f-bab5-6d5b262d5bda

import Definitions.Def_ResourceScheduling_Graph_Decoder
import Theorems.Thm_ResourceScheduling_Graph_unary_codec_correct

set_option autoImplicit false

open ResourceScheduling.Graph

private def tableWord {n : ℕ} (f : Fin n → Fin n → Letter) : List Letter :=
  (List.finRange n).flatMap fun i => (List.finRange n).map (f i)

private theorem tableWord_length {n : ℕ} (f : Fin n → Fin n → Letter) :
    (tableWord f).length = n * n := by
  simp [tableWord, List.length_flatMap]

private theorem tableWord_recover (n : ℕ) (bits : List Letter) (h : bits.length = n * n) :
    tableWord (fun i j : Fin n => bits.getD (i.val * n + j.val) Letter.sep) = bits := by
  have hget (k : Fin (n * n)) : bits.getD k.val Letter.sep = bits[k.val]'(by omega) := by
    simp [List.getD_eq_getElem?_getD, h, k.isLt]
  have e := List.ofFn_mul (fun k : Fin (n * n) => bits.getD k.val Letter.sep)
  rw [show List.ofFn (fun k : Fin (n * n) => bits.getD k.val Letter.sep) = bits by
    simp_rw [hget]
    apply List.ext_getElem
    · simpa using h.symm
    · intro i h₁ h₂; simp] at e
  simpa [tableWord, List.ofFn_eq_map, List.flatMap_def] using e.symm

private theorem tableWord_get {n : ℕ} (f : Fin n → Fin n → Letter) (i j : Fin n) :
    (tableWord f).getD (i.val * n + j.val) Letter.sep = f i j := by
  let g : Fin (n * n) → Letter := fun k => f k.divNat k.modNat
  have hg (a b : Fin n) : g (Fin.mkDivMod a b) = f a b := by simp [g]
  have e : List.ofFn g = tableWord f := by
    rw [List.ofFn_mul']
    change (List.ofFn fun a : Fin n => List.ofFn fun b : Fin n =>
      g (Fin.mkDivMod a b)).flatten = tableWord f
    simp_rw [hg]
    simp [tableWord, List.ofFn_eq_map, List.flatMap_def]
  rw [← e]
  have hidx : i.val * n + j.val < n * n := by
    calc
      i.val * n + j.val < (i.val + 1) * n := by nlinarith [j.isLt]
      _ ≤ n * n := Nat.mul_le_mul_right n i.isLt
  calc
    _ = g (Fin.mkDivMod i j) := by
      have hnidx : n * i.val + j.val < n * n := by simpa [Nat.mul_comm] using hidx
      simp [List.getD_eq_getElem?_getD, hnidx, Fin.mkDivMod, Nat.mul_comm]
    _ = f i j := hg i j

private theorem rawAdj_encoded (d : GraphData) (i j : Fin (3 * d.t)) :
    rawAdj (3 * d.t) (tableWord (fun a b => if d.G.Adj a b then Letter.one else Letter.sep))
      i j ↔ d.G.Adj i j := by
  unfold rawAdj
  rw [tableWord_get]
  by_cases h : d.G.Adj i j <;> simp [h]

private theorem valid_encoded (d : GraphData) : ValidGraphBody (3 * d.t)
    (tableWord (fun a b => if d.G.Adj a b then Letter.one else Letter.sep)) := by
  refine ⟨tableWord_length _, ?_, ?_⟩
  · intro i j h
    exact (rawAdj_encoded d j i).mpr (d.G.adj_symm ((rawAdj_encoded d i j).mp h))
  · intro i h
    exact d.G.irrefl ((rawAdj_encoded d i i).mp h)

private theorem decode_encode (d : GraphData) : decodeGraph (encGraph d) = some d := by
  unfold encGraph
  change decodeGraph (unary d.t ++ tableWord _) = some d
  simp only [decodeGraph, unary_codec_correct.1, dif_pos (valid_encoded d)]
  congr 1
  rcases d with ⟨t, G, decAdj⟩
  congr 1
  ext i j
  exact rawAdj_encoded { t := t, G := G } i j

private theorem bit_test (a : Letter) :
    (if a = Letter.one then Letter.one else Letter.sep) = a := by
  cases a <;> rfl

private theorem tableWord_decode (n : ℕ) (bits : List Letter) (h : bits.length = n * n) :
    tableWord (fun i j => if rawAdj n bits i j then Letter.one else Letter.sep) = bits := by
  trans tableWord (fun i j : Fin n => bits.getD (i.val * n + j.val) Letter.sep)
  · congr 1
    funext i j
    unfold rawAdj
    exact bit_test _
  · exact tableWord_recover n bits h

private theorem decode_sound (w : List Letter) (d : GraphData)
    (h : decodeGraph w = some d) : encGraph d = w := by
  unfold decodeGraph at h
  cases hp : readUnary w with
  | none => simp [hp] at h
  | some p =>
    rcases p with ⟨t, bits⟩
    simp only [hp] at h
    split at h
    next hv =>
      simp only [Option.some.injEq] at h
      subst d
      rw [unary_codec_correct.2.1 w t bits hp]
      change unary t ++ tableWord _ = unary t ++ bits
      rw [tableWord_decode (3 * t) bits hv.1]
    next _ => simp at h

/-- Exact decoding of graph codes, and reconstruction for every successful parse. -/
theorem solution :
    (∀ d, decodeGraph (encGraph d) = some d) ∧
    (∀ w d, decodeGraph w = some d → encGraph d = w) := by
  exact ⟨decode_encode, decode_sound⟩

#print axioms solution

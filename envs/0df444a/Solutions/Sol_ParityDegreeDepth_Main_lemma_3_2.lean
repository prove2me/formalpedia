-- Prove2me | solution 1 for ParityDegreeDepth.Main.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:24:53.831982+00:00
-- url     : https://prove2.me/submissions/b8c41d19-9cde-46b0-b3f3-d214b74ea10b

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol
import Theorems.Thm_ParityDegreeDepth_Core_anf_degree_differences
import Theorems.Thm_ParityDegreeDepth_Core_contraction_rank_bound

open scoped BigOperators
noncomputable section


namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private def phase {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (x : Vec n (ZMod 2)) : ℝ :=
  (-1 : ℝ) ^ (p x).val

private def spectralNorm {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℝ :=
  ∑ a, |QAlgorithms.boolFourier f a|

private def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

private def coefficient {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
  then 1 else 0

private def anfDegree {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) : WithBot ℕ :=
  Finset.univ.sup fun S : Finset (Fin n) =>
    if coefficient p S = 0 then ⊥ else (S.card : WithBot ℕ)

private def delta {n : ℕ} (h : Vec n (ZMod 2)) (p : Vec n (ZMod 2) → ZMod 2)
    (x : Vec n (ZMod 2)) : ZMod 2 := p (x + h) + p x

private def differences {n k : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (h : Fin k → Vec n (ZMod 2)) : Vec n (ZMod 2) → ZMod 2 :=
  (List.ofFn h).foldl (fun q v => delta v q) p

private abbrev Form (F : Type) (n d : ℕ) := (Fin d → Vec n F) → F

private def topForm {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (d : ℕ) : Form (ZMod 2) n d :=
  fun h => differences p h 0

private def contraction {F : Type} [Field F] {n d : ℕ} (T : Form F n d)
    (h : Fin (d - 2) → Vec n F) : Matrix (Fin n) (Fin n) F :=
  fun i j => T (fun s => if hs : s.val < d - 2 then h ⟨s.val, hs⟩
    else if s.val = d - 2 then Pi.single i 1 else Pi.single j 1)

private def binaryRank {n d : ℕ} (T : Form (ZMod 2) n d) : ℕ :=
  Finset.univ.sup fun h : Fin (d - 2) → Vec n (ZMod 2) => (contraction T h).rank



/-- ANF degree `d` gives vanishing `(d+1)`-fold differences -/
private lemma degLe_of_anf {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (hp : anfDegree p = (d : WithBot ℕ)) :
    ∀ (h : Fin (d + 1) → Fin n → ZMod 2) (x : Fin n → ZMod 2),
      (List.ofFn h).foldl (fun q v y => q (y + v) + q y) p x = 0 := by
  classical
  apply (ParityDegreeDepth.Core.anf_degree_differences (d := d) p).1
  intro S hS
  by_contra hne
  have : ((S.card : ℕ) : WithBot ℕ) ≤ anfDegree p := by
    unfold anfDegree
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun S : Finset (Fin n) =>
      if coefficient p S = 0 then (⊥ : WithBot ℕ) else (S.card : WithBot ℕ)) (Finset.mem_univ S))
    simp only [show coefficient p S = (if ParityCubes.anfCoeff
      (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S then (1 : ZMod 2) else 0) from rfl,
      if_neg hne]
  rw [hp] at this
  have : S.card ≤ d := by exact_mod_cast this
  omega

end ParityDegreeDepth.Main

open ParityDegreeDepth.Main in
/-- lemma 3 2; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem solution {n d : ℕ} (p : Vec n (ZMod 2) → ZMod 2)
    (hd : 2 ≤ d) (hp : anfDegree p = (d : WithBot ℕ)) :
    (binaryRank (topForm p d) : ℝ) ≤ (2 : ℝ) ^ (d - 1) * logTwo (spectralNorm (phase p)) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hdeg := degLe_of_anf p hp
  have hL : ∀ h : Fin (k + 2 - 2) → Vec n (ZMod 2),
      ((contraction (topForm p (k + 2)) h).rank : ℝ) ≤
        (2 : ℝ) ^ (k + 2 - 1) * logTwo (spectralNorm (phase p)) := by
    intro h
    have hfun : ∀ i j : Fin n, (fun s : Fin (k + 2) => if hs : s.val < k + 2 - 2 then h ⟨s.val, hs⟩
        else if s.val = k + 2 - 2 then (Pi.single i 1 : Fin n → ZMod 2) else Pi.single j 1) =
        Fin.append (fun l : Fin k => h ⟨l.val, by omega⟩) ![Pi.single i 1, Pi.single j 1] := by
      intro i j
      funext s
      refine Fin.addCases (fun l => ?_) (fun t => ?_) s
      · simp only [Fin.append_left, Fin.val_castAdd]
        rw [dif_pos (by omega)]
      · simp only [Fin.append_right, Fin.val_natAdd]
        fin_cases t
        · simp
        · simp
    have hM : contraction (topForm p (k + 2)) h = Matrix.of fun i j : Fin n =>
        (List.ofFn (Fin.append (fun l : Fin k => h ⟨l.val, by omega⟩)
          ![Pi.single i 1, Pi.single j 1])).foldl (fun q v y => q (y + v) + q y) p 0 := by
      ext i j
      simp only [contraction, topForm, Matrix.of_apply]
      rw [hfun i j]
      rfl
    rw [hM, show k + 2 - 1 = k + 1 by omega]
    exact ParityDegreeDepth.Core.contraction_rank_bound (k := k) p hdeg _
  obtain ⟨h0, -, h0eq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (k + 2 - 2) → Vec n (ZMod 2)))
    Finset.univ_nonempty (fun h => (contraction (topForm p (k + 2)) h).rank)
  unfold binaryRank
  rw [h0eq]
  exact hL h0




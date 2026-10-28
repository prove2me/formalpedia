-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.axis_commutations_and_rewriting
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:55:17.84488+00:00
-- url     : https://prove2.me/submissions/fb0fe410-bbb4-436a-860f-318d47fb099a

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_e_order_and_basis_cycle
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_et_normal_form
noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

local notation "Mat" => Matrix Bool Bool ℂ

namespace S173N

abbrev E : Mat := cliffordE.val

lemma cwm_append (w1 w2 : List CliffordLetter) :
    cliffordWordMatrix (w1 ++ w2) = cliffordWordMatrix w1 * cliffordWordMatrix w2 := by
  simp [cliffordWordMatrix, List.map_append, List.prod_append]

lemma E2_eq : cliffordE2.val = E * E := by
  show cliffordWordMatrix _ = cliffordWordMatrix _ * cliffordWordMatrix _
  rw [cwm_append]

lemma E3 : E ^ 3 = 1 := e_order_and_basis_cycle.1

lemma Epow_mod (n : ℕ) : E ^ n = E ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, E3, one_pow, one_mul]

def ePow (k : Fin 3) : Mat := E ^ k.val

lemma ePow_add (a b : Fin 3) : ePow a * ePow b = ePow (a + b) := by
  unfold ePow
  rw [← pow_add, Epow_mod, Fin.val_add]

lemma ePow_zero : ePow 0 = 1 := by simp [ePow]

lemma mem_mul {A B : Mat} (hA : A ∈ cliffordSet) (hB : B ∈ cliffordSet) : A * B ∈ cliffordSet := by
  obtain ⟨w1, rfl⟩ := hA; obtain ⟨w2, rfl⟩ := hB
  exact ⟨w1 ++ w2, cwm_append w1 w2⟩

lemma ePow_mem (k : Fin 3) : ePow k ∈ cliffordSet := by
  unfold ePow
  induction k.val with
  | zero => exact ⟨[], by simp [cliffordWordMatrix]⟩
  | succ m ih => rw [pow_succ]; exact mem_mul ih cliffordE.property

def cmul (k : Fin 3) (C : Clifford) : Clifford := ⟨ePow k * C.val, mem_mul (ePow_mem k) C.property⟩

lemma ePow1 : ePow 1 = E := by simp [ePow]
lemma ePow2 : ePow 2 = E * E := by simp [ePow, pow_two]

lemma axis_eq (r : Fin 3) : axisTGate r = ePow (r + 1) * QAlgorithms.gateT * ePow (-(r + 1)) := by
  rcases (by decide : ∀ r : Fin 3, r = 0 ∨ r = 1 ∨ r = 2) r with rfl | rfl | rfl
  · rw [show ((0 : Fin 3) + 1) = 1 by decide, show -(1 : Fin 3) = 2 by decide, ePow1, ePow2]
    simp [axisTGate, E2_eq]
  · rw [show ((1 : Fin 3) + 1) = 2 by decide, show -(2 : Fin 3) = 1 by decide, ePow1, ePow2]
    simp [axisTGate, E2_eq]
  · rw [show ((2 : Fin 3) + 1) = 0 by decide, show -(0 : Fin 3) = 0 by decide, ePow_zero]
    simp [axisTGate]

lemma axis_conj (r : Fin 3) : axisTGate r * ePow (r + 1) = ePow (r + 1) * QAlgorithms.gateT := by
  rw [axis_eq, Matrix.mul_assoc, ePow_add, neg_add_cancel, ePow_zero, Matrix.mul_one]

lemma E_T (r : Fin 3) : E * axisTGate r = axisTGate (r + 1) * E := by
  rw [← ePow1, axis_eq, axis_eq]
  simp only [← Matrix.mul_assoc]
  rw [ePow_add, Matrix.mul_assoc _ (ePow (-(r + 1 + 1))) (ePow 1), ePow_add,
    show (1 : Fin 3) + (r + 1) = r + 1 + 1 by revert r; decide, show -(r + 1 + 1) + 1 = -(r + 1) by revert r; decide]

def syl (q : Bool) : Fin 3 := if q then 2 else 1

def bodyV (body : List Bool) : Mat := (body.map (fun q => ePow (syl q) * QAlgorithms.gateT)).prod

lemma normalValue_eq (M : NormalForm) :
    normalValue cliffordE cliffordE2 M =
      (if M.leadingT then QAlgorithms.gateT else 1) * bodyV M.body * M.terminal.val := by
  unfold normalValue normalTokens
  simp only [List.map_append, List.prod_append]
  congr 1
  · congr 1
    · split_ifs <;> simp [tokenMatrix]
    · unfold bodyV
      induction M.body with
      | nil => simp
      | cons q qs ih =>
        simp only [List.flatMap_cons, List.map_append, List.prod_append, List.map_cons, List.prod_cons, ih]
        cases q <;> simp [tokenMatrix, syl, ePow, E2_eq, pow_two, Matrix.mul_assoc]
  · simp [tokenMatrix]

lemma axisValue_eq (A : AxisForm) : axisValue A = (A.axes.map axisTGate).prod * A.terminal.val := by
  simp [axisValue, axisTokens, List.map_append, List.prod_append, tokenMatrix, Function.comp_def]

def toBody : Fin 3 → List (Fin 3) → List Bool
  | _, [] => []
  | p, r :: rs => decide (r - p = 2) :: toBody r rs

def scan : Fin 3 → List Bool → List (Fin 3)
  | _, [] => []
  | p, q :: qs => (p + syl q) :: scan (p + syl q) qs

def lastA : Fin 3 → List (Fin 3) → Fin 3
  | p, [] => p
  | _, r :: rs => lastA r rs

lemma syl_ne (q : Bool) : syl q ≠ 0 := by cases q <;> decide

lemma syl_toBody (p r : Fin 3) (h : r ≠ p) : syl (decide (r - p = 2)) = r - p := by
  fin_cases p <;> fin_cases r <;> simp_all [syl] <;> decide

lemma toBody_scan (p : Fin 3) (qs : List Bool) : toBody p (scan p qs) = qs := by
  induction qs generalizing p with
  | nil => rfl
  | cons q qs ih =>
    simp only [scan, toBody, ih, List.cons.injEq, and_true]
    cases q <;> simp [syl] <;> decide

lemma scan_toBody (p : Fin 3) (rs : List (Fin 3)) (h : (p :: rs).IsChain (· ≠ ·)) :
    scan p (toBody p rs) = rs := by
  induction rs generalizing p with
  | nil => rfl
  | cons r rs ih =>
    rw [List.isChain_cons_cons] at h
    simp only [toBody, scan]
    rw [syl_toBody p r (Ne.symm h.1), add_sub_cancel, ih r h.2]

lemma scan_chain (p : Fin 3) (qs : List Bool) : (p :: scan p qs).IsChain (· ≠ ·) := by
  induction qs generalizing p with
  | nil => simp [scan]
  | cons q qs ih =>
    simp only [scan]
    rw [List.isChain_cons_cons]
    refine ⟨?_, ih _⟩
    intro h
    have : syl q = 0 := by
      have h' : p + syl q - p = p - p := by rw [← h]
      simpa using h'
    exact syl_ne q this

lemma scan_length (p : Fin 3) (qs : List Bool) : (scan p qs).length = qs.length := by
  induction qs generalizing p with
  | nil => rfl
  | cons q qs ih => simp [scan, ih]

lemma key (p : Fin 3) (rs : List (Fin 3)) (h : (p :: rs).IsChain (· ≠ ·)) :
    ePow (p + 1) * bodyV (toBody p rs) = (rs.map axisTGate).prod * ePow (lastA p rs + 1) := by
  induction rs generalizing p with
  | nil => simp [bodyV, toBody, lastA]
  | cons r rs ih =>
    rw [List.isChain_cons_cons] at h
    simp only [toBody, bodyV, List.map_cons, List.prod_cons, lastA]
    rw [syl_toBody p r (Ne.symm h.1)]
    have e1 : ePow (p + 1) * (ePow (r - p) * QAlgorithms.gateT *
        (List.map (fun q => ePow (syl q) * QAlgorithms.gateT) (toBody r rs)).prod) =
        ePow (r + 1) * QAlgorithms.gateT * bodyV (toBody r rs) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ePow_add]
      unfold bodyV
      rw [(by decide : ∀ a b : Fin 3, a + 1 + (b - a) = b + 1) p r]
    rw [e1, ← axis_conj, Matrix.mul_assoc, ih r h.2, Matrix.mul_assoc]

def Nf (A : AxisForm) : NormalForm where
  leadingT := decide (A.axes.head? = some 2)
  body := if A.axes.head? = some 2 then toBody 2 A.axes.tail else toBody 2 A.axes
  terminal := cmul (-(lastA 2 A.axes + 1)) A.terminal

def Fm (M : NormalForm) : AxisForm where
  axes := (if M.leadingT then [2] else []) ++ scan 2 M.body
  adjacentDistinct := by
    split_ifs
    · exact scan_chain 2 M.body
    · exact (scan_chain 2 M.body).tail
  terminal := cmul (lastA 2 ((if M.leadingT then [2] else []) ++ scan 2 M.body) + 1) M.terminal

lemma cmul_cmul (a b : Fin 3) (C : Clifford) : cmul a (cmul b C) = cmul (a + b) C := by
  apply Subtype.ext
  simp only [cmul, ← Matrix.mul_assoc, ePow_add]

lemma cmul_zero (C : Clifford) : cmul 0 C = C := by
  apply Subtype.ext; simp [cmul, ePow_zero]

lemma scan_head (qs : List Bool) : (scan 2 qs).head? ≠ some 2 := by
  cases qs with
  | nil => simp [scan]
  | cons q qs => cases q <;> simp [scan, syl] <;> decide

lemma NF (M : NormalForm) : Nf (Fm M) = M := by
  obtain ⟨lead, body, C⟩ := M
  cases lead
  · simp only [Nf, Fm, Bool.false_eq_true, if_false, List.nil_append]
    have hh := scan_head body
    simp only [hh, decide_false, if_false, toBody_scan, cmul_cmul, neg_add_cancel, cmul_zero]
  · simp only [Nf, Fm, if_true, List.singleton_append, List.head?_cons, decide_true, List.tail_cons,
      toBody_scan, cmul_cmul, neg_add_cancel, cmul_zero]

lemma FN (A : AxisForm) : Fm (Nf A) = A := by
  obtain ⟨axes, hch, C⟩ := A
  have hax : (if decide (axes.head? = some 2) = true then [(2 : Fin 3)] else []) ++
      scan 2 (if axes.head? = some 2 then toBody 2 axes.tail else toBody 2 axes) = axes := by
    by_cases h : axes.head? = some 2
    · obtain ⟨r, rs, rfl⟩ : ∃ r rs, axes = r :: rs := by
        cases axes with
        | nil => simp at h
        | cons r rs => exact ⟨r, rs, rfl⟩
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      simp only [List.head?_cons, decide_true, if_true, List.tail_cons, List.singleton_append]
      rw [scan_toBody 2 rs hch]
    · simp only [h, decide_false, Bool.false_eq_true, if_false, List.nil_append]
      apply scan_toBody
      cases axes with
      | nil => simp
      | cons r rs =>
        rw [List.isChain_cons_cons]
        refine ⟨fun h2 => h (by simp [h2]), hch⟩
  simp only [Fm, Nf]
  congr 1
  · rw [hax, cmul_cmul, add_neg_cancel, cmul_zero]

lemma value_N (A : AxisForm) : normalValue cliffordE cliffordE2 (Nf A) = axisValue A := by
  obtain ⟨axes, hch, C⟩ := A
  rw [normalValue_eq, axisValue_eq]
  simp only [Nf, cmul]
  by_cases h : axes.head? = some 2
  · obtain ⟨rs, rfl⟩ : ∃ rs, axes = 2 :: rs := by
      cases axes with
      | nil => simp at h
      | cons r rs => simp at h; exact ⟨rs, by rw [h]⟩
    simp only [List.head?_cons, decide_true, if_true, List.tail_cons, List.map_cons, List.prod_cons]
    have hk := key 2 rs hch
    rw [show (2 : Fin 3) + 1 = 0 by decide, ePow_zero, Matrix.one_mul] at hk
    simp only [lastA]
    rw [hk, show axisTGate 2 = QAlgorithms.gateT by simp [axisTGate]]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (ePow _) (ePow _), ePow_add, add_neg_cancel, ePow_zero, Matrix.one_mul]
  · simp only [h, decide_false, Bool.false_eq_true, if_false, Matrix.one_mul]
    have hch2 : ((2 : Fin 3) :: axes).IsChain (· ≠ ·) := by
      cases axes with
      | nil => simp
      | cons r rs =>
        rw [List.isChain_cons_cons]
        exact ⟨fun h2 => h (by simp [h2]), hch⟩
    have hk := key 2 axes hch2
    rw [show (2 : Fin 3) + 1 = 0 by decide, ePow_zero, Matrix.one_mul] at hk
    rw [hk]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (ePow _) (ePow _), ePow_add, add_neg_cancel, ePow_zero, Matrix.one_mul]

lemma cliffordT_normal (M : NormalForm) : CliffordT (normalValue cliffordE cliffordE2 M) := by
  refine ⟨(if M.leadingT then [Input.t] else []) ++
    M.body.flatMap (fun q => [Input.clifford (if q then cliffordE2 else cliffordE), Input.t]) ++
    [Input.clifford M.terminal], ?_⟩
  unfold inputWordMatrix normalValue normalTokens
  simp only [List.map_append, List.prod_append]
  congr 1
  · congr 1
    · split_ifs <;> simp [tokenMatrix, inputMatrix]
    · induction M.body with
      | nil => simp
      | cons q qs ih =>
        simp only [List.flatMap_cons, List.map_append, List.prod_append, ih]
        cases q <;> simp [tokenMatrix, inputMatrix]

end S173N

open S173N in
theorem S173N_main :
    cliffordE.val * axisTGate 0 = axisTGate 1 * cliffordE.val ∧
    cliffordE.val * axisTGate 1 = axisTGate 2 * cliffordE.val ∧
    cliffordE.val * axisTGate 2 = axisTGate 0 * cliffordE.val ∧
    ∀ M : NormalForm, ∃! A : AxisForm,
      axisValue A = normalValue cliffordE cliffordE2 M ∧ A.axes.length = normalTCount M := by
  refine ⟨E_T 0, E_T 1, E_T 2, fun M => ⟨Fm M, ⟨?_, ?_⟩, ?_⟩⟩
  · rw [← value_N, NF]
  · simp only [Fm, normalTCount, List.length_append, scan_length]
    split_ifs <;> simp
  · rintro A ⟨hA, -⟩
    have h1 := (et_normal_form.1 _ (cliffordT_normal M)).unique (y₁ := Nf A) (y₂ := M)
      (by rw [value_N, hA]) rfl
    rw [← FN A, h1]

end QAlgorithms.Papers.Independent.Gap48.P10

end

open QAlgorithms.Papers.Independent.Gap48.P10 in
theorem solution :
    cliffordE.val * axisTGate 0 = axisTGate 1 * cliffordE.val ∧
    cliffordE.val * axisTGate 1 = axisTGate 2 * cliffordE.val ∧
    cliffordE.val * axisTGate 2 = axisTGate 0 * cliffordE.val ∧
    ∀ M : NormalForm, ∃! A : AxisForm,
      axisValue A = normalValue cliffordE cliffordE2 M ∧ A.axes.length = normalTCount M :=
  S173N_main

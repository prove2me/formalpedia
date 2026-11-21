-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P66.separatingF_separates
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-21T00:00:00.297566+00:00
-- url     : https://prove2.me/submissions/09eb21b8-9306-4c62-b009-bbe6654454d9

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66
noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators
open QAlgorithms (IsDensityMatrix vnEntropy)
attribute [local instance] Classical.propDecidable Classical.decEq
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def AuxSF_G (n : ℕ) (K : Finset (Fin 3)) (j : ℕ) : ℝ :=
  clwTheta n K + (j : ℝ) * clwLambda n K -
    (if 0 ∈ K ∧ 1 ∉ K ∧ 2 ∉ K ∧ j = 0 then 2*(n:ℝ)^2*((n:ℝ)+1)
     else if 0 ∈ K ∧ 1 ∈ K ∧ 2 ∉ K ∧ j = 0 then 2*(n:ℝ)*((n:ℝ)+1)^2 else 0)

section EvLemmas
variable {P : Type*} [Fintype P] [DecidableEq P]

theorem AuxSE_ev_add (L1 L2 : Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (L1 + L2) h = evaluateEntropyForm L1 h + evaluateEntropyForm L2 h := by
  simp [evaluateEntropyForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem AuxSE_ev_sub (L1 L2 : Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (L1 - L2) h = evaluateEntropyForm L1 h - evaluateEntropyForm L2 h := by
  simp [evaluateEntropyForm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem AuxSE_ev_neg (L : Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (-L) h = - evaluateEntropyForm L h := by
  simp [evaluateEntropyForm, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem AuxSE_ev_smul (c : ℝ) (L : Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (c • L) h = c * evaluateEntropyForm L h := by
  simp [evaluateEntropyForm, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem AuxSE_ev_zero (h : Finset P → ℝ) :
    evaluateEntropyForm (0 : Form P) h = 0 := by
  simp [evaluateEntropyForm]

theorem AuxSE_ev_atom (U : Finset P) (h : Finset P → ℝ) :
    evaluateEntropyForm (entropyAtom U) h = if U = ∅ then 0 else h U := by
  unfold evaluateEntropyForm entropyAtom
  split_ifs with hU
  · simp
  · simp [hU, Finset.sum_ite_eq]

theorem AuxSE_ev_atom' (U : Finset P) (h : Finset P → ℝ) (h0 : h ∅ = 0) :
    evaluateEntropyForm (entropyAtom U) h = h U := by
  rw [AuxSE_ev_atom]
  split_ifs with hU
  · simp [hU, h0]
  · rfl

theorem AuxSE_ev_sum {ι : Type*} [Fintype ι] (f : ι → Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (∑ i, f i) h = ∑ i, evaluateEntropyForm (f i) h := by
  unfold evaluateEntropyForm
  have hfun : ∀ U, (∑ i, f i) U = ∑ i, f i U := by
    intro U
    change ((Finset.univ : Finset ι).sum f) U = Finset.univ.sum (fun i => f i U)
    refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Pi.add_apply, ih]
  calc
    ∑ U, (∑ i, f i) U * h U
        = ∑ U, (∑ i, f i U) * h U := by
          congr 1; ext U; rw [hfun]
    _ = ∑ U, ∑ i, f i U * h U := by
          congr 1; ext U; exact Finset.sum_mul _ _ _
    _ = ∑ i, ∑ U, f i U * h U := Finset.sum_comm
    _ = ∑ i, evaluateEntropyForm (f i) h := by
          simp only [evaluateEntropyForm]

theorem AuxSE_ev_sum_smul {ι : Type*} [Fintype ι] (w : ι → ℝ) (L : ι → Form P)
    (h : Finset P → ℝ) :
    evaluateEntropyForm (∑ i, w i • L i) h =
      ∑ i, w i * evaluateEntropyForm (L i) h := by
  simp [AuxSE_ev_sum, AuxSE_ev_smul]

end EvLemmas

theorem AuxSF_spU {n : ℕ} (U V : Finset (entropyParty n)) :
    specialPart (U ∪ V) = specialPart U ∪ specialPart V := by
  ext j; simp [specialPart]

theorem AuxSF_spI {n : ℕ} (U V : Finset (entropyParty n)) :
    specialPart (U ∩ V) = specialPart U ∩ specialPart V := by
  ext j; simp [specialPart]

theorem AuxSF_xc {n : ℕ} (U V : Finset (entropyParty n)) :
    xCount (U ∪ V) + xCount (U ∩ V) = xCount U + xCount V := by
  unfold xCount
  have e1 : (Finset.univ.filter (fun i : Fin n => x i ∈ U ∪ V)) =
      Finset.univ.filter (fun i : Fin n => x i ∈ U) ∪ Finset.univ.filter (fun i : Fin n => x i ∈ V) := by
    ext i; simp
  have e2 : (Finset.univ.filter (fun i : Fin n => x i ∈ U ∩ V)) =
      Finset.univ.filter (fun i : Fin n => x i ∈ U) ∩ Finset.univ.filter (fun i : Fin n => x i ∈ V) := by
    ext i; simp
  rw [e1, e2, Finset.card_union_add_card_inter]

theorem AuxSF_xle {n : ℕ} (U V : Finset (entropyParty n)) (h : U ⊆ V) :
    xCount U ≤ xCount V := by
  unfold xCount
  exact Finset.card_le_card (fun i hi => by simp at hi ⊢; exact h hi)

theorem AuxSF_xn {n : ℕ} (U : Finset (entropyParty n)) : xCount U ≤ n := by
  unfold xCount
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem AuxSF_sep (n : ℕ) (M : Finset (entropyParty n)) :
    separatingF n M = AuxSF_G n (specialPart M) (xCount M) := by
  have hx : xCount M = 0 ↔ ∀ i : Fin n, Sum.inr i ∉ M := by
    unfold xCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp [x]
  have e1 : M = {entropyLabelA} ↔
      (0 ∈ specialPart M ∧ 1 ∉ specialPart M ∧ 2 ∉ specialPart M ∧ xCount M = 0) := by
    rw [hx]
    simp only [specialPart, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl; simp [entropyLabelA]
    · rintro ⟨h0, h1, h2, h3⟩
      ext y
      rcases y with j | i
      · fin_cases j <;> simp_all [entropyLabelA]
      · simp_all [entropyLabelA]
  have e2 : M = {entropyLabelA, b} ↔
      (0 ∈ specialPart M ∧ 1 ∈ specialPart M ∧ 2 ∉ specialPart M ∧ xCount M = 0) := by
    rw [hx]
    simp only [specialPart, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl; simp [entropyLabelA, b]
    · rintro ⟨h0, h1, h2, h3⟩
      ext y
      rcases y with j | i
      · fin_cases j <;> simp_all [entropyLabelA, b]
      · simp_all [entropyLabelA, b]
  unfold separatingF AuxSF_G clwMu
  by_cases c1 : M = {entropyLabelA}
  · rw [if_pos c1, if_pos (e1.mp c1)]
  · rw [if_neg c1, if_neg (fun h => c1 (e1.mpr h))]
    by_cases c2 : M = {entropyLabelA, b}
    · rw [if_pos c2, if_pos (e2.mp c2)]
    · rw [if_neg c2, if_neg (fun h => c2 (e2.mpr h))]





theorem AuxSE_f0 (n : ℕ) : separatingF n (∅ : Finset (entropyParty n)) = 0 := by
  have hAB : (∅ : Finset (entropyParty n)) ≠ {entropyLabelA, b} :=
    Ne.symm (Finset.insert_ne_empty _ _)
  simp [separatingF, clwTheta, clwLambda, specialPart, xCount, clwMu, hAB]

theorem AuxSE_ev_cmi {P : Type*} [Fintype P] [DecidableEq P]
    (U V W : Finset P) (h : Finset P → ℝ) (h0 : h ∅ = 0) :
    evaluateEntropyForm (cmiForm U V W) h =
      h (U ∪ W) + h (V ∪ W) - h W - h (U ∪ V ∪ W) := by
  unfold cmiForm
  rw [AuxSE_ev_sub, AuxSE_ev_sub, AuxSE_ev_add,
      AuxSE_ev_atom' _ _ h0, AuxSE_ev_atom' _ _ h0,
      AuxSE_ev_atom' _ _ h0, AuxSE_ev_atom' _ _ h0]

theorem AuxSE_ev_mi {P : Type*} [Fintype P] [DecidableEq P]
    (U V : Finset P) (h : Finset P → ℝ) (h0 : h ∅ = 0) :
    evaluateEntropyForm (miForm U V) h = h U + h V - h (U ∪ V) := by
  unfold miForm
  rw [AuxSE_ev_sub, AuxSE_ev_add,
      AuxSE_ev_atom' _ _ h0, AuxSE_ev_atom' _ _ h0, AuxSE_ev_atom' _ _ h0]

theorem AuxSE_sp_A {n : ℕ} : specialPart ({entropyLabelA} : Finset (entropyParty n)) = {0} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA]
theorem AuxSE_sp_B {n : ℕ} : specialPart ({b} : Finset (entropyParty n)) = {1} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA, b]
theorem AuxSE_sp_C {n : ℕ} : specialPart ({c} : Finset (entropyParty n)) = {2} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA, b, c]
theorem AuxSE_sp_AB {n : ℕ} : specialPart ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) = {0, 1} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA, b]
theorem AuxSE_sp_AC {n : ℕ} : specialPart ({entropyLabelA} ∪ {c} : Finset (entropyParty n)) = {0, 2} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA, b, c]
theorem AuxSE_sp_BC {n : ℕ} : specialPart ({b} ∪ {c} : Finset (entropyParty n)) = {1, 2} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA, b, c]
theorem AuxSE_sp_ABC {n : ℕ} :
    specialPart ({entropyLabelA} ∪ {b} ∪ {c} : Finset (entropyParty n)) = {0, 1, 2} := by
  ext j; fin_cases j <;> simp [specialPart, entropyLabelA, b, c]

theorem AuxSE_xc0_A {n : ℕ} : xCount ({entropyLabelA} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA]
theorem AuxSE_xc0_B {n : ℕ} : xCount ({b} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA, b]
theorem AuxSE_xc0_C {n : ℕ} : xCount ({c} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA, b, c]
theorem AuxSE_xc0_AB {n : ℕ} : xCount ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA, b]
theorem AuxSE_xc0_AC {n : ℕ} : xCount ({entropyLabelA} ∪ {c} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA, b, c]
theorem AuxSE_xc0_BC {n : ℕ} : xCount ({b} ∪ {c} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA, b, c]
theorem AuxSE_xc0_ABC {n : ℕ} :
    xCount ({entropyLabelA} ∪ {b} ∪ {c} : Finset (entropyParty n)) = 0 := by
  unfold xCount; simp [x, entropyLabelA, b, c]

theorem AuxSE_G_A0 (n : ℕ) :
    AuxSF_G n {0} 0 = 2 * (n:ℝ)^4 + 5 * (n:ℝ)^3 + 3 * (n:ℝ)^2 := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_B0 (n : ℕ) :
    AuxSF_G n {1} 0 = 4 * (n:ℝ)^3 + 6 * (n:ℝ)^2 + (n:ℝ) - 1 := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_C0 (n : ℕ) :
    AuxSF_G n {2} 0 = 3 * (n:ℝ)^3 + 4 * (n:ℝ)^2 + (n:ℝ) := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_AB0 (n : ℕ) :
    AuxSF_G n {0, 1} 0 = 2 * (n:ℝ)^4 + 8 * (n:ℝ)^3 + 8 * (n:ℝ)^2 + (n:ℝ) - 1 := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_AC0 (n : ℕ) :
    AuxSF_G n {0, 2} 0 = 2 * (n:ℝ)^4 + 7 * (n:ℝ)^3 + 7 * (n:ℝ)^2 + 2 * (n:ℝ) := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_BC0 (n : ℕ) :
    AuxSF_G n {1, 2} 0 = 6 * (n:ℝ)^3 + 10 * (n:ℝ)^2 + 3 * (n:ℝ) - 1 := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_ABC0 (n : ℕ) :
    AuxSF_G n {0, 1, 2} 0 = 2 * (n:ℝ)^4 + 10 * (n:ℝ)^3 + 12 * (n:ℝ)^2 + 3 * (n:ℝ) - 1 := by
  simp [AuxSF_G, clwTheta, clwLambda]; ring
theorem AuxSE_G_empty (n j : ℕ) :
    AuxSF_G n ∅ j = - (j : ℝ) * (n:ℝ)^2 := by
  simp [AuxSF_G, clwTheta, clwLambda]

theorem AuxSE_G_A_pos (n j : ℕ) (hj : 0 < j) :
    AuxSF_G n {0} j =
      ((n:ℝ) + 1) * (2*(n:ℝ)^3 + 5*(n:ℝ)^2) + (j:ℝ) * (-(2*(n:ℝ)^3 + 5*(n:ℝ)^2 + 2*(n:ℝ))) := by
  have : ¬ (j = 0) := Nat.pos_iff_ne_zero.mp hj
  simp [AuxSF_G, clwTheta, clwLambda, this]

theorem AuxSE_G_B_pos (n j : ℕ) (hj : 0 < j) :
    AuxSF_G n {1} j =
      ((n:ℝ) + 1) * (4*(n:ℝ)^2 + 2*(n:ℝ) - 1) + (j:ℝ) * (-(4*(n:ℝ)^2 + 2*(n:ℝ) - 1)) := by
  have : ¬ (j = 0) := Nat.pos_iff_ne_zero.mp hj
  simp [AuxSF_G, clwTheta, clwLambda, this]

theorem AuxSE_G_AB_pos (n j : ℕ) (hj : 0 < j) :
    AuxSF_G n {0, 1} j =
      ((n:ℝ) + 1) * (2*(n:ℝ)^3 + 8*(n:ℝ)^2 + 4*(n:ℝ) - 1) +
        (j:ℝ) * (-(2*(n:ℝ)^3 + 8*(n:ℝ)^2 + 4*(n:ℝ) - 1)) := by
  have : ¬ (j = 0) := Nat.pos_iff_ne_zero.mp hj
  simp [AuxSF_G, clwTheta, clwLambda, this]

theorem AuxSE_f_set {n : ℕ} (M : Finset (entropyParty n)) :
    separatingF n M = AuxSF_G n (specialPart M) (xCount M) := AuxSF_sep n M

theorem AuxSE_I_AC_B (n : ℕ) :
    evaluateEntropyForm (cmiForm {entropyLabelA} {c} {b}) (separatingF n) = 0 := by
  rw [AuxSE_ev_cmi _ _ _ _ (AuxSE_f0 n)]
  simp only [AuxSE_f_set]
  have e1 : specialPart ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) = {0, 1} := AuxSE_sp_AB
  have e2 : specialPart ({c} ∪ {b} : Finset (entropyParty n)) = {1, 2} := by
    rw [Finset.union_comm]; exact AuxSE_sp_BC
  have e3 : specialPart ({b} : Finset (entropyParty n)) = {1} := AuxSE_sp_B
  have e4 : specialPart ({entropyLabelA} ∪ {c} ∪ {b} : Finset (entropyParty n)) = {0, 1, 2} := by
    have : ({entropyLabelA} ∪ {c} ∪ {b} : Finset (entropyParty n)) =
        {entropyLabelA} ∪ {b} ∪ {c} := by ac_rfl
    rw [this]; exact AuxSE_sp_ABC
  have x1 : xCount ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) = 0 := AuxSE_xc0_AB
  have x2 : xCount ({c} ∪ {b} : Finset (entropyParty n)) = 0 := by
    rw [Finset.union_comm]; exact AuxSE_xc0_BC
  have x3 : xCount ({b} : Finset (entropyParty n)) = 0 := AuxSE_xc0_B
  have x4 : xCount ({entropyLabelA} ∪ {c} ∪ {b} : Finset (entropyParty n)) = 0 := by
    have : ({entropyLabelA} ∪ {c} ∪ {b} : Finset (entropyParty n)) =
        {entropyLabelA} ∪ {b} ∪ {c} := by ac_rfl
    rw [this]; exact AuxSE_xc0_ABC
  rw [e1, e2, e3, e4, x1, x2, x3, x4, AuxSE_G_AB0, AuxSE_G_BC0, AuxSE_G_B0, AuxSE_G_ABC0]
  ring

theorem AuxSE_I_BC_A (n : ℕ) :
    evaluateEntropyForm (cmiForm {b} {c} {entropyLabelA}) (separatingF n) = 0 := by
  rw [AuxSE_ev_cmi _ _ _ _ (AuxSE_f0 n)]
  simp only [AuxSE_f_set]
  have e1 : specialPart ({b} ∪ {entropyLabelA} : Finset (entropyParty n)) = {0, 1} := by
    rw [Finset.union_comm]; exact AuxSE_sp_AB
  have e2 : specialPart ({c} ∪ {entropyLabelA} : Finset (entropyParty n)) = {0, 2} := by
    rw [Finset.union_comm]; exact AuxSE_sp_AC
  have e3 : specialPart ({entropyLabelA} : Finset (entropyParty n)) = {0} := AuxSE_sp_A
  have e4 : specialPart ({b} ∪ {c} ∪ {entropyLabelA} : Finset (entropyParty n)) = {0, 1, 2} := by
    have : ({b} ∪ {c} ∪ {entropyLabelA} : Finset (entropyParty n)) =
        {entropyLabelA} ∪ {b} ∪ {c} := by ac_rfl
    rw [this]; exact AuxSE_sp_ABC
  have x1 : xCount ({b} ∪ {entropyLabelA} : Finset (entropyParty n)) = 0 := by
    rw [Finset.union_comm]; exact AuxSE_xc0_AB
  have x2 : xCount ({c} ∪ {entropyLabelA} : Finset (entropyParty n)) = 0 := by
    rw [Finset.union_comm]; exact AuxSE_xc0_AC
  have x3 : xCount ({entropyLabelA} : Finset (entropyParty n)) = 0 := AuxSE_xc0_A
  have x4 : xCount ({b} ∪ {c} ∪ {entropyLabelA} : Finset (entropyParty n)) = 0 := by
    have : ({b} ∪ {c} ∪ {entropyLabelA} : Finset (entropyParty n)) =
        {entropyLabelA} ∪ {b} ∪ {c} := by ac_rfl
    rw [this]; exact AuxSE_xc0_ABC
  rw [e1, e2, e3, e4, x1, x2, x3, x4, AuxSE_G_AB0, AuxSE_G_AC0, AuxSE_G_A0, AuxSE_G_ABC0]
  ring

theorem AuxSE_I_AB_C (n : ℕ) :
    evaluateEntropyForm (miForm ({entropyLabelA} ∪ {b}) {c}) (separatingF n) =
      (n:ℝ)^3 - (n:ℝ) := by
  rw [AuxSE_ev_mi _ _ _ (AuxSE_f0 n)]
  simp only [AuxSE_f_set]
  have e1 : specialPart ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) = {0, 1} := AuxSE_sp_AB
  have e2 : specialPart ({c} : Finset (entropyParty n)) = {2} := AuxSE_sp_C
  have e3 : specialPart ({entropyLabelA} ∪ {b} ∪ {c} : Finset (entropyParty n)) = {0, 1, 2} :=
    AuxSE_sp_ABC
  have x1 : xCount ({entropyLabelA} ∪ {b} : Finset (entropyParty n)) = 0 := AuxSE_xc0_AB
  have x2 : xCount ({c} : Finset (entropyParty n)) = 0 := AuxSE_xc0_C
  have x3 : xCount ({entropyLabelA} ∪ {b} ∪ {c} : Finset (entropyParty n)) = 0 := AuxSE_xc0_ABC
  rw [e1, e2, e3, x1, x2, x3, AuxSE_G_AB0, AuxSE_G_C0, AuxSE_G_ABC0]
  ring


def AuxSE_isX {n : ℕ} (W : Finset (entropyParty n)) : Prop :=
  W ⊆ Finset.univ.filter (fun j => ∃ t : Fin n, j = x t)

theorem AuxSE_eq_of_isX {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    W = (Finset.univ.filter (fun i : Fin n => x i ∈ W)).image x := by
  ext y
  constructor
  · intro hy
    have hy' : y ∈ Finset.univ.filter (fun j => ∃ t : Fin n, j = x t) := h hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy'
    obtain ⟨t, rfl⟩ := hy'
    exact Finset.mem_image.mpr ⟨t, ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ t, hy⟩, rfl⟩⟩
  · intro hy
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact ht

theorem AuxSE_sp_ofX {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    specialPart W = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  have hmem : Sum.inl j ∈ W := (Finset.mem_filter.mp hj).2
  have hx : Sum.inl j ∈ Finset.univ.filter (fun k => ∃ t : Fin n, k = x t) := h hmem
  obtain ⟨_, ⟨t, ht⟩⟩ := Finset.mem_filter.mp hx
  simp only [x] at ht
  exact Sum.inl_ne_inr ht

theorem AuxSE_xc_eq_card {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    xCount W = W.card := by
  let F := Finset.univ.filter (fun i : Fin n => x i ∈ W)
  have hW : W = F.image x := AuxSE_eq_of_isX h
  have hinj : Function.Injective (x : Fin n → entropyParty n) := by
    intro a b hab; simpa [x] using hab
  unfold xCount
  change F.card = W.card
  rw [hW, Finset.card_image_of_injective F hinj]

theorem AuxSE_empty_of_xc0 {n : ℕ} {W : Finset (entropyParty n)}
    (h : AuxSE_isX W) (hx : xCount W = 0) : W = ∅ := by
  rw [← Finset.card_eq_zero, ← AuxSE_xc_eq_card h, hx]

theorem AuxSE_sp_A_unionX {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    specialPart ({entropyLabelA} ∪ W) = {0} := by
  rw [AuxSF_spU, AuxSE_sp_A, AuxSE_sp_ofX h]; simp

theorem AuxSE_sp_B_unionX {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    specialPart ({b} ∪ W) = {1} := by
  rw [AuxSF_spU, AuxSE_sp_B, AuxSE_sp_ofX h]; simp

theorem AuxSE_sp_AB_unionX {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    specialPart (({entropyLabelA} ∪ {b}) ∪ W) = {0, 1} := by
  rw [AuxSF_spU, AuxSE_sp_AB, AuxSE_sp_ofX h]; simp

theorem AuxSE_xc_A_unionX {n : ℕ} {W : Finset (entropyParty n)} :
    xCount ({entropyLabelA} ∪ W) = xCount W := by
  unfold xCount
  refine congr_arg Finset.card ?_
  apply Finset.ext
  intro i
  constructor
  · intro hi
    obtain ⟨_, hmem⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    cases Finset.mem_union.mp hmem with
    | inl hA =>
      have heq : x i = entropyLabelA := Finset.mem_singleton.mp hA
      simp only [x, entropyLabelA] at heq
      exact (Sum.inr_ne_inl heq).elim
    | inr hW => exact hW
  · intro hi
    obtain ⟨_, hW⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Finset.mem_union.mpr (Or.inr hW)⟩

theorem AuxSE_xc_B_unionX {n : ℕ} {W : Finset (entropyParty n)} :
    xCount ({b} ∪ W) = xCount W := by
  unfold xCount
  refine congr_arg Finset.card ?_
  apply Finset.ext
  intro i
  constructor
  · intro hi
    obtain ⟨_, hmem⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    cases Finset.mem_union.mp hmem with
    | inl hB =>
      have heq : x i = b := Finset.mem_singleton.mp hB
      simp only [x, b] at heq
      exact (Sum.inr_ne_inl heq).elim
    | inr hW => exact hW
  · intro hi
    obtain ⟨_, hW⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Finset.mem_union.mpr (Or.inr hW)⟩

theorem AuxSE_xc_AB_unionX {n : ℕ} {W : Finset (entropyParty n)} :
    xCount (({entropyLabelA} ∪ {b}) ∪ W) = xCount W := by
  unfold xCount
  refine congr_arg Finset.card ?_
  apply Finset.ext
  intro i
  constructor
  · intro hi
    obtain ⟨_, hmem⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    cases Finset.mem_union.mp hmem with
    | inl hAB =>
      cases Finset.mem_union.mp hAB with
      | inl hA =>
        have heq : x i = entropyLabelA := Finset.mem_singleton.mp hA
        simp only [x, entropyLabelA] at heq
        exact (Sum.inr_ne_inl heq).elim
      | inr hB =>
        have heq : x i = b := Finset.mem_singleton.mp hB
        simp only [x, b] at heq
        exact (Sum.inr_ne_inl heq).elim
    | inr hW => exact hW
  · intro hi
    obtain ⟨_, hW⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Finset.mem_union.mpr (Or.inr hW)⟩

theorem AuxSE_I_AB_W_empty (n : ℕ) :
    evaluateEntropyForm (cmiForm {entropyLabelA} {b} (∅ : Finset (entropyParty n))) (separatingF n) =
      (n:ℝ)^3 + (n:ℝ)^2 := by
  rw [AuxSE_ev_cmi _ _ _ _ (AuxSE_f0 n)]
  simp only [AuxSE_f_set, Finset.union_empty]
  have e3 : specialPart (∅ : Finset (entropyParty n)) = ∅ := by simp [specialPart]
  have z : xCount (∅ : Finset (entropyParty n)) = 0 := by simp [xCount]
  rw [AuxSE_sp_A, AuxSE_sp_B, e3, AuxSE_sp_AB, AuxSE_xc0_A, AuxSE_xc0_B, z, AuxSE_xc0_AB,
      AuxSE_G_A0, AuxSE_G_B0, AuxSE_G_empty, AuxSE_G_AB0]
  ring

theorem AuxSE_I_AB_W_pos (n : ℕ) {W : Finset (entropyParty n)}
    (hX : AuxSE_isX W) (hj : 0 < xCount W) :
    evaluateEntropyForm (cmiForm {entropyLabelA} {b} W) (separatingF n) =
      (n:ℝ)^3 - (n:ℝ)^2 - 2 * (n:ℝ) := by
  rw [AuxSE_ev_cmi _ _ _ _ (AuxSE_f0 n)]
  simp only [AuxSE_f_set]
  have : ({entropyLabelA} ∪ {b} ∪ W : Finset (entropyParty n)) =
      ({entropyLabelA} ∪ {b}) ∪ W := by
    simp [Finset.union_assoc]
  rw [this, AuxSE_sp_A_unionX hX, AuxSE_sp_B_unionX hX, AuxSE_sp_ofX hX, AuxSE_sp_AB_unionX hX,
      AuxSE_xc_A_unionX, AuxSE_xc_B_unionX, AuxSE_xc_AB_unionX,
      AuxSE_G_A_pos n _ hj, AuxSE_G_B_pos n _ hj, AuxSE_G_empty, AuxSE_G_AB_pos n _ hj]
  ring

theorem AuxSE_I_AB_W (n : ℕ) {W : Finset (entropyParty n)} (hX : AuxSE_isX W) :
    evaluateEntropyForm (cmiForm {entropyLabelA} {b} W) (separatingF n) =
      if xCount W = 0 then (n:ℝ)^3 + (n:ℝ)^2 else (n:ℝ)^3 - (n:ℝ)^2 - 2 * (n:ℝ) := by
  by_cases hj : xCount W = 0
  · have hW : W = ∅ := AuxSE_empty_of_xc0 hX hj
    subst hW
    rw [if_pos hj, AuxSE_I_AB_W_empty]
  · have : 0 < xCount W := Nat.pos_of_ne_zero hj
    rw [if_neg hj, AuxSE_I_AB_W_pos n hX this]


def AuxSE_k {n p : ℕ} (alpha : Fin p → Finset (entropyParty n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅)).card

theorem AuxSE_isX_biUnion {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (h : ∀ i, AuxSE_isX (alpha i)) : AuxSE_isX (Finset.univ.biUnion alpha) := by
  intro y hy
  obtain ⟨i, _, hyi⟩ := Finset.mem_biUnion.mp hy
  exact h i hyi

theorem AuxSE_X_card (n : ℕ) :
    (Finset.univ.filter (fun j : entropyParty n => ∃ t : Fin n, j = x t)).card = n := by
  have h : Finset.univ.filter (fun j : entropyParty n => ∃ t : Fin n, j = x t) =
      (Finset.univ : Finset (Fin n)).image x := by
    ext y
    constructor
    · intro hy
      obtain ⟨_, ⟨t, rfl⟩⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩
    · intro hy
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨t, rfl⟩⟩
  rw [h, Finset.card_image_of_injective]
  · simp [Finset.card_univ]
  · intro a b hab; simpa [x] using hab

theorem AuxSE_pairwise {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    (↑(Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint alpha := by
  intro i _ j _ hij
  exact hdisj i j hij

theorem AuxSE_card_biUnion {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    (Finset.univ.biUnion alpha).card = ∑ i, (alpha i).card :=
  Finset.card_biUnion (AuxSE_pairwise hdisj)

theorem AuxSE_xc_biUnion_disjoint {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hX : ∀ i, AuxSE_isX (alpha i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    xCount (Finset.univ.biUnion alpha) = ∑ i, xCount (alpha i) := by
  rw [AuxSE_xc_eq_card (AuxSE_isX_biUnion hX), AuxSE_card_biUnion hdisj]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact (AuxSE_xc_eq_card (hX i)).symm

theorem AuxSE_k_le_p {n p : ℕ} (alpha : Fin p → Finset (entropyParty n)) :
    AuxSE_k alpha ≤ p := by
  simpa [AuxSE_k, Finset.card_univ] using
    (Finset.card_le_card (Finset.filter_subset (fun i : Fin p => alpha i ≠ ∅) Finset.univ))

theorem AuxSE_k_le_n {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hX : ∀ i, AuxSE_isX (alpha i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    AuxSE_k alpha ≤ n := by
  have hsum : ∑ i, (alpha i).card = (Finset.univ.biUnion alpha).card :=
    (AuxSE_card_biUnion hdisj).symm
  have hk : AuxSE_k alpha ≤ ∑ i, (alpha i).card := by
    have hrestr :
        ∑ i ∈ Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅), (alpha i).card =
          ∑ i, (alpha i).card := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      have : alpha i = ∅ := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
        exact hi
      simp [this]
    rw [← hrestr, AuxSE_k]
    have h1 : ∀ i ∈ Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅),
        1 ≤ (alpha i).card := by
      intro i hi
      have : alpha i ≠ ∅ := (Finset.mem_filter.mp hi).2
      exact Nat.one_le_iff_ne_zero.mpr (mt Finset.card_eq_zero.mp this)
    have : ∑ i ∈ Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅), (1 : ℕ) =
        (Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅)).card := by
      simp [Finset.sum_const]
    calc
      (Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅)).card
          = ∑ i ∈ Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅), (1 : ℕ) := this.symm
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅), (alpha i).card :=
        Finset.sum_le_sum h1
  have hunion : (Finset.univ.biUnion alpha).card ≤ n := by
    have hle : (Finset.univ.biUnion alpha).card ≤
        (Finset.univ.filter (fun j : entropyParty n => ∃ t : Fin n, j = x t)).card :=
      Finset.card_le_card (AuxSE_isX_biUnion hX)
    rwa [AuxSE_X_card] at hle
  exact hk.trans (hsum.trans_le hunion)

theorem AuxSE_S_ofX {n : ℕ} {W : Finset (entropyParty n)} (h : AuxSE_isX W) :
    separatingF n W = - (xCount W : ℝ) * (n : ℝ)^2 := by
  rw [AuxSE_f_set, AuxSE_sp_ofX h, AuxSE_G_empty]

theorem AuxSE_ev_family {n p : ℕ} (alpha : Fin p → Finset (entropyParty n)) :
    evaluateEntropyForm (familyForm {entropyLabelA} {b} {c} alpha) (separatingF n) =
      (∑ i, evaluateEntropyForm (cmiForm {entropyLabelA} {b} (alpha i)) (separatingF n)) +
      (∑ i, separatingF n (alpha i)) -
      separatingF n (Finset.univ.biUnion alpha) -
      ((p : ℝ) - 1) *
        evaluateEntropyForm (miForm ({entropyLabelA} ∪ {b}) {c}) (separatingF n) := by
  unfold familyForm
  rw [AuxSE_ev_sub, AuxSE_ev_sub, AuxSE_ev_add, AuxSE_ev_sum, AuxSE_ev_sum, AuxSE_ev_smul]
  simp only [AuxSE_ev_atom' _ _ (AuxSE_f0 n)]

theorem AuxSE_sum_I (n : ℕ) {p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hX : ∀ i, AuxSE_isX (alpha i)) :
    ∑ i, evaluateEntropyForm (cmiForm {entropyLabelA} {b} (alpha i)) (separatingF n) =
      ((p - AuxSE_k alpha : ℕ) : ℝ) * ((n : ℝ)^3 + (n : ℝ)^2) +
        (AuxSE_k alpha : ℝ) * ((n : ℝ)^3 - (n : ℝ)^2 - 2 * (n : ℝ)) := by
  have hterm : ∀ i,
      evaluateEntropyForm (cmiForm {entropyLabelA} {b} (alpha i)) (separatingF n) =
        if alpha i = ∅ then (n : ℝ)^3 + (n : ℝ)^2
        else (n : ℝ)^3 - (n : ℝ)^2 - 2 * (n : ℝ) := by
    intro i
    have hiff : xCount (alpha i) = 0 ↔ alpha i = ∅ := by
      constructor
      · exact AuxSE_empty_of_xc0 (hX i)
      · intro h; simp [h, xCount]
    rw [AuxSE_I_AB_W n (hX i)]
    by_cases h0 : xCount (alpha i) = 0
    · rw [if_pos h0, if_pos (hiff.mp h0)]
    · rw [if_neg h0, if_neg (mt hiff.mpr h0)]
  simp_rw [hterm]
  rw [Finset.sum_ite]
  have hempty :
      (Finset.univ.filter (fun i : Fin p => alpha i = ∅)).card = p - AuxSE_k alpha := by
    have hD : Disjoint
        (Finset.univ.filter (fun i : Fin p => alpha i = ∅))
        (Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅)) := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      exact (Finset.mem_filter.mp hiB).2 (Finset.mem_filter.mp hiA).2
    have hU :
        Finset.univ.filter (fun i : Fin p => alpha i = ∅) ∪
          Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅) = Finset.univ := by
      ext i
      by_cases h : alpha i = ∅ <;> simp [h]
    have hcard := Finset.card_union_of_disjoint hD
    rw [hU, Finset.card_univ, Fintype.card_fin] at hcard
    have hk : (Finset.univ.filter (fun i : Fin p => alpha i ≠ ∅)).card = AuxSE_k alpha := rfl
    omega
  have hne :
      (Finset.univ.filter (fun i : Fin p => ¬ alpha i = ∅)).card = AuxSE_k alpha := rfl
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hempty, hne]
  try ring

theorem AuxSE_S_cancel {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hX : ∀ i, AuxSE_isX (alpha i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    (∑ i, separatingF n (alpha i)) - separatingF n (Finset.univ.biUnion alpha) = 0 := by
  have h1 : ∀ i, separatingF n (alpha i) = - (xCount (alpha i) : ℝ) * (n : ℝ)^2 :=
    fun i => AuxSE_S_ofX (hX i)
  have h2 : separatingF n (Finset.univ.biUnion alpha) =
      - (xCount (Finset.univ.biUnion alpha) : ℝ) * (n : ℝ)^2 :=
    AuxSE_S_ofX (AuxSE_isX_biUnion hX)
  simp_rw [h1, h2, AuxSE_xc_biUnion_disjoint hX hdisj]
  have hsum :
      ∑ x, (-(xCount (alpha x) : ℝ) * (n : ℝ)^2) =
        - (∑ x, (xCount (alpha x) : ℝ)) * (n : ℝ)^2 := by
    simp [mul_comm ((n : ℝ)^2), Finset.sum_mul, Finset.sum_neg_distrib]
  rw [hsum, Nat.cast_sum]
  ring

theorem AuxSE_family_eval {n p : ℕ} {alpha : Fin p → Finset (entropyParty n)}
    (hX : ∀ i, AuxSE_isX (alpha i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    evaluateEntropyForm (familyForm {entropyLabelA} {b} {c} alpha) (separatingF n) =
      (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + p - 1 - 2 * (AuxSE_k alpha : ℝ)) := by
  rw [AuxSE_ev_family, AuxSE_sum_I n hX, AuxSE_I_AB_C n]
  have hS := AuxSE_S_cancel hX hdisj
  have hpk : ((p - AuxSE_k alpha : ℕ) : ℝ) = (p : ℝ) - (AuxSE_k alpha : ℝ) :=
    Nat.cast_sub (AuxSE_k_le_p alpha)
  rw [hpk]
  linarith

theorem AuxSE_family_nonneg (n p : ℕ) (hn : 2 ≤ n) (hp : 2 ≤ p) (hne : p ≠ n)
    {alpha : Fin p → Finset (entropyParty n)}
    (hX : ∀ i, AuxSE_isX (alpha i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) :
    0 ≤ evaluateEntropyForm (familyForm {entropyLabelA} {b} {c} alpha) (separatingF n) := by
  rw [AuxSE_family_eval hX hdisj]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hk : (0 : ℝ) ≤ (n : ℝ) + p - 1 - 2 * (AuxSE_k alpha : ℝ) := by
    have hk_p := AuxSE_k_le_p (n := n) alpha
    have hk_n := AuxSE_k_le_n hX hdisj
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (p : ℝ) + 1 ≤ n := by
        rw [← Nat.cast_succ]
        exact Nat.cast_le.mpr (Nat.succ_le_of_lt hlt)
      have hk_pR : (AuxSE_k alpha : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hk_p
      have : 2 * (AuxSE_k alpha : ℝ) ≤ 2 * (p : ℝ) := by nlinarith [hk_pR]
      nlinarith
    · have : (n : ℝ) + 1 ≤ p := by
        rw [← Nat.cast_succ]
        exact Nat.cast_le.mpr (Nat.succ_le_of_lt hgt)
      have hk_nR : (AuxSE_k alpha : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hk_n
      have : 2 * (AuxSE_k alpha : ℝ) ≤ 2 * (n : ℝ) := by nlinarith [hk_nR]
      nlinarith
  exact mul_nonneg (mul_nonneg hn0 hn1) hk

theorem AuxSE_isX_standard {n : ℕ} (i : Fin n) : AuxSE_isX (standardX i) := by
  intro y hy
  have : y = x i := Finset.mem_singleton.mp hy
  subst this
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, rfl⟩⟩

theorem AuxSE_disj_standard {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Disjoint (standardX i) (standardX j) := by
  simp only [standardX, Finset.disjoint_singleton]
  intro h
  have : i = j := by simpa [x] using h
  exact hij this

theorem AuxSE_k_standard (n : ℕ) : AuxSE_k (standardX : Fin n → Finset (entropyParty n)) = n := by
  have h : Finset.univ.filter (fun i : Fin n => standardX i ≠ ∅) = Finset.univ := by
    ext i
    simp [standardX]
  simp [AuxSE_k, h, Finset.card_univ]

theorem AuxSE_standard_eval (n : ℕ) :
    evaluateEntropyForm (standardFamily n) (separatingF n) =
      - (n : ℝ) * ((n : ℝ) + 1) := by
  unfold standardFamily
  have hX : ∀ i : Fin n, AuxSE_isX (standardX i) := AuxSE_isX_standard
  have hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (standardX i) (standardX j) :=
    fun i j hij => AuxSE_disj_standard hij
  rw [AuxSE_family_eval hX hdisj, AuxSE_k_standard]
  ring

theorem separatingF_separates (n : ℕ) (hn : 2 ≤ n) :
    evaluateEntropyForm (cmiForm {entropyLabelA} {c} {b}) (separatingF n) = 0 ∧
    evaluateEntropyForm (cmiForm {b} {c} {entropyLabelA}) (separatingF n) = 0 ∧
    (∀ (p : ℕ), 2 ≤ p → p ≠ n → ∀ alpha : Fin p → Finset (entropyParty n),
      (∀ i, alpha i ⊆ Finset.univ.filter (fun j => ∃ t : Fin n, j = x t)) →
      (∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) →
      0 ≤ evaluateEntropyForm (familyForm {entropyLabelA} {b} {c} alpha) (separatingF n)) ∧
    evaluateEntropyForm (standardFamily n) (separatingF n) < 0 := by
  refine ⟨AuxSE_I_AC_B n, AuxSE_I_BC_A n, ?_, ?_⟩
  · intro p hp hpne alpha hXα hdisj
    exact AuxSE_family_nonneg n p hn hp hpne (fun i => hXα i) hdisj
  · rw [AuxSE_standard_eval]
    have hn0 : (0 : ℝ) < n :=
      Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn)
    nlinarith

theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) :
    evaluateEntropyForm (cmiForm {entropyLabelA} {c} {b}) (separatingF n) = 0 ∧
    evaluateEntropyForm (cmiForm {b} {c} {entropyLabelA}) (separatingF n) = 0 ∧
    (∀ (p : ℕ), 2 ≤ p → p ≠ n → ∀ alpha : Fin p → Finset (entropyParty n),
      (∀ i, alpha i ⊆ Finset.univ.filter (fun j => ∃ t : Fin n, j = x t)) →
      (∀ i j, i ≠ j → Disjoint (alpha i) (alpha j)) →
      0 ≤ evaluateEntropyForm (familyForm {entropyLabelA} {b} {c} alpha) (separatingF n)) ∧
    evaluateEntropyForm (standardFamily n) (separatingF n) < 0 :=
  separatingF_separates n hn

end QAlgorithms.Papers.Independent.Intake100.P66

end

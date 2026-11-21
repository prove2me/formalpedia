-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P66.lindenWinter_independent
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-20T23:40:32.643125+00:00
-- url     : https://prove2.me/submissions/9614e972-7b26-46ce-a450-92ecc44203b2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66
noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators
open QAlgorithms (IsDensityMatrix vnEntropy)
attribute [local instance] Classical.propDecidable Classical.decEq
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def AuxLW_owZ (M : Finset (entropyParty 1)) : ℤ :=
  if entropyLabelA ∈ M then
    if b ∈ M then
      if c ∈ M then (if x 0 ∈ M then (4 : ℤ) else 6) else 6
    else 5
  else if b ∈ M then 5
  else if c ∈ M then (if x 0 ∈ M then 6 else 2)
  else if x 0 ∈ M then 4 else 0

def AuxLW_owBits (aA aB aC aD : Bool) : ℤ :=
  if aA then
    if aB then
      if aC then (if aD then (4 : ℤ) else 6) else 6
    else 5
  else if aB then 5
  else if aC then (if aD then 6 else 2)
  else if aD then 4 else 0

theorem AuxLW_ow_empty : oldWitness (∅ : Finset (entropyParty 1)) = 0 := by
  simp [oldWitness]

theorem AuxLW_ow_eq (M : Finset (entropyParty 1)) :
    oldWitness M = (AuxLW_owZ M : ℝ) := by
  unfold oldWitness AuxLW_owZ
  split_ifs <;> simp

theorem AuxLW_owZ_bits (M : Finset (entropyParty 1)) :
    AuxLW_owZ M =
      AuxLW_owBits (decide (entropyLabelA ∈ M)) (decide (b ∈ M))
        (decide (c ∈ M)) (decide (x 0 ∈ M)) := by
  by_cases hA : entropyLabelA ∈ M
    <;> by_cases hB : b ∈ M
    <;> by_cases hC : c ∈ M
    <;> by_cases hD : x 0 ∈ M
    <;> simp [AuxLW_owZ, AuxLW_owBits, hA, hB, hC, hD]

theorem AuxLW_bits_of (M : Finset (entropyParty 1)) :
    oldWitness M =
      (AuxLW_owBits (decide (entropyLabelA ∈ M)) (decide (b ∈ M))
        (decide (c ∈ M)) (decide (x 0 ∈ M)) : ℝ) := by
  rw [AuxLW_ow_eq, AuxLW_owZ_bits]

theorem AuxLW_owBits_submod :
    ∀ aA aB aC aD bA bB bC bD : Bool,
      AuxLW_owBits (aA || bA) (aB || bB) (aC || bC) (aD || bD) +
        AuxLW_owBits (aA && bA) (aB && bB) (aC && bC) (aD && bD) ≤
      AuxLW_owBits aA aB aC aD + AuxLW_owBits bA bB bC bD := by
  decide

theorem AuxLW_owZ_submod (U V : Finset (entropyParty 1)) :
    AuxLW_owZ (U ∪ V) + AuxLW_owZ (U ∩ V) ≤ AuxLW_owZ U + AuxLW_owZ V := by
  have h := AuxLW_owBits_submod
    (decide (entropyLabelA ∈ U)) (decide (b ∈ U)) (decide (c ∈ U)) (decide (x 0 ∈ U))
    (decide (entropyLabelA ∈ V)) (decide (b ∈ V)) (decide (c ∈ V)) (decide (x 0 ∈ V))
  have hOr (p : entropyParty 1) :
      decide (p ∈ U ∪ V) = (decide (p ∈ U) || decide (p ∈ V)) := by
    simp only [Finset.mem_union]
    by_cases hU : p ∈ U <;> by_cases hV : p ∈ V <;> simp [hU, hV]
  have hAnd (p : entropyParty 1) :
      decide (p ∈ U ∩ V) = (decide (p ∈ U) && decide (p ∈ V)) := by
    simp only [Finset.mem_inter]
    by_cases hU : p ∈ U <;> by_cases hV : p ∈ V <;> simp [hU, hV]
  rw [AuxLW_owZ_bits U, AuxLW_owZ_bits V, AuxLW_owZ_bits (U ∪ V), AuxLW_owZ_bits (U ∩ V),
    hOr, hOr, hOr, hOr, hAnd, hAnd, hAnd, hAnd]
  exact h

theorem AuxLW_submod : IsSubmodular (oldWitness : Finset (entropyParty 1) → ℝ) := by
  intro U V
  have h := AuxLW_owZ_submod U V
  simp only [AuxLW_ow_eq]
  exact_mod_cast h

variable {P : Type*} [Fintype P] [DecidableEq P]

theorem AuxLW_ev_add (L1 L2 : Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (L1 + L2) h = evaluateEntropyForm L1 h + evaluateEntropyForm L2 h := by
  simp [evaluateEntropyForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem AuxLW_ev_sub (L1 L2 : Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (L1 - L2) h = evaluateEntropyForm L1 h - evaluateEntropyForm L2 h := by
  simp [evaluateEntropyForm, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem AuxLW_ev_neg (L : Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (-L) h = - evaluateEntropyForm L h := by
  simp [evaluateEntropyForm, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem AuxLW_ev_smul (c : ℝ) (L : Form P) (h : Finset P → ℝ) :
    evaluateEntropyForm (c • L) h = c * evaluateEntropyForm L h := by
  simp [evaluateEntropyForm, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem AuxLW_ev_zero (h : Finset P → ℝ) :
    evaluateEntropyForm (0 : Form P) h = 0 := by
  simp [evaluateEntropyForm]

theorem AuxLW_ev_atom (U : Finset P) (h : Finset P → ℝ) :
    evaluateEntropyForm (entropyAtom U) h = if U = ∅ then 0 else h U := by
  unfold evaluateEntropyForm entropyAtom
  split_ifs with hU
  · simp
  · simp [hU, Finset.sum_ite_eq]

theorem AuxLW_ev_atom' (U : Finset P) (h : Finset P → ℝ) (h0 : h ∅ = 0) :
    evaluateEntropyForm (entropyAtom U) h = h U := by
  rw [AuxLW_ev_atom]
  split_ifs with hU
  · simp [hU, h0]
  · rfl

theorem AuxLW_ev_sum {ι : Type*} [Fintype ι] (f : ι → Form P) (h : Finset P → ℝ) :
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

theorem AuxLW_ev_sum_smul {ι : Type*} [Fintype ι] (w : ι → ℝ) (L : ι → Form P)
    (h : Finset P → ℝ) :
    evaluateEntropyForm (∑ i, w i • L i) h =
      ∑ i, w i * evaluateEntropyForm (L i) h := by
  simp [AuxLW_ev_sum, AuxLW_ev_smul]

theorem AuxLW_ev_cmi (U V W : Finset (entropyParty 1)) :
    evaluateEntropyForm (cmiForm U V W) oldWitness =
      oldWitness (U ∪ W) + oldWitness (V ∪ W) - oldWitness W - oldWitness (U ∪ V ∪ W) := by
  unfold cmiForm
  rw [AuxLW_ev_sub, AuxLW_ev_sub, AuxLW_ev_add,
      AuxLW_ev_atom' _ _ AuxLW_ow_empty, AuxLW_ev_atom' _ _ AuxLW_ow_empty,
      AuxLW_ev_atom' _ _ AuxLW_ow_empty, AuxLW_ev_atom' _ _ AuxLW_ow_empty]

theorem AuxLW_ev_wmo (U V W : Finset (entropyParty 1)) :
    evaluateEntropyForm (wmoForm U V W) oldWitness =
      oldWitness (U ∪ V) + oldWitness (U ∪ W) - oldWitness V - oldWitness W := by
  unfold wmoForm
  rw [AuxLW_ev_sub, AuxLW_ev_sub, AuxLW_ev_add,
      AuxLW_ev_atom' _ _ AuxLW_ow_empty, AuxLW_ev_atom' _ _ AuxLW_ow_empty,
      AuxLW_ev_atom' _ _ AuxLW_ow_empty, AuxLW_ev_atom' _ _ AuxLW_ow_empty]

theorem AuxLW_ev_mi (U V : Finset (entropyParty 1)) :
    evaluateEntropyForm (miForm U V) oldWitness =
      oldWitness U + oldWitness V - oldWitness (U ∪ V) := by
  unfold miForm
  rw [AuxLW_ev_sub, AuxLW_ev_add,
      AuxLW_ev_atom' _ _ AuxLW_ow_empty, AuxLW_ev_atom' _ _ AuxLW_ow_empty,
      AuxLW_ev_atom' _ _ AuxLW_ow_empty]

theorem AuxLW_union_inter_cmi (U V W : Finset (entropyParty 1)) (hUV : Disjoint U V) :
    (U ∪ W) ∪ (V ∪ W) = U ∪ V ∪ W ∧ (U ∪ W) ∩ (V ∪ W) = W := by
  constructor
  · ext; simp [or_or_distrib_right, or_left_comm, or_comm]
  · ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hUW, hVW⟩
      rcases hUW with hU | hW
      · rcases hVW with hV | hW
        · exact (Finset.disjoint_left.mp hUV hU hV).elim
        · exact hW
      · exact hW
    · intro hx; exact ⟨Or.inr hx, Or.inr hx⟩

theorem AuxLW_cmi_nonneg (U V W : Finset (entropyParty 1)) (hUV : Disjoint U V) :
    0 ≤ evaluateEntropyForm (cmiForm U V W) oldWitness := by
  rw [AuxLW_ev_cmi]
  obtain ⟨hu, hi⟩ := AuxLW_union_inter_cmi U V W hUV
  have sm := AuxLW_submod (U ∪ W) (V ∪ W)
  rw [hu, hi] at sm
  linarith

def AuxLW_mem (d : Fin 4) (s1 s2 : Fin 4) : Bool := d = s1 || d = s2
def AuxLW_mem1 (d s : Fin 4) : Bool := d = s

theorem AuxLW_wmo_bits :
    ∀ dA dB dC dD : Fin 4,
      AuxLW_owBits (AuxLW_mem dA 0 1) (AuxLW_mem dB 0 1) (AuxLW_mem dC 0 1) (AuxLW_mem dD 0 1) +
        AuxLW_owBits (AuxLW_mem dA 0 2) (AuxLW_mem dB 0 2) (AuxLW_mem dC 0 2) (AuxLW_mem dD 0 2) ≥
      AuxLW_owBits (AuxLW_mem1 dA 1) (AuxLW_mem1 dB 1) (AuxLW_mem1 dC 1) (AuxLW_mem1 dD 1) +
        AuxLW_owBits (AuxLW_mem1 dA 2) (AuxLW_mem1 dB 2) (AuxLW_mem1 dC 2) (AuxLW_mem1 dD 2) := by
  decide

def AuxLW_dest (U V W : Finset (entropyParty 1)) (p : entropyParty 1) : Fin 4 :=
  if p ∈ U then 0 else if p ∈ V then 1 else if p ∈ W then 2 else 3

theorem AuxLW_dest_U {U V W : Finset (entropyParty 1)} {p : entropyParty 1}
    (hUV : Disjoint U V) (hUW : Disjoint U W) :
    p ∈ U ↔ AuxLW_dest U V W p = 0 := by
  unfold AuxLW_dest
  by_cases hU : p ∈ U
  · simp [hU]
  · by_cases hV : p ∈ V
    · simp [hU, hV]
    · by_cases hW : p ∈ W
      · simp [hU, hV, hW]
      · simp [hU, hV, hW]

theorem AuxLW_dest_V {U V W : Finset (entropyParty 1)} {p : entropyParty 1}
    (hUV : Disjoint U V) (hVW : Disjoint V W) :
    p ∈ V ↔ AuxLW_dest U V W p = 1 := by
  unfold AuxLW_dest
  by_cases hU : p ∈ U
  · have hV : p ∉ V := fun hV => Finset.disjoint_left.mp hUV hU hV
    simp [hU, hV]
  · by_cases hV : p ∈ V
    · simp [hU, hV]
    · by_cases hW : p ∈ W
      · simp [hU, hV, hW]
      · simp [hU, hV, hW]

theorem AuxLW_dest_W {U V W : Finset (entropyParty 1)} {p : entropyParty 1}
    (hUW : Disjoint U W) (hVW : Disjoint V W) :
    p ∈ W ↔ AuxLW_dest U V W p = 2 := by
  unfold AuxLW_dest
  by_cases hU : p ∈ U
  · have hW : p ∉ W := fun hW => Finset.disjoint_left.mp hUW hU hW
    by_cases hV : p ∈ V
    · simp [hU, hV, hW]
    · simp [hU, hV, hW]
  · by_cases hV : p ∈ V
    · have hW : p ∉ W := fun hW => Finset.disjoint_left.mp hVW hV hW
      simp [hU, hV, hW]
    · by_cases hW : p ∈ W
      · simp [hU, hV, hW]
      · simp [hU, hV, hW]

theorem AuxLW_decide_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  by_cases hp : p
  · simp [hp, h.1 hp]
  · have hq : ¬ q := fun hq => hp (h.2 hq)
    simp [hp, hq]

theorem AuxLW_decide_eq {p : Prop} [Decidable p] {b : Bool} (h : p ↔ b = true) :
    decide p = b := by
  have : decide p = decide (b = true) := AuxLW_decide_iff h
  simpa using this

theorem AuxLW_decide_or_bool (p q : Prop) [Decidable p] [Decidable q] :
    decide (p ∨ q) = (decide p || decide q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem AuxLW_owZ_mems (S : Finset (entropyParty 1))
    {aA aB aC aD : Bool}
    (hA : decide (entropyLabelA ∈ S) = aA) (hB : decide (b ∈ S) = aB)
    (hC : decide (c ∈ S) = aC) (hD : decide (x 0 ∈ S) = aD) :
    AuxLW_owZ S = AuxLW_owBits aA aB aC aD := by
  rw [AuxLW_owZ_bits, hA, hB, hC, hD]

theorem AuxLW_wmo_disj (U V W : Finset (entropyParty 1))
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W) :
    0 ≤ evaluateEntropyForm (wmoForm U V W) oldWitness := by
  rw [AuxLW_ev_wmo]
  have hAU := AuxLW_dest_U (p := entropyLabelA) hUV hUW
  have hAV := AuxLW_dest_V (p := entropyLabelA) hUV hVW
  have hAW := AuxLW_dest_W (p := entropyLabelA) hUW hVW
  have hBU := AuxLW_dest_U (p := b) hUV hUW
  have hBV := AuxLW_dest_V (p := b) hUV hVW
  have hBW := AuxLW_dest_W (p := b) hUW hVW
  have hCU := AuxLW_dest_U (p := c) hUV hUW
  have hCV := AuxLW_dest_V (p := c) hUV hVW
  have hCW := AuxLW_dest_W (p := c) hUW hVW
  have hDU := AuxLW_dest_U (p := x 0) hUV hUW
  have hDV := AuxLW_dest_V (p := x 0) hUV hVW
  have hDW := AuxLW_dest_W (p := x 0) hUW hVW
  have evUV : AuxLW_owZ (U ∪ V) =
      AuxLW_owBits (AuxLW_mem (AuxLW_dest U V W entropyLabelA) 0 1)
        (AuxLW_mem (AuxLW_dest U V W b) 0 1)
        (AuxLW_mem (AuxLW_dest U V W c) 0 1)
        (AuxLW_mem (AuxLW_dest U V W (x 0)) 0 1) := by
    apply AuxLW_owZ_mems
    · have : decide (entropyLabelA ∈ U ∪ V) = decide (entropyLabelA ∈ U ∨ entropyLabelA ∈ V) := by
        simp [Finset.mem_union]
      rw [this, AuxLW_decide_or_bool, AuxLW_decide_iff hAU, AuxLW_decide_iff hAV]; rfl
    · have : decide (b ∈ U ∪ V) = decide (b ∈ U ∨ b ∈ V) := by
        simp [Finset.mem_union]
      rw [this, AuxLW_decide_or_bool, AuxLW_decide_iff hBU, AuxLW_decide_iff hBV]; rfl
    · have : decide (c ∈ U ∪ V) = decide (c ∈ U ∨ c ∈ V) := by
        simp [Finset.mem_union]
      rw [this, AuxLW_decide_or_bool, AuxLW_decide_iff hCU, AuxLW_decide_iff hCV]; rfl
    · have : decide (x 0 ∈ U ∪ V) = decide (x 0 ∈ U ∨ x 0 ∈ V) := by
        simp [Finset.mem_union]
      rw [this, AuxLW_decide_or_bool, AuxLW_decide_iff hDU, AuxLW_decide_iff hDV]; rfl
  have evUW : AuxLW_owZ (U ∪ W) =
      AuxLW_owBits (AuxLW_mem (AuxLW_dest U V W entropyLabelA) 0 2)
        (AuxLW_mem (AuxLW_dest U V W b) 0 2)
        (AuxLW_mem (AuxLW_dest U V W c) 0 2)
        (AuxLW_mem (AuxLW_dest U V W (x 0)) 0 2) := by
    apply AuxLW_owZ_mems
    · have : decide (entropyLabelA ∈ U ∪ W) = decide (entropyLabelA ∈ U ∨ entropyLabelA ∈ W) := by
        simp [Finset.mem_union]
      rw [this, AuxLW_decide_or_bool, AuxLW_decide_iff hAU, AuxLW_decide_iff hAW]; rfl
    · have : decide (b ∈ U ∪ W) = decide (b ∈ U ∨ b ∈ W) := by
        simp [Finset.mem_union]
      rw [this, AuxLW_decide_or_bool, AuxLW_decide_iff hBU, AuxLW_decide_iff hBW]; rfl
    · have : decide (c ∈ U ∪ W) = decide (c ∈ U ∨ c ∈ W) := by
        simp [Finset.mem_union]
      rw [this, AuxLW_decide_or_bool, AuxLW_decide_iff hCU, AuxLW_decide_iff hCW]; rfl
    · have : decide (x 0 ∈ U ∪ W) = decide (x 0 ∈ U ∨ x 0 ∈ W) := by
        simp [Finset.mem_union]
      rw [this, AuxLW_decide_or_bool, AuxLW_decide_iff hDU, AuxLW_decide_iff hDW]; rfl
  have evV : AuxLW_owZ V =
      AuxLW_owBits (AuxLW_mem1 (AuxLW_dest U V W entropyLabelA) 1)
        (AuxLW_mem1 (AuxLW_dest U V W b) 1)
        (AuxLW_mem1 (AuxLW_dest U V W c) 1)
        (AuxLW_mem1 (AuxLW_dest U V W (x 0)) 1) := by
    apply AuxLW_owZ_mems
    · rw [AuxLW_decide_iff hAV]; rfl
    · rw [AuxLW_decide_iff hBV]; rfl
    · rw [AuxLW_decide_iff hCV]; rfl
    · rw [AuxLW_decide_iff hDV]; rfl
  have evW : AuxLW_owZ W =
      AuxLW_owBits (AuxLW_mem1 (AuxLW_dest U V W entropyLabelA) 2)
        (AuxLW_mem1 (AuxLW_dest U V W b) 2)
        (AuxLW_mem1 (AuxLW_dest U V W c) 2)
        (AuxLW_mem1 (AuxLW_dest U V W (x 0)) 2) := by
    apply AuxLW_owZ_mems
    · rw [AuxLW_decide_iff hAW]; rfl
    · rw [AuxLW_decide_iff hBW]; rfl
    · rw [AuxLW_decide_iff hCW]; rfl
    · rw [AuxLW_decide_iff hDW]; rfl
  have hb := AuxLW_wmo_bits (AuxLW_dest U V W entropyLabelA) (AuxLW_dest U V W b)
    (AuxLW_dest U V W c) (AuxLW_dest U V W (x 0))
  have hb' : (AuxLW_owZ (U ∪ V) : ℝ) + AuxLW_owZ (U ∪ W) ≥ AuxLW_owZ V + AuxLW_owZ W := by
    exact_mod_cast (by rw [evUV, evUW, evV, evW]; exact hb)
  simp only [AuxLW_ow_eq]
  linarith

theorem AuxLW_quantum (L : Form (entropyParty 1)) (hL : QuantumBasic L) :
    0 ≤ evaluateEntropyForm L oldWitness := by
  obtain ⟨U, V, W, hdis, hform⟩ := hL
  rcases hdis with ⟨hUV, hUW, hVW⟩
  rcases hform with hform | hform
  · subst hform
    exact AuxLW_cmi_nonneg U V W hUV
  · subst hform
    exact AuxLW_wmo_disj U V W hUV hUW hVW


theorem AuxLW_mems {S : Finset (entropyParty 1)} {aA aB aC aD : Bool}
    (hA : (entropyLabelA ∈ S) ↔ aA = true) (hB : (b ∈ S) ↔ aB = true)
    (hC : (c ∈ S) ↔ aC = true) (hD : (x 0 ∈ S) ↔ aD = true) :
    oldWitness S = (AuxLW_owBits aA aB aC aD : ℝ) := by
  rw [AuxLW_bits_of, AuxLW_decide_eq hA, AuxLW_decide_eq hB, AuxLW_decide_eq hC,
    AuxLW_decide_eq hD]

theorem AuxLW_I_AB_D :
    evaluateEntropyForm (cmiForm {entropyLabelA} {b} {x 0}) oldWitness = 0 := by
  rw [AuxLW_ev_cmi, AuxLW_bits_of, AuxLW_bits_of, AuxLW_bits_of, AuxLW_bits_of]
  simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  try norm_num

theorem AuxLW_I_AC_B :
    evaluateEntropyForm (cmiForm {entropyLabelA} {c} {b}) oldWitness = 0 := by
  rw [AuxLW_ev_cmi, AuxLW_bits_of, AuxLW_bits_of, AuxLW_bits_of, AuxLW_bits_of]
  simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  try norm_num

theorem AuxLW_I_BC_A :
    evaluateEntropyForm (cmiForm {b} {c} {entropyLabelA}) oldWitness = 0 := by
  rw [AuxLW_ev_cmi, AuxLW_bits_of, AuxLW_bits_of, AuxLW_bits_of, AuxLW_bits_of]
  simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  try norm_num

theorem AuxLW_I_C_D :
    evaluateEntropyForm (miForm {c} {x 0}) oldWitness = 0 := by
  rw [AuxLW_ev_mi, AuxLW_bits_of, AuxLW_bits_of, AuxLW_bits_of]
  simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  try norm_num

theorem AuxLW_I_AB_C :
    evaluateEntropyForm (miForm ({entropyLabelA} ∪ {b}) {c}) oldWitness = 2 := by
  rw [AuxLW_ev_mi, AuxLW_bits_of, AuxLW_bits_of, AuxLW_bits_of]
  simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  try norm_num

theorem AuxLW_I_AB_C_pair :
    evaluateEntropyForm (miForm {entropyLabelA, b} {c}) oldWitness = 2 := by
  rw [AuxLW_ev_mi, AuxLW_bits_of, AuxLW_bits_of, AuxLW_bits_of]
  simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  try norm_num

theorem AuxLW_I_AB_C_cmi :
    evaluateEntropyForm (cmiForm {entropyLabelA} {b} {c}) oldWitness = 2 := by
  rw [AuxLW_ev_cmi, AuxLW_bits_of, AuxLW_bits_of, AuxLW_bits_of, AuxLW_bits_of]
  simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  try norm_num

theorem AuxLW_I_AB_CD :
    evaluateEntropyForm (cmiForm {entropyLabelA} {b} ({c} ∪ {x 0})) oldWitness = 0 := by
  rw [AuxLW_ev_cmi, AuxLW_bits_of, AuxLW_bits_of, AuxLW_bits_of, AuxLW_bits_of]
  simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  try norm_num

theorem AuxLW_oldForm : evaluateEntropyForm oldForm oldWitness = -2 := by
  unfold oldForm
  rw [AuxLW_ev_sub, AuxLW_I_C_D, AuxLW_I_AB_C_pair]
  norm_num

theorem AuxLW_constraints :
    ∀ Z ∈ oldConstraints, evaluateEntropyForm Z oldWitness = 0 := by
  intro Z hZ
  simp [oldConstraints, constraints] at hZ
  rcases hZ with hZ | hZ | hZ
  · subst hZ; exact AuxLW_I_AB_D
  · subst hZ; exact AuxLW_I_AC_B
  · subst hZ; exact AuxLW_I_BC_A

theorem AuxLW_standardX (i : Fin 1) :
    standardX i = ({x 0} : Finset (entropyParty 1)) := by
  fin_cases i
  simp [standardX, x]

theorem AuxLW_biUnion_X :
    (Finset.univ.biUnion (standardX : Fin 1 → Finset (entropyParty 1))) = {x 0} := by
  ext y
  simp [standardX, x]

theorem AuxLW_sum_univ_one {α : Type*} [AddCommMonoid α] (f : Fin 1 → α) :
    ∑ i : Fin 1, f i = f 0 := by
  simp

theorem AuxLW_prime :
    evaluateEntropyForm (primeForm {entropyLabelA} {b} {c} standardX) oldWitness = 0 := by
  unfold primeForm
  rw [AuxLW_ev_sub, AuxLW_ev_sub, AuxLW_ev_add, AuxLW_ev_add, AuxLW_ev_add,
      AuxLW_ev_sum, AuxLW_ev_sum, AuxLW_ev_smul]
  simp only [AuxLW_standardX, AuxLW_sum_univ_one, AuxLW_biUnion_X]
  erw [AuxLW_I_AB_D, AuxLW_ev_atom' (h0 := AuxLW_ow_empty)]
  have hD : oldWitness ({x 0} : Finset (entropyParty 1)) = (4 : ℝ) := by
    rw [AuxLW_bits_of]
    simp [Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  erw [hD, AuxLW_I_AB_CD]
  erw [AuxLW_ev_atom' (h0 := AuxLW_ow_empty), AuxLW_ev_atom' (h0 := AuxLW_ow_empty)]
  have hABCD : oldWitness ({entropyLabelA} ∪ {b} ∪ {c} ∪ {x 0}) = (4 : ℝ) := by
    rw [AuxLW_bits_of]
    simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  have hABC : oldWitness ({entropyLabelA} ∪ {b} ∪ {c}) = (6 : ℝ) := by
    rw [AuxLW_bits_of]
    simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  erw [hABCD, hABC, AuxLW_I_AB_C]
  norm_num

theorem AuxLW_casx :
    evaluateEntropyForm (cAsXForm {entropyLabelA} {b} {c} standardX) oldWitness = 0 := by
  unfold cAsXForm
  rw [AuxLW_ev_sub, AuxLW_ev_sub, AuxLW_ev_add, AuxLW_ev_add, AuxLW_ev_add,
      AuxLW_ev_sum, AuxLW_ev_sum, AuxLW_ev_smul]
  simp only [AuxLW_standardX, AuxLW_sum_univ_one, AuxLW_biUnion_X]
  erw [AuxLW_I_AB_D, AuxLW_ev_atom' (h0 := AuxLW_ow_empty)]
  have hD : oldWitness ({x 0} : Finset (entropyParty 1)) = (4 : ℝ) := by
    rw [AuxLW_bits_of]
    simp [Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  erw [hD, AuxLW_I_AB_C_cmi, AuxLW_ev_atom' (h0 := AuxLW_ow_empty)]
  have hC : oldWitness ({c} : Finset (entropyParty 1)) = (2 : ℝ) := by
    rw [AuxLW_bits_of]
    simp [Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  erw [hC, AuxLW_ev_atom' (h0 := AuxLW_ow_empty)]
  have hCD : oldWitness ({c} ∪ {x 0}) = (6 : ℝ) := by
    rw [AuxLW_bits_of]
    simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  erw [hCD, AuxLW_I_AB_C]
  norm_num

theorem AuxLW_casxp :
    evaluateEntropyForm (cAsXPrimeForm {entropyLabelA} {b} {c} standardX) oldWitness = 2 := by
  unfold cAsXPrimeForm
  rw [AuxLW_ev_sub, AuxLW_ev_sub, AuxLW_ev_add, AuxLW_ev_add, AuxLW_ev_add, AuxLW_ev_add,
      AuxLW_ev_add, AuxLW_ev_sum, AuxLW_ev_sum, AuxLW_ev_smul]
  simp only [AuxLW_standardX, AuxLW_sum_univ_one, AuxLW_biUnion_X]
  erw [AuxLW_I_AB_D, AuxLW_ev_atom' (h0 := AuxLW_ow_empty)]
  have hD : oldWitness ({x 0} : Finset (entropyParty 1)) = (4 : ℝ) := by
    rw [AuxLW_bits_of]
    simp [Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  erw [hD, AuxLW_I_AB_CD, AuxLW_ev_atom' (h0 := AuxLW_ow_empty)]
  have hABCD : oldWitness ({entropyLabelA} ∪ {b} ∪ {c} ∪ {x 0}) = (4 : ℝ) := by
    rw [AuxLW_bits_of]
    simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  erw [hABCD, AuxLW_I_AB_C_cmi, AuxLW_ev_atom' (h0 := AuxLW_ow_empty)]
  have hC : oldWitness ({c} : Finset (entropyParty 1)) = (2 : ℝ) := by
    rw [AuxLW_bits_of]
    simp [Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  erw [hC, AuxLW_ev_atom' (h0 := AuxLW_ow_empty)]
  have hAB : oldWitness ({entropyLabelA} ∪ {b}) = (6 : ℝ) := by
    rw [AuxLW_bits_of]
    simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, entropyLabelA, b, c, x, Fin.ext_iff, AuxLW_owBits]
  erw [hAB, AuxLW_I_AB_C]
  norm_num

theorem AuxLW_new (L : Form (entropyParty 1)) (hL : NewFourParty L) :
    0 ≤ evaluateEntropyForm L oldWitness := by
  rcases hL with hL | hL | hL
  · subst hL; rw [AuxLW_prime]
  · subst hL; rw [AuxLW_casx]
  · subst hL; rw [AuxLW_casxp]; norm_num

theorem AuxLW_not_derivable :
    ¬ Derivable {L | QuantumBasic L ∨ NewFourParty L} oldConstraints oldForm := by
  rintro ⟨k, L, w, r, hAll, hnn, heq⟩
  have hev :
      evaluateEntropyForm oldForm oldWitness =
        (∑ i, w i * evaluateEntropyForm (L i) oldWitness) +
          ∑ z : oldConstraints, r z * evaluateEntropyForm z.1 oldWitness := by
    rw [heq, AuxLW_ev_add, AuxLW_ev_sum_smul, AuxLW_ev_sum_smul]
  have hz : ∀ z : oldConstraints, evaluateEntropyForm z.1 oldWitness = 0 := by
    intro z
    exact AuxLW_constraints z.1 z.2
  simp only [hz, mul_zero, Finset.sum_const_zero, add_zero] at hev
  have hnn' : 0 ≤ ∑ i, w i * evaluateEntropyForm (L i) oldWitness := by
    apply Finset.sum_nonneg
    intro i _
    refine mul_nonneg (hnn i) ?_
    have hi := hAll i
    simp only [Set.mem_ofPred_eq] at hi
    rcases hi with hB | hN
    · exact AuxLW_quantum (L i) hB
    · exact AuxLW_new (L i) hN
  have : evaluateEntropyForm oldForm oldWitness = -2 := AuxLW_oldForm
  linarith

theorem _root_.solution :
    (∀ L : Form (entropyParty 1), QuantumBasic L → 0 ≤ evaluateEntropyForm L oldWitness) ∧
    (∀ Z ∈ oldConstraints, evaluateEntropyForm Z oldWitness = 0) ∧
    evaluateEntropyForm oldForm oldWitness = -2 ∧
    (∀ L : Form (entropyParty 1), NewFourParty L → 0 ≤ evaluateEntropyForm L oldWitness) ∧
    ¬ Derivable {L | QuantumBasic L ∨ NewFourParty L} oldConstraints oldForm := by
  exact ⟨AuxLW_quantum, AuxLW_constraints, AuxLW_oldForm, AuxLW_new, AuxLW_not_derivable⟩

end QAlgorithms.Papers.Independent.Intake100.P66

end

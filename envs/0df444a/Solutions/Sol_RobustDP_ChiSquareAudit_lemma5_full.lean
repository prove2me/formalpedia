-- Prove2me | solution 1 for RobustDP.ChiSquareAudit.lemma5_full
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T22:05:32.893201+00:00
-- url     : https://prove2.me/submissions/c26f4e64-1e3e-4419-b340-03c2c29bf18f

import Mathlib
import Definitions.Def_RobustDP_ChiSquareAudit_Program

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace RobustDP.ChiSquareAudit

open RobustDP.ChiSquare

theorem L1_bind_value {α β : Type} (x : Run α) (f : α → Run β) :
    (x >>= f).value = (f x.value).value := rfl
theorem L1_bind_steps {α β : Type} (x : Run α) (f : α → Run β) :
    (x >>= f).steps = x.steps + (f x.value).steps := rfl
theorem L1_pure_value {α : Type} (a : α) : (pure a : Run α).value = a := rfl
theorem L1_pure_steps {α : Type} (a : α) : (pure a : Run α).steps = 0 := rfl

theorem L1_rsqrt_value (x : ℝ) : (rsqrt x).value = Real.sqrt x := by
  unfold rsqrt
  split_ifs with h
  · exact (Real.sqrt_eq_zero'.2 h.le).symm
  · rfl
theorem L1_rsqrt_steps (x : ℝ) : (rsqrt x).steps ≤ 2 := by
  unfold rsqrt; split_ifs <;> simp
theorem L1_rdiv_value (x y : ℝ) : (rdiv x y).value = x / y := by
  unfold rdiv
  split_ifs with h
  · simp [h]
  · rfl
theorem L1_rdiv_steps (x y : ℝ) : (rdiv x y).steps ≤ 2 := by
  unfold rdiv; split_ifs <;> simp
theorem L1_rlt_value (x y : ℝ) : (rlt x y).value = true ↔ x < y := by
  simp [rlt]
theorem L1_rle_value (x y : ℝ) : (rle x y).value = true ↔ x ≤ y := by
  simp [rle]
theorem L1_req_value (x y : ℝ) : (req x y).value = true ↔ x = y := by
  simp [req]

/-! score -/

theorem L1_score_value (t : ℝ) (cell : Cell) (α : ℝ) :
    (score t cell α).value = intervalObjective t cell.a cell.b cell.c α := by
  simp only [score, L1_bind_value, rmul, radd, rsub, overhead, L1_rsqrt_value]
  unfold intervalObjective intervalVariance
  ring_nf

theorem L1_score_steps (t : ℝ) (cell : Cell) (α : ℝ) : (score t cell α).steps ≤ 19 := by
  simp only [score, L1_bind_steps, L1_bind_value, rmul, radd, rsub, overhead]
  have := L1_rsqrt_steps (t * (cell.c + cell.b * (α * α) - (cell.a + cell.b * α) * (cell.a + cell.b * α)))
  omega

/-! coefficients -/

theorem L1_coeff_value (t : ℝ) (cell : Cell) :
    (coefficients t cell).value =
      (cell.b * cell.b * (cell.b - cell.b * cell.b - t * ((1 - cell.b) * (1 - cell.b))),
       cell.b * cell.b * (2 * (t * ((1 - cell.b) * cell.a)) - 2 * (cell.a * cell.b)),
       cell.b * cell.b * (cell.c - cell.a * cell.a - t * (cell.a * cell.a))) := by
  simp only [coefficients, L1_bind_value, rmul, rsub, overhead, L1_pure_value]

theorem L1_coeff_steps (t : ℝ) (cell : Cell) : (coefficients t cell).steps = 27 := by
  simp only [coefficients, L1_bind_value, L1_bind_steps, rmul, rsub, overhead, L1_pure_steps]

theorem L1_coeff_poly (t : ℝ) (cell : Cell) (x : ℝ) :
    (coefficients t cell).value.1 * x ^ 2 + (coefficients t cell).value.2.1 * x
      + (coefficients t cell).value.2.2 = stationaryPolynomial t cell.a cell.b cell.c x := by
  rw [L1_coeff_value]
  unfold stationaryPolynomial intervalVariance
  ring

/-! quadratic roots -/

theorem L1_quad_mem (A B D x : ℝ) (hx : A * x ^ 2 + B * x + D = 0) (hAB : ¬ (A = 0 ∧ B = 0)) :
    x ∈ (quadraticRoots A B D).value := by
  unfold quadraticRoots
  simp only [L1_bind_value, overhead, rmul, rsub, radd]
  by_cases hA : A = 0
  · have hB : B ≠ 0 := fun hB => hAB ⟨hA, hB⟩
    have h1 : (req A 0).value = true := (L1_req_value A 0).2 hA
    have h2 : (req B 0).value = false := by
      cases h : (req B 0).value
      · rfl
      · exact absurd ((L1_req_value B 0).1 h) hB
    simp only [h1, h2, L1_bind_value, L1_pure_value, L1_rdiv_value, rsub, List.mem_singleton,
      ↓reduceIte, Bool.false_eq_true]
    subst hA
    field_simp
    linarith
  · have h1 : (req A 0).value = false := by
      cases h : (req A 0).value
      · rfl
      · exact absurd ((L1_req_value A 0).1 h) hA
    simp only [h1, Bool.false_eq_true, ↓reduceIte, L1_bind_value]
    have hdisc : B * B - 4 * (A * D) = (2 * A * x + B) ^ 2 := by
      have : D = -(A * x ^ 2 + B * x) := by linarith
      rw [this]; ring
    have h3 : (rlt (B * B - 4 * (A * D)) 0).value = false := by
      cases h : (rlt (B * B - 4 * (A * D)) 0).value
      · rfl
      · have := (L1_rlt_value _ _).1 h
        rw [hdisc] at this
        exact absurd this (not_lt.2 (sq_nonneg _))
    simp only [h3, Bool.false_eq_true, ↓reduceIte, L1_bind_value, L1_pure_value, L1_rdiv_value,
      L1_rsqrt_value, rsub, radd, rmul, List.mem_cons, List.not_mem_nil, or_false]
    rw [hdisc, Real.sqrt_sq_eq_abs]
    have h2A : (2 : ℝ) * A ≠ 0 := by positivity
    rcases le_total 0 (2 * A * x + B) with h | h
    · left
      rw [abs_of_nonneg h]
      field_simp
      ring
    · right
      rw [abs_of_nonpos h]
      field_simp
      ring

theorem L1_quad_len (A B D : ℝ) : (quadraticRoots A B D).value.length ≤ 2 := by
  unfold quadraticRoots
  simp only [L1_bind_value, overhead, rmul, rsub, radd]
  split_ifs <;> simp only [L1_bind_value, L1_pure_value] <;> (try split_ifs) <;>
    simp [L1_bind_value, L1_pure_value]

theorem L1_quad_steps (A B D : ℝ) : (quadraticRoots A B D).steps ≤ 24 := by
  unfold quadraticRoots
  simp only [L1_bind_value, L1_bind_steps, overhead, rmul, rsub, radd, L1_pure_steps]
  have h1 := L1_rsqrt_steps (B * B - 4 * (A * D))
  have h2 := L1_rdiv_steps (0 - D) B
  have h3 := L1_rdiv_steps (0 - B + Real.sqrt (B * B - 4 * (A * D))) (2 * A)
  have h4 := L1_rdiv_steps (0 - B - Real.sqrt (B * B - 4 * (A * D))) (2 * A)
  split_ifs <;> simp only [L1_bind_value, L1_bind_steps, L1_pure_steps, L1_pure_value] <;>
    (try split_ifs) <;>
    simp only [L1_bind_value, L1_bind_steps, L1_pure_steps, L1_pure_value, req, rlt, rmul, rsub,
      radd, L1_rsqrt_value] <;> omega

end RobustDP.ChiSquareAudit

/-! ## L2: scan semantics (value: max over candidates; steps) -/

namespace RobustDP.ChiSquareAudit

open RobustDP.ChiSquare

/-- Candidates scanned in a cell. -/
def L2_cands (t : ℝ) (cell : Cell) : Set ℝ :=
  {x | x = cell.low ∨ ∃ h : ℝ, cell.high = some h ∧ cell.low < h ∧
      x ∈ (quadraticRoots (coefficients t cell).value.1 (coefficients t cell).value.2.1
        (coefficients t cell).value.2.2).value ∧ cell.low < x ∧ x < h}

noncomputable def L2_f (t : ℝ) (cell : Cell) (x : ℝ) : ℝ :=
  intervalObjective t cell.a cell.b cell.c x

theorem L2_consider (t : ℝ) (cell : Cell) (α : ℝ) (best : Option Best) :
    ∃ b, (consider t cell α best).value = some b ∧
      (∀ old, best = some old → old.val ≤ b.val) ∧ L2_f t cell α ≤ b.val ∧
      (b = ⟨α, L2_f t cell α⟩ ∨ best = some b) := by
  unfold consider
  simp only [L1_bind_value, overhead]
  cases best with
  | none =>
    refine ⟨⟨α, L2_f t cell α⟩, ?_, by simp, le_rfl, Or.inl rfl⟩
    simp [L1_pure_value, L2_f, L1_score_value]
  | some old =>
    simp only [L1_bind_value, L1_pure_value]
    by_cases h : old.val < (score t cell α).value
    · rw [if_pos ((L1_rlt_value _ _).2 h)]
      refine ⟨⟨α, L2_f t cell α⟩, ?_, ?_, le_rfl, Or.inl rfl⟩
      · simp [L2_f, L1_score_value]
      · intro o ho
        cases ho
        rw [L1_score_value] at h
        exact h.le
    · have hf : (rlt old.val (score t cell α).value).value = false := by
        cases hh : (rlt old.val (score t cell α).value).value
        · rfl
        · exact absurd ((L1_rlt_value _ _).1 hh) h
      rw [if_neg (by rw [hf]; decide)]
      refine ⟨old, rfl, fun o ho => by cases ho; exact le_rfl, ?_, Or.inr rfl⟩
      rw [L1_score_value] at h
      exact not_lt.1 h

theorem L2_consider_steps (t : ℝ) (cell : Cell) (α : ℝ) (best : Option Best) :
    (consider t cell α best).steps ≤ 26 := by
  unfold consider
  simp only [L1_bind_value, L1_bind_steps, overhead]
  have := L1_score_steps t cell α
  cases best with
  | none => simp only [L1_pure_steps]; omega
  | some old => simp only [L1_bind_steps, L1_pure_steps, rlt]; omega

theorem L2_considerRoots (t : ℝ) (cell : Cell) (high : ℝ) (xs : List ℝ) (old : Best) :
    ∃ b, (considerRoots t cell high xs (some old)).value = some b ∧ old.val ≤ b.val ∧
      (∀ x ∈ xs, cell.low < x → x < high → L2_f t cell x ≤ b.val) ∧
      (b = old ∨ ∃ x ∈ xs, cell.low < x ∧ x < high ∧ b = ⟨x, L2_f t cell x⟩) := by
  induction xs generalizing old with
  | nil => exact ⟨old, rfl, le_rfl, by simp, Or.inl rfl⟩
  | cons x xs ih =>
    unfold considerRoots
    simp only [L1_bind_value, overhead]
    by_cases hx : cell.low < x ∧ x < high
    · have e : ((rlt cell.low x).value && (rlt x high).value) = true := by
        rw [Bool.and_eq_true, L1_rlt_value, L1_rlt_value]; exact hx
      rw [if_pos e]
      simp only [L1_bind_value]
      obtain ⟨b1, hb1, hmono1, hf1, ho1⟩ := L2_consider t cell x (some old)
      rw [hb1]
      obtain ⟨b, hb, hmono, hf, ho⟩ := ih b1
      refine ⟨b, hb, le_trans (hmono1 old rfl) hmono, ?_, ?_⟩
      · intro y hy hly hyh
        rcases List.mem_cons.1 hy with rfl | hy
        · exact le_trans hf1 hmono
        · exact hf y hy hly hyh
      · rcases ho with rfl | ⟨y, hy, h1, h2, rfl⟩
        · rcases ho1 with rfl | h
          · exact Or.inr ⟨x, List.mem_cons_self .., hx.1, hx.2, rfl⟩
          · cases h; exact Or.inl rfl
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h1, h2, rfl⟩
    · have e : ((rlt cell.low x).value && (rlt x high).value) = false := by
        cases hh : ((rlt cell.low x).value && (rlt x high).value)
        · rfl
        · rw [Bool.and_eq_true, L1_rlt_value, L1_rlt_value] at hh; exact absurd hh hx
      rw [if_neg (by rw [e]; decide)]
      simp only [L1_bind_value, L1_pure_value]
      obtain ⟨b, hb, hmono, hf, ho⟩ := ih old
      refine ⟨b, hb, hmono, ?_, ?_⟩
      · intro y hy hly hyh
        rcases List.mem_cons.1 hy with rfl | hy
        · exact absurd ⟨hly, hyh⟩ hx
        · exact hf y hy hly hyh
      · rcases ho with rfl | ⟨y, hy, h1, h2, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h1, h2, rfl⟩

theorem L2_considerRoots_steps (t : ℝ) (cell : Cell) (high : ℝ) (xs : List ℝ) (best : Option Best) :
    (considerRoots t cell high xs best).steps ≤ 2 + 36 * xs.length := by
  induction xs generalizing best with
  | nil => simp [considerRoots]
  | cons x xs ih =>
    unfold considerRoots
    simp only [L1_bind_value, L1_bind_steps, overhead, rlt, List.length_cons]
    split_ifs with h
    · have h1 := L2_consider_steps t cell x best
      have h2 := ih (consider t cell x best).value
      simp only [L1_bind_steps, L1_bind_value]
      omega
    · have h2 := ih best
      simp only [L1_bind_steps, L1_bind_value, L1_pure_steps, L1_pure_value]
      omega

theorem L2_scanCell (t : ℝ) (cell : Cell) (best : Option Best) :
    ∃ b, (scanCell t cell best).value = some b ∧
      (∀ old, best = some old → old.val ≤ b.val) ∧
      (∀ x ∈ L2_cands t cell, L2_f t cell x ≤ b.val) ∧
      ((∃ x ∈ L2_cands t cell, b = ⟨x, L2_f t cell x⟩) ∨ best = some b) := by
  unfold scanCell
  simp only [L1_bind_value, overhead]
  obtain ⟨b1, hb1, hmono1, hf1, ho1⟩ := L2_consider t cell cell.low best
  rw [hb1]
  have ho1' : (∃ x ∈ L2_cands t cell, b1 = ⟨x, L2_f t cell x⟩) ∨ best = some b1 := by
    rcases ho1 with h | h
    · exact Or.inl ⟨cell.low, Or.inl rfl, h⟩
    · exact Or.inr h
  rcases hh : cell.high with _ | high
  · simp only [L1_pure_value]
    refine ⟨b1, rfl, hmono1, ?_, ho1'⟩
    rintro x (rfl | ⟨h, hh', -⟩)
    · exact hf1
    · rw [hh] at hh'; cases hh'
  · simp only [L1_bind_value]
    by_cases hlh : cell.low < high
    · rw [if_pos ((L1_rlt_value _ _).2 hlh)]
      simp only [L1_bind_value]
      obtain ⟨b, hb, hmono, hf, ho⟩ := L2_considerRoots t cell high
        (quadraticRoots (coefficients t cell).value.1 (coefficients t cell).value.2.1
          (coefficients t cell).value.2.2).value b1
      refine ⟨b, hb, fun old h => le_trans (hmono1 old h) hmono, ?_, ?_⟩
      · rintro x (rfl | ⟨h, hh', -, hx, hlx, hxh⟩)
        · exact le_trans hf1 hmono
        · rw [hh] at hh'; cases hh'
          exact hf x hx hlx hxh
      · rcases ho with rfl | ⟨x, hx, hlx, hxh, rfl⟩
        · exact ho1'
        · exact Or.inl ⟨x, Or.inr ⟨high, hh, hlh, hx, hlx, hxh⟩, rfl⟩
    · have hf : (rlt cell.low high).value = false := by
        cases h' : (rlt cell.low high).value
        · rfl
        · exact absurd ((L1_rlt_value _ _).1 h') hlh
      rw [if_neg (by rw [hf]; decide)]
      simp only [L1_pure_value]
      refine ⟨b1, rfl, hmono1, ?_, ho1'⟩
      rintro x (rfl | ⟨h, hh', hlh', -⟩)
      · exact hf1
      · rw [hh] at hh'; cases hh'; exact absurd hlh' hlh

theorem L2_scanCell_steps (t : ℝ) (cell : Cell) (best : Option Best) :
    (scanCell t cell best).steps ≤ 158 := by
  unfold scanCell
  simp only [L1_bind_value, L1_bind_steps, overhead]
  have h1 := L2_consider_steps t cell cell.low best
  rcases cell.high with _ | high
  · simp only [L1_pure_steps]; omega
  · simp only [L1_bind_value, L1_bind_steps, rlt]
    split_ifs
    · simp only [L1_bind_value, L1_bind_steps, L1_coeff_steps]
      have h2 := L1_quad_steps (coefficients t cell).value.1 (coefficients t cell).value.2.1
          (coefficients t cell).value.2.2
      have h3 := L1_quad_len (coefficients t cell).value.1 (coefficients t cell).value.2.1
          (coefficients t cell).value.2.2
      have h4 := L2_considerRoots_steps t cell high
        (quadraticRoots (coefficients t cell).value.1 (coefficients t cell).value.2.1
          (coefficients t cell).value.2.2).value (consider t cell cell.low best).value
      omega
    · simp only [L1_pure_steps]; omega

theorem L2_scanPass (t : ℝ) (cells : List Cell) (best : Option Best)
    (hne : cells ≠ [] ∨ best ≠ none) :
    ∃ b, (scanPass t cells best).value = some b ∧
      (∀ old, best = some old → old.val ≤ b.val) ∧
      (∀ cell ∈ cells, ∀ x ∈ L2_cands t cell, L2_f t cell x ≤ b.val) ∧
      ((∃ cell ∈ cells, ∃ x ∈ L2_cands t cell, b = ⟨x, L2_f t cell x⟩) ∨ best = some b) := by
  induction cells generalizing best with
  | nil =>
    rcases best with _ | old
    · simp at hne
    · exact ⟨old, rfl, fun o h => by cases h; exact le_rfl, by simp, Or.inr rfl⟩
  | cons c cs ih =>
    unfold scanPass
    simp only [L1_bind_value, overhead]
    obtain ⟨b1, hb1, hmono1, hf1, ho1⟩ := L2_scanCell t c best
    rw [hb1]
    obtain ⟨b, hb, hmono, hf, ho⟩ := ih (some b1) (Or.inr (by simp))
    refine ⟨b, hb, fun old h => le_trans (hmono1 old h) (hmono b1 rfl), ?_, ?_⟩
    · intro cell hcell x hx
      rcases List.mem_cons.1 hcell with rfl | hcell
      · exact le_trans (hf1 x hx) (hmono b1 rfl)
      · exact hf cell hcell x hx
    · rcases ho with ⟨cell, hcell, x, hx, rfl⟩ | h
      · exact Or.inl ⟨cell, List.mem_cons_of_mem _ hcell, x, hx, rfl⟩
      · cases h
        rcases ho1 with ⟨x, hx, rfl⟩ | h
        · exact Or.inl ⟨c, List.mem_cons_self .., x, hx, rfl⟩
        · exact Or.inr h

theorem L2_scanPass_steps (t : ℝ) (cells : List Cell) (best : Option Best) :
    (scanPass t cells best).steps ≤ 2 + 162 * cells.length := by
  induction cells generalizing best with
  | nil => simp [scanPass]
  | cons c cs ih =>
    unfold scanPass
    simp only [L1_bind_value, L1_bind_steps, overhead, List.length_cons]
    have h1 := L2_scanCell_steps t c best
    have h2 := ih (scanCell t c best).value
    omega

end RobustDP.ChiSquareAudit

/-! ## L3: support pass, output pass, prefix pass -/

namespace RobustDP.ChiSquareAudit

open RobustDP.ChiSquare

theorem L3_sum_succ {n : ℕ} (G : Fin n → ℝ) (m : ℕ) (h : m < n) :
    (∑ i : Fin n, if i.val < m + 1 then G i else 0)
      = (∑ i : Fin n, if i.val < m then G i else 0) + G ⟨m, h⟩ := by
  have e : ∀ i : Fin n, (if i.val < m + 1 then G i else 0)
      = (if i.val < m then G i else 0) + (if i = ⟨m, h⟩ then G i else 0) := by
    intro i
    by_cases h1 : i.val < m
    · have h2 : i ≠ ⟨m, h⟩ := by
        intro e; rw [e] at h1; exact lt_irrefl _ h1
      rw [if_pos (by omega), if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : i = ⟨m, h⟩
      · subst h2
        rw [if_pos (by simp), if_neg h1, if_pos rfl, zero_add]
      · have h3 : ¬ i.val < m + 1 := by
          intro h3; apply h2; ext; simp only; omega
        rw [if_neg h3, if_neg h1, if_neg h2, add_zero]
  rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem L3_support {n : ℕ} (q v : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i) :
    ∀ (m : ℕ) (h : m ≤ n),
      (∀ r ∈ (supportPass q v m h).value, 0 < r.q ∧ ∃ i : Fin n, i.val < m ∧ r.v = v i ∧ r.q = q i) ∧
      (∀ i : Fin n, i.val < m → 0 < q i → ∃ r ∈ (supportPass q v m h).value, r.v = v i) ∧
      (∀ F : ℝ → ℝ → ℝ, (∀ x, F x 0 = 0) →
        ((supportPass q v m h).value.map (fun r => F r.v r.q)).sum
          = ∑ i : Fin n, if i.val < m then F (v i) (q i) else 0) ∧
      (supportPass q v m h).value.length ≤ m ∧
      (supportPass q v m h).steps = 2 + 13 * m := by
  intro m
  induction m with
  | zero =>
    intro h
    refine ⟨by simp [supportPass], fun i hi => absurd hi (Nat.not_lt_zero _), ?_, by simp [supportPass],
      by simp [supportPass]⟩
    intro F _
    simp [supportPass]
  | succ m ih =>
    intro h
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih (by omega)
    have hm : m < n := by omega
    unfold supportPass
    simp only [L1_bind_value, L1_bind_steps, overhead, inputRead]
    by_cases hp : 0 < q ⟨m, hm⟩
    · have e : (rlt 0 (q ⟨m, hm⟩)).value = true := (L1_rlt_value _ _).2 hp
      simp only [rlt, decide_eq_true_eq, hp, ↓reduceIte, L1_pure_value, L1_pure_steps]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r hr
        rcases List.mem_cons.1 hr with rfl | hr
        · exact ⟨hp, ⟨m, hm⟩, by simp, rfl, rfl⟩
        · obtain ⟨h1, i, hi, h2, h3⟩ := ih1 r hr
          exact ⟨h1, i, by omega, h2, h3⟩
      · intro i hi hqi
        by_cases him : i.val < m
        · obtain ⟨r, hr, hrv⟩ := ih2 i him hqi
          exact ⟨r, List.mem_cons_of_mem _ hr, hrv⟩
        · have : i = ⟨m, hm⟩ := by ext; simp only; omega
          subst this
          exact ⟨_, List.mem_cons_self .., rfl⟩
      · intro F hF
        rw [List.map_cons, List.sum_cons, ih3 F hF, L3_sum_succ (fun i => F (v i) (q i)) m hm]
        ring
      · simp only [List.length_cons]; omega
      · omega
    · have e : (rlt 0 (q ⟨m, hm⟩)).value = false := by
        cases hh : (rlt 0 (q ⟨m, hm⟩)).value
        · rfl
        · exact absurd ((L1_rlt_value _ _).1 hh) hp
      have hq0 : q ⟨m, hm⟩ = 0 := le_antisymm (not_lt.1 hp) (hq _)
      simp only [rlt, decide_eq_true_eq, hp, ↓reduceIte, L1_pure_value, L1_pure_steps]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r hr
        obtain ⟨h1, i, hi, h2, h3⟩ := ih1 r hr
        exact ⟨h1, i, by omega, h2, h3⟩
      · intro i hi hqi
        by_cases him : i.val < m
        · exact ih2 i him hqi
        · have : i = ⟨m, hm⟩ := by ext; simp only; omega
          subst this
          exact absurd hqi hp
      · intro F hF
        rw [ih3 F hF, L3_sum_succ (fun i => F (v i) (q i)) m hm, hq0, hF, add_zero]
      · omega
      · omega

theorem L3_output {n : ℕ} (v : Fin n → ℝ) (α : ℝ) :
    ∀ (m : ℕ) (h : m ≤ n),
      (outputPass v α m h).value.size = m ∧
      (∀ (i : ℕ) (hi : i < m), (outputPass v α m h).value[i]? = some (max (v ⟨i, by omega⟩ - α) 0)) ∧
      (outputPass v α m h).steps = 2 + 13 * m := by
  intro m
  induction m with
  | zero => intro h; simp [outputPass]
  | succ m ih =>
    intro h
    obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
    unfold outputPass
    simp only [L1_bind_value, L1_bind_steps, overhead, inputRead, rsub, rlt, L1_pure_value,
      L1_pure_steps]
    refine ⟨by simp [ih1], ?_, by omega⟩
    intro i hi
    rw [Array.getElem?_push]
    by_cases him : i < m
    · rw [if_neg (by omega)]
      exact ih2 i him
    · have him' : i = m := by omega
      subst him'
      rw [if_pos ih1.symm]
      congr 1
      by_cases hp : 0 < v ⟨i, by omega⟩ - α
      · simp [hp, max_eq_left hp.le]
      · simp [hp, max_eq_right (not_lt.1 hp)]

/-- Cell formula for the prefix pass. -/
theorem L3_prefix : ∀ (l : List Row) (a b c : ℝ),
    (prefixPass l a b c).value.length = l.length ∧
    (prefixPass l a b c).steps = 2 + 20 * l.length ∧
    ∀ (j : ℕ) (hj : j < l.length), (prefixPass l a b c).value[j]? = some
      ⟨l[j].v, (l[j + 1]?).map Row.v,
        a + ((l.take (j + 1)).map (fun r => r.q * r.v)).sum,
        b - ((l.take (j + 1)).map (fun r => r.q)).sum,
        c + ((l.take (j + 1)).map (fun r => r.q * (r.v * r.v))).sum⟩ := by
  intro l
  induction l with
  | nil => intro a b c; simp [prefixPass]
  | cons x xs ih =>
    intro a b c
    obtain ⟨ih1, ih2, ih3⟩ := ih (a + x.q * x.v) (b - x.q) (c + x.q * (x.v * x.v))
    unfold prefixPass
    simp only [L1_bind_value, L1_bind_steps, overhead, rmul, radd, rsub, L1_pure_value,
      L1_pure_steps]
    refine ⟨by simp [ih1], by simp only [List.length_cons]; omega, ?_⟩
    intro j hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, List.getElem_cons_zero, zero_add, List.take_succ_cons,
        List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Option.some.injEq]
      cases xs with
      | nil => simp
      | cons y ys => simp
    | succ j =>
      simp only [List.getElem?_cons_succ, List.getElem_cons_succ]
      rw [ih3 j (by simp at hj; omega)]
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, Option.some.injEq,
        Cell.mk.injEq]
      refine ⟨trivial, by simp, by ring, by ring, by ring⟩

end RobustDP.ChiSquareAudit

/-! ## L4: mergesort correctness and cost -/

namespace RobustDP.ChiSquareAudit

open RobustDP.ChiSquare

theorem L4_split : ∀ (N : ℕ) (l : List Row), l.length ≤ N →
    ((splitRows l).value.1 ++ (splitRows l).value.2).Perm l ∧
    (splitRows l).value.1.length = (l.length + 1) / 2 ∧
    (splitRows l).value.2.length = l.length / 2 ∧
    (splitRows l).steps ≤ 4 * l.length + 4 := by
  intro N
  induction N with
  | zero =>
    intro l hl
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [splitRows]
  | succ N ih =>
    intro l hl
    match l with
    | [] => simp [splitRows]
    | [x] => simp [splitRows]
    | x :: y :: xs =>
      obtain ⟨h1, h2, h3, h4⟩ := ih xs (by simp at hl; omega)
      simp only [splitRows, L1_bind_value, L1_bind_steps, overhead, L1_pure_value, L1_pure_steps,
        List.length_cons]
      refine ⟨?_, by simp [h2]; omega, by simp [h3]; omega, by omega⟩
      simp only [List.cons_append]
      exact List.Perm.cons x (List.perm_middle.trans (List.Perm.cons y h1))

theorem L4_merge : ∀ (fuel : ℕ) (xs ys : List Row), xs.length + ys.length ≤ fuel →
    (mergeRows fuel xs ys).value.Perm (xs ++ ys) ∧
    (xs.Pairwise (fun a b => a.v ≤ b.v) → ys.Pairwise (fun a b => a.v ≤ b.v) →
      (mergeRows fuel xs ys).value.Pairwise (fun a b => a.v ≤ b.v)) ∧
    (mergeRows fuel xs ys).steps ≤ 9 * (xs.length + ys.length) + 3 := by
  intro fuel
  induction fuel with
  | zero =>
    intro xs ys h
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx hy
    simp [mergeRows]
  | succ fuel ih =>
    intro xs ys h
    match xs, ys with
    | [], ys => simp [mergeRows]
    | x :: xs, [] => simp [mergeRows]
    | x :: xs, y :: ys =>
      simp only [mergeRows, L1_bind_value, L1_bind_steps, overhead, L1_pure_value, L1_pure_steps,
        List.length_cons]
      simp only [List.length_cons] at h
      by_cases hxy : x.v ≤ y.v
      · have e : (rle x.v y.v).value = true := (L1_rle_value _ _).2 hxy
        simp only [e, ↓reduceIte, L1_bind_value, L1_bind_steps, L1_pure_value, L1_pure_steps]
        obtain ⟨h1, h2, h3⟩ := ih xs (y :: ys) (by simp; omega)
        refine ⟨List.Perm.cons x h1, ?_, ?_⟩
        · intro hxs hys
          rw [List.pairwise_cons]
          refine ⟨?_, h2 (List.pairwise_cons.1 hxs).2 hys⟩
          intro a ha
          rcases List.mem_append.1 (h1.mem_iff.1 ha) with ha | ha
          · exact (List.pairwise_cons.1 hxs).1 a ha
          · rcases List.mem_cons.1 ha with rfl | ha
            · exact hxy
            · exact le_trans hxy ((List.pairwise_cons.1 hys).1 a ha)
        · simp only [List.length_cons] at h3
          simp only [rle]
          omega
      · have e : (rle x.v y.v).value = false := by
          cases hh : (rle x.v y.v).value
          · rfl
          · exact absurd ((L1_rle_value _ _).1 hh) hxy
        simp only [e, Bool.false_eq_true, ↓reduceIte, L1_bind_value, L1_bind_steps, L1_pure_value,
          L1_pure_steps]
        have hyx : y.v ≤ x.v := le_of_lt (not_le.1 hxy)
        obtain ⟨h1, h2, h3⟩ := ih (x :: xs) ys (by simp; omega)
        refine ⟨(List.Perm.cons y h1).trans List.perm_middle.symm, ?_, ?_⟩
        · intro hxs hys
          rw [List.pairwise_cons]
          refine ⟨?_, h2 hxs (List.pairwise_cons.1 hys).2⟩
          intro a ha
          rcases List.mem_append.1 (h1.mem_iff.1 ha) with ha | ha
          · rcases List.mem_cons.1 ha with rfl | ha
            · exact hyx
            · exact le_trans hyx ((List.pairwise_cons.1 hxs).1 a ha)
          · exact (List.pairwise_cons.1 hys).1 a ha
        · simp only [List.length_cons] at h3
          simp only [rle]
          omega

theorem L4_sort : ∀ (fuel : ℕ) (l : List Row), l.length ≤ fuel →
    (sortRows fuel l).value.Perm l ∧ (sortRows fuel l).value.Pairwise (fun a b => a.v ≤ b.v) ∧
    (l.length = 0 → (sortRows fuel l).steps ≤ 3) ∧
    (1 ≤ l.length → (sortRows fuel l).steps + 15 ≤
      13 * (l.length * Nat.clog 2 l.length) + 30 * l.length) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l hl
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [sortRows]
  | succ fuel ih =>
    intro l hl
    match l with
    | [] => simp [sortRows]
    | [x] => simp [sortRows]
    | x :: y :: xs =>
      simp only [List.length_cons] at hl
      obtain ⟨s1, s2, s3, s4⟩ := L4_split (x :: y :: xs).length (x :: y :: xs) le_rfl
      simp only [List.length_cons] at s2 s3 s4
      set h1 := (splitRows (x :: y :: xs)).value.1 with hh1
      set h2 := (splitRows (x :: y :: xs)).value.2 with hh2
      obtain ⟨a1, a2, -, a4⟩ := ih h1 (by omega)
      obtain ⟨b1, b2, -, b4⟩ := ih h2 (by omega)
      set left := (sortRows fuel h1).value with hleft
      set right := (sortRows fuel h2).value with hright
      have hlen1 : left.length = (xs.length + 1 + 1 + 1) / 2 := by rw [a1.length_eq, s2]
      have hlen2 : right.length = (xs.length + 1 + 1) / 2 := by rw [b1.length_eq, s3]
      obtain ⟨m1, m2, m3⟩ := L4_merge (fuel + 1) left right (by omega)
      simp only [sortRows, L1_bind_value, L1_bind_steps, overhead]
      rw [← hh1, ← hh2, ← hleft, ← hright]
      refine ⟨m1.trans ((a1.append b1).trans s1), m2 a2 b2, by simp, ?_⟩
      intro _
      have ha4 := a4 (by omega)
      have hb4 := b4 (by omega)
      rw [hlen1, hlen2] at m3
      rw [s2] at ha4
      rw [s3] at hb4
      set L1 := (xs.length + 1 + 1 + 1) / 2 with hL1
      set L2 := (xs.length + 1 + 1) / 2 with hL2
      have hk : Nat.clog 2 (xs.length + 1 + 1) = Nat.clog 2 L1 + 1 := by
        rw [Nat.clog_of_two_le (by norm_num) (by omega)]
        congr 2
      have hk2 : Nat.clog 2 L2 ≤ Nat.clog 2 L1 := Nat.clog_mono_right 2 (by omega)
      set k := Nat.clog 2 L1
      have p1 : L2 * Nat.clog 2 L2 ≤ L2 * k := Nat.mul_le_mul_left _ hk2
      have p2 : (xs.length + 1 + 1) * (k + 1) = L1 * k + L2 * k + (xs.length + 1 + 1) := by
        have : L1 + L2 = xs.length + 1 + 1 := by omega
        rw [← this]; ring
      simp only [List.length_cons]
      rw [hk, p2]
      omega

end RobustDP.ChiSquareAudit

/-! ## L5: duality for q ≥ 0 over the support ball (generalizes Sol_pv_63fa1f77) -/

namespace RobustDP.ChiSquareAudit

open RobustDP.ChiSquare

noncomputable def L5_H {S : Type*} [Fintype S] (q : S → ℝ) (t : ℝ) (v : S → ℝ) (κ : ℝ) : ℝ :=
  (∑ s, q s * (max (κ - v s) 0) ^ 2) - (1 + t) * (∑ s, q s * max (κ - v s) 0) ^ 2

theorem L5_mem_ball {S : Type*} [Fintype S] (q p : S → ℝ) (t : ℝ) :
    p ∈ supportBall q t ↔ p ∈ stdSimplex ℝ S ∧ (∀ s, q s = 0 → p s = 0) ∧
      (∑ s, if 0 < q s then (p s - q s) ^ 2 / q s else 0) ≤ t := by
  unfold supportBall
  exact Iff.rfl

theorem L5_weak {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S)
    (t : ℝ) (v p : S → ℝ) (hp : p ∈ supportBall q t)
    (μ : S → ℝ) (hμ : 0 ≤ μ) : dualObj q t v μ ≤ expect p v := by
  obtain ⟨⟨hp0, hp1⟩, hpz, hpd⟩ := (L5_mem_ball q p t).1 hp
  obtain ⟨hq0, hq1⟩ := hq
  have h1 : expect p (v - μ) ≤ expect p v := by
    unfold expect
    apply Finset.sum_le_sum
    intro s _
    have := hμ s
    simp only [Pi.sub_apply, Pi.zero_apply] at this ⊢
    nlinarith [hp0 s]
  have h2 : expect p (v - μ) - expect q (v - μ)
      = ∑ s, (p s - q s) * ((v - μ) s - expect q (v - μ)) := by
    have e : ∀ s, (p s - q s) * ((v - μ) s - expect q (v - μ))
        = p s * (v - μ) s - q s * (v - μ) s - expect q (v - μ) * p s + expect q (v - μ) * q s := by
      intro s; ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hp1, hq1]
    unfold expect
    ring
  have hCS : (∑ s, (p s - q s) * ((v - μ) s - expect q (v - μ))) ^ 2
      ≤ (∑ s, if 0 < q s then (p s - q s) ^ 2 / q s else 0) *
        (∑ s, q s * ((v - μ) s - expect q (v - μ)) ^ 2) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun s => if 0 < q s then (p s - q s) / Real.sqrt (q s) else 0)
      (fun s => Real.sqrt (q s) * ((v - μ) s - expect q (v - μ)))
    have ea : ∀ s, (if 0 < q s then (p s - q s) / Real.sqrt (q s) else 0) *
        (Real.sqrt (q s) * ((v - μ) s - expect q (v - μ)))
        = (p s - q s) * ((v - μ) s - expect q (v - μ)) := by
      intro s
      by_cases h : 0 < q s
      · rw [if_pos h]
        have hs := Real.sqrt_pos.2 h
        field_simp
      · rw [if_neg h]
        have h0 : q s = 0 := le_antisymm (not_lt.1 h) (hq0 s)
        rw [hpz s h0, h0]
        simp
    have eb : ∀ s, (if 0 < q s then (p s - q s) / Real.sqrt (q s) else 0) ^ 2
        = (if 0 < q s then (p s - q s) ^ 2 / q s else 0) := by
      intro s
      by_cases h : 0 < q s
      · rw [if_pos h, if_pos h, div_pow, Real.sq_sqrt h.le]
      · rw [if_neg h, if_neg h]; ring
    have ec : ∀ s, (Real.sqrt (q s) * ((v - μ) s - expect q (v - μ))) ^ 2
        = q s * ((v - μ) s - expect q (v - μ)) ^ 2 := by
      intro s; rw [mul_pow, Real.sq_sqrt (hq0 s)]
    simp only [ea, eb, ec] at this
    exact this
  have hV : 0 ≤ ∑ s, q s * ((v - μ) s - expect q (v - μ)) ^ 2 :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (hq0 s) (sq_nonneg _))
  have h3 : (∑ s, (p s - q s) * ((v - μ) s - expect q (v - μ))) ^ 2
      ≤ t * variance q (v - μ) := by
    have hvar : variance q (v - μ) = ∑ s, q s * ((v - μ) s - expect q (v - μ)) ^ 2 := rfl
    rw [hvar]
    exact hCS.trans (mul_le_mul_of_nonneg_right hpd hV)
  have h4 := Real.abs_le_sqrt h3
  have h5 := neg_abs_le (∑ s, (p s - q s) * ((v - μ) s - expect q (v - μ)))
  unfold dualObj
  linarith

/-- The tilted measure `q u / d` lies in the support ball with radius `∑ q u² / d² - 1`. -/
theorem L5_tilt {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S)
    (u : S → ℝ) (hu : ∀ s, 0 ≤ u s) (hd : 0 < ∑ s, q s * u s) (t : ℝ)
    (ht : (∑ s, q s * u s ^ 2) / (∑ s, q s * u s) ^ 2 - 1 ≤ t) :
    (fun s => q s * u s / ∑ s, q s * u s) ∈ supportBall q t := by
  obtain ⟨hq0, hq1⟩ := hq
  rw [L5_mem_ball]
  set d := ∑ s, q s * u s with hdd
  refine ⟨⟨fun s => div_nonneg (mul_nonneg (hq0 s) (hu s)) hd.le, ?_⟩, ?_, ?_⟩
  · rw [← Finset.sum_div, ← hdd]; exact div_self hd.ne'
  · intro s h; simp [h]
  · have e : ∀ s, (if 0 < q s then (q s * u s / d - q s) ^ 2 / q s else 0)
        = (q s * u s ^ 2) / d ^ 2 - 2 * (q s * u s) / d + q s := by
      intro s
      by_cases h : 0 < q s
      · rw [if_pos h]
        have := h.ne'
        field_simp
        ring
      · rw [if_neg h]
        have h0 : q s = 0 := le_antisymm (not_lt.1 h) (hq0 s)
        rw [h0]; ring
    rw [Finset.sum_congr rfl (fun s _ => e s)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
      ← Finset.mul_sum, ← hdd, hq1]
    have : (∑ s, q s * u s ^ 2) / d ^ 2 - 2 * d / d + 1 = (∑ s, q s * u s ^ 2) / d ^ 2 - 1 := by
      rw [mul_div_assoc, div_self hd.ne']; ring
    rw [this]; exact ht

theorem L5_clip_nonneg {S : Type*} (v : S → ℝ) (α : ℝ) : 0 ≤ clippedMultiplier v α :=
  fun s => le_max_right _ _

/-- Active certificate: any `κ > m` with `H κ = 0` gives a primal point of value `g κ`. -/
theorem L5_cert_active {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S)
    (t : ℝ) (ht : 0 ≤ t) (v : S → ℝ) (m : ℝ) (hm1 : ∃ s, 0 < q s ∧ v s = m)
    (κ : ℝ) (hκm : m < κ) (hH : L5_H q t v κ = 0) :
    ∃ p ∈ supportBall q t, expect p v = scalarObjective q t v κ := by
  have hq0 := hq.1
  have hq1 := hq.2
  obtain ⟨s0, hs0q, hs0v⟩ := hm1
  set u : S → ℝ := fun s => max (κ - v s) 0 with hu
  have hu0 : ∀ s, 0 ≤ u s := fun s => le_max_right _ _
  have hd : 0 < ∑ s, q s * u s := by
    apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun s => q s * u s)
      (fun s _ => mul_nonneg (hq0 s) (hu0 s)) (Finset.mem_univ s0))
    apply mul_pos hs0q
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  set d := ∑ s, q s * u s with hdd
  have hHk : (∑ s, q s * u s ^ 2) = (1 + t) * d ^ 2 := by
    have : L5_H q t v κ = (∑ s, q s * u s ^ 2) - (1 + t) * d ^ 2 := rfl
    linarith
  have huv : ∀ s, u s * v s = u s * (κ - u s) := by
    intro s
    by_cases h : v s ≤ κ
    · have : u s = κ - v s := max_eq_left (by linarith)
      rw [this]; ring
    · have : u s = 0 := max_eq_right (by linarith)
      rw [this]; ring
  have hw : (v - clippedMultiplier v κ) = fun s => κ - u s := by
    funext s
    simp only [Pi.sub_apply, hu, clippedMultiplier]
    by_cases h : v s ≤ κ
    · rw [max_eq_right (by linarith : v s - κ ≤ 0), max_eq_left (by linarith : 0 ≤ κ - v s)]
      ring
    · rw [max_eq_left (by linarith : 0 ≤ v s - κ), max_eq_right (by linarith : κ - v s ≤ 0)]
      ring
  have hEw : expect q (fun s => κ - u s) = κ - d := by
    unfold expect
    have e : ∀ s, q s * (κ - u s) = κ * q s - q s * u s := fun s => by ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hq1]; ring
  have hVw : variance q (fun s => κ - u s) = t * d ^ 2 := by
    unfold variance
    rw [hEw]
    have e : ∀ s, q s * (κ - u s - (κ - d)) ^ 2
        = q s * u s ^ 2 - 2 * d * (q s * u s) + d ^ 2 * q s := fun s => by ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hq1, hHk]
    ring
  refine ⟨fun s => q s * u s / d, L5_tilt q hq u hu0 hd t ?_, ?_⟩
  · rw [hHk]
    have hd2 : 0 < d ^ 2 := by positivity
    rw [mul_div_assoc, div_self hd2.ne']; linarith
  · unfold scalarObjective dualObj
    rw [hw, hEw, hVw]
    have hs : Real.sqrt (t * (t * d ^ 2)) = t * d := by
      rw [show t * (t * d ^ 2) = (t * d) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [hs]
    unfold expect
    have e : ∀ s, q s * u s / d * v s = (κ * (q s * u s) - q s * u s ^ 2) / d := by
      intro s
      have := huv s
      field_simp
      linear_combination q s * this
    simp_rw [e]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hdd, hHk]
    field_simp
    ring

/-- At the support minimum the clipped objective equals `m`. -/
theorem L5_obj_min {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S)
    (t : ℝ) (v : S → ℝ) (m : ℝ) (hm2 : ∀ s, 0 < q s → m ≤ v s) :
    scalarObjective q t v m = m := by
  have hq0 := hq.1
  have hq1 := hq.2
  have hw : ∀ s, q s * (v - clippedMultiplier v m) s = q s * m := by
    intro s
    simp only [Pi.sub_apply, clippedMultiplier]
    rcases (hq0 s).eq_or_lt with h | h
    · rw [← h]; ring
    · rw [max_eq_left (by linarith [hm2 s h])]; ring
  have hE : expect q (v - clippedMultiplier v m) = m := by
    unfold expect
    rw [Finset.sum_congr rfl (fun s _ => hw s), ← Finset.sum_mul, hq1, one_mul]
  have hV : variance q (v - clippedMultiplier v m) = 0 := by
    unfold variance
    rw [hE]
    apply Finset.sum_eq_zero
    intro s _
    have := hw s
    rcases (hq0 s).eq_or_lt with h | h
    · rw [← h]; ring
    · have : (v - clippedMultiplier v m) s = m := by
        have := mul_left_cancel₀ h.ne' this
        exact this
      rw [this]; ring
  unfold scalarObjective dualObj
  rw [hE, hV]
  simp

/-- Inactive certificate. -/
theorem L5_cert_inactive {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S)
    (t : ℝ) (v : S → ℝ) (m : ℝ) (hm1 : ∃ s, 0 < q s ∧ v s = m)
    (κ0 : ℝ) (hκ0m : m < κ0) (hκ0v : ∀ s, 0 < q s → v s < κ0 → v s = m)
    (hH0 : L5_H q t v κ0 ≤ 0) :
    ∃ p ∈ supportBall q t, expect p v = m := by
  have hq0 := hq.1
  obtain ⟨s0, hs0q, hs0v⟩ := hm1
  set u : S → ℝ := fun s => max (κ0 - v s) 0 with hu
  have hu0 : ∀ s, 0 ≤ u s := fun s => le_max_right _ _
  have hd : 0 < ∑ s, q s * u s := by
    apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun s => q s * u s)
      (fun s _ => mul_nonneg (hq0 s) (hu0 s)) (Finset.mem_univ s0))
    apply mul_pos hs0q
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have huv : ∀ s, q s * u s * v s = m * (q s * u s) := by
    intro s
    rcases (hq0 s).eq_or_lt with h | h
    · rw [← h]; ring
    · by_cases h' : v s < κ0
      · rw [hκ0v s h h']; ring
      · have : u s = 0 := by simp only [hu]; exact max_eq_right (by linarith)
        rw [this]; ring
  refine ⟨fun s => q s * u s / ∑ s, q s * u s, L5_tilt q hq u hu0 hd t ?_, ?_⟩
  · have hd2 : 0 < (∑ s, q s * u s) ^ 2 := by positivity
    rw [div_sub_one hd2.ne', div_le_iff₀ hd2]
    have : L5_H q t v κ0 = (∑ s, q s * u s ^ 2) - (1 + t) * (∑ s, q s * u s) ^ 2 := rfl
    nlinarith
  · unfold expect
    have e1 : ∀ s, q s * u s / (∑ s, q s * u s) * v s = m * (q s * u s) / ∑ s, q s * u s := by
      intro s; rw [← huv s]; ring
    simp_rw [e1]
    rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc, div_self hd.ne', mul_one]

/-- Duality with a located optimal threshold. -/
theorem L5_dual {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S)
    (t : ℝ) (ht : 0 ≤ t) (v : S → ℝ) (m : ℝ) (hm1 : ∃ s, 0 < q s ∧ v s = m)
    (hm2 : ∀ s, 0 < q s → m ≤ v s) :
    ∃ V : ℝ, IsLeast ((fun p => expect p v) '' supportBall q t) V ∧
      IsGreatest ((fun ν => dualObj q t v ν) '' {ν : S → ℝ | 0 ≤ ν}) V ∧
      (∀ κ, m < κ → L5_H q t v κ = 0 → scalarObjective q t v κ = V) ∧
      ∃ κ, scalarObjective q t v κ = V ∧
        ((∃ s, 0 < q s ∧ v s = κ) ∨ (m < κ ∧ L5_H q t v κ = 0)) := by
  have hq0 := hq.1
  have hq1 := hq.2
  -- a certificate pair
  have key : ∃ p ∈ supportBall q t, ∃ κ, expect p v = scalarObjective q t v κ ∧
      ((∃ s, 0 < q s ∧ v s = κ) ∨ (m < κ ∧ L5_H q t v κ = 0)) := by
    obtain ⟨s0, hs0q, hs0v⟩ := hm1
    have hneU : (Finset.univ : Finset S).Nonempty := ⟨s0, Finset.mem_univ _⟩
    rcases ht.lt_or_eq with htpos | ht0
    swap
    · -- t = 0: p = q, κ = support maximum
      subst ht0
      have hneP : (Finset.univ.filter (fun s => 0 < q s)).Nonempty :=
        ⟨s0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs0q⟩⟩
      obtain ⟨s1, hs1, hmax⟩ := Finset.exists_max_image _ v hneP
      have hs1q : 0 < q s1 := (Finset.mem_filter.1 hs1).2
      refine ⟨q, ?_, v s1, ?_, Or.inl ⟨s1, hs1q, rfl⟩⟩
      · rw [L5_mem_ball]
        refine ⟨hq, fun s h => h, ?_⟩
        simp
      · unfold scalarObjective dualObj
        simp only [zero_mul, Real.sqrt_zero, sub_zero]
        unfold expect
        apply Finset.sum_congr rfl
        intro s _
        simp only [Pi.sub_apply, clippedMultiplier]
        rcases (hq0 s).eq_or_lt with h | h
        · rw [← h]; ring
        · have := hmax s (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
          rw [max_eq_right (by linarith)]; ring
    set κ0 := Finset.univ.inf' hneU (fun s => if 0 < q s ∧ m < v s then v s else m + 1) with hκ0
    have hκ0m : m < κ0 := by
      rw [hκ0, Finset.lt_inf'_iff]
      intro s _
      split_ifs with h
      · exact h.2
      · linarith
    have hκ0v : ∀ s, 0 < q s → v s < κ0 → v s = m := by
      intro s hs hlt
      by_contra hne
      have h' : m < v s := lt_of_le_of_ne (hm2 s hs) (Ne.symm hne)
      have := Finset.inf'_le (fun s => if 0 < q s ∧ m < v s then v s else m + 1)
        (Finset.mem_univ s)
      rw [← hκ0, if_pos ⟨hs, h'⟩] at this
      linarith
    by_cases hH0 : L5_H q t v κ0 ≤ 0
    · obtain ⟨p, hp, hpv⟩ := L5_cert_inactive q hq t v m ⟨s0, hs0q, hs0v⟩ κ0 hκ0m hκ0v hH0
      exact ⟨p, hp, m, by rw [hpv, L5_obj_min q hq t v m hm2], Or.inl ⟨s0, hs0q, hs0v⟩⟩
    · rw [not_le] at hH0
      set M := Finset.univ.sup' hneU v with hM
      have hMge : ∀ s, v s ≤ M := fun s => Finset.le_sup' _ (Finset.mem_univ s)
      set D := M - m with hD
      have hD0 : 0 ≤ D := by have := hMge s0; linarith
      set x := (2 * D + D ^ 2 + 1) / t + 1 with hx
      set κ2 := max κ0 M + x with hκ2
      have hx1 : 1 ≤ x := by
        have : 0 ≤ (2 * D + D ^ 2 + 1) / t := by positivity
        linarith
      have htx : 2 * D + D ^ 2 + 1 ≤ t * x := by
        rw [hx, mul_add, mul_div_cancel₀ _ htpos.ne']; linarith
      have hκ2le : κ0 ≤ κ2 := by
        have := le_max_left κ0 M; linarith
      have hH2 : L5_H q t v κ2 ≤ 0 := by
        set y := κ2 - M with hy
        have hyx : x ≤ y := by have := le_max_right κ0 M; linarith
        have hmx : ∀ s, max (κ2 - v s) 0 = κ2 - v s := fun s =>
          max_eq_left (by have := hMge s; linarith)
        have hA : ∑ s, q s * (max (κ2 - v s) 0) ^ 2 ≤ (y + D) ^ 2 := by
          calc ∑ s, q s * (max (κ2 - v s) 0) ^ 2 ≤ ∑ s, q s * (y + D) ^ 2 := by
                apply Finset.sum_le_sum; intro s _
                rcases (hq0 s).eq_or_lt with h | h
                · rw [← h]; simp
                apply mul_le_mul_of_nonneg_left _ (hq0 s)
                rw [hmx s]
                have := hMge s; have := hm2 s h
                apply pow_le_pow_left₀ (by linarith) (by linarith)
            _ = (y + D) ^ 2 := by rw [← Finset.sum_mul, hq1, one_mul]
        have hB : y ≤ ∑ s, q s * max (κ2 - v s) 0 := by
          calc y = ∑ s, q s * y := by rw [← Finset.sum_mul, hq1, one_mul]
            _ ≤ ∑ s, q s * max (κ2 - v s) 0 := by
                apply Finset.sum_le_sum; intro s _
                rw [hmx s]
                apply mul_le_mul_of_nonneg_left _ (hq0 s)
                have := hMge s; linarith
        have hy0 : 0 ≤ y := by linarith
        have hB2 : y ^ 2 ≤ (∑ s, q s * max (κ2 - v s) 0) ^ 2 := pow_le_pow_left₀ hy0 hB 2
        have hty : 2 * D + D ^ 2 + 1 ≤ t * y :=
          le_trans htx (mul_le_mul_of_nonneg_left hyx htpos.le)
        have key : (y + D) ^ 2 ≤ (1 + t) * y ^ 2 := by nlinarith
        show (∑ s, q s * (max (κ2 - v s) 0) ^ 2)
          - (1 + t) * (∑ s, q s * max (κ2 - v s) 0) ^ 2 ≤ 0
        nlinarith
      have hcont : ContinuousOn (L5_H q t v) (Set.Icc κ0 κ2) := by
        apply Continuous.continuousOn
        unfold L5_H
        fun_prop
      obtain ⟨κ, ⟨hκlo, -⟩, hκ⟩ :=
        intermediate_value_Icc' hκ2le hcont ⟨hH2, hH0.le⟩
      have hκm : m < κ := lt_of_lt_of_le hκ0m hκlo
      obtain ⟨p, hp, hpv⟩ := L5_cert_active q hq t ht v m ⟨s0, hs0q, hs0v⟩ κ hκm hκ
      exact ⟨p, hp, κ, hpv, Or.inr ⟨hκm, hκ⟩⟩
  obtain ⟨p, hp, κ, hpκ, hgood⟩ := key
  refine ⟨expect p v, ⟨⟨p, hp, rfl⟩, ?_⟩, ⟨⟨clippedMultiplier v κ, L5_clip_nonneg v κ, ?_⟩, ?_⟩,
    ?_, κ, hpκ.symm, hgood⟩
  · rintro _ ⟨p', hp', rfl⟩
    rw [hpκ]
    exact L5_weak q hq t v p' hp' _ (L5_clip_nonneg v κ)
  · exact hpκ.symm
  · rintro _ ⟨μ', hμ', rfl⟩
    exact L5_weak q hq t v p hp μ' hμ'
  · intro κ' hκ' hH'
    obtain ⟨p', hp', hp'v⟩ := L5_cert_active q hq t ht v m hm1 κ' hκ' hH'
    apply le_antisymm
    · exact L5_weak q hq t v p hp _ (L5_clip_nonneg v κ')
    · rw [← hp'v, hpκ]
      exact L5_weak q hq t v p' hp' _ (L5_clip_nonneg v κ)

end RobustDP.ChiSquareAudit

/-! ## L6: the support ball, the extended divergence and the ordinary chi-square set -/

namespace RobustDP.ChiSquareAudit

open RobustDP.ChiSquare

theorem L6_ext_eq {S : Type*} [Fintype S] (p q : S → ℝ) (hq0 : ∀ s, 0 ≤ q s)
    (hz : ∀ s, q s = 0 → p s = 0) :
    extendedDistance p q = ENNReal.ofReal (∑ s, if 0 < q s then (p s - q s) ^ 2 / q s else 0) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => by
    split_ifs with h
    · exact div_nonneg (sq_nonneg _) h.le
    · exact le_rfl)]
  unfold extendedDistance
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : q s = 0
  · rw [if_pos h, if_pos (hz s h), if_neg (by rw [h]; exact lt_irrefl 0)]
    simp
  · rw [if_neg h, if_pos (lt_of_le_of_ne (hq0 s) (Ne.symm h))]

theorem L6_ball_iff {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S)
    (t : ℝ) (ht : 0 ≤ t) (p : S → ℝ) :
    p ∈ supportBall q t ↔ p ∈ stdSimplex ℝ S ∧ extendedDistance p q ≤ ENNReal.ofReal t := by
  constructor
  · intro hp
    obtain ⟨hs, hz, hd⟩ := (L5_mem_ball q p t).1 hp
    refine ⟨hs, ?_⟩
    rw [L6_ext_eq p q hq.1 hz]
    exact ENNReal.ofReal_le_ofReal hd
  · rintro ⟨hs, hd⟩
    have hz : ∀ s, q s = 0 → p s = 0 := by
      intro s hqs
      by_contra hps
      have htop : extendedDistance p q = ⊤ := by
        unfold extendedDistance
        exact ENNReal.sum_eq_top.2 ⟨s, Finset.mem_univ _, by rw [if_pos hqs, if_neg hps]⟩
      rw [htop, top_le_iff] at hd
      exact ENNReal.ofReal_ne_top hd
    rw [L6_ext_eq p q hq.1 hz, ENNReal.ofReal_le_ofReal_iff ht] at hd
    exact (L5_mem_ball q p t).2 ⟨hs, hz, hd⟩

theorem L6_ball_chiSq {S : Type*} [Fintype S] (q : S → ℝ) (t : ℝ) (hpos : ∀ s, 0 < q s) :
    supportBall q t = chiSqSet q t := by
  ext p
  rw [L5_mem_ball]
  have e : (∑ s, if 0 < q s then (p s - q s) ^ 2 / q s else 0) = chiSqDist p q :=
    Finset.sum_congr rfl (fun s _ => if_pos (hpos s))
  rw [e]
  constructor
  · rintro ⟨hs, -, hd⟩
    exact ⟨hs, hd⟩
  · rintro ⟨hs, hd⟩
    exact ⟨hs, fun s h => absurd h (hpos s).ne', hd⟩

end RobustDP.ChiSquareAudit

/-! ## L7: cell validity on the sorted support list and location of the optimal threshold -/

namespace RobustDP.ChiSquareAudit

open RobustDP.ChiSquare

noncomputable def L7_sQ (l : List Row) : ℝ := (l.map (fun r => r.q)).sum
noncomputable def L7_sA (l : List Row) : ℝ := (l.map (fun r => r.q * r.v)).sum
noncomputable def L7_sC (l : List Row) : ℝ := (l.map (fun r => r.q * (r.v * r.v))).sum

theorem L7_sq_expand (l : List Row) (x : ℝ) :
    (l.map (fun r => r.q * (x - r.v) ^ 2)).sum = x ^ 2 * L7_sQ l - 2 * x * L7_sA l + L7_sC l := by
  induction l with
  | nil => simp [L7_sQ, L7_sA, L7_sC]
  | cons r l ih =>
    simp only [List.map_cons, List.sum_cons, L7_sQ, L7_sA, L7_sC] at ih ⊢
    rw [ih]; ring

theorem L7_lin_expand (l : List Row) (x : ℝ) :
    (l.map (fun r => r.q * (x - r.v))).sum = x * L7_sQ l - L7_sA l := by
  induction l with
  | nil => simp [L7_sQ, L7_sA]
  | cons r l ih =>
    simp only [List.map_cons, List.sum_cons, L7_sQ, L7_sA] at ih ⊢
    rw [ih]; ring

theorem L7_split (l : List Row) (k : ℕ) (φ ψ : ℝ → ℝ) (x : ℝ)
    (h1 : ∀ r ∈ l.take k, φ r.v = ψ r.v) (h2 : ∀ r ∈ l.drop k, φ r.v = φ x) :
    (l.map (fun r => r.q * φ r.v)).sum
      = ((l.take k).map (fun r => r.q * ψ r.v)).sum + φ x * L7_sQ (l.drop k) := by
  conv_lhs => rw [← List.take_append_drop k l]
  rw [List.map_append, List.sum_append]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro r hr
    rw [h1 r hr]
  · rw [List.map_congr_left (g := fun r => r.q * φ x) (fun r hr => by rw [h2 r hr])]
    unfold L7_sQ
    rw [List.sum_map_mul_right]
    ring

theorem L7_take_le (l : List Row) (hs : l.Pairwise (fun a b => a.v ≤ b.v)) (j : ℕ)
    (hj : j < l.length) : ∀ r ∈ l.take (j + 1), r.v ≤ l[j].v := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  simp only [List.getElem_take]
  have hi' : i ≤ j := by simp at hi; omega
  rcases hi'.lt_or_eq with h | h
  · exact List.pairwise_iff_getElem.1 hs i j (by omega) hj h
  · subst h; exact le_rfl

theorem L7_drop_ge (l : List Row) (hs : l.Pairwise (fun a b => a.v ≤ b.v)) (j : ℕ)
    (hj : j + 1 < l.length) : ∀ r ∈ l.drop (j + 1), l[j + 1].v ≤ r.v := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  simp only [List.getElem_drop]
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp
  · exact List.pairwise_iff_getElem.1 hs (j + 1) (j + 1 + i) hj (by simp at hi; omega) (by omega)

theorem L7_valid {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S) (t : ℝ)
    (v : S → ℝ) (ls : List Row) (hs : ls.Pairwise (fun a b => a.v ≤ b.v))
    (hsum : ∀ φ : ℝ → ℝ, (ls.map (fun r => r.q * φ r.v)).sum = ∑ s, q s * φ (v s))
    (j : ℕ) (hj : j < ls.length) (x : ℝ) (hlow : ls[j].v ≤ x)
    (hhigh : ∀ h : j + 1 < ls.length, x ≤ ls[j + 1].v) :
    scalarObjective q t v x = intervalObjective t (L7_sA (ls.take (j + 1)))
      (1 - L7_sQ (ls.take (j + 1))) (L7_sC (ls.take (j + 1))) x ∧
    L5_H q t v x = (x ^ 2 * L7_sQ (ls.take (j + 1)) - 2 * x * L7_sA (ls.take (j + 1))
      + L7_sC (ls.take (j + 1))) - (1 + t) * (x * L7_sQ (ls.take (j + 1))
      - L7_sA (ls.take (j + 1))) ^ 2 := by
  have hT1 : ∀ r ∈ ls.take (j + 1), r.v ≤ x := fun r hr => le_trans (L7_take_le ls hs j hj r hr) hlow
  have hD1 : ∀ r ∈ ls.drop (j + 1), x ≤ r.v := by
    intro r hr
    by_cases h : j + 1 < ls.length
    · exact le_trans (hhigh h) (L7_drop_ge ls hs j h r hr)
    · have : ls.drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
      rw [this] at hr; simp at hr
  have htot : L7_sQ (ls.take (j + 1)) + L7_sQ (ls.drop (j + 1)) = 1 := by
    have h1 := hsum (fun _ => 1)
    simp only [mul_one] at h1
    rw [hq.2] at h1
    unfold L7_sQ
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
    exact h1
  have hdrop : L7_sQ (ls.drop (j + 1)) = 1 - L7_sQ (ls.take (j + 1)) := by linarith
  have hw : ∀ s, (v - clippedMultiplier v x) s = min (v s) x := by
    intro s
    simp only [Pi.sub_apply, clippedMultiplier]
    rcases le_total (v s) x with h | h
    · rw [max_eq_right (by linarith), min_eq_left h]; ring
    · rw [max_eq_left (by linarith), min_eq_right h]; ring
  have hE : expect q (v - clippedMultiplier v x)
      = L7_sA (ls.take (j + 1)) + (1 - L7_sQ (ls.take (j + 1))) * x := by
    unfold expect
    simp_rw [hw]
    rw [← hsum (fun y => min y x), L7_split ls (j + 1) (fun y => min y x) (fun y => y) x
      (fun r hr => min_eq_left (hT1 r hr)) (fun r hr => by
        simp only [min_self]; exact min_eq_right (hD1 r hr)), hdrop, min_self]
    unfold L7_sA
    ring
  have hM2 : ∑ s, q s * (v - clippedMultiplier v x) s ^ 2
      = L7_sC (ls.take (j + 1)) + (1 - L7_sQ (ls.take (j + 1))) * x ^ 2 := by
    simp_rw [hw]
    rw [← hsum (fun y => (min y x) ^ 2), L7_split ls (j + 1) (fun y => (min y x) ^ 2)
      (fun y => y * y) x
      (fun r hr => by rw [min_eq_left (hT1 r hr)]; ring) (fun r hr => by
        simp only [min_self]; rw [min_eq_right (hD1 r hr)]), hdrop, min_self]
    unfold L7_sC
    ring
  have hvar_id : variance q (v - clippedMultiplier v x)
      = (∑ s, q s * (v - clippedMultiplier v x) s ^ 2) - (expect q (v - clippedMultiplier v x)) ^ 2 := by
    unfold variance
    set E := expect q (v - clippedMultiplier v x) with hEdef
    have e : ∀ s, q s * ((v - clippedMultiplier v x) s - E) ^ 2
        = q s * (v - clippedMultiplier v x) s ^ 2
          - 2 * E * (q s * (v - clippedMultiplier v x) s) + E ^ 2 * q s := fun s => by ring
    rw [Finset.sum_congr rfl (fun s _ => e s), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hq.2]
    have : ∑ s, q s * (v - clippedMultiplier v x) s = E := rfl
    rw [this]
    ring
  constructor
  · have hVar : variance q (v - clippedMultiplier v x) = intervalVariance (L7_sA (ls.take (j + 1)))
        (1 - L7_sQ (ls.take (j + 1))) (L7_sC (ls.take (j + 1))) x := by
      rw [hvar_id, hM2, hE]
      unfold intervalVariance
      ring
    unfold scalarObjective dualObj intervalObjective
    rw [hE, hVar]
  · unfold L5_H
    have hA : ∑ s, q s * (max (x - v s) 0) ^ 2 = ((ls.take (j + 1)).map
        (fun r : Row => r.q * (x - r.v) ^ 2)).sum := by
      rw [← hsum (fun y => (max (x - y) 0) ^ 2), L7_split ls (j + 1) (fun y => (max (x - y) 0) ^ 2)
        (fun y => (x - y) ^ 2) x
        (fun r hr => by rw [max_eq_left (by linarith [hT1 r hr])]) (fun r hr => by
          simp only [sub_self, max_self]; rw [max_eq_right (by linarith [hD1 r hr])])]
      simp
    have hB : ∑ s, q s * max (x - v s) 0 = ((ls.take (j + 1)).map
        (fun r : Row => r.q * (x - r.v))).sum := by
      rw [← hsum (fun y => max (x - y) 0), L7_split ls (j + 1) (fun y => max (x - y) 0)
        (fun y => x - y) x
        (fun r hr => by rw [max_eq_left (by linarith [hT1 r hr])]) (fun r hr => by
          simp only [sub_self, max_self]; rw [max_eq_right (by linarith [hD1 r hr])])]
      simp
    rw [hA, hB, L7_sq_expand, L7_lin_expand]

theorem L7_cell (ls : List Row) (j : ℕ) (hj : j < ls.length) :
    (prefixPass ls 0 1 0).value[j]? = some ⟨ls[j].v, (ls[j + 1]?).map Row.v,
      L7_sA (ls.take (j + 1)), 1 - L7_sQ (ls.take (j + 1)), L7_sC (ls.take (j + 1))⟩ := by
  rw [(L3_prefix ls 0 1 0).2.2 j hj]
  simp [L7_sA, L7_sQ, L7_sC]

theorem L7_mem_cells (ls : List Row) (cell : Cell) (h : cell ∈ (prefixPass ls 0 1 0).value) :
    ∃ j, ∃ hj : j < ls.length, cell = ⟨ls[j].v, (ls[j + 1]?).map Row.v,
      L7_sA (ls.take (j + 1)), 1 - L7_sQ (ls.take (j + 1)), L7_sC (ls.take (j + 1))⟩ := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
  have hjl : j < ls.length := by
    rw [← (L3_prefix ls 0 1 0).1]
    exact (List.getElem?_eq_some_iff.1 hj).1
  refine ⟨j, hjl, ?_⟩
  rw [L7_cell ls j hjl] at hj
  exact (Option.some.inj hj).symm

theorem L7_cands_valid {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S) (t : ℝ)
    (v : S → ℝ) (ls : List Row) (hs : ls.Pairwise (fun a b => a.v ≤ b.v))
    (hsum : ∀ φ : ℝ → ℝ, (ls.map (fun r => r.q * φ r.v)).sum = ∑ s, q s * φ (v s)) :
    ∀ cell ∈ (prefixPass ls 0 1 0).value, ∀ x ∈ L2_cands t cell,
      L2_f t cell x = scalarObjective q t v x := by
  intro cell hcell x hx
  obtain ⟨j, hj, rfl⟩ := L7_mem_cells ls cell hcell
  have key : ls[j].v ≤ x ∧ ∀ h : j + 1 < ls.length, x ≤ ls[j + 1].v := by
    rcases hx with hx | ⟨h, hh, -, -, hlx, hxh⟩
    · simp only at hx
      subst hx
      refine ⟨le_rfl, fun h => List.pairwise_iff_getElem.1 hs j (j + 1) hj h (by omega)⟩
    · simp only at hh hlx
      refine ⟨hlx.le, fun h' => ?_⟩
      rw [List.getElem?_eq_getElem h'] at hh
      simp only [Option.map_some, Option.some.injEq] at hh
      rw [hh]; exact hxh.le
  rw [(L7_valid q hq t v ls hs hsum j hj x key.1 key.2).1]
  rfl

theorem L7_locate {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S) (t : ℝ)
    (v : S → ℝ) (ls : List Row) (hs : ls.Pairwise (fun a b => a.v ≤ b.v))
    (hpos : ∀ r ∈ ls, 0 < r.q)
    (hsum : ∀ φ : ℝ → ℝ, (ls.map (fun r => r.q * φ r.v)).sum = ∑ s, q s * φ (v s))
    (hne : 0 < ls.length) (V : ℝ)
    (hV : ∀ κ', ls[0].v < κ' → L5_H q t v κ' = 0 → scalarObjective q t v κ' = V)
    (κ : ℝ) (hκV : scalarObjective q t v κ = V)
    (hgood : (∃ r ∈ ls, r.v = κ) ∨ (ls[0].v < κ ∧ L5_H q t v κ = 0)) :
    ∃ cell ∈ (prefixPass ls 0 1 0).value, ∃ x ∈ L2_cands t cell, V ≤ L2_f t cell x := by
  have hvalid := L7_cands_valid q hq t v ls hs hsum
  -- cell j as a member, with its low as a candidate
  have hmem : ∀ j (hj : j < ls.length), (⟨ls[j].v, (ls[j + 1]?).map Row.v,
      L7_sA (ls.take (j + 1)), 1 - L7_sQ (ls.take (j + 1)), L7_sC (ls.take (j + 1))⟩ : Cell)
      ∈ (prefixPass ls 0 1 0).value := fun j hj => List.mem_of_getElem? (L7_cell ls j hj)
  have hlowc : ∀ j (hj : j < ls.length), V = scalarObjective q t v ls[j].v →
      ∃ cell ∈ (prefixPass ls 0 1 0).value, ∃ x ∈ L2_cands t cell, V ≤ L2_f t cell x := by
    intro j hj hVj
    refine ⟨_, hmem j hj, ls[j].v, Or.inl rfl, ?_⟩
    rw [hvalid _ (hmem j hj) _ (Or.inl rfl), hVj]
  rcases hgood with ⟨r, hr, hrκ⟩ | ⟨hmκ, hHκ⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hr
    exact hlowc j hj (by rw [hrκ, hκV])
  · -- the cell containing κ
    have hex : ∃ j, j + 1 < ls.length → κ < ls[j + 1]!.v := ⟨ls.length, fun h => by omega⟩
    classical
    let j := Nat.find hex
    have hjP : j + 1 < ls.length → κ < ls[j + 1]!.v := Nat.find_spec hex
    have hjL : j < ls.length := by
      by_contra hc
      have := Nat.find_min' hex (m := ls.length - 1) (fun h => by omega)
      omega
    have hlow : ls[j].v ≤ κ := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos'
      · have : ls[j].v = ls[0].v := by simp only [h0]
        rw [this]; exact hmκ.le
      · have hmin := Nat.find_min hex (m := j - 1) (by omega)
        push_neg at hmin
        obtain ⟨h1, h2⟩ := hmin
        have e : j - 1 + 1 = j := by omega
        simp only [e] at h2
        rw [getElem!_pos ls j hjL] at h2
        exact h2
    rcases eq_or_lt_of_le hlow with heq | hlt
    · exact hlowc j hjL (by rw [heq, hκV])
    by_cases hlast : j + 1 < ls.length
    · have hκh : κ < ls[j + 1].v := by
        have := hjP hlast
        rwa [getElem!_pos ls (j + 1) hlast] at this
      obtain ⟨hgκ, hHκ'⟩ := L7_valid q hq t v ls hs hsum j hjL κ hlow (fun _ => hκh.le)
      set cell : Cell := ⟨ls[j].v, (ls[j + 1]?).map Row.v,
        L7_sA (ls.take (j + 1)), 1 - L7_sQ (ls.take (j + 1)), L7_sC (ls.take (j + 1))⟩ with hcell
      have hhigh : cell.high = some ls[j + 1].v := by
        simp only [hcell, List.getElem?_eq_getElem hlast, Option.map_some]
      have hP : ∀ y, stationaryPolynomial t cell.a cell.b cell.c y
          = (1 - L7_sQ (ls.take (j + 1))) ^ 2 * ((y ^ 2 * L7_sQ (ls.take (j + 1))
            - 2 * y * L7_sA (ls.take (j + 1)) + L7_sC (ls.take (j + 1)))
            - (1 + t) * (y * L7_sQ (ls.take (j + 1)) - L7_sA (ls.take (j + 1))) ^ 2) := by
        intro y
        simp only [hcell]
        unfold stationaryPolynomial intervalVariance
        ring
      have hPκ : (coefficients t cell).value.1 * κ ^ 2 + (coefficients t cell).value.2.1 * κ
          + (coefficients t cell).value.2.2 = 0 := by
        rw [L1_coeff_poly, hP, ← hHκ', hHκ, mul_zero]
      by_cases hAB : (coefficients t cell).value.1 = 0 ∧ (coefficients t cell).value.2.1 = 0
      · -- degenerate: the polynomial vanishes identically, so H vanishes at the next breakpoint
        have hD : (coefficients t cell).value.2.2 = 0 := by
          rw [hAB.1, hAB.2] at hPκ; linarith
        set h := ls[j + 1].v with hh
        have hjL' : j + 1 < ls.length := hlast
        obtain ⟨-, hHh⟩ := L7_valid q hq t v ls hs hsum j hjL h (le_of_lt (lt_trans hlt hκh))
          (fun _ => le_rfl)
        have hPh : stationaryPolynomial t cell.a cell.b cell.c h = 0 := by
          rw [← L1_coeff_poly, hAB.1, hAB.2, hD]; ring
        rw [hP, ← hHh] at hPh
        have hb : 0 < 1 - L7_sQ (ls.take (j + 1)) := by
          have htot : L7_sQ (ls.take (j + 1)) + L7_sQ (ls.drop (j + 1)) = 1 := by
            have h1 := hsum (fun _ => 1)
            simp only [mul_one] at h1
            rw [hq.2] at h1
            unfold L7_sQ
            rw [← List.sum_append, ← List.map_append, List.take_append_drop]
            exact h1
          have hpos2 : 0 < L7_sQ (ls.drop (j + 1)) := by
            unfold L7_sQ
            apply List.sum_pos
            · intro y hy
              obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
              exact hpos r (List.mem_of_mem_drop hr)
            · simp only [ne_eq, List.map_eq_nil_iff, List.drop_eq_nil_iff, not_le]
              exact hlast
          linarith
        have hH0 : L5_H q t v h = 0 := (mul_eq_zero.1 hPh).resolve_left (pow_ne_zero 2 hb.ne')
        have hm0 : ls[0].v < h := lt_trans hmκ hκh
        exact hlowc (j + 1) hlast (by rw [hV h hm0 hH0])
      · refine ⟨cell, hmem j hjL, κ, Or.inr ⟨ls[j + 1].v, hhigh, lt_trans hlt hκh,
          L1_quad_mem _ _ _ κ hPκ hAB, hlt, hκh⟩, ?_⟩
        rw [hvalid cell (hmem j hjL) κ (Or.inr ⟨ls[j + 1].v, hhigh, lt_trans hlt hκh,
          L1_quad_mem _ _ _ κ hPκ hAB, hlt, hκh⟩), hκV]
    · -- last cell: the objective is constant beyond the maximum
      have hall : ls.take (j + 1) = ls := List.take_of_length_le (by omega)
      have hQ1 : L7_sQ (ls.take (j + 1)) = 1 := by
        rw [hall]
        have h1 := hsum (fun _ => 1)
        simp only [mul_one] at h1
        rw [hq.2] at h1
        exact h1
      obtain ⟨hgκ, -⟩ := L7_valid q hq t v ls hs hsum j hjL κ hlow (fun h => absurd h hlast)
      obtain ⟨hgl, -⟩ := L7_valid q hq t v ls hs hsum j hjL ls[j].v le_rfl
        (fun h => absurd h hlast)
      apply hlowc j hjL
      rw [← hκV, hgκ, hgl, hQ1]
      unfold intervalObjective intervalVariance
      ring_nf

end RobustDP.ChiSquareAudit

open RobustDP.ChiSquareAudit RobustDP.ChiSquare in
theorem solution :
    ∃ C n₀ : ℕ, 0 < C ∧ n₀ = 0 ∧
    ∀ {S : Type} [Fintype S] (q : S → ℝ), q ∈ stdSimplex ℝ S →
      ∀ (t : ℝ), 0 ≤ t → ∀ (v : S → ℝ)
        (e : Fin (Fintype.card S) ≃ S),
      let n := Fintype.card S
      let execution := solve n (q ∘ e) t (v ∘ e)
      let out := execution.value
      let μ : S → ℝ := fun s => answerMultiplier (n := n) out (e.symm s)
      out.multiplier.size = n ∧
      μ = clippedMultiplier v out.best.alpha ∧ (∀ s, 0 ≤ μ s) ∧
      out.best.val = dualObj q t v μ ∧
      IsLeast ((fun p => expect p v) '' supportBall q t) out.best.val ∧
      IsGreatest ((fun ν => dualObj q t v ν) '' {ν : S → ℝ | 0 ≤ ν}) out.best.val ∧
      (∀ p : S → ℝ, p ∈ supportBall q t ↔
        p ∈ stdSimplex ℝ S ∧ extendedDistance p q ≤ ENNReal.ofReal t) ∧
      ((∀ s, 0 < q s) → supportBall q t = chiSqSet q t) ∧
      execution.steps ≤ 512 * (n + 1) * (1 + sortingLevels n) ∧
      (n₀ ≤ n → execution.steps ≤ C * (n + 1) * (1 + sortingLevels n)) := by
  refine ⟨512, 0, by norm_num, rfl, ?_⟩
  intro S _ q hq t ht v e
  intro n execution out μ
  have hq0 : ∀ s, 0 ≤ q s := hq.1
  have hq'0 : ∀ i, 0 ≤ (q ∘ e) i := fun i => hq0 (e i)
  obtain ⟨sp1, sp2, sp3, sp4, sp5⟩ := L3_support (q ∘ e) (v ∘ e) hq'0 n le_rfl
  set l0 := (supportPass (q ∘ e) (v ∘ e) n le_rfl).value with hl0
  obtain ⟨so1, so2, so3, so4⟩ := L4_sort n l0 sp4
  set ls := (sortRows n l0).value with hls
  have hlen : ls.length = l0.length := so1.length_eq
  obtain ⟨pp1, pp2, -⟩ := L3_prefix ls 0 1 0
  set cells := (prefixPass ls 0 1 0).value with hcells
  obtain ⟨s0, hs0⟩ : ∃ s, 0 < q s := by
    by_contra h
    push_neg at h
    have h1 : ∑ s, q s = 0 := Finset.sum_eq_zero (fun s _ => le_antisymm (h s) (hq0 s))
    have h2 : ∑ s, q s = 1 := hq.2
    linarith
  have hsum : ∀ φ : ℝ → ℝ, (ls.map (fun r => r.q * φ r.v)).sum = ∑ s, q s * φ (v s) := by
    intro φ
    rw [(so1.map _).sum_eq]
    have h3 := sp3 (fun x y => y * φ x) (fun x => zero_mul _)
    try simp only at h3
    rw [h3, Finset.sum_congr rfl (fun i _ => if_pos i.isLt)]
    exact Equiv.sum_comp e (fun s => q s * φ (v s))
  have hls_mem : ∀ r ∈ ls, 0 < r.q ∧ ∃ s, 0 < q s ∧ r.v = v s := by
    intro r hr
    obtain ⟨h1, i, -, h2, h3⟩ := sp1 r (so1.mem_iff.1 hr)
    refine ⟨h1, e i, ?_, h2⟩
    have : r.q = q (e i) := h3
    rw [← this]; exact h1
  have hls_cover : ∀ s, 0 < q s → ∃ r ∈ ls, r.v = v s := by
    intro s hs
    obtain ⟨r, hr, hrv⟩ := sp2 (e.symm s) (e.symm s).isLt (by simpa using hs)
    exact ⟨r, so1.mem_iff.2 hr, by rw [hrv]; simp⟩
  have hLpos : 0 < ls.length := by
    obtain ⟨r, hr, -⟩ := hls_cover s0 hs0
    exact List.length_pos_of_mem hr
  have hm1 : ∃ s, 0 < q s ∧ v s = ls[0].v := by
    obtain ⟨-, s, hs, hv⟩ := hls_mem ls[0] (List.getElem_mem _)
    exact ⟨s, hs, hv.symm⟩
  have hm2 : ∀ s, 0 < q s → ls[0].v ≤ v s := by
    intro s hs
    obtain ⟨r, hr, hrv⟩ := hls_cover s hs
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hr
    rw [← hrv]
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact le_rfl
    · exact List.pairwise_iff_getElem.1 so2 0 k hLpos hk h
  obtain ⟨V, hLeast, hGreat, hHV, κ, hκV, hgood⟩ := L5_dual q hq t ht v ls[0].v hm1 hm2
  have hgood' : (∃ r ∈ ls, r.v = κ) ∨ (ls[0].v < κ ∧ L5_H q t v κ = 0) := by
    rcases hgood with ⟨s, hs, hsv⟩ | h
    · obtain ⟨r, hr, hrv⟩ := hls_cover s hs
      exact Or.inl ⟨r, hr, by rw [hrv, hsv]⟩
    · exact Or.inr h
  obtain ⟨cellA, hcellA, xA, hxA, hVle⟩ := L7_locate q hq t v ls so2
    (fun r hr => (hls_mem r hr).1) hsum hLpos V hHV κ hκV hgood'
  have hcne : cells ≠ [] := List.ne_nil_of_length_pos (by rw [pp1]; exact hLpos)
  obtain ⟨b, hb, -, hdom, horig⟩ := L2_scanPass t cells none (Or.inl hcne)
  have hvalid := L7_cands_valid q hq t v ls so2 hsum
  have hbα : b.val = scalarObjective q t v b.alpha := by
    rcases horig with ⟨cell, hcell, x, hx, rfl⟩ | h
    · exact hvalid cell hcell x hx
    · cases h
  have hbV : b.val = V := by
    apply le_antisymm
    · rw [hbα]
      exact hGreat.2 ⟨clippedMultiplier v b.alpha, L5_clip_nonneg v b.alpha, rfl⟩
    · exact le_trans hVle (hdom cellA hcellA xA hxA)
  have hout : out = ⟨b, (outputPass (v ∘ e) b.alpha n le_rfl).value⟩ := by
    show (solve n (q ∘ e) t (v ∘ e)).value = _
    simp only [solve, L1_bind_value, overhead, L1_pure_value]
    rw [← hl0, ← hls, ← hcells, hb]
    rfl
  obtain ⟨op1, op2, op3⟩ := L3_output (v ∘ e) b.alpha n le_rfl
  have hμ : μ = clippedMultiplier v b.alpha := by
    show (fun s => answerMultiplier (n := n) out (e.symm s)) = _
    rw [hout]
    funext s
    unfold answerMultiplier clippedMultiplier
    simp only
    rw [op2 (e.symm s).val (e.symm s).isLt]
    simp
  have hsteps : execution.steps ≤ 512 * (n + 1) * (1 + sortingLevels n) := by
    show (solve n (q ∘ e) t (v ∘ e)).steps ≤ _
    simp only [solve, L1_bind_steps, L1_bind_value, overhead, L1_pure_steps]
    rw [← hl0, ← hls, ← hcells, hb]
    simp only [Option.getD_some]
    rw [sp5, pp2, op3]
    have hsc := L2_scanPass_steps t cells none
    rw [pp1, hlen] at hsc
    rw [hlen]
    have hL : l0.length ≤ n := sp4
    have hk : Nat.clog 2 l0.length ≤ sortingLevels n := Nat.clog_mono_right 2 (by omega)
    have hP : l0.length * Nat.clog 2 l0.length ≤ n * sortingLevels n := Nat.mul_le_mul hL hk
    have e512 : 512 * (n + 1) * (1 + sortingLevels n)
        = 512 + 512 * n + 512 * sortingLevels n + 512 * (n * sortingLevels n) := by ring
    rw [e512]
    rcases Nat.eq_zero_or_pos l0.length with h0 | hpos
    · have := so3 h0
      omega
    · have := so4 hpos
      omega
  have hbest : out.best = b := by rw [hout]
  rw [hbest]
  refine ⟨?_, hμ, ?_, ?_, ?_, ?_, fun p => L6_ball_iff q hq t ht p,
    fun hpos => L6_ball_chiSq q t hpos, hsteps, fun _ => hsteps⟩
  · rw [hout]; simpa using op1
  · rw [hμ]; exact L5_clip_nonneg v b.alpha
  · rw [hμ]; exact hbα
  · rw [hbV]; exact hLeast
  · rw [hbV]; exact hGreat

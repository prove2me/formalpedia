-- Prove2me | solution 1 for PersistClust.Count.t6_assemble
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T12:08:53.717+00:00
-- url     : https://prove2.me/submissions/e74315ae-a815-4d3f-a68b-497f2f16ae52

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

theorem t6_closeE_refl {ε : ℝ} (hε : 0 ≤ ε) (x : EReal) : closeE x x ε := by
  have h1 : x ≤ x + ((ε : ℝ) : EReal) := by
    cases x with
    | bot => exact bot_le
    | coe xr =>
        simp only [← EReal.coe_add]
        exact EReal.coe_le_coe_iff.mpr (by linarith)
    | top => exact le_top
  exact ⟨h1, h1⟩

theorem t6_offPos {D : EReal × EReal → ℕ∞} (a : offD D) : D a.1.1 ≠ 0 := by
  intro h0
  have hA := a.2
  rw [h0] at hA
  have hle : ((0 : ℕ) : ℕ∞) ≤ ((a.1.2 : ℕ) : ℕ∞) :=
    ENat.natCast_le_natCast.mpr (Nat.zero_le a.1.2)
  exact absurd hA (not_lt.mpr hle)

noncomputable def t6_idx {D : EReal × EReal → ℕ∞} [Fintype {p : EReal × EReal | D p ≠ 0}]
    (a : offD D) : Fin (Fintype.card {p : EReal × EReal | D p ≠ 0}) :=
  Fintype.equivFin (α := {p : EReal × EReal | D p ≠ 0}) ⟨a.1.1, t6_offPos a⟩

theorem t6_idxInj {D : EReal × EReal → ℕ∞} [Fintype {p : EReal × EReal | D p ≠ 0}]
    {a₁ a₂ : offD D} (h : (t6_idx a₁).val = (t6_idx a₂).val) : a₁.1.1 = a₂.1.1 := by
  have hfin : t6_idx a₁ = t6_idx a₂ := Fin.val_injective h
  simp only [t6_idx] at hfin
  exact congrArg Subtype.val
    ((Fintype.equivFin (α := {p : EReal × EReal | D p ≠ 0})).injective hfin)

noncomputable def t6_code {D : EReal × EReal → ℕ∞} [Fintype {p : EReal × EReal | D p ≠ 0}]
    (a : offD D) : ℕ :=
  Fintype.card {p : EReal × EReal | D p ≠ 0} * a.1.2 + (t6_idx a).val

theorem t6_codeInj {D : EReal × EReal → ℕ∞} [Fintype {p : EReal × EReal | D p ≠ 0}] :
    Function.Injective (t6_code (D := D)) := by
  intro a₁ a₂ heq
  simp only [t6_code] at heq
  have hb₁ : (t6_idx a₁).val < Fintype.card {p : EReal × EReal | D p ≠ 0} :=
    Fin.is_lt _
  have hb₂ : (t6_idx a₂).val < Fintype.card {p : EReal × EReal | D p ≠ 0} :=
    Fin.is_lt _
  have hNX : 0 < Fintype.card {p : EReal × EReal | D p ≠ 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨a₁.1.1, t6_offPos a₁⟩⟩
  have hmod : (t6_idx a₁).val % Fintype.card {p : EReal × EReal | D p ≠ 0}
      = (t6_idx a₂).val % Fintype.card {p : EReal × EReal | D p ≠ 0} := by
    rw [Nat.add_comm (Fintype.card {p : EReal × EReal | D p ≠ 0} * a₁.1.2) (t6_idx a₁).val,
        Nat.add_comm (Fintype.card {p : EReal × EReal | D p ≠ 0} * a₂.1.2) (t6_idx a₂).val] at heq
    rw [← Nat.add_mul_mod_self_left (t6_idx a₁).val
        (Fintype.card {p : EReal × EReal | D p ≠ 0}) a₁.1.2,
        ← Nat.add_mul_mod_self_left (t6_idx a₂).val
        (Fintype.card {p : EReal × EReal | D p ≠ 0}) a₂.1.2, heq]
  rw [Nat.mod_eq_of_lt hb₁, Nat.mod_eq_of_lt hb₂] at hmod
  have hpt : a₁.1.1 = a₂.1.1 := t6_idxInj hmod
  rw [hmod] at heq
  have hmul : Fintype.card {p : EReal × EReal | D p ≠ 0} * a₁.1.2
      = Fintype.card {p : EReal × EReal | D p ≠ 0} * a₂.1.2 :=
    Nat.add_right_cancel heq
  exact Subtype.ext (Prod.ext hpt (Nat.eq_of_mul_eq_mul_left hNX hmul))

theorem t6_doubleInj (A B : ℕ) (h : 2 * A + 1 = 2 * B + 1) : A = B := by omega

theorem t6_odd_ne_even (A b : ℕ) : 2 * A + 1 ≠ 2 * b := by omega

theorem t6_killPos {D : EReal × EReal → ℕ∞} (α ε : ℝ) (hε : 0 ≤ ε)
    (hD : IsDiagramLike D) (a : offD D) (hnd : ¬ DemandsOff α ε a) :
    ∃ x : EReal,
      (offPt a ∈ QNE α → closeE (offPt a).1 x ε ∧ closeE (offPt a).2 x ε) ∧
      ((x, x) ∈ QNE α → closeE (offPt a).1 x ε ∧ closeE (offPt a).2 x ε) ∧
      (offPt a ∈ QSE α → closeE (offPt a).1 x ε) ∧
      ((x, x) ∈ QSE α → closeE (offPt a).1 x ε) := by
  have hdb : (offPt a).2 < (offPt a).1 := hD _ (t6_offPos a)
  by_cases hqne : offPt a ∈ QNE α
  · -- non-prominent QNE copy: the ∃x-witness kills it
    have hnp : ¬ PromQNE α ε a := fun h => hnd (Or.inl h)
    obtain ⟨x, hx⟩ : ∃ x : EReal, closeE (offPt a).1 x ε ∧ closeE (offPt a).2 x ε := by
      by_contra hc
      exact hnp ⟨hqne, hc⟩
    exact ⟨x, fun _ => hx, fun _ => hx, fun _ => hx.1, fun _ => hx.1⟩
  · by_cases hqse : offPt a ∈ QSE α
    · have hnq : ¬ (((α + ε : ℝ) : EReal) < (offPt a).1 ∧
          ((2 * ε : ℝ) : EReal) < (offPt a).1 - (offPt a).2) :=
        fun h => hnd (Or.inr ⟨hqse, h⟩)
      by_cases hlow : (offPt a).1 ≤ ((α + ε : ℝ) : EReal)
      · -- low QSE: kill at x = b − ε ≤ α
        have hq1 := hqse.1
        have hq2 := hqse.2
        have hbbot : (offPt a).1 ≠ ⊥ := by
          intro h
          rw [h] at hq1
          exact absurd (le_antisymm (le_of_lt hq1) bot_le) (EReal.coe_ne_bot α)
        have hbtop : (offPt a).1 ≠ ⊤ := by
          intro h
          rw [h] at hlow
          exact absurd (le_antisymm hlow le_top).symm (EReal.coe_ne_top (α + ε))
        have hbcoe : (((offPt a).1).toReal : EReal) = (offPt a).1 :=
          EReal.coe_toReal hbtop hbbot
        have hbr : ((offPt a).1).toReal ≤ α + ε := by
          have hc : ((((offPt a).1).toReal : ℝ) : EReal) ≤ ((α + ε : ℝ) : EReal) := by
            rw [hbcoe]
            exact hlow
          exact EReal.coe_le_coe_iff.mp hc
        have hxα : ((((offPt a).1).toReal - ε : ℝ) : EReal) ≤ ((α : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (by linarith)
        have hbxc : closeE ((((offPt a).1).toReal : ℝ) : EReal)
            ((((offPt a).1).toReal - ε : ℝ) : EReal) ε := by
          refine ⟨?_, ?_⟩
          · rw [← EReal.coe_add]
            exact EReal.coe_le_coe_iff.mpr (by linarith)
          · rw [← EReal.coe_add]
            exact EReal.coe_le_coe_iff.mpr (by linarith)
        have hbx : closeE (offPt a).1 ((((offPt a).1).toReal - ε : ℝ) : EReal) ε :=
          hbcoe ▸ hbxc
        exact ⟨((((offPt a).1).toReal - ε : ℝ) : EReal),
          fun hne => absurd hne.2 (not_lt_of_ge hq2),
          fun hne => absurd hne.1 (not_lt_of_ge hxα),
          fun _ => hbx,
          fun hse => absurd hse.1 (not_lt_of_ge hxα)⟩
      · -- near-diagonal QSE: kill at x = d + ε
        have hnear : (offPt a).1 - (offPt a).2 ≤ ((2 * ε : ℝ) : EReal) :=
          not_not.mp (fun hc => hnq ⟨not_le.mp hlow, not_le.mp hc⟩)
        have hb2 : (offPt a).1 ≤ ((2 * ε : ℝ) : EReal) + (offPt a).2 :=
          (EReal.sub_le_iff_le_add (Or.inr (EReal.coe_ne_top _))
            (Or.inr (EReal.coe_ne_bot _))).mp hnear
        have h2add : ∀ d : EReal, ((2 * ε : ℝ) : EReal) + d
            ≤ (d + ((ε : ℝ) : EReal)) + ((ε : ℝ) : EReal) := by
          intro d
          induction d with
          | bot => exact bot_le
          | coe dr =>
              simp only [← EReal.coe_add]
              exact EReal.coe_le_coe_iff.mpr (by linarith)
          | top => exact le_top
        have hdle : ∀ d : EReal, d ≤ (d + ((ε : ℝ) : EReal)) + ((ε : ℝ) : EReal) := by
          intro d
          induction d with
          | bot => exact bot_le
          | coe dr =>
              simp only [← EReal.coe_add]
              exact EReal.coe_le_coe_iff.mpr (by linarith)
          | top => exact le_top
        have hdb' : (offPt a).2 ≤ (offPt a).1 := le_of_lt hdb
        have hclosebx : closeE (offPt a).1 ((offPt a).2 + ((ε : ℝ) : EReal)) ε :=
          ⟨hb2.trans (h2add (offPt a).2), add_le_add hdb' (le_refl _)⟩
        have hclosedx : closeE (offPt a).2 ((offPt a).2 + ((ε : ℝ) : EReal)) ε :=
          ⟨hdle (offPt a).2, le_refl _⟩
        exact ⟨(offPt a).2 + ((ε : ℝ) : EReal),
          fun _ => ⟨hclosebx, hclosedx⟩,
          fun _ => ⟨hclosebx, hclosedx⟩,
          fun _ => hclosebx,
          fun _ => hclosebx⟩
    · -- QSW: kill at x = b ≤ α (free position)
      have hble : (offPt a).1 ≤ ((α : ℝ) : EReal) := by
        by_contra hb
        have hlt := not_le.mp hb
        rcases le_or_gt (offPt a).2 ((α : ℝ) : EReal) with hd | hd
        · exact hqse ⟨hlt, hd⟩
        · exact hqne ⟨hlt, hd⟩
      exact ⟨(offPt a).1,
        fun h => absurd h hqne,
        fun hne => absurd hne.1 (not_lt_of_ge hble),
        fun h => absurd h hqse,
        fun hse => absurd hse.1 (not_lt_of_ge hble)⟩

noncomputable def t6_kill (D : EReal × EReal → ℕ∞) (α ε : ℝ) (hε : 0 ≤ ε)
    (hD : IsDiagramLike D) (a : offD D) (hnd : ¬ DemandsOff α ε a) : EReal :=
  (t6_killPos α ε hε hD a hnd).choose

theorem t6_kill_spec (D : EReal × EReal → ℕ∞) (α ε : ℝ) (hε : 0 ≤ ε)
    (hD : IsDiagramLike D) (a : offD D) (hnd : ¬ DemandsOff α ε a) :
    (offPt a ∈ QNE α →
        closeE (offPt a).1 (t6_kill D α ε hε hD a hnd) ε ∧
      closeE (offPt a).2 (t6_kill D α ε hε hD a hnd) ε) ∧
    ((t6_kill D α ε hε hD a hnd, t6_kill D α ε hε hD a hnd) ∈ QNE α →
        closeE (offPt a).1 (t6_kill D α ε hε hD a hnd) ε ∧
      closeE (offPt a).2 (t6_kill D α ε hε hD a hnd) ε) ∧
    (offPt a ∈ QSE α → closeE (offPt a).1 (t6_kill D α ε hε hD a hnd) ε) ∧
    ((t6_kill D α ε hε hD a hnd, t6_kill D α ε hε hD a hnd) ∈ QSE α →
      closeE (offPt a).1 (t6_kill D α ε hε hD a hnd) ε) :=
  (t6_killPos α ε hε hD a hnd).choose_spec

/-- Schroeder-Bernstein matching assembly: for two diagram-like
diagrams of finite support at (alpha, eps), injective maps on
the demanded off-diagonal copies in BOTH directions (X to Y and
Y to X) that send prominent copies to eps-close full partners
and QSE copies to birth-close partners (upgraded to full
closeness when the image lands in the strict quadrant) yield a
full equivalence of copy types satisfying the gate clauses
I and II. The construction codes each copy by an injective
natural number (index and slot, odd/even split by demand
status), kills the non-demanded copies to eps-close diagonal
points, and patches the demanded sectors with the given
injections; the two injections are reassembled through the
copy codes into a bijection. -/
theorem solution {DX DY : EReal × EReal → ℕ∞} (α ε : ℝ) (hε : 0 ≤ ε)
    (hDX : IsDiagramLike DX) (hDY : IsDiagramLike DY)
    (hFinX : {p : EReal × EReal | DX p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | DY p ≠ 0}.Finite)
    (hGX : ∃ F : {a : offD DX // DemandsOff α ε a} → offD DY,
        Function.Injective F ∧
        (∀ a, PromQNE α ε a.1 → CloseCopy2 ε a.1 (F a)) ∧
        (∀ a, offPt a.1 ∈ QSE α → CloseCopy1 ε a.1 (F a) ∧
          (offPt (F a) ∈ QNE α → CloseCopy2 ε a.1 (F a))))
    (hGY : ∃ F : {a : offD DY // DemandsOff α ε a} → offD DX,
        Function.Injective F ∧
        (∀ a, PromQNE α ε a.1 → CloseCopy2 ε a.1 (F a)) ∧
        (∀ a, offPt a.1 ∈ QSE α → CloseCopy1 ε a.1 (F a) ∧
          (offPt (F a) ∈ QNE α → CloseCopy2 ε a.1 (F a)))) :
    ∃ γ : Copies DX ≃ Copies DY, SatisfiesIIV γ α ε := by
  classical
  obtain ⟨FX, hFXinj, hFXprom, hFXqse⟩ := hGX
  obtain ⟨FY, hFYinj, hFYprom, hFYqse⟩ := hGY
  haveI : Fintype {p : EReal × EReal | DX p ≠ 0} := hFinX.fintype
  haveI : Fintype {p : EReal × EReal | DY p ≠ 0} := hFinY.fintype
  have hcodeX := t6_codeInj (D := DX)
  have hcodeY := t6_codeInj (D := DY)
  have hfinj_f : Function.Injective (Sum.elim
      (fun (q : offD DX) =>
        if h : DemandsOff α ε q then Sum.inl (FX ⟨q, h⟩)
        else Sum.inr (t6_kill DX α ε hε hDX q h, 2 * t6_code q + 1))
      (fun (xk : EReal × ℕ) => Sum.inr (xk.1, 2 * xk.2))) := by
    intro a₁ a₂ heq
    rcases a₁ with q₁ | xk₁ <;> rcases a₂ with q₂ | xk₂
    · simp only [Sum.elim_inl] at heq
      by_cases hd₁ : DemandsOff α ε q₁
      · by_cases hd₂ : DemandsOff α ε q₂
        · simp only [dif_pos hd₁, dif_pos hd₂, Sum.inl.injEq] at heq
          exact congrArg Sum.inl (congrArg Subtype.val (hFXinj heq))
        · simp only [dif_pos hd₁, dif_neg hd₂] at heq
          exact absurd heq Sum.inl_ne_inr
      · by_cases hd₂ : DemandsOff α ε q₂
        · simp only [dif_neg hd₁, dif_pos hd₂] at heq
          exact absurd heq Sum.inr_ne_inl
        · simp only [dif_neg hd₁, dif_neg hd₂, Sum.inr.injEq, Prod.mk.injEq] at heq
          exact congrArg Sum.inl (hcodeX (t6_doubleInj _ _ heq.2))
    · simp only [Sum.elim_inl, Sum.elim_inr] at heq
      by_cases hd₁ : DemandsOff α ε q₁
      · simp only [dif_pos hd₁] at heq
        exact absurd heq Sum.inl_ne_inr
      · simp only [dif_neg hd₁, Sum.inr.injEq, Prod.mk.injEq] at heq
        exact absurd heq.2 (t6_odd_ne_even _ _)
    · simp only [Sum.elim_inl, Sum.elim_inr] at heq
      by_cases hd₂ : DemandsOff α ε q₂
      · simp only [dif_pos hd₂] at heq
        exact absurd heq Sum.inr_ne_inl
      · simp only [dif_neg hd₂, Sum.inr.injEq, Prod.mk.injEq] at heq
        exact absurd heq.2.symm (t6_odd_ne_even _ _)
    · simp only [Sum.elim_inr, Sum.inr.injEq, Prod.mk.injEq] at heq
      have hk : xk₁.2 = xk₂.2 := by omega
      exact congrArg Sum.inr (Prod.ext heq.1 hk)
  have hfinj_g : Function.Injective (Sum.elim
      (fun (q : offD DY) =>
        if h : DemandsOff α ε q then Sum.inl (FY ⟨q, h⟩)
        else Sum.inr (t6_kill DY α ε hε hDY q h, 2 * t6_code q + 1))
      (fun (xk : EReal × ℕ) => Sum.inr (xk.1, 2 * xk.2))) := by
    intro a₁ a₂ heq
    rcases a₁ with q₁ | xk₁ <;> rcases a₂ with q₂ | xk₂
    · simp only [Sum.elim_inl] at heq
      by_cases hd₁ : DemandsOff α ε q₁
      · by_cases hd₂ : DemandsOff α ε q₂
        · simp only [dif_pos hd₁, dif_pos hd₂, Sum.inl.injEq] at heq
          exact congrArg Sum.inl (congrArg Subtype.val (hFYinj heq))
        · simp only [dif_pos hd₁, dif_neg hd₂] at heq
          exact absurd heq Sum.inl_ne_inr
      · by_cases hd₂ : DemandsOff α ε q₂
        · simp only [dif_neg hd₁, dif_pos hd₂] at heq
          exact absurd heq Sum.inr_ne_inl
        · simp only [dif_neg hd₁, dif_neg hd₂, Sum.inr.injEq, Prod.mk.injEq] at heq
          exact congrArg Sum.inl (hcodeY (t6_doubleInj _ _ heq.2))
    · simp only [Sum.elim_inl, Sum.elim_inr] at heq
      by_cases hd₁ : DemandsOff α ε q₁
      · simp only [dif_pos hd₁] at heq
        exact absurd heq Sum.inl_ne_inr
      · simp only [dif_neg hd₁, Sum.inr.injEq, Prod.mk.injEq] at heq
        exact absurd heq.2 (t6_odd_ne_even _ _)
    · simp only [Sum.elim_inl, Sum.elim_inr] at heq
      by_cases hd₂ : DemandsOff α ε q₂
      · simp only [dif_pos hd₂] at heq
        exact absurd heq Sum.inr_ne_inl
      · simp only [dif_neg hd₂, Sum.inr.injEq, Prod.mk.injEq] at heq
        exact absurd heq.2.symm (t6_odd_ne_even _ _)
    · simp only [Sum.elim_inr, Sum.inr.injEq, Prod.mk.injEq] at heq
      have hk : xk₁.2 = xk₂.2 := by omega
      exact congrArg Sum.inr (Prod.ext heq.1 hk)
  obtain ⟨h, hbij, hR⟩ := Function.Embedding.schroeder_bernstein_of_rel
    (R := fun a b =>
      (pt a ∈ QNE α → closeE (pt a).1 (pt b).1 ε ∧ closeE (pt a).2 (pt b).2 ε) ∧
      (pt b ∈ QNE α → closeE (pt a).1 (pt b).1 ε ∧ closeE (pt a).2 (pt b).2 ε) ∧
      (pt a ∈ QSE α → closeE (pt a).1 (pt b).1 ε) ∧
      (pt b ∈ QSE α → closeE (pt a).1 (pt b).1 ε))
    hfinj_f hfinj_g
    (by
      intro a
      rcases a with q | xk
      · simp only [Sum.elim_inl, pt]
        by_cases hd : DemandsOff α ε q
        · simp only [dif_pos hd, pt]
          rcases hd with hprom | hqseb
          · have hcc := hFXprom ⟨q, Or.inl hprom⟩ hprom
            exact ⟨fun _ => hcc, fun _ => hcc,
              fun hqse2 => absurd hprom.1.2 (not_lt_of_ge hqse2.2), fun _ => hcc.1⟩
          · have hcc1 := (hFXqse ⟨q, Or.inr hqseb⟩ hqseb.1).1
            have hcc2 := (hFXqse ⟨q, Or.inr hqseb⟩ hqseb.1).2
            exact ⟨fun hne => absurd hne.2 (not_lt_of_ge hqseb.1.2),
              fun hne2 => hcc2 hne2,
              fun _ => hcc1, fun _ => hcc1⟩
        · simp only [dif_neg hd, pt]
          exact t6_kill_spec DX α ε hε hDX q hd
      · simp only [Sum.elim_inr, pt]
        exact ⟨fun _ => ⟨t6_closeE_refl hε xk.1, t6_closeE_refl hε xk.1⟩,
          fun _ => ⟨t6_closeE_refl hε xk.1, t6_closeE_refl hε xk.1⟩,
          fun hse => absurd hse.1 (not_lt_of_ge hse.2),
          fun hse => absurd hse.1 (not_lt_of_ge hse.2)⟩)
    (by
      intro b
      rcases b with q | xk
      · simp only [Sum.elim_inl, pt]
        by_cases hd : DemandsOff α ε q
        · simp only [dif_pos hd, pt]
          rcases hd with hprom | hqseb
          · have hcc := hFYprom ⟨q, Or.inl hprom⟩ hprom
            exact ⟨fun _ => ⟨⟨hcc.1.2, hcc.1.1⟩, ⟨hcc.2.2, hcc.2.1⟩⟩,
              fun _ => ⟨⟨hcc.1.2, hcc.1.1⟩, ⟨hcc.2.2, hcc.2.1⟩⟩,
              fun _ => ⟨hcc.1.2, hcc.1.1⟩, fun _ => ⟨hcc.1.2, hcc.1.1⟩⟩
          · have hcc1 := (hFYqse ⟨q, Or.inr hqseb⟩ hqseb.1).1
            have hcc2 := (hFYqse ⟨q, Or.inr hqseb⟩ hqseb.1).2
            exact ⟨fun hne => ⟨⟨(hcc2 hne).1.2, (hcc2 hne).1.1⟩,
                    ⟨(hcc2 hne).2.2, (hcc2 hne).2.1⟩⟩,
              fun hne2 => absurd hne2.2 (not_lt_of_ge hqseb.1.2),
              fun _ => ⟨hcc1.2, hcc1.1⟩, fun _ => ⟨hcc1.2, hcc1.1⟩⟩
        · simp only [dif_neg hd, pt]
          obtain ⟨h1, h2, h3, h4⟩ := t6_kill_spec DY α ε hε hDY q hd
          exact ⟨fun hne => ⟨⟨(h2 hne).1.2, (h2 hne).1.1⟩, ⟨(h2 hne).2.2, (h2 hne).2.1⟩⟩,
            fun hne => ⟨⟨(h1 hne).1.2, (h1 hne).1.1⟩, ⟨(h1 hne).2.2, (h1 hne).2.1⟩⟩,
            fun hse => ⟨(h4 hse).2, (h4 hse).1⟩,
            fun hse => ⟨(h3 hse).2, (h3 hse).1⟩⟩
      · simp only [Sum.elim_inr, pt]
        exact ⟨fun _ => ⟨t6_closeE_refl hε xk.1, t6_closeE_refl hε xk.1⟩,
          fun _ => ⟨t6_closeE_refl hε xk.1, t6_closeE_refl hε xk.1⟩,
          fun hse => absurd hse.1 (not_lt_of_ge hse.2),
          fun hse => absurd hse.1 (not_lt_of_ge hse.2)⟩)
  refine ⟨Equiv.ofBijective h hbij, ?_, ?_, ?_, ?_⟩
  · exact fun a hmem => (hR a).1 hmem
  · intro b hmem
    have hb : h ((Equiv.ofBijective h hbij).symm b) = b :=
      Equiv.apply_symm_apply (Equiv.ofBijective h hbij) b
    have hRb := hR ((Equiv.ofBijective h hbij).symm b)
    rw [hb] at hRb
    exact hRb.2.1 hmem
  · exact fun a hmem => (hR a).2.2.1 hmem
  · intro b hmem
    have hb : h ((Equiv.ofBijective h hbij).symm b) = b :=
      Equiv.apply_symm_apply (Equiv.ofBijective h hbij) b
    have hRb := hR ((Equiv.ofBijective h hbij).symm b)
    rw [hb] at hRb
    exact hRb.2.2.2 hmem

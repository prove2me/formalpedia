-- Prove2me | solution 1 for PersistClust.Count.theorem_4_5_gamma_degenerate
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T16:25:17.177402+00:00
-- url     : https://prove2.me/submissions/076acfd8-9931-4a1e-a400-61f2505c8991

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Theorems.Thm_PersistClust_Count_theorem_4_5_interleaving_corrected

open PersistClust.Count
open Bundle
open scoped ContDiff Manifold ENNReal

namespace t45deg

/-! ## att62: the degenerate `𝔽^α = ∅` case of theorem 4.5 (from the att59 recipe). -/

/-! ### Step 1: emptiness of the stages above α -/

/-- Under `hvac : ∀ x, f x < α` the superlevel sets at levels `≥ α` are empty. -/
theorem t45deg_super_empty {X : Type*} [TopologicalSpace X] {f : X → ℝ} {α : ℝ}
    (hvac : ∀ x : X, f x < α) {s : ℝ} (hs : α ≤ s) : superlevel f s = ∅ := by
  unfold superlevel
  refine (Set.eq_empty_iff_forall_notMem).mpr (fun x hx => ?_)
  simp only [Set.mem_ofPred_eq] at hx
  exact absurd (hs.trans hx) (not_le.mpr (hvac x))

/-- Under `hvac : ∀ x, f x < α` the superlevel rank is identically `0` on `s ≥ α`. -/
theorem t45deg_superRank_zero {X : Type*} [TopologicalSpace X] {f : X → ℝ} {α : ℝ}
    (hvac : ∀ x : X, f x < α) {s t : ℝ} (hs : α ≤ s) : superRank f s t = 0 := by
  unfold superRank rankFn
  rw [t45deg_super_empty hvac hs, Set.image_empty, Set.encard_empty]

/-- Under `hvac : ∀ x, f x < α` the sampled-vertex stage `{i | s ≤ g i}` is empty for `s ≥ α`.
Every vertex `i` of the sample is a point of `X`, so `f (i : X) < α`. -/
theorem t45deg_ripsStage_empty {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ} {α : ℝ}
    (hvac : ∀ x : X, f x < α) {s : ℝ} (hs : α ≤ s) : {i : ↥L | s ≤ (fun x : ↥L => f x) i} = ∅ := by
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
  exact ⟨fun h => absurd (hs.trans h) (not_le.mpr (hvac (i : X))), False.elim⟩

/-- Under `hvac : ∀ x, f x < α` the Rips rank is identically `0` on `s ≥ α`. -/
theorem t45deg_ripsRank_zero {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ} {α : ℝ}
    (hvac : ∀ x : X, f x < α) (Dm : ↥L → ↥L → ℝ) (δ : ℝ) {s t : ℝ} (hs : α ≤ s) :
    ripsRank Dm (fun x : ↥L => f x) δ s t = 0 := by
  unfold ripsRank rankFn
  show ((fun x => {y | ripsJoined Dm (fun x : ↥L => f x) δ t x y}) ''
      {i : ↥L | s ≤ (fun x : ↥L => f x) i}).encard = 0
  rw [t45deg_ripsStage_empty hvac hs, Set.image_empty, Set.encard_empty]

/-! ### Step 2: the strict support bounds via the mult window collapse -/

/-- If `r s t = 0` for every `s ≥ α`, then `mult r` vanishes on every point whose birth
coordinate is strictly above `α`.  (The window collapse: pick `ε₀` with both window birth-levels
`b ± ε₀ ≥ α`, so every rank term in the bracket is `0`.) -/
theorem t45deg_mult_strict_support (r : ℝ → ℝ → ℕ∞) (α : ℝ)
    (hr : ∀ s t : ℝ, α ≤ s → r s t = 0) {p : EReal × EReal}
    (hp : ((α : ℝ) : EReal) < p.1) : mult r p = 0 := by
  unfold mult
  by_cases htop : p.1 = ⊤
  · rw [if_neg (fun h => h.2 htop)]
  · have hbot : p.1 ≠ ⊥ := by
      intro h
      rw [h] at hp
      exact absurd hp (fun hp' => lt_irrefl ((α : ℝ) : EReal) (lt_of_lt_of_le hp' bot_le))
    rw [if_pos ⟨hbot, htop⟩]
    have hcoe : ((p.1.toReal : ℝ) : EReal) = p.1 := EReal.coe_toReal htop hbot
    rw [← hcoe] at hp
    have hbα : α < p.1.toReal := EReal.coe_lt_coe_iff.mp hp
    by_cases h2 : p.2 = ⊥
    · -- the immortal branch: `⨅ ε > 0, ⨅ t ≤ b - ε, r (b-ε) t - r (b+ε) t`
      rw [if_pos h2]
      apply le_antisymm
      · refine iInf_le_of_le ((p.1.toReal - α) / 2)
          (iInf_le_of_le (div_pos (show 0 < p.1.toReal - α by linarith) two_pos) ?_)
        refine iInf_le_of_le (p.1.toReal - (p.1.toReal - α) / 2) (iInf_le_of_le (le_refl _) ?_)
        have hb1 : α ≤ p.1.toReal - (p.1.toReal - α) / 2 := by linarith
        have hb2 : α ≤ p.1.toReal + (p.1.toReal - α) / 2 := by linarith
        have e1 : r (p.1.toReal - (p.1.toReal - α) / 2)
            (p.1.toReal - (p.1.toReal - α) / 2) = 0 := hr _ _ hb1
        have e2 : r (p.1.toReal + (p.1.toReal - α) / 2)
            (p.1.toReal - (p.1.toReal - α) / 2) = 0 := hr _ _ hb2
        rw [e1, e2]
        simp
      · exact zero_le
    · rw [if_neg h2]
      by_cases h3 : p.2 < p.1
      · -- the main branch: both coordinates real, death < birth
        rw [if_pos h3]
        have h2top : p.2 ≠ ⊤ :=
          fun h => absurd (lt_of_lt_of_le (h ▸ h3) le_top) (lt_irrefl (⊤ : EReal))
        have h2coe : ((p.2.toReal : ℝ) : EReal) = p.2 := EReal.coe_toReal h2top h2
        have hdb : p.2.toReal < p.1.toReal := by
          rw [← hcoe, ← h2coe] at h3
          exact EReal.coe_lt_coe_iff.mp h3
        -- the window point: small enough for the `Ioo` window and for `b - ε₀ ≥ α`
        have he0pos : 0 < min ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4) := by
          have h1 : 0 < (p.1.toReal - α) / 2 := by linarith
          have h2' : 0 < (p.1.toReal - p.2.toReal) / 4 := by linarith
          exact lt_min h1 h2'
        have he0lt : min ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4) <
            (p.1.toReal - p.2.toReal) / 2 := by
          have hB := min_le_right ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4)
          have h4 : (p.1.toReal - p.2.toReal) / 4 < (p.1.toReal - p.2.toReal) / 2 := by linarith
          exact lt_of_le_of_lt hB h4
        have hb1 : α ≤ p.1.toReal -
            min ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4) := by
          have hA := min_le_left ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4)
          linarith
        have hb2 : α ≤ p.1.toReal +
            min ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4) := by linarith
        apply le_antisymm
        · refine iInf_le_of_le (min ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4))
              (iInf_le_of_le ⟨he0pos, he0lt⟩ ?_)
          have e1 : r (p.1.toReal -
              min ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4))
              (p.2.toReal + min ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4)) = 0 :=
            hr _ _ hb1
          have e2 : r (p.1.toReal +
              min ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4))
              (p.2.toReal + min ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4)) = 0 :=
            hr _ _ hb2
          have e3 : r (p.1.toReal -
              min ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4))
              (p.2.toReal - min ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4)) = 0 :=
            hr _ _ hb1
          have e4 : r (p.1.toReal +
              min ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4))
              (p.2.toReal - min ((p.1.toReal - α) / 2) ((p.1.toReal - p.2.toReal) / 4)) = 0 :=
            hr _ _ hb2
          rw [e1, e2, e3, e4]
          simp
        · exact zero_le
      · rw [if_neg h3]

/-- Under `hvac` the superlevel diagram has no support strictly above `α`. -/
theorem t45deg_diagram0_support {X : Type*} [TopologicalSpace X] {f : X → ℝ} {α : ℝ}
    (hvac : ∀ x : X, f x < α) {P : EReal × EReal} (hP : ((α : ℝ) : EReal) < P.1) :
    diagram0 f P = 0 := by
  unfold diagram0
  exact t45deg_mult_strict_support (superRank f) α (fun s t hs => t45deg_superRank_zero hvac hs) hP

/-- Under `hvac` the Rips diagram has no support strictly above `α`
(every sampled vertex has `f < α`). -/
theorem t45deg_ripsDiagram_support {X : Type*} [MetricSpace X] {L : Finset X} {f : X → ℝ}
    {α : ℝ} (hvac : ∀ x : X, f x < α) (Dm : ↥L → ↥L → ℝ) (δ : ℝ) {P : EReal × EReal}
    (hP : ((α : ℝ) : EReal) < P.1) : ripsDiagram Dm (fun x : ↥L => f x) δ P = 0 := by
  unfold ripsDiagram
  exact t45deg_mult_strict_support (ripsRank Dm (fun x : ↥L => f x) δ) α
    (fun s t hs => t45deg_ripsRank_zero hvac Dm δ hs) hP

/-! ### Step 3: the γ-construction and `SatisfiesIIV` -/

/-- The off-diagonal copies of a diagram `D` (the first summand of `Copies D`). -/
abbrev t45deg_offdiag (D : EReal × EReal → ℕ∞) : Type :=
  {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < D q.1}

/-- The full off-diagonal copy set is countable whenever the diagram has finite support. -/
theorem t45deg_offdiag_countable (D : EReal × EReal → ℕ∞)
    (hFin : {p : EReal × EReal | D p ≠ 0}.Finite) :
    Countable (t45deg_offdiag D) := by
  have hkey : ∀ q : (EReal × EReal) × ℕ, (q.2 : ℕ∞) < D q.1 → D q.1 ≠ 0 := by
    intro q hq h0
    rw [h0] at hq
    exact absurd (lt_of_le_of_lt (Nat.cast_nonneg q.2) hq) (lt_irrefl (0 : ℕ∞))
  have : Countable {p : EReal × EReal | D p ≠ 0} := hFin.countable
  refine Function.Injective.countable
    (f := fun q : t45deg_offdiag D =>
      ((⟨q.val.1, hkey q.val q.property⟩ : {p : EReal × EReal | D p ≠ 0}), q.val.2)) ?_
  intro q q' h
  obtain ⟨hX, h2⟩ := Prod.mk.inj h
  have h1 : q.val.1 = q'.val.1 := by
    have hval := congrArg Subtype.val hX
    exact hval
  exact Subtype.ext (Prod.ext h1 h2)

/-- Diagonal copies above `α` (the constrained set, fixed pointwise by `γ`). -/
abbrev t45deg_diagAbove (α : ℝ) : Type := {p : EReal × ℕ // ((α : ℝ) : EReal) < p.1}
/-- Diagonal copies at-or-below `α` (the free part). -/
abbrev t45deg_diagBelow (α : ℝ) : Type := {p : EReal × ℕ // ¬ ((α : ℝ) : EReal) < p.1}

/-- Split the diagonal `EReal × ℕ` into below-first `diagBelow ⊕ diagAbove`. -/
noncomputable def t45deg_diagSplit (α : ℝ) :
    (EReal × ℕ) ≃ t45deg_diagBelow α ⊕ t45deg_diagAbove α where
  toFun p := if h : ((α : ℝ) : EReal) < p.1 then Sum.inr ⟨p, h⟩ else Sum.inl ⟨p, h⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv := by
    intro p
    by_cases h : ((α : ℝ) : EReal) < p.1
    · show Sum.elim Subtype.val Subtype.val
        (if h' : ((α : ℝ) : EReal) < p.1 then
            (Sum.inr ⟨p, h'⟩ : t45deg_diagBelow α ⊕ t45deg_diagAbove α) else Sum.inl ⟨p, h'⟩) = p
      rw [dif_pos h]
      rfl
    · show Sum.elim Subtype.val Subtype.val
        (if h' : ((α : ℝ) : EReal) < p.1 then
            (Sum.inr ⟨p, h'⟩ : t45deg_diagBelow α ⊕ t45deg_diagAbove α) else Sum.inl ⟨p, h'⟩) = p
      rw [dif_neg h]
      rfl
  right_inv := by
    rintro (⟨p, h⟩ | ⟨p, h⟩)
    · show (if h' : ((α : ℝ) : EReal) < p.1 then
            (Sum.inr ⟨p, h'⟩ : t45deg_diagBelow α ⊕ t45deg_diagAbove α) else Sum.inl ⟨p, h'⟩) =
          Sum.inl ⟨p, h⟩
      rw [dif_neg h]
    · show (if h' : ((α : ℝ) : EReal) < p.1 then
            (Sum.inr ⟨p, h'⟩ : t45deg_diagBelow α ⊕ t45deg_diagAbove α) else Sum.inl ⟨p, h'⟩) =
          Sum.inr ⟨p, h⟩
      rw [dif_pos h]

theorem t45deg_diagSplit_apply_above (α : ℝ) {p : EReal × ℕ} (h : ((α : ℝ) : EReal) < p.1) :
    t45deg_diagSplit α p = Sum.inr (⟨p, h⟩ : t45deg_diagAbove α) := by
  show (if h' : ((α : ℝ) : EReal) < p.1 then
        (Sum.inr ⟨p, h'⟩ : t45deg_diagBelow α ⊕ t45deg_diagAbove α) else Sum.inl ⟨p, h'⟩) =
        (Sum.inr (⟨p, h⟩ : t45deg_diagAbove α) : t45deg_diagBelow α ⊕ t45deg_diagAbove α)
  rw [dif_pos h]

theorem t45deg_diagSplit_symm_apply_above (α : ℝ) {p : EReal × ℕ}
    (h : ((α : ℝ) : EReal) < p.1) :
    (t45deg_diagSplit α).symm (Sum.inr (⟨p, h⟩ : t45deg_diagAbove α)) = p := by
  have h1 : t45deg_diagSplit α p = Sum.inr (⟨p, h⟩ : t45deg_diagAbove α) :=
    t45deg_diagSplit_apply_above α h
  have h2 := (t45deg_diagSplit α).right_inv (Sum.inr (⟨p, h⟩ : t45deg_diagAbove α))
  exact (t45deg_diagSplit α).injective (h2.trans h1.symm)

/-- The key soaking lemma: a countable type absorbed into `ℕ` is `ℕ`. -/
noncomputable def t45deg_key (C : Type) [Countable C] : (C ⊕ ℕ) ≃ ℕ := by
  have hNe : Nonempty {f : C → ℕ // Function.Injective f} := by
    rcases Countable.exists_injective_nat C with ⟨f, hf⟩
    exact ⟨f, hf⟩
  -- Classical.choice extracts the subtype element (Nonempty.casesOn is Prop-only)
  set esub : {f : C → ℕ // Function.Injective f} := Classical.choice hNe
  have he : Function.Injective esub.val := esub.property
  have hf : Function.Injective
      (Sum.elim (fun c => 2 * esub.val c + 1) (fun n => 2 * n)) := by
    rintro (c | n) (c' | n') h
    · simp only [Sum.elim_inl, Sum.inl.injEq] at h ⊢
      exact he (by omega)
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      omega
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      omega
    · simp only [Sum.elim_inr, Sum.inr.injEq] at h ⊢
      omega
  have hg : Function.Injective (fun n : ℕ => Sum.inr n : ℕ → C ⊕ ℕ) := by
    intros _ _ h
    simpa using h
  exact (Function.Embedding.antisymm ⟨_, hf⟩ ⟨_, hg⟩).some

/-- Diagonal copies strictly below `α`. -/
abbrev t45deg_diagStrict (α : ℝ) : Type := {p : EReal × ℕ // p.1 < ((α : ℝ) : EReal)}

/-- `diagBelow α ≃ diagStrict α ⊕ ℕ` via `Equiv.ofBijective`.
Splits each below-α diagonal copy: if `p.1 = α` route to `Sum.inr k` (the `ℕ`-room),
otherwise `p.1 < α` route to `Sum.inl ⟨p, proof⟩`. -/
noncomputable def t45deg_diagBelowEquivN (α : ℝ) :
    t45deg_diagBelow α ≃ t45deg_diagStrict α ⊕ ℕ := by
  refine Equiv.ofBijective
    (fun q => if h : q.val.1 = ((α : ℝ) : EReal) then Sum.inr q.val.2
              else Sum.inl ⟨q.val, lt_of_le_of_ne (not_lt.mp q.property) h⟩) ?_
  constructor
  · -- injective
    intro q q' heq
    by_cases hq : q.val.1 = ((α : ℝ) : EReal)
    · by_cases hq' : q'.val.1 = ((α : ℝ) : EReal)
      · dsimp only at heq
        rw [dif_pos hq, dif_pos hq'] at heq
        injection heq with hk
        have h1 : q.val.1 = q'.val.1 := hq.trans hq'.symm
        exact Subtype.ext (Prod.ext h1 hk)
      · dsimp only at heq
        rw [dif_pos hq, dif_neg hq'] at heq
        simp at heq
    · by_cases hq' : q'.val.1 = ((α : ℝ) : EReal)
      · dsimp only at heq
        rw [dif_neg hq, dif_pos hq'] at heq
        simp at heq
      · dsimp only at heq
        rw [dif_neg hq, dif_neg hq'] at heq
        injection heq with hsub
        have hval := congrArg Subtype.val hsub
        exact Subtype.ext hval
  · -- surjective
    rintro (⟨p, h⟩ | k)
    · refine ⟨⟨p, not_lt.mpr (le_of_lt h)⟩, ?_⟩
      have hne : p.1 ≠ ((α : ℝ) : EReal) := ne_of_lt h
      dsimp only
      rw [dif_neg hne]
    · refine ⟨⟨(((α : ℝ) : EReal), k), lt_irrefl _⟩, ?_⟩
      dsimp only
      rw [dif_pos rfl]

/-- `(A ⊕ W) ⊕ N ≃ W ⊕ (A ⊕ N)` (keep `W` on the side, pair `A` with the `ℕ`-room). -/
def t45deg_shuffle3 (A W N : Type) : (A ⊕ W) ⊕ N ≃ W ⊕ (A ⊕ N) :=
  (Equiv.sumCongr (Equiv.sumComm A W) (Equiv.refl N)).trans (Equiv.sumAssoc W A N)

/-- The free blob: `(offdiag DX ⊕ diagBelow) ≃ (offdiag DY ⊕ diagBelow)`, soaking the countable
off-diagonal parts into the `ℕ`-room of `diagBelow` while keeping `diagStrict` fixed. -/
noncomputable def t45deg_blob (DX DY : EReal × EReal → ℕ∞) (α : ℝ)
    (hFX : {p | DX p ≠ 0}.Finite) (hFY : {p | DY p ≠ 0}.Finite) :
    (t45deg_offdiag DX ⊕ t45deg_diagBelow α) ≃
      (t45deg_offdiag DY ⊕ t45deg_diagBelow α) := by
  have cX : Countable (t45deg_offdiag DX) := t45deg_offdiag_countable _ hFX
  have cY : Countable (t45deg_offdiag DY) := t45deg_offdiag_countable _ hFY
  let e := t45deg_diagBelowEquivN α
  exact
    ((Equiv.sumCongr (Equiv.refl _) e).trans
      ((Equiv.sumAssoc _ _ _).symm.trans
        ((t45deg_shuffle3 _ _ _).trans
          ((Equiv.sumCongr (Equiv.refl _) (t45deg_key (t45deg_offdiag DX))).trans
            ((Equiv.sumCongr (Equiv.refl _) (t45deg_key (t45deg_offdiag DY)).symm).trans
              ((t45deg_shuffle3 _ _ _).symm.trans
                ((Equiv.sumAssoc _ _ _).trans
                  (Equiv.sumCongr (Equiv.refl _) e.symm))))))))

/-- Rearrange `Copies E ≃ (offdiag E ⊕ diagBelow) ⊕ diagAbove` (diagAbove alone on the right). -/
noncomputable def t45deg_rearrange (E : EReal × EReal → ℕ∞) (α : ℝ) :
    Copies E ≃ (t45deg_offdiag E ⊕ t45deg_diagBelow α) ⊕ t45deg_diagAbove α :=
  (Equiv.sumCongr (Equiv.refl _) (t45deg_diagSplit α)).trans (Equiv.sumAssoc _ _ _).symm

/-- The backward rearrange (explicit, avoiding `(sumCongr _ _).symm` which simp can't unfold):
`(offdiag ⊕ diagBelow) ⊕ diagAbove ≃ Copies E` via `sumAssoc` then `sumCongr (refl) (diagSplit).symm`. -/
noncomputable def t45deg_rearrangeSymm (E : EReal × EReal → ℕ∞) (α : ℝ) :
    (t45deg_offdiag E ⊕ t45deg_diagBelow α) ⊕ t45deg_diagAbove α ≃ Copies E :=
  (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) (t45deg_diagSplit α).symm)

/-- The degenerate-case multi-bijection: fixes the above-`α` diagonal pointwise. -/
noncomputable def t45deg_γ (DX DY : EReal × EReal → ℕ∞) (α : ℝ)
    (hFX : {p | DX p ≠ 0}.Finite) (hFY : {p | DY p ≠ 0}.Finite) :
    Copies DX ≃ Copies DY :=
  (t45deg_rearrange DX α).trans
    ((Equiv.sumCongr (t45deg_blob DX DY α hFX hFY) (Equiv.refl _)).trans
      (t45deg_rearrangeSymm DY α))

/-- `γ` fixes every above-`α` diagonal copy. -/
theorem t45deg_γ_fix (DX DY : EReal × EReal → ℕ∞) (α : ℝ)
    (hFX : {p | DX p ≠ 0}.Finite) (hFY : {p | DY p ≠ 0}.Finite)
    (p : EReal × ℕ) (h : ((α : ℝ) : EReal) < p.1) :
    t45deg_γ DX DY α hFX hFY (Sum.inr p) = Sum.inr p := by
  unfold t45deg_γ t45deg_rearrange t45deg_rearrangeSymm
  simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.coe_refl,
    t45deg_diagSplit_apply_above α h]
  rfl

lemma t45deg_closeE_refl (x : EReal) {r : ℝ} (hr : 0 ≤ r) : closeE x x r := by
  have h0 : ((0 : ℝ) : EReal) ≤ r := EReal.coe_le_coe_iff.mpr hr
  refine ⟨?_, ?_⟩
  · have h1 : x + ((0 : ℝ) : EReal) ≤ x + r := add_le_add_right h0 x
    simpa only [EReal.coe_zero, add_zero] using h1
  · have h1 : x + ((0 : ℝ) : EReal) ≤ x + r := add_le_add_right h0 x
    simpa only [EReal.coe_zero, add_zero] using h1

end t45deg

/-! ## The degenerate-case MAIN LEMMA (top-level; name matches the assembly rehearsal). -/

/-- **The degenerate `𝔽^α = ∅` case of theorem 4.5.**  Under `hvac : ¬ ∃ x, α ≤ f x`
(every value of `f` is strictly below `α`), both diagrams vanish strictly above `α`, and the
multi-bijection `γ` (diag-identity above `α` + free countable routing below) satisfies (i)–(iv). -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
    [IsRiemannianManifold I X]
    (hconv : 0 < convexityRadius X)
    (L : Finset X) (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (htame : IsTame0 f)
    (δ : ℝ) (hδ : 0 < δ) (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (α : ℝ) (hL : IsGeodesicSample (L : Set X) (superlevel f α) (δ / 4))
    (hvac : ¬ ∃ x : X, α ≤ f x) :
    ∃ γ : Copies (diagram0 f) ≃
        Copies (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ),
      SatisfiesIIV γ α (c * δ) := by
  -- convert the ¬∃-form to the ∀-form used by the support-bound machinery
  have hvacF : ∀ x : X, f x < α := fun x => not_le.mp (fun h => hvac ⟨x, h⟩)
  -- finiteness of both diagrams (from the ACCEPTED solution; no nonemptiness needed)
  obtain ⟨-, -, -, -, hFinX, hFinY, -⟩ :=
    theorem_4_5_interleaving_corrected (E := E) (H := H) (I := I) (X := X) hconv L f c hc hLip htame δ hδ hδρ α hL
  set DX := diagram0 f with hDXdef
  set DY := ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ with hDYdef
  have hsupX : ∀ P : EReal × EReal, ((α : ℝ) : EReal) < P.1 → DX P = 0 :=
    fun P hP => t45deg.t45deg_diagram0_support hvacF hP
  have hsupY : ∀ P : EReal × EReal, ((α : ℝ) : EReal) < P.1 → DY P = 0 :=
    fun P hP => t45deg.t45deg_ripsDiagram_support hvacF
      (fun x y : L => dist (x : X) (y : X)) δ hP
  let γ : Copies DX ≃ Copies DY := t45deg.t45deg_γ DX DY α hFinX hFinY
  have hfix : ∀ p : EReal × ℕ, ((α : ℝ) : EReal) < p.1 → γ (Sum.inr p) = Sum.inr p :=
    fun p h => t45deg.t45deg_γ_fix DX DY α hFinX hFinY p h
  have hfixSymm : ∀ p : EReal × ℕ, ((α : ℝ) : EReal) < p.1 →
      γ.symm (Sum.inr p) = Sum.inr p := by
    intro p h
    have key : γ (Sum.inr p) = Sum.inr p := hfix p h
    rw [← key]
    exact Equiv.symm_apply_apply _ _
  have hr : 0 ≤ c * δ := mul_nonneg hc hδ.le
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  -- (i): a : Copies DX, pt a ∈ QNE α
  · intro a ha
    rcases a with q | ⟨x, k⟩
    · have ha' : ((α : ℝ) : EReal) < (pt (Sum.inl q)).1 ∧
          ((α : ℝ) : EReal) < (pt (Sum.inl q)).2 := ha
      have hz : DX q.val.1 = 0 := hsupX _ ha'.1
      have hq := q.property
      rw [hz] at hq
      exfalso
      exact absurd (lt_of_le_of_lt (Nat.cast_nonneg q.val.2) hq) (lt_irrefl (0 : ℕ∞))
    · have ha' : ((α : ℝ) : EReal) < (pt (Sum.inr (x, k))).1 ∧
          ((α : ℝ) : EReal) < (pt (Sum.inr (x, k))).2 := ha
      have hγ : γ (Sum.inr (x, k)) = Sum.inr (x, k) := hfix (x, k) ha'.1
      rw [hγ]
      exact ⟨t45deg.t45deg_closeE_refl _ hr, t45deg.t45deg_closeE_refl _ hr⟩
  -- (ii): b : Copies DY, pt b ∈ QNE α
  · intro b hb
    rcases b with q | ⟨x, k⟩
    · have hb' : ((α : ℝ) : EReal) < (pt (Sum.inl q)).1 ∧
          ((α : ℝ) : EReal) < (pt (Sum.inl q)).2 := hb
      have hz : DY q.val.1 = 0 := hsupY _ hb'.1
      have hq := q.property
      rw [hz] at hq
      exfalso
      exact absurd (lt_of_le_of_lt (Nat.cast_nonneg q.val.2) hq) (lt_irrefl (0 : ℕ∞))
    · have hb' : ((α : ℝ) : EReal) < (pt (Sum.inr (x, k))).1 ∧
          ((α : ℝ) : EReal) < (pt (Sum.inr (x, k))).2 := hb
      have hγ : γ.symm (Sum.inr (x, k)) = Sum.inr (x, k) := hfixSymm (x, k) hb'.1
      rw [hγ]
      exact ⟨t45deg.t45deg_closeE_refl _ hr, t45deg.t45deg_closeE_refl _ hr⟩
  -- (iii): a : Copies DX, pt a ∈ QSE α
  · intro a ha
    rcases a with q | ⟨x, k⟩
    · have ha' : ((α : ℝ) : EReal) < (pt (Sum.inl q)).1 ∧
        (pt (Sum.inl q)).2 ≤ ((α : ℝ) : EReal) := ha
      have hz : DX q.val.1 = 0 := hsupX _ ha'.1
      have hq := q.property
      rw [hz] at hq
      exfalso
      exact absurd (lt_of_le_of_lt (Nat.cast_nonneg q.val.2) hq) (lt_irrefl (0 : ℕ∞))
    · have ha' : ((α : ℝ) : EReal) < (pt (Sum.inr (x, k))).1 ∧
        (pt (Sum.inr (x, k))).2 ≤ ((α : ℝ) : EReal) := ha
      exfalso
      exact absurd ha'.1 (not_lt.mpr ha'.2)
  -- (iv): b : Copies DY, pt b ∈ QSE α
  · intro b hb
    rcases b with q | ⟨x, k⟩
    · have hb' : ((α : ℝ) : EReal) < (pt (Sum.inl q)).1 ∧
        (pt (Sum.inl q)).2 ≤ ((α : ℝ) : EReal) := hb
      have hz : DY q.val.1 = 0 := hsupY _ hb'.1
      have hq := q.property
      rw [hz] at hq
      exfalso
      exact absurd (lt_of_le_of_lt (Nat.cast_nonneg q.val.2) hq) (lt_irrefl (0 : ℕ∞))
    · have hb' : ((α : ℝ) : EReal) < (pt (Sum.inr (x, k))).1 ∧
        (pt (Sum.inr (x, k))).2 ≤ ((α : ℝ) : EReal) := hb
      exfalso
      exact absurd hb'.1 (not_lt.mpr hb'.2)

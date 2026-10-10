-- Prove2me | solution 1 for PersistClust.Count.proof_thm_4_8_partition_count_transport_reverse
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T14:48:22.222996+00:00
-- url     : https://prove2.me/submissions/0787ae66-668b-4323-b379-269a807efc4b

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram

open PersistClust.Count

/-!
## Reverse inequality for the partition transport (Theorem 4.8, child 2)

`#copies(D', Δ^S_τ ∩ Λ^E_τ) ≤ #copies(D, Δ^S_d₂ ∩ Λ^E_d₂)`.

`γ.symm` pulls each `D'`-copy of the τ-window back to a `D`-copy whose
prominence `p.2 ≤ p.1 − (τ − 2cδ) ≤ p.1 − d₁`, hence off the `d₁`-diagonal, so
`hsep` lands it in `Δ^S_d₂ ∩ Λ^E_d₂`. Injectivity gives an injection,
hence the `encard` inequality.
-/

/-- `τ − 2cδ > d₁`, the key slack estimate (pure ℝ arithmetic from hτ₁). -/
private lemma rev_tau_minus_2cd_gt_d1
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) :
    d₁ < τ - 2 * c * δ := by
  linarith

/-- `τ − 2cδ > 0`. -/
private lemma rev_tau_minus_2cd_pos
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ) :
    0 < τ - 2 * c * δ := by
  linarith

/-- `c * δ < τ`. -/
private lemma rev_tau_gt_cd
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (d₁ : ℝ) (hd₁ : 0 ≤ d₁) (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) :
    c * δ < τ := by
  have hcd : 0 ≤ c * δ := by positivity
  linarith

/-- A point below the `τ`-diagonal with `x > cδ` is in `QNE (cδ)` or `QSE (cδ)`. -/
private lemma rev_quad_split {α : ℝ} (p : EReal × EReal)
    (hDS : p.2 ≤ p.1 - (α : EReal)) (hxE : (α : EReal) < p.1) :
    (α : EReal) < p.2 ∨ p.2 ≤ (α : EReal) := by
  by_cases h : p.2 ≤ (α : EReal)
  · exact Or.inr h
  · exact Or.inl (not_le.mp h)

/-- EReal shift estimate: for all `y : EReal`, `y + r + d₁ ≤ y + T − r`
whenever `d₁ + 2r < T` (reals `r T d₁`).  Handles `±∞` by cases. -/
private lemma rev_shift (r T d₁ : ℝ) (h : d₁ + 2 * r < T) (y : EReal) :
    (y + (r : EReal)) + (d₁ : EReal) ≤ (y + (T : EReal)) - (r : EReal) := by
  induction y with
  | bot =>
      rw [EReal.bot_add (r : EReal), EReal.bot_add (d₁ : EReal),
        EReal.bot_add (T : EReal), EReal.bot_sub (r : EReal)]
  | coe s => exact EReal.coe_le_coe_iff.mpr (by linarith)
  | top =>
      rw [EReal.top_add_coe r, EReal.top_add_coe d₁, EReal.top_add_coe T,
        EReal.top_sub_coe r]

/-- QNE chain: if the pulled-back point `(X, Y)` is `r`-close in both coordinates to the
τ-window point `(x, y)`, with `y ≤ x − T` and `d₁ + 2r < T`, then `Y ≤ X − d₁`. -/
private lemma rev_prom_chain
    (r T d₁ : ℝ) (h : d₁ + 2 * r < T) (x X y Y : EReal)
    (hcx : X ≤ x + (r : EReal) ∧ x ≤ X + (r : EReal))
    (hcy : Y ≤ y + (r : EReal) ∧ y ≤ Y + (r : EReal))
    (hyx : y ≤ x - (T : EReal)) :
    Y ≤ X - (d₁ : EReal) := by
  rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot d₁)) (Or.inl (EReal.coe_ne_top d₁))]
  have h1 : Y + (d₁ : EReal) ≤ (y + (r : EReal)) + (d₁ : EReal) := add_le_add hcy.1 le_rfl
  have h2 := rev_shift r T d₁ h y
  have hmeas : y + (T : EReal) ≤ x := EReal.add_le_of_le_sub hyx
  have h3 : (y + (T : EReal)) - (r : EReal) ≤ X :=
    EReal.sub_le_of_le_add (le_trans hmeas hcx.2)
  exact le_trans (le_trans h1 h2) h3

/-- QSE-low chain: if only the first coordinates are `r`-close (`X` close to `x`, `T < x`)
and `Y ≤ r`, then `Y ≤ X − d₁`. -/
private lemma rev_quad_chain
    (r T d₁ : ℝ) (h : d₁ + 2 * r < T) (x X Y : EReal)
    (hxT : (T : EReal) < x)
    (hcx : X ≤ x + (r : EReal) ∧ x ≤ X + (r : EReal))
    (hY : Y ≤ (r : EReal)) :
    Y ≤ X - (d₁ : EReal) := by
  rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot d₁)) (Or.inl (EReal.coe_ne_top d₁))]
  have h1 : Y + (d₁ : EReal) ≤ (r : EReal) + (d₁ : EReal) := add_le_add hY le_rfl
  have hco1 : ((r + d₁ : ℝ) : EReal) = (r : EReal) + (d₁ : EReal) := EReal.coe_add r d₁
  have hlt : (r + d₁ : ℝ) < T - r := by linarith
  have hco3 : ((r + d₁ : ℝ) : EReal) < ((T - r : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr hlt
  have hco4 : ((T - r : ℝ) : EReal) = (T : EReal) - (r : EReal) := (EReal.coe_sub T r).symm
  have h4 : ((T - r : ℝ) : EReal) < x - (r : EReal) := by
    rw [hco4]
    exact EReal.sub_lt_sub_of_lt_of_le hxT (le_refl (r : EReal)) (EReal.coe_ne_bot r)
      (EReal.coe_ne_top r)
  have h5 : x - (r : EReal) ≤ X := EReal.sub_le_of_le_add hcx.2
  calc Y + (d₁ : EReal) ≤ (r : EReal) + (d₁ : EReal) := h1
    _ = ((r + d₁ : ℝ) : EReal) := hco1.symm
    _ ≤ ((T - r : ℝ) : EReal) := le_of_lt hco3
    _ ≤ x - (r : EReal) := le_of_lt h4
    _ ≤ X := h5

/-- Given a `D'`-copy `Sum.inl ⟨q, hq⟩` of a point in the τ-window `Δ^S_τ ∩ Λ^E_τ`, the
`γ.symm`-preimage is an off-diagonal `D`-copy `Sum.inl ⟨p, hp⟩`.

A diagonal preimage `Sum.inr x₀` is excluded: `q.1.1 > τ > cδ` puts `q.1` in `QNE (cδ)`
or `QSE (cδ)`, so assertions (ii)/(iv) give `closeE x₀.1 q.1.1 (cδ)`; if `x₀.1 ≤ cδ`
then `q.1.1 ≤ 2cδ < τ < q.1.1`, while if `x₀.1 > cδ` then `(x₀.1, x₀.1) ∈ QNE (cδ)`
and assertion (i) gives `closeE x₀.1 q.1.2 (cδ)` too, forcing `τ ≤ 2cδ` against
`τ > d₁ + 2cδ ≥ 2cδ` (with the ±∞ cases handled by diagram-likeness of `D'`). -/
private lemma rev_preimage_inl
    (D D' : EReal × EReal → ℕ∞) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ)
    (q : (EReal × EReal) × ℕ) (hq : (q.2 : ℕ∞) < D' q.1)
    (hqDS : q.1 ∈ DeltaS τ) (hqE : q.1 ∈ LamE τ) :
    ∃ (p : (EReal × EReal) × ℕ) (hp : (p.2 : ℕ∞) < D p.1),
      γ (Sum.inl ⟨p, hp⟩) = Sum.inl ⟨q, hq⟩ := by
  obtain ⟨hi, hii, hiii, hiv⟩ := hγ
  have h2cδ : (2 * c * δ : ℝ) < τ := by linarith
  have hcdτ : (c * δ : ℝ) < τ := by
    have h0 : 0 < c * δ := mul_pos hc hδ
    linarith
  have hLE : (τ : EReal) < q.1.1 := hqE
  have hDS : q.1.2 ≤ q.1.1 - (τ : EReal) := hqDS
  have hD'q : D' q.1 ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le : (0 : ℕ∞) ≤ (q.2 : ℕ∞)) hq)
  have hxy : q.1.2 < q.1.1 := hD' q.1 hD'q
  have hqx_gt_r : (c * δ : EReal) < q.1.1 :=
    lt_trans (EReal.coe_lt_coe_iff.mpr hcdτ) hLE
  -- the pullback cannot be a diagonal copy
  have hnotdiag : ∀ x₀ : EReal × ℕ, γ.symm (Sum.inl ⟨q, hq⟩) ≠ Sum.inr x₀ := by
    intro x₀ hxr
    have hgsymm : γ (Sum.inr x₀) = Sum.inl ⟨q, hq⟩ := by
      have hgs := Equiv.apply_symm_apply γ (Sum.inl ⟨q, hq⟩)
      rwa [hxr] at hgs
    -- first-coordinate closeness, from (ii) or (iv)
    have hcx : closeE x₀.1 q.1.1 (c * δ) := by
      by_cases hqy : (c * δ : EReal) < q.1.2
      · have hQNE' : pt (Sum.inl ⟨q, hq⟩) ∈ QNE (c * δ) := by
          show (c * δ : EReal) < q.1.1 ∧ (c * δ : EReal) < q.1.2
          exact ⟨hqx_gt_r, hqy⟩
        have hcc := hii (Sum.inl ⟨q, hq⟩) hQNE'
        rw [hxr] at hcc
        exact hcc.1
      · have hQSE' : pt (Sum.inl ⟨q, hq⟩) ∈ QSE (c * δ) := by
          show (c * δ : EReal) < q.1.1 ∧ q.1.2 ≤ (c * δ : EReal)
          exact ⟨hqx_gt_r, le_of_not_gt hqy⟩
        have hcc := hiv (Sum.inl ⟨q, hq⟩) hQSE'
        rw [hxr] at hcc
        exact hcc
    by_cases hx0 : x₀.1 ≤ (c * δ : EReal)
    · -- q.1.1 ≤ x₀.1 + cδ ≤ 2cδ < τ < q.1.1 : contradiction
      have h1 : x₀.1 + (c * δ : EReal) ≤ (c * δ : EReal) + (c * δ : EReal) :=
        add_le_add hx0 le_rfl
      have h2le : q.1.1 ≤ (c * δ : EReal) + (c * δ : EReal) :=
        le_trans hcx.2 h1
      have h2sum : (c * δ : EReal) + (c * δ : EReal) < (τ : EReal) := by
        have hreal : (c * δ + c * δ : ℝ) < τ := by linarith
        exact EReal.coe_lt_coe_iff.mpr hreal
      exact absurd (lt_trans h2sum hLE) (not_lt.mpr h2le)
    · -- x₀.1 > cδ : the diagonal copy lies in QNE, so (i) gives both-coordinate closeness
      have hx0' : (c * δ : EReal) < x₀.1 := not_le.mp hx0
      have hQNEb : pt (Sum.inr x₀ : Copies D) ∈ QNE (c * δ) := by
        show (c * δ : EReal) < (pt (Sum.inr x₀ : Copies D)).1
          ∧ (c * δ : EReal) < (pt (Sum.inr x₀ : Copies D)).2
        exact ⟨hx0', hx0'⟩
      obtain ⟨_, hcB⟩ := hi (Sum.inr x₀) hQNEb
      rw [hgsymm] at hcB
      -- hcB : closeE x₀.1 q.1.2 (cδ)
      have hu1 : x₀.1 ≤ q.1.2 + ((c * δ : ℝ) : EReal) := hcB.1
      by_cases hyt : q.1.2 = ⊤
      · rw [hyt] at hxy
        exact absurd hxy (not_lt.mpr le_top)
      by_cases hyb : q.1.2 = ⊥
      · rw [hyb, EReal.bot_add] at hu1
        rw [le_bot_iff] at hu1
        rw [hu1] at hx0'
        exact absurd hx0' (not_lt.mpr bot_le)
      · -- all of x₀.1, q.1.2, q.1.1 are real; τ ≤ 2cδ follows, contradicting hτ₁
        have hyreal : ((q.1.2).toReal : EReal) = q.1.2 := EReal.coe_toReal hyt hyb
        have hx0nt : x₀.1 ≠ ⊤ := by
          intro hcon
          rw [hcon, ← hyreal] at hu1
          exact absurd hu1 (not_le_of_gt (EReal.coe_lt_top (q.1.2.toReal + c * δ)))
        have hx0nb : x₀.1 ≠ ⊥ := by
          intro hcon
          rw [hcon] at hx0'
          exact absurd hx0' (not_lt.mpr bot_le)
        have hx0real : ((x₀.1).toReal : EReal) = x₀.1 := EReal.coe_toReal hx0nt hx0nb
        have hxqnt : q.1.1 ≠ ⊤ := by
          intro hcon
          have huq : q.1.1 ≤ x₀.1 + (c * δ : EReal) := hcx.2
          rw [hcon, ← hx0real] at huq
          exact absurd huq (not_le_of_gt (EReal.coe_lt_top (x₀.1.toReal + c * δ)))
        have hxqnb : q.1.1 ≠ ⊥ := by
          intro hcon
          rw [hcon] at hLE
          exact absurd hLE (not_lt.mpr bot_le)
        have hxqreal : ((q.1.1).toReal : EReal) = q.1.1 := EReal.coe_toReal hxqnt hxqnb
        have hDSreal : q.1.2.toReal ≤ q.1.1.toReal - τ := by
          have hDSc := hDS
          rw [← hyreal, ← hxqreal, ← EReal.coe_sub] at hDSc
          exact EReal.coe_le_coe_iff.mp hDSc
        have hxqreal2 : q.1.1.toReal ≤ x₀.1.toReal + c * δ := by
          have huq := hcx.2
          rw [← hxqreal, ← hx0real, ← EReal.coe_add] at huq
          exact EReal.coe_le_coe_iff.mp huq
        have hu1real : x₀.1.toReal ≤ q.1.2.toReal + c * δ := by
          rw [← hx0real, ← hyreal, ← EReal.coe_add] at hu1
          exact EReal.coe_le_coe_iff.mp hu1
        exact absurd (show τ ≤ 2 * c * δ by linarith) (not_le_of_gt h2cδ)
  cases hb : γ.symm (Sum.inl ⟨q, hq⟩) with
  | inl w =>
      obtain ⟨p, hp⟩ := w
      refine ⟨p, hp, ?_⟩
      have hgs := Equiv.apply_symm_apply γ (Sum.inl ⟨q, hq⟩)
      rwa [hb] at hgs
  | inr x₀ => exact absurd hb (hnotdiag x₀)

/-- Core prominence bound: the `γ.symm`-pullback `p := pt b` of a `Δ^S_τ`-copy satisfies
`p.2 ≤ p.1 − d₁`, hence `p ∉ Δ^N_{d₁}`.

This combines the three subcases (QNE / QSE-hi / QSE-lo) using SatisfiesIIV assertions
(i)/(ii)/(iv) and the τ-window membership of `q.1`.  -/
private lemma rev_not_deltaN
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ)
    (q : (EReal × EReal) × ℕ) (hq : (q.2 : ℕ∞) < D' q.1)
    (hqDS : q.1 ∈ DeltaS τ) (hqE : q.1 ∈ LamE τ)
    (b : Copies D) (hb : γ b = Sum.inl ⟨q, hq⟩) :
    pt b ∉ DeltaN d₁ := by
  obtain ⟨p, hp, hpb⟩ :=
    rev_preimage_inl D D' hD' c δ hc hδ γ hγ d₁ d₂ hd₁ hδc τ hτ₁ hτ₂ q hq hqDS hqE
  obtain ⟨hi, hii, hiii, hiv⟩ := hγ
  -- the preimage is the off-diagonal copy Sum.inl ⟨p, hp⟩
  have hbs2 : γ.symm (Sum.inl ⟨q, hq⟩) = Sum.inl ⟨p, hp⟩ := by
    have hgg : γ (γ.symm (Sum.inl ⟨q, hq⟩)) = γ (Sum.inl ⟨p, hp⟩) := by
      rw [Equiv.apply_symm_apply, hpb]
    exact γ.injective hgg
  have hbs : b = Sum.inl ⟨p, hp⟩ := by
    have h1 : γ.symm (γ b) = b := Equiv.symm_apply_apply γ b
    rw [hb] at h1
    rw [hbs2] at h1
    exact h1.symm
  -- arithmetic setup
  have h2r : d₁ + 2 * (c * δ) < τ := by linarith
  have h2cδ : (2 * c * δ : ℝ) < τ := by linarith
  have hcdτ : (c * δ : ℝ) < τ := by
    have h0 : 0 < c * δ := mul_pos hc hδ
    linarith
  have hLE : (τ : EReal) < q.1.1 := hqE
  have hDS : q.1.2 ≤ q.1.1 - (τ : EReal) := hqDS
  have hqx_gt_r : (c * δ : EReal) < q.1.1 :=
    lt_trans (EReal.coe_lt_coe_iff.mpr hcdτ) hLE
  -- the prominence bound p.1.2 ≤ p.1.1 − d₁, by quadrant split on q.1.2
  have hprom : p.1.2 ≤ p.1.1 - (d₁ : EReal) := by
    by_cases hqy : (c * δ : EReal) < q.1.2
    · -- QNE: assertion (ii) gives both-coordinate closeness
      have hQNE' : pt (Sum.inl ⟨q, hq⟩) ∈ QNE (c * δ) := by
        show (c * δ : EReal) < q.1.1 ∧ (c * δ : EReal) < q.1.2
        exact ⟨hqx_gt_r, hqy⟩
      have hcc := hii (Sum.inl ⟨q, hq⟩) hQNE'
      rw [hbs2] at hcc
      have hcx : p.1.1 ≤ q.1.1 + (c * δ : EReal) ∧ q.1.1 ≤ p.1.1 + (c * δ : EReal) := hcc.1
      have hcy : p.1.2 ≤ q.1.2 + (c * δ : EReal) ∧ q.1.2 ≤ p.1.2 + (c * δ : EReal) := hcc.2
      exact rev_prom_chain (c * δ) τ d₁ h2r q.1.1 p.1.1 q.1.2 p.1.2 hcx hcy hDS
    · -- QSE: assertion (iv) gives first-coordinate closeness
      have hqyle : q.1.2 ≤ (c * δ : EReal) := le_of_not_gt hqy
      have hQSE' : pt (Sum.inl ⟨q, hq⟩) ∈ QSE (c * δ) := by
        show (c * δ : EReal) < q.1.1 ∧ q.1.2 ≤ (c * δ : EReal)
        exact ⟨hqx_gt_r, hqyle⟩
      have hcc := hiv (Sum.inl ⟨q, hq⟩) hQSE'
      rw [hbs2] at hcc
      have hcx : p.1.1 ≤ q.1.1 + (c * δ : EReal) ∧ q.1.1 ≤ p.1.1 + (c * δ : EReal) := hcc
      -- p.1.1 > τ − cδ > cδ
      have hTmrx : ((τ - c * δ : ℝ) : EReal) < q.1.1 - (c * δ : EReal) :=
        EReal.sub_lt_sub_of_lt_of_le hLE (le_refl (c * δ : EReal)) (EReal.coe_ne_bot (c * δ))
          (EReal.coe_ne_top (c * δ))
      have hcd1 : (c * δ : ℝ) < τ - c * δ := by linarith
      have hXgt : (c * δ : EReal) < p.1.1 :=
        lt_of_lt_of_le (lt_trans (EReal.coe_lt_coe_iff.mpr hcd1) hTmrx)
          (EReal.sub_le_of_le_add hcx.2)
      by_cases hpY : (c * δ : EReal) < p.1.2
      · -- p.1 ∈ QNE : assertion (i) (forward) gives the second-coordinate closeness
        have hQNEp : pt (Sum.inl ⟨p, hp⟩) ∈ QNE (c * δ) := by
          show (c * δ : EReal) < p.1.1 ∧ (c * δ : EReal) < p.1.2
          exact ⟨hXgt, hpY⟩
        have hcc2 := hi (Sum.inl ⟨p, hp⟩) hQNEp
        rw [hpb] at hcc2
        have hcy : p.1.2 ≤ q.1.2 + (c * δ : EReal) ∧ q.1.2 ≤ p.1.2 + (c * δ : EReal) :=
          hcc2.2
        exact rev_prom_chain (c * δ) τ d₁ h2r q.1.1 p.1.1 q.1.2 p.1.2 hcx hcy hDS
      · -- p.1.2 ≤ cδ : the low-quadrant chain
        have hpYle : p.1.2 ≤ (c * δ : EReal) := le_of_not_gt hpY
        exact rev_quad_chain (c * δ) τ d₁ h2r q.1.1 p.1.1 p.1.2 hLE hcx hpYle
  rw [hbs]
  intro hN
  exact absurd hN (not_lt.mpr hprom)

/-- `hsep` landing: `D (pt b) ≠ 0` and `pt b ∉ Δ^N_{d₁}` ⟹ `pt b ∈ Δ^S_{d₂} ∩ Λ^E_{d₂}`. -/
private lemma rev_sep_landing
    (D : EReal × EReal → ℕ∞) {d₁ d₂ : ℝ} (hsep : IsSeparated D d₁ d₂)
    (b : Copies D) (hDp : D (pt b) ≠ 0) (hnotN : pt b ∉ DeltaN d₁) :
    pt b ∈ DeltaS d₂ ∧ pt b ∈ LamE d₂ := by
  rcases hsep (pt b) hDp with hN | hS
  · exact absurd hN hnotN
  · exact hS

/-- Pointwise membership: `γ.symm` of a `Sum.inl` `D'`-copy of `Δ^S_τ ∩ Λ^E_τ` lands in
`Δ^S_{d₂} ∩ Λ^E_{d₂}` as a `Sum.inl` `D`-copy `p` with `D p.1 ≠ 0`. -/
private lemma rev_pointwise
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (hsep : IsSeparated D d₁ d₂)
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ)
    (q : (EReal × EReal) × ℕ) (hq : (q.2 : ℕ∞) < D' q.1)
    (hqDS : q.1 ∈ DeltaS τ) (hqE : q.1 ∈ LamE τ) :
    ∃ (p : (EReal × EReal) × ℕ) (hp : (p.2 : ℕ∞) < D p.1),
      γ (Sum.inl ⟨p, hp⟩) = Sum.inl ⟨q, hq⟩ ∧ p.1 ∈ DeltaS d₂ ∩ LamE d₂ := by
  obtain ⟨p, hp, hpb⟩ :=
    rev_preimage_inl D D' hD' c δ hc hδ γ hγ d₁ d₂ hd₁ hδc τ hτ₁ hτ₂ q hq hqDS hqE
  refine ⟨p, hp, hpb, ?_⟩
  have hnotN : pt (Sum.inl ⟨p, hp⟩) ∉ DeltaN d₁ :=
    rev_not_deltaN D D' hD hD' c δ hc hδ γ hγ d₁ d₂ hd₁ hδc τ hτ₁ hτ₂ q hq hqDS hqE
      (Sum.inl ⟨p, hp⟩) hpb
  have hDp : D (pt (Sum.inl ⟨p, hp⟩)) ≠ 0 :=
    ne_of_gt (lt_of_le_of_lt (zero_le : (0 : ℕ∞) ≤ (p.2 : ℕ∞)) hp)
  exact rev_sep_landing D hsep (Sum.inl ⟨p, hp⟩) hDp hnotN

/-- Encard-lift assembly: injectivity of `γ` + pointwise membership ⟹ encard inequality. -/
private lemma rev_encard_lift
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (hsep : IsSeparated D d₁ d₂)
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ) :
    {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D' q.1 ∧ q.1 ∈ DeltaS τ ∩ LamE τ}.encard
      ≤ {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D q.1 ∧ q.1 ∈ DeltaS d₂ ∩ LamE d₂}.encard := by
  have key : ∀ (q : (EReal × EReal) × ℕ) (hq : (q.2 : ℕ∞) < D' q.1)
      (hqin : q.1 ∈ DeltaS τ ∩ LamE τ),
      ∃ (p : (EReal × EReal) × ℕ) (hp : (p.2 : ℕ∞) < D p.1),
        γ (Sum.inl ⟨p, hp⟩) = Sum.inl ⟨q, hq⟩ ∧ p.1 ∈ DeltaS d₂ ∩ LamE d₂ :=
    fun q hq hqin =>
      rev_pointwise D D' hD hD' c δ hc hδ γ hγ d₁ d₂ hd₁ hδc hsep τ hτ₁ hτ₂ q hq
        hqin.1 hqin.2
  choose p hp H using key
  have hInj : Function.Injective
      (fun a : {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < D' q.1 ∧ q.1 ∈ DeltaS τ ∩ LamE τ} =>
        (⟨p a.1 a.2.1 a.2.2, ⟨hp a.1 a.2.1 a.2.2, (H a.1 a.2.1 a.2.2).2⟩⟩ :
          {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < D q.1 ∧ q.1 ∈ DeltaS d₂ ∩ LamE d₂})) := by
    intro a₁ a₂ heq
    have hp' : p a₁.1 a₁.2.1 a₁.2.2 = p a₂.1 a₂.2.1 a₂.2.2 := congrArg Subtype.val heq
    have h₁ : γ (Sum.inl ⟨p a₁.1 a₁.2.1 a₁.2.2, hp a₁.1 a₁.2.1 a₁.2.2⟩)
        = Sum.inl ⟨a₁.1, a₁.2.1⟩ := (H a₁.1 a₁.2.1 a₁.2.2).1
    have h₂ : γ (Sum.inl ⟨p a₂.1 a₂.2.1 a₂.2.2, hp a₂.1 a₂.2.1 a₂.2.2⟩)
        = Sum.inl ⟨a₂.1, a₂.2.1⟩ := (H a₂.1 a₂.2.1 a₂.2.2).1
    have hga : (Sum.inl ⟨a₁.1, a₁.2.1⟩ : Copies D') = Sum.inl ⟨a₂.1, a₂.2.1⟩ := by
      have hX : (Sum.inl ⟨p a₁.1 a₁.2.1 a₁.2.2, hp a₁.1 a₁.2.1 a₁.2.2⟩ : Copies D)
          = Sum.inl ⟨p a₂.1 a₂.2.1 a₂.2.2, hp a₂.1 a₂.2.1 a₂.2.2⟩ :=
        congrArg Sum.inl (Subtype.ext hp')
      calc Sum.inl ⟨a₁.1, a₁.2.1⟩
          = γ (Sum.inl ⟨p a₁.1 a₁.2.1 a₁.2.2, hp a₁.1 a₁.2.1 a₁.2.2⟩) := h₁.symm
        _ = γ (Sum.inl ⟨p a₂.1 a₂.2.1 a₂.2.2, hp a₂.1 a₂.2.1 a₂.2.2⟩) := congrArg γ hX
        _ = Sum.inl ⟨a₂.1, a₂.2.1⟩ := h₂
    have hinj : (⟨a₁.1, a₁.2.1⟩ :
        {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < D' q.1}) = ⟨a₂.1, a₂.2.1⟩ :=
      Sum.inl.inj hga
    have hv : a₁.1 = a₂.1 := by
      have hinjval := congrArg Subtype.val hinj
      exact hinjval
    exact Subtype.ext hv
  exact ENat.card_le_card_of_injective hInj

/-- The main reverse inequality. -/
theorem solution
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (hsep : IsSeparated D d₁ d₂)
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ) :
    {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D' q.1 ∧ q.1 ∈ DeltaS τ ∩ LamE τ}.encard
      ≤ {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D q.1 ∧ q.1 ∈ DeltaS d₂ ∩ LamE d₂}.encard := by
  exact rev_encard_lift D D' hD hD' c δ hc hδ γ hγ d₁ d₂ hd₁ hδc hsep τ hτ₁ hτ₂

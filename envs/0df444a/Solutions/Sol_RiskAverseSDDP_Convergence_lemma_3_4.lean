-- Prove2me | solution 1 for RiskAverseSDDP.Convergence.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:04:29.405396+00:00
-- url     : https://prove2.me/submissions/b47e824f-7ac4-48c7-b6ef-f5222829072a

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run

open RiskAverseSDDP.Convergence

namespace RASDDPLemma34

/-- `w * (z + c) = w * z + w * c` for a real `w ≥ 0` and a real `c`. -/
lemma mul_add_coe {w : ℝ} (hw : 0 ≤ w) (z : EReal) (c : ℝ) :
    (w : EReal) * (z + (c : EReal)) = (w : EReal) * z + ((w * c : ℝ) : EReal) := by
  rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hw) (EReal.coe_ne_top w),
    EReal.coe_mul]

lemma sum_add_coe {M : ℕ} (a : Fin M → EReal) (b : Fin M → ℝ) :
    ∑ j, (a j + ((b j : ℝ) : EReal)) = (∑ j, a j) + ((∑ j, b j : ℝ) : EReal) := by
  rw [Finset.sum_add_distrib]
  congr 1
  induction (Finset.univ : Finset (Fin M)) using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

lemma stageVal_mono {T n M q p : ℕ} (D : Model T n M q p) (s : ℕ) (j : Fin M)
    {V W : Hist n (s + 1) → EReal} (h : ∀ y, V y ≤ W y) (x : Hist n s) :
    D.stageVal s j V x ≤ D.stageVal s j W x := by
  unfold Model.stageVal
  exact iInf₂_mono fun y _ => add_le_add_right (h _) _

end RASDDPLemma34

open RASDDPLemma34 in
theorem solution {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r) :
    ∀ s, s + 2 ≤ T → ∀ k, 1 ≤ k →
      r.Qm k (s + 1) (r.hist k s (sampNode ys k s)) = r.θ k s := by
  intro s hs k hk
  obtain ⟨hQ0, hQT, _, hcut⟩ := hr
  set xt : ℕ → Hist n (s + 1) := fun l => r.hist l s (sampNode ys l s) with hxt
  -- monotonicity at stage s+2
  have hmono2 : ∀ a b, a ≤ b → ∀ y, r.Qm a (s + 2) y ≤ r.Qm b (s + 2) y := by
    rcases Nat.lt_or_ge (s + 2) T with hlt | hge
    · have hstep : ∀ a y, r.Qm a (s + 2) y ≤ r.Qm (a + 1) (s + 2) y := by
        intro a y
        obtain ⟨-, -, -, -, -, this⟩ := hcut a (s + 1) (by omega)
        rw [this]
        exact le_max_left _ _
      intro a b hab y
      induction b, hab using Nat.le_induction with
      | base => exact le_rfl
      | succ b _ ih => exact ih.trans (hstep b y)
    · have hT : s + 2 = T := by omega
      intro a b _ y
      subst hT
      rw [hQT a, hQT b]
  -- the key inequality: earlier cuts are below θ at the current trial point
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have key : ∀ l, l ≤ k' →
      r.θ (l + 1) s + ((inner ℝ (r.β (l + 1) s) (xt (k' + 1) - xt (l + 1)) : ℝ) : EReal) ≤
        r.θ (k' + 1) s := by
    intro l hl
    obtain ⟨hpl, _, hπl, hθl, hβl, _⟩ := hcut l s hs
    obtain ⟨_, hrk, _, hθk, _, _⟩ := hcut k' s hs
    set Zl : Fin M → EReal := fun j => D.stageVal (s + 1) j (r.Qm l (s + 2)) (xt (l + 1))
    set Zk : Fin M → EReal := fun j => D.stageVal (s + 1) j (r.Qm k' (s + 2)) (xt (k' + 1))
    set pl := R.pRule (s + 2) Zl
    set d := xt (k' + 1) - xt (l + 1)
    have hw : ∀ j, 0 ≤ pl j * D.Φ (s + 2) j := by
      intro j
      have hS' := hS (s + 2) (by omega) hs
      have hpd := hS'.2.2.1 hpl
      exact mul_nonneg (hpd.1 j) (hS'.1 j).le
    -- subgradient inequality, then monotonicity
    have hsub : ∀ j, Zl j + ((inner ℝ (r.π (l + 1) s j) d : ℝ) : EReal) ≤ Zk j := by
      intro j
      have h1 := (hπl j).2 (xt (k' + 1))
      exact h1.trans (stageVal_mono D (s + 1) j (hmono2 l k' hl) _)
    have hinner : inner ℝ (r.β (l + 1) s) d =
        ∑ j, (pl j * D.Φ (s + 2) j) * inner ℝ (r.π (l + 1) s j) d := by
      rw [hβl, sum_inner]
      simp only [real_inner_smul_left]
    calc r.θ (l + 1) s + ((inner ℝ (r.β (l + 1) s) d : ℝ) : EReal)
        = ∑ j, (((pl j * D.Φ (s + 2) j : ℝ) : EReal) * Zl j +
            (((pl j * D.Φ (s + 2) j) * inner ℝ (r.π (l + 1) s j) d : ℝ) : EReal)) := by
          rw [sum_add_coe, hθl, hinner]; rfl
      _ = ∑ j, ((pl j * D.Φ (s + 2) j : ℝ) : EReal) *
            (Zl j + ((inner ℝ (r.π (l + 1) s j) d : ℝ) : EReal)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_add_coe (hw j)]
      _ ≤ ∑ j, ((pl j * D.Φ (s + 2) j : ℝ) : EReal) * Zk j := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_left (hsub j) (by exact_mod_cast hw j)
      _ = D.wsum (s + 2) pl Zk := rfl
      _ ≤ D.rho (s + 2) Zk := by
          unfold Model.rho
          exact le_iSup₂ (f := fun π _ => D.wsum (s + 2) π Zk) pl hpl
      _ = r.θ (k' + 1) s := by rw [hθk, hrk]
  -- all approximations before iteration k'+1 are below θ at the trial point
  have hbelow : ∀ j, j ≤ k' → r.Qm j (s + 1) (xt (k' + 1)) ≤ r.θ (k' + 1) s := by
    intro j hj
    induction j with
    | zero => rw [hQ0 (s + 1) (by omega) (by omega)]; exact bot_le
    | succ j ih =>
      obtain ⟨-, -, -, -, -, this⟩ := hcut j s hs
      rw [this]
      exact max_le (ih (by omega)) (key j (by omega))
  obtain ⟨-, -, -, -, -, hupd⟩ := hcut k' s hs
  show r.Qm (k' + 1) (s + 1) (xt (k' + 1)) = r.θ (k' + 1) s
  rw [hupd]
  have h0 : xt (k' + 1) - r.hist (k' + 1) s (sampNode ys (k' + 1) s) = 0 := sub_self _
  simp only [h0, inner_zero_right, EReal.coe_zero, add_zero]
  exact max_eq_right (hbelow k' le_rfl)

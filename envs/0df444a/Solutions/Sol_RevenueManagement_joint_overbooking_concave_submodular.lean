-- Prove2me | solution 1 for RevenueManagement.joint_overbooking_concave_submodular
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T09:56:40.335694+00:00
-- url     : https://prove2.me/submissions/5e6e2193-5b5e-4352-b2fe-a8813cb6ddc2

import Mathlib
import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

open Finset
open scoped Pointwise

/-! ### The service-period transportation problem and its Lagrangian dual -/

section TP

variable {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ) (Cap : Fin (m + 1) → ℝ)

/-- The attainable net benefits of (TP) with real supplies `w`. -/
def tpSet (w : Fin n → ℝ) : Set ℝ :=
  {x | ∃ a : Fin n → Fin (m + 1) → ℝ, (∀ j i, 0 ≤ a j i) ∧ (∀ j, ∑ i, a j i = w j) ∧
    (∀ i, i ≠ 0 → ∑ j, a j i ≤ Cap i) ∧ x = ∑ j, ∑ i, h j i * a j i}

/-- `V(w, C)`, the value of (TP). -/
noncomputable def tpVal (w : Fin n → ℝ) : ℝ := sSup (tpSet h Cap w)

lemma serviceValue_eq_tpVal (z : Fin n → ℕ) :
    serviceValue h Cap z = tpVal h Cap (fun j => (z j : ℝ)) := rfl

lemma tp_nonempty (hCap : ∀ i, 0 ≤ Cap i) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) :
    (tpSet h Cap w).Nonempty := by
  classical
  refine ⟨_, fun j i => if i = 0 then w j else 0, fun j i => ?_, fun j => ?_, fun i hi => ?_, rfl⟩
  · dsimp only; split_ifs <;> simp [hw j]
  · simp
  · simp [hi, hCap i]

lemma tp_row_le {w : Fin n → ℝ} {a : Fin n → Fin (m + 1) → ℝ} (ha : ∀ j i, 0 ≤ a j i)
    (hrow : ∀ j, ∑ i, a j i = w j) (j : Fin n) (i : Fin (m + 1)) : a j i ≤ w j := by
  rw [← hrow j]
  exact Finset.single_le_sum (f := fun i => a j i) (fun i _ => ha j i) (Finset.mem_univ i)

lemma tp_bdd (w : Fin n → ℝ) : BddAbove (tpSet h Cap w) := by
  refine ⟨∑ j, ∑ i, |h j i| * w j, ?_⟩
  rintro x ⟨a, ha, hrow, -, rfl⟩
  apply Finset.sum_le_sum; intro j _
  apply Finset.sum_le_sum; intro i _
  calc h j i * a j i ≤ |h j i| * a j i := mul_le_mul_of_nonneg_right (le_abs_self _) (ha j i)
    _ ≤ |h j i| * w j := mul_le_mul_of_nonneg_left (tp_row_le ha hrow j i) (abs_nonneg _)

/-- `g_j(v) = max_i (h_{ji} − v_i)`. -/
noncomputable def tpG (v : Fin (m + 1) → ℝ) (j : Fin n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => h j i - v i)

/-- The Lagrangian dual objective `Ψ_w(v) = ∑_i C_i v_i + ∑_j w_j g_j(v)`. -/
noncomputable def tpPsi (w : Fin n → ℝ) (v : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i, Cap i * v i + ∑ j, w j * tpG h v j

/-- Dual feasibility: nonnegative prices, none for the virtual resource. -/
def tpDual (v : Fin (m + 1) → ℝ) : Prop := v 0 = 0 ∧ ∀ i, 0 ≤ v i

lemma tpG_ge (v : Fin (m + 1) → ℝ) (j : Fin n) (i : Fin (m + 1)) : h j i - v i ≤ tpG h v j :=
  Finset.le_sup' (fun i => h j i - v i) (Finset.mem_univ i)

/-- Weak duality. -/
lemma tp_weak (w : Fin n → ℝ) (v : Fin (m + 1) → ℝ) (hv : tpDual v)
    (a : Fin n → Fin (m + 1) → ℝ) (ha : ∀ j i, 0 ≤ a j i) (hrow : ∀ j, ∑ i, a j i = w j)
    (hcap : ∀ i, i ≠ 0 → ∑ j, a j i ≤ Cap i) :
    ∑ j, ∑ i, h j i * a j i ≤ tpPsi h Cap w v := by
  have e : ∑ j, ∑ i, h j i * a j i
      = ∑ j, ∑ i, (h j i - v i) * a j i + ∑ i, v i * ∑ j, a j i := by
    have h1 : ∑ j, ∑ i, h j i * a j i = ∑ j, ∑ i, ((h j i - v i) * a j i + v i * a j i) := by
      apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
    rw [h1]
    simp only [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
  rw [e]
  unfold tpPsi
  have h1 : ∑ j, ∑ i, (h j i - v i) * a j i ≤ ∑ j, w j * tpG h v j := by
    apply Finset.sum_le_sum; intro j _
    rw [← hrow j, Finset.sum_mul]
    apply Finset.sum_le_sum; intro i _
    rw [mul_comm (a j i)]
    exact mul_le_mul_of_nonneg_right (tpG_ge h v j i) (ha j i)
  have h2 : ∑ i, v i * ∑ j, a j i ≤ ∑ i, Cap i * v i := by
    apply Finset.sum_le_sum; intro i _
    by_cases hi : i = 0
    · subst hi; rw [hv.1]; simp
    · rw [mul_comm (Cap i)]
      exact mul_le_mul_of_nonneg_left (hcap i hi) (hv.2 i)
  linarith

lemma tp_val_le_psi (hCap : ∀ i, 0 ≤ Cap i) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (v : Fin (m + 1) → ℝ) (hv : tpDual v) : tpVal h Cap w ≤ tpPsi h Cap w v := by
  apply csSup_le (tp_nonempty h Cap hCap w hw)
  rintro x ⟨a, ha, hrow, hcap, rfl⟩
  exact tp_weak h Cap w v hv a ha hrow hcap

/-- Approximate strong duality, by separating `(0, V + ε)` from the closed convex set of
attainable (constraint slack, benefit) pairs. -/
lemma tp_strong (hCap : ∀ i, 0 ≤ Cap i) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (ε : ℝ)
    (hε : 0 < ε) : ∃ v, tpDual v ∧ tpPsi h Cap w v ≤ tpVal h Cap w + ε := by
  classical
  set V := tpVal h Cap w with hVdef
  set P : Set (Fin n → Fin (m + 1) → ℝ) := {a | (∀ j i, 0 ≤ a j i) ∧ ∀ j, ∑ i, a j i = w j}
    with hPdef
  set Φ : (Fin n → Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) × ℝ := fun a =>
    (fun i => if i = 0 then 0 else ∑ j, a j i - Cap i, ∑ j, ∑ i, h j i * a j i) with hΦdef
  set Cc : Set ((Fin (m + 1) → ℝ) × ℝ) := {x | ∀ i, 0 ≤ x.1 i} ∩ {x | x.2 ≤ 0} with hCcdef
  set A := Φ '' P + Cc with hAdef
  -- the pieces are compact / closed / convex
  have hPcl : IsClosed P := by
    have e : P = (⋂ j, ⋂ i, {a : Fin n → Fin (m + 1) → ℝ | 0 ≤ a j i}) ∩
        ⋂ j, {a : Fin n → Fin (m + 1) → ℝ | ∑ i, a j i = w j} := by
      ext a; simp [hPdef]
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun i => ?_)
      (isClosed_iInter fun j => ?_)
    · exact isClosed_le continuous_const ((continuous_apply i).comp (continuous_apply j))
    · exact isClosed_eq (continuous_finsetSum _ fun i _ =>
        (continuous_apply i).comp (continuous_apply j)) continuous_const
  have hPsub : P ⊆ Set.Icc 0 (fun j _ => w j) := by
    rintro a ⟨ha, hrow⟩
    exact ⟨fun j i => ha j i, fun j i => tp_row_le ha hrow j i⟩
  have hPc : IsCompact P := isCompact_Icc.of_isClosed_subset hPcl hPsub
  have hΦc : Continuous Φ := by
    refine Continuous.prodMk (continuous_pi fun i => ?_) ?_
    · by_cases hi : i = 0
      · simp only [hi, if_true]; exact continuous_const
      · simp only [hi, if_false]
        exact (continuous_finsetSum _ fun j _ =>
          (continuous_apply i).comp (continuous_apply j)).sub continuous_const
    · exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((continuous_apply i).comp (continuous_apply j))
  have hKc : IsCompact (Φ '' P) := hPc.image hΦc
  have hKconv : Convex ℝ (Φ '' P) := by
    rintro _ ⟨p1, ⟨hp1, hr1⟩, rfl⟩ _ ⟨p2, ⟨hp2, hr2⟩, rfl⟩ a b ha hb hab
    refine ⟨a • p1 + b • p2, ⟨fun j i => ?_, fun j => ?_⟩, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hp1 j i; have := hp2 j i; positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hr1 j, hr2 j]
      rw [← add_mul, hab, one_mul]
    · simp only [hΦdef, Prod.smul_mk, Prod.mk_add_mk]
      refine Prod.ext ?_ ?_
      · funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        split_ifs
        · ring
        · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          linear_combination (Cap i) * hab
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _
        ring
  have hCcl : IsClosed Cc := by
    refine IsClosed.inter ?_ (isClosed_le continuous_snd continuous_const)
    have e : {x : (Fin (m + 1) → ℝ) × ℝ | ∀ i, 0 ≤ x.1 i} = ⋂ i, {x | 0 ≤ x.1 i} := by
      ext x; simp
    rw [e]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      ((continuous_apply i).comp continuous_fst)
  have hCconv : Convex ℝ Cc := by
    rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ a b ha hb hab
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hx1 i; have := hy1 i; positivity
    · have hx2' : x.2 ≤ 0 := hx2
      have hy2' : y.2 ≤ 0 := hy2
      show (a • x + b • y).2 ≤ 0
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith
  have hCmem : ∀ x : (Fin (m + 1) → ℝ) × ℝ, (∀ i, 0 ≤ x.1 i) → x.2 ≤ 0 → x ∈ Cc :=
    fun x h1 h2 => ⟨h1, h2⟩
  have hAcl : IsClosed A := hCcl.add_left_of_isCompact hKc
  have hAconv : Convex ℝ A := hKconv.add hCconv
  -- the all-virtual assignment
  set a0 : Fin n → Fin (m + 1) → ℝ := fun j i => if i = 0 then w j else 0 with ha0def
  have ha0 : a0 ∈ P := by
    refine ⟨fun j i => ?_, fun j => ?_⟩
    · show 0 ≤ (if i = 0 then w j else 0)
      split_ifs <;> simp [hw j]
    · simp [ha0def]
  have hb0 : Φ a0 ∈ A :=
    ⟨Φ a0, ⟨a0, ha0, rfl⟩, 0, hCmem 0 (fun i => le_refl _) (le_refl _), add_zero _⟩
  -- `(0, V + ε)` is not attainable
  have hx0 : ((0 : Fin (m + 1) → ℝ), V + ε) ∉ A := by
    rintro ⟨_, ⟨a, ⟨ha, hrow⟩, rfl⟩, c, ⟨hc1, hc2⟩, hsum⟩
    have hc2' : c.2 ≤ 0 := hc2
    have e1 : ∀ i, (Φ a).1 i + c.1 i = 0 := fun i => by
      have := congrArg (fun x => x.1 i) hsum; simpa using this
    have e2 : (Φ a).2 + c.2 = V + ε := by
      have := congrArg (fun x => x.2) hsum; simpa using this
    have hcap : ∀ i, i ≠ 0 → ∑ j, a j i ≤ Cap i := by
      intro i hi
      have := e1 i
      simp only [hΦdef, hi, if_false] at this
      have := hc1 i
      linarith
    have hle : ∑ j, ∑ i, h j i * a j i ≤ V :=
      le_csSup (tp_bdd h Cap w) ⟨a, ha, hrow, hcap, rfl⟩
    simp only [hΦdef] at e2
    linarith
  obtain ⟨f, u0, hf0, hfA⟩ := geometric_hahn_banach_point_closed hAconv hAcl hx0
  -- coordinates of the separating functional
  set lam : Fin (m + 1) → ℝ := fun i => f ((Pi.single i 1 : Fin (m + 1) → ℝ), (0 : ℝ)) with hlam
  set μ : ℝ := f ((0 : Fin (m + 1) → ℝ), (1 : ℝ)) with hμ
  have hrep : ∀ x : (Fin (m + 1) → ℝ) × ℝ, f x = ∑ i, x.1 i * lam i + x.2 * μ := by
    intro x
    have hx : x = ∑ i, x.1 i • ((Pi.single i 1 : Fin (m + 1) → ℝ), (0 : ℝ))
        + x.2 • ((0 : Fin (m + 1) → ℝ), (1 : ℝ)) := by
      refine Prod.ext ?_ ?_
      · funext i
        simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    conv_lhs => rw [hx]
    rw [map_add, map_sum]
    simp only [map_smul, smul_eq_mul, hlam, hμ]
  -- signs of the coordinates
  have hfb0 : u0 < f (Φ a0) := hfA _ hb0
  have hlam0 : ∀ i, 0 ≤ lam i := by
    intro i
    by_contra hneg
    push Not at hneg
    set s := (f (Φ a0) - u0) / (-lam i) with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith)
    have hmem : Φ a0 + ((s • (Pi.single i 1 : Fin (m + 1) → ℝ)), (0 : ℝ)) ∈ A := by
      refine ⟨Φ a0, ⟨a0, ha0, rfl⟩, _, hCmem _ (fun i' => ?_) (le_refl _), rfl⟩
      simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs <;> simp [hs0]
    have := hfA _ hmem
    rw [map_add, hrep ((s • (Pi.single i 1 : Fin (m + 1) → ℝ)), (0 : ℝ))] at this
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero] at this
    have hcalc : s * lam i = -(f (Φ a0) - u0) := by
      have hne : lam i ≠ 0 := ne_of_lt hneg
      rw [hs]; field_simp
    linarith
  have hμ0 : μ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set s := (f (Φ a0) - u0) / μ with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith)
    have hmem : Φ a0 + ((0 : Fin (m + 1) → ℝ), -s) ∈ A :=
      ⟨Φ a0, ⟨a0, ha0, rfl⟩, _, hCmem _ (fun i' => le_refl _) (show -s ≤ 0 by linarith), rfl⟩
    have := hfA _ hmem
    rw [map_add, hrep ((0 : Fin (m + 1) → ℝ), -s)] at this
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] at this
    have hcalc : -s * μ = -(f (Φ a0) - u0) := by
      rw [hs]; field_simp
    linarith
  have hfx0 : f ((0 : Fin (m + 1) → ℝ), V + ε) = (V + ε) * μ := by
    rw [hrep]; simp
  have hμneg : μ < 0 := by
    rcases lt_or_eq_of_le hμ0 with h' | h'
    · exact h'
    · exfalso
      have h1 : f (Φ a0) ≤ 0 := by
        rw [hrep]
        simp only [hΦdef, ha0def, h', mul_zero, add_zero]
        apply Finset.sum_nonpos; intro i _
        split_ifs with hi
        · simp
        · simp only [hi, if_false, Finset.sum_const_zero, zero_sub]
          have := hCap i; have := hlam0 i; nlinarith
      rw [hfx0, h', mul_zero] at hf0
      linarith
  -- the dual prices
  set v : Fin (m + 1) → ℝ := fun i => if i = 0 then 0 else lam i / (-μ) with hvdef
  have hv : tpDual v := by
    refine ⟨by simp [hvdef], fun i => ?_⟩
    simp only [hvdef]; split_ifs
    · exact le_refl _
    · exact div_nonneg (hlam0 i) (by linarith)
  refine ⟨v, hv, ?_⟩
  -- every assignment has Lagrangian value below `V + ε`
  have hL : ∀ a ∈ P, ∑ j, ∑ i, h j i * a j i - ∑ i, (∑ j, a j i - Cap i) * v i < V + ε := by
    intro a haP
    have h1 := hfA _ ⟨Φ a, ⟨a, haP, rfl⟩, 0, hCmem 0 (fun i => le_refl _) (le_refl _), add_zero _⟩
    rw [hrep] at h1
    have h2 : ∑ i, (Φ a).1 i * lam i = (-μ) * ∑ i, (∑ j, a j i - Cap i) * v i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      simp only [hΦdef, hvdef]
      split_ifs with hi
      · simp
      · have hμne : μ ≠ 0 := ne_of_lt hμneg
        field_simp
    rw [h2] at h1
    have h3 := lt_trans hf0 h1
    rw [hfx0] at h3
    simp only [hΦdef] at h3
    nlinarith
  -- the best vertex attains the dual objective
  have hσ : ∀ j, ∃ i, tpG h v j = h j i - v i := by
    intro j
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => h j i - v i)
    exact ⟨i, hi⟩
  choose σ hσ using hσ
  set a1 : Fin n → Fin (m + 1) → ℝ := fun j i => if i = σ j then w j else 0 with ha1def
  have ha1 : a1 ∈ P := by
    refine ⟨fun j i => ?_, fun j => ?_⟩
    · simp only [ha1def]; split_ifs <;> simp [hw j]
    · simp [ha1def]
  have hval : ∑ j, ∑ i, h j i * a1 j i - ∑ i, (∑ j, a1 j i - Cap i) * v i
      = tpPsi h Cap w v := by
    unfold tpPsi
    have e1 : ∑ j, ∑ i, h j i * a1 j i = ∑ j, w j * h j (σ j) := by
      apply Finset.sum_congr rfl; intro j _
      simp [ha1def, mul_comm]
    have e2 : ∑ i, (∑ j, a1 j i - Cap i) * v i = ∑ j, w j * v (σ j) - ∑ i, Cap i * v i := by
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl; intro j _
      simp [ha1def]
    rw [e1, e2]
    have e3 : ∑ j, w j * tpG h v j = ∑ j, w j * (h j (σ j) - v (σ j)) :=
      Finset.sum_congr rfl (fun j _ => by rw [hσ j])
    rw [e3]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have := hL a1 ha1
  rw [hval] at this
  exact le_of_lt this

/-! ### Submodularity and concavity of `V` in the supplies -/

lemma tpG_inf (v1 v2 : Fin (m + 1) → ℝ) (j : Fin n) :
    tpG h (v1 ⊓ v2) j = max (tpG h v1 j) (tpG h v2 j) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    simp only [Pi.inf_apply]
    rcases le_total (v1 i) (v2 i) with hh | hh
    · rw [min_eq_left hh]; exact le_trans (tpG_ge h v1 j i) (le_max_left _ _)
    · rw [min_eq_right hh]; exact le_trans (tpG_ge h v2 j i) (le_max_right _ _)
  · apply max_le
    · apply Finset.sup'_le; intro i _
      exact le_trans (by simp only [Pi.inf_apply]; linarith [min_le_left (v1 i) (v2 i)])
        (tpG_ge h (v1 ⊓ v2) j i)
    · apply Finset.sup'_le; intro i _
      exact le_trans (by simp only [Pi.inf_apply]; linarith [min_le_right (v1 i) (v2 i)])
        (tpG_ge h (v1 ⊓ v2) j i)

lemma tpG_anti {v1 v2 : Fin (m + 1) → ℝ} (hv : v1 ≤ v2) (j : Fin n) : tpG h v2 j ≤ tpG h v1 j := by
  apply Finset.sup'_le; intro i _
  exact le_trans (by linarith [hv i]) (tpG_ge h v1 j i)

lemma tp_psi_lattice (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (k l : Fin n)
    (v1 v2 : Fin (m + 1) → ℝ) :
    tpPsi h Cap (w + Pi.single k 1 + Pi.single l 1) (v1 ⊔ v2) + tpPsi h Cap w (v1 ⊓ v2)
      ≤ tpPsi h Cap (w + Pi.single k 1) v1 + tpPsi h Cap (w + Pi.single l 1) v2 := by
  classical
  unfold tpPsi
  have hsingle : ∀ (u : Fin n → ℝ) (c : Fin n), ∑ j, (Pi.single c (1 : ℝ) : Fin n → ℝ) j * u j = u c := by
    intro u c; simp [Pi.single_apply]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hsingle]
  have hcap : ∑ i, Cap i * (v1 ⊔ v2) i + ∑ i, Cap i * (v1 ⊓ v2) i
      = ∑ i, Cap i * v1 i + ∑ i, Cap i * v2 i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    simp only [Pi.sup_apply, Pi.inf_apply]
    rcases le_total (v1 i) (v2 i) with hh | hh
    · rw [max_eq_right hh, min_eq_left hh]; ring
    · rw [max_eq_left hh, min_eq_right hh]
  have hg : ∑ j, w j * tpG h (v1 ⊔ v2) j + ∑ j, w j * tpG h (v1 ⊓ v2) j
      ≤ ∑ j, w j * tpG h v1 j + ∑ j, w j * tpG h v2 j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro j _
    rw [tpG_inf]
    have h1 := tpG_anti h (le_sup_left : v1 ≤ v1 ⊔ v2) j
    have h2 := tpG_anti h (le_sup_right : v2 ≤ v1 ⊔ v2) j
    have hw' := hw j
    rcases le_total (tpG h v1 j) (tpG h v2 j) with hh | hh
    · rw [max_eq_right hh]; nlinarith
    · rw [max_eq_left hh]; nlinarith
  have hk := tpG_anti h (le_sup_left : v1 ≤ v1 ⊔ v2) k
  have hl := tpG_anti h (le_sup_right : v2 ≤ v1 ⊔ v2) l
  linarith

/-- `V(w + e_k + e_l) + V(w) ≤ V(w + e_k) + V(w + e_l)`: submodularity for `k ≠ l` and
concavity along a coordinate for `k = l`. -/
lemma tp_submod (hCap : ∀ i, 0 ≤ Cap i) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (k l : Fin n) :
    tpVal h Cap (w + Pi.single k 1 + Pi.single l 1) + tpVal h Cap w
      ≤ tpVal h Cap (w + Pi.single k 1) + tpVal h Cap (w + Pi.single l 1) := by
  classical
  have hs : ∀ (c : Fin n) (j : Fin n), 0 ≤ (Pi.single c (1 : ℝ) : Fin n → ℝ) j := by
    intro c j; simp only [Pi.single_apply]; split_ifs <;> norm_num
  have hwk : ∀ j, 0 ≤ (w + (Pi.single k 1 : Fin n → ℝ)) j := fun j => by
    simp only [Pi.add_apply]; linarith [hw j, hs k j]
  have hwl : ∀ j, 0 ≤ (w + (Pi.single l 1 : Fin n → ℝ)) j := fun j => by
    simp only [Pi.add_apply]; linarith [hw j, hs l j]
  have hwkl : ∀ j, 0 ≤ (w + (Pi.single k 1 : Fin n → ℝ) + (Pi.single l 1 : Fin n → ℝ)) j :=
    fun j => by simp only [Pi.add_apply]; linarith [hw j, hs k j, hs l j]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨v1, hv1, h1⟩ := tp_strong h Cap hCap _ hwk (ε / 2) (by linarith)
  obtain ⟨v2, hv2, h2⟩ := tp_strong h Cap hCap _ hwl (ε / 2) (by linarith)
  have hsup : tpDual (v1 ⊔ v2) := ⟨by simp [hv1.1, hv2.1], fun i => le_trans (hv1.2 i) le_sup_left⟩
  have hinf : tpDual (v1 ⊓ v2) := ⟨by simp [hv1.1, hv2.1], fun i => le_inf (hv1.2 i) (hv2.2 i)⟩
  have h3 := tp_val_le_psi h Cap hCap _ hwkl _ hsup
  have h4 := tp_val_le_psi h Cap hCap _ hw _ hinf
  have h5 := tp_psi_lattice h Cap w hw k l v1 v2
  linarith

end TP


/-! ### Poisson counts -/

section Poisson

lemma rm2_poi_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) : 0 ≤ poissonPmf μ k := by
  unfold poissonPmf; positivity

lemma rm2_poi_hasSum {μ : ℝ} (hμ : 0 ≤ μ) : HasSum (poissonPmf μ) 1 :=
  ProbabilityTheory.hasSum_one_poissonMeasure ⟨μ, hμ⟩

/-- The Poisson mean. -/
lemma rm2_poi_mean {μ : ℝ} (hμ : 0 ≤ μ) : HasSum (fun k : ℕ => poissonPmf μ k * k) μ := by
  rw [← hasSum_nat_add_iff' 1]
  have e2 : μ - ∑ i ∈ range 1, poissonPmf μ i * (i : ℝ) = μ * 1 := by simp
  rw [e2]
  refine ((rm2_poi_hasSum hμ).mul_left μ).congr_fun (fun k => ?_)
  unfold poissonPmf
  rw [Nat.factorial_succ]; push_cast
  field_simp
  ring

lemma rm2_poi_lin_hasSum {a : ℝ} (ha : 0 ≤ a) (A B : ℝ) :
    HasSum (fun c : ℕ => poissonPmf a c * (A + B * c)) (A + B * a) := by
  have := ((rm2_poi_hasSum ha).mul_left A).add ((rm2_poi_mean ha).mul_left B)
  rw [mul_one] at this
  exact this.congr_fun (fun c => by ring)

lemma rm2_poi_summable {a : ℝ} (ha : 0 ≤ a) {g : ℕ → ℝ} {A B : ℝ} (hg : ∀ c : ℕ, |g c| ≤ A + B * c) :
    Summable (fun c => poissonPmf a c * g c) := by
  refine Summable.of_norm_bounded (rm2_poi_lin_hasSum ha A B).summable (fun c => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rm2_poi_nonneg ha c)]
  exact mul_le_mul_of_nonneg_left (hg c) (rm2_poi_nonneg ha c)

/-- Superposition of independent Poisson counts: `Poi(μ + a) = Poi(a) ∗ Poi(μ)`. -/
lemma rm2_poi_conv (μ a : ℝ) (m : ℕ) :
    poissonPmf (μ + a) m = ∑ c ∈ range (m + 1), poissonPmf a c * poissonPmf μ (m - c) := by
  unfold poissonPmf
  rw [show μ + a = a + μ by ring, add_pow, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c hc
  have hcm : c ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
  have h1 : (m.choose c : ℝ) * (c.factorial : ℝ) * ((m - c).factorial : ℝ) = (m.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hcm
  have hc0 : (c.factorial : ℝ) ≠ 0 := by positivity
  have hmc0 : ((m - c).factorial : ℝ) ≠ 0 := by positivity
  have hch : (m.choose c : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hcm).ne'
  rw [neg_add, Real.exp_add, ← h1]
  field_simp

/-! Independent Poisson counts on `Fin n → ℕ`. -/

variable {n : ℕ}

/-- The joint pmf of independent Poisson counts with means `μ`. -/
noncomputable def rm2P (μ : Fin n → ℝ) (z : Fin n → ℕ) : ℝ := ∏ j, poissonPmf (μ j) (z j)

lemma rm2P_nonneg {μ : Fin n → ℝ} (hμ : ∀ j, 0 ≤ μ j) (z : Fin n → ℕ) : 0 ≤ rm2P μ z :=
  Finset.prod_nonneg fun j _ => rm2_poi_nonneg (hμ j) (z j)

lemma rm2_hasSum_pi_prod (R : ℕ) : ∀ (f : Fin R → ℕ → ℝ) (a : Fin R → ℝ),
    (∀ i n, 0 ≤ f i n) → (∀ i, HasSum (f i) (a i)) →
    HasSum (fun n : Fin R → ℕ => ∏ i, f i (n i)) (∏ i, a i) := by
  induction R with
  | zero =>
    intro f a _ _
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact hasSum_single default (fun b hb => (hb (Subsingleton.elim b default)).elim)
  | succ R ih =>
    intro f a h0 ha
    set g : (Fin R → ℕ) → ℝ := fun n => ∏ i, f i.succ (n i) with hgdef
    have ih' : HasSum g (∏ i : Fin R, a i.succ) := ih (fun i : Fin R => f i.succ)
      (fun i : Fin R => a i.succ) (fun (i : Fin R) n => h0 _ _) (fun i : Fin R => ha _)
    have hf0 : ∀ n, 0 ≤ f 0 n := fun n => h0 0 n
    have hg0 : ∀ n, 0 ≤ g n := fun n => Finset.prod_nonneg fun i _ => h0 _ _
    have hsum : Summable fun x : ℕ × (Fin R → ℕ) => f 0 x.1 * g x.2 := by
      apply summable_mul_of_summable_norm
      · simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using (ha 0).summable
      · simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using ih'.summable
    have hm := HasSum.mul (ha 0) ih' hsum
    have hfun : (fun n : Fin (R + 1) → ℕ => ∏ i, f i (n i)) ∘ (Fin.consEquiv (fun _ => ℕ))
        = fun x : ℕ × (Fin R → ℕ) => f 0 x.1 * g x.2 := by
      funext x
      simp [Fin.consEquiv, Fin.prod_univ_succ, hgdef]
    rw [← (Fin.consEquiv (fun _ : Fin (R + 1) => ℕ)).hasSum_iff, hfun, Fin.prod_univ_succ]
    exact hm

lemma rm2P_hasSum {μ : Fin n → ℝ} (hμ : ∀ j, 0 ≤ μ j) : HasSum (rm2P μ) 1 := by
  have := rm2_hasSum_pi_prod n (fun j => poissonPmf (μ j)) (fun _ => 1)
    (fun j k => rm2_poi_nonneg (hμ j) k) (fun j => rm2_poi_hasSum (hμ j))
  rw [Finset.prod_const_one] at this
  exact this

lemma rm2P_mom {μ : Fin n → ℝ} (hμ : ∀ j, 0 ≤ μ j) (k : Fin n) :
    HasSum (fun z => rm2P μ z * (z k : ℝ)) (μ k) := by
  classical
  have := rm2_hasSum_pi_prod n
    (fun j c => if j = k then poissonPmf (μ j) c * c else poissonPmf (μ j) c)
    (fun j => if j = k then μ j else 1)
    (fun j c => by
      split_ifs
      · exact mul_nonneg (rm2_poi_nonneg (hμ j) c) (Nat.cast_nonneg c)
      · exact rm2_poi_nonneg (hμ j) c)
    (fun j => by
      split_ifs
      · exact rm2_poi_mean (hμ j)
      · exact rm2_poi_hasSum (hμ j))
  have e1 : (∏ j, if j = k then μ j else 1) = μ k := by simp
  rw [e1] at this
  refine this.congr_fun (fun z => ?_)
  unfold rm2P
  rw [show (∏ j, if j = k then poissonPmf (μ j) (z j) * (z j : ℝ) else poissonPmf (μ j) (z j))
      = ∏ j, (poissonPmf (μ j) (z j) * if j = k then (z j : ℝ) else 1) from
      Finset.prod_congr rfl (fun j _ => by split_ifs <;> simp)]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

lemma rm2P_lin_hasSum {μ : Fin n → ℝ} (hμ : ∀ j, 0 ≤ μ j) (A B : ℝ) :
    HasSum (fun z => rm2P μ z * (A + B * ∑ j, (z j : ℝ))) (A + B * ∑ j, μ j) := by
  have h1 := (rm2P_hasSum hμ).mul_left A
  have h2 := (hasSum_sum (fun j (_ : j ∈ Finset.univ) => rm2P_mom hμ j)).mul_left B
  have := h1.add h2
  rw [mul_one] at this
  refine this.congr_fun (fun z => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [mul_add, Finset.mul_sum]
  ring_nf

/-- Expectation under independent Poisson counts. -/
noncomputable def rm2Ex (μ : Fin n → ℝ) (Φ : (Fin n → ℕ) → ℝ) : ℝ := ∑' z, rm2P μ z * Φ z

/-- Linear growth. -/
def rm2Lin (Φ : (Fin n → ℕ) → ℝ) : Prop :=
  ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z, |Φ z| ≤ A + B * ∑ j, (z j : ℝ)

lemma rm2_sum_nonneg (z : Fin n → ℕ) : 0 ≤ ∑ j, (z j : ℝ) :=
  Finset.sum_nonneg fun j _ => Nat.cast_nonneg _

lemma rm2_summable {μ : Fin n → ℝ} (hμ : ∀ j, 0 ≤ μ j) {Φ : (Fin n → ℕ) → ℝ} (hΦ : rm2Lin Φ) :
    Summable (fun z => rm2P μ z * Φ z) := by
  obtain ⟨A, B, -, -, hAB⟩ := hΦ
  refine Summable.of_norm_bounded (rm2P_lin_hasSum hμ A B).summable (fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rm2P_nonneg hμ z)]
  exact mul_le_mul_of_nonneg_left (hAB z) (rm2P_nonneg hμ z)

lemma rm2_sum_single (z : Fin n → ℕ) (i : Fin n) (c : ℕ) :
    ∑ j, (((z + Pi.single i c : Fin n → ℕ) j : ℕ) : ℝ) = ∑ j, (z j : ℝ) + c := by
  classical
  simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  congr 1
  simp [Pi.single_apply]

lemma rm2Lin.line {Φ : (Fin n → ℕ) → ℝ} (hΦ : rm2Lin Φ) (z : Fin n → ℕ) (i : Fin n) :
    ∃ A B : ℝ, ∀ c : ℕ, |Φ (z + Pi.single i c)| ≤ A + B * c := by
  obtain ⟨A, B, -, -, hAB⟩ := hΦ
  refine ⟨A + B * ∑ j, (z j : ℝ), B, fun c => ?_⟩
  have := hAB (z + Pi.single i c)
  rw [rm2_sum_single] at this
  linarith

lemma rm2Lin.summable_line {Φ : (Fin n → ℕ) → ℝ} (hΦ : rm2Lin Φ) {a : ℝ} (ha : 0 ≤ a)
    (z : Fin n → ℕ) (i : Fin n) : Summable (fun c => poissonPmf a c * Φ (z + Pi.single i c)) := by
  obtain ⟨A, B, hAB⟩ := hΦ.line z i
  exact rm2_poi_summable ha hAB

lemma rm2Lin.sub {Φ Ψ : (Fin n → ℕ) → ℝ} (hΦ : rm2Lin Φ) (hΨ : rm2Lin Ψ) :
    rm2Lin (fun z => Φ z - Ψ z) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := hΦ
  obtain ⟨A', B', hA', hB', hAB'⟩ := hΨ
  refine ⟨A + A', B + B', by linarith, by linarith, fun z => ?_⟩
  have h1 := hAB z
  have h2 := hAB' z
  calc |Φ z - Ψ z| ≤ |Φ z| + |Ψ z| := abs_sub _ _
    _ ≤ _ := by linarith

/-- `T_{a,i}Φ(z) = E[Φ(z + N e_i)]` with `N ~ Poisson(a)`. -/
noncomputable def rm2T (a : ℝ) (i : Fin n) (Φ : (Fin n → ℕ) → ℝ) (z : Fin n → ℕ) : ℝ :=
  ∑' c, poissonPmf a c * Φ (z + Pi.single i c)

lemma rm2T_lin {a : ℝ} (ha : 0 ≤ a) (i : Fin n) {Φ : (Fin n → ℕ) → ℝ} (hΦ : rm2Lin Φ) :
    rm2Lin (rm2T a i Φ) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := hΦ
  refine ⟨A + B * a, B, add_nonneg hA (mul_nonneg hB ha), hB, fun z => ?_⟩
  have hb : ∀ c : ℕ, |Φ (z + Pi.single i c)| ≤ (A + B * ∑ j, (z j : ℝ)) + B * c := by
    intro c; have := hAB (z + Pi.single i c); rw [rm2_sum_single] at this; linarith
  generalize ∑ j, (z j : ℝ) = S at hb ⊢
  have hs := rm2_poi_summable ha hb
  have hbd := rm2_poi_lin_hasSum ha (A + B * S) B
  have hlow : ∀ c : ℕ, -(poissonPmf a c * ((A + B * S) + B * c))
      ≤ poissonPmf a c * Φ (z + Pi.single i c) := by
    intro c
    have h1 := hb c
    have h2 := rm2_poi_nonneg ha c
    rw [abs_le] at h1
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left h1.1 h2
  have hup : ∀ c : ℕ, poissonPmf a c * Φ (z + Pi.single i c)
      ≤ poissonPmf a c * ((A + B * S) + B * c) := by
    intro c
    have h1 := hb c
    have h2 := rm2_poi_nonneg ha c
    rw [abs_le] at h1
    exact mul_le_mul_of_nonneg_left h1.2 h2
  have t1 := Summable.tsum_le_tsum hlow hbd.neg.summable hs
  have t2 := Summable.tsum_le_tsum hup hs hbd.summable
  rw [tsum_neg, hbd.tsum_eq] at t1
  rw [hbd.tsum_eq] at t2
  unfold rm2T
  rw [abs_le]
  constructor <;> linarith

lemma rm2P_split (μ : Fin n → ℝ) (i : Fin n) (z : Fin n → ℕ) :
    rm2P μ z = poissonPmf (μ i) (z i) * ∏ j ∈ univ.erase i, poissonPmf (μ j) (z j) :=
  (Finset.mul_prod_erase univ (fun j => poissonPmf (μ j) (z j)) (mem_univ i)).symm

lemma rm2P_conv (μ : Fin n → ℝ) (a : ℝ) (i : Fin n) (z : Fin n → ℕ) :
    rm2P (μ + Pi.single i a) z
      = ∑ c ∈ range (z i + 1), poissonPmf a c * rm2P μ (z - Pi.single i c) := by
  classical
  have hR : ∏ j ∈ univ.erase i, poissonPmf ((μ + Pi.single i a : Fin n → ℝ) j) (z j)
      = ∏ j ∈ univ.erase i, poissonPmf (μ j) (z j) := by
    apply Finset.prod_congr rfl; intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [Pi.single_apply, hji]
  have hR2 : ∀ c : ℕ, ∏ j ∈ univ.erase i, poissonPmf (μ j) ((z - Pi.single i c : Fin n → ℕ) j)
      = ∏ j ∈ univ.erase i, poissonPmf (μ j) (z j) := by
    intro c; apply Finset.prod_congr rfl; intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [Pi.single_apply, hji]
  rw [rm2P_split _ i, hR]
  simp_rw [rm2P_split μ i, hR2]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.sub_apply]
  rw [rm2_poi_conv, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro c _; ring

/-- Superposition: adding an independent `Poisson(a)` count to coordinate `i`. -/
lemma rm2_super {μ : Fin n → ℝ} (hμ : ∀ j, 0 ≤ μ j) {a : ℝ} (ha : 0 ≤ a) (i : Fin n)
    {Φ : (Fin n → ℕ) → ℝ} (hΦ : rm2Lin Φ) :
    rm2Ex (μ + Pi.single i a) Φ = rm2Ex μ (rm2T a i Φ) := by
  classical
  obtain ⟨A, B, hA, hB, hAB⟩ := hΦ
  set F : (Fin n → ℕ) × ℕ → ℝ :=
    fun p => rm2P μ p.1 * (poissonPmf a p.2 * Φ (p.1 + Pi.single i p.2)) with hF
  have hFs : Summable F := by
    have hs1 : Summable (fun p : (Fin n → ℕ) × ℕ =>
        (rm2P μ p.1 * (A + B * ∑ j, (p.1 j : ℝ))) * poissonPmf a p.2) :=
      Summable.mul_of_nonneg (rm2P_lin_hasSum hμ A B).summable (rm2_poi_hasSum ha).summable
        (fun z => mul_nonneg (rm2P_nonneg hμ z)
          (add_nonneg hA (mul_nonneg hB (rm2_sum_nonneg z))))
        (fun c => rm2_poi_nonneg ha c)
    have hs2 : Summable (fun p : (Fin n → ℕ) × ℕ => rm2P μ p.1 * (poissonPmf a p.2 * p.2)) :=
      Summable.mul_of_nonneg (rm2P_hasSum hμ).summable (rm2_poi_mean ha).summable
        (fun z => rm2P_nonneg hμ z) (fun c => mul_nonneg (rm2_poi_nonneg ha c) (Nat.cast_nonneg c))
    refine Summable.of_norm_bounded (hs1.add (hs2.mul_left B)) (fun p => ?_)
    rw [Real.norm_eq_abs, hF]
    dsimp only
    rw [abs_mul, abs_mul, abs_of_nonneg (rm2P_nonneg hμ _), abs_of_nonneg (rm2_poi_nonneg ha _)]
    have hb := hAB (p.1 + Pi.single i p.2)
    rw [rm2_sum_single] at hb
    have hP := rm2P_nonneg hμ p.1
    have hQ := rm2_poi_nonneg ha p.2
    calc rm2P μ p.1 * (poissonPmf a p.2 * |Φ (p.1 + Pi.single i p.2)|)
        ≤ rm2P μ p.1 * (poissonPmf a p.2 * (A + B * (∑ j, (p.1 j : ℝ) + p.2))) := by gcongr
      _ = _ := by ring
  -- the right-hand side as a double sum
  have hRHS : rm2Ex μ (rm2T a i Φ) = ∑' p, F p := by
    rw [hFs.tsum_prod]
    unfold rm2Ex rm2T
    apply tsum_congr; intro z
    rw [← tsum_mul_left]
  -- reindex `(z, c) ↦ (z + c e_i, c)`
  set S : Set ((Fin n → ℕ) × ℕ) := {q | q.2 ≤ q.1 i} with hS
  set G : (Fin n → ℕ) × ℕ → ℝ :=
    fun q => poissonPmf a q.2 * rm2P μ (q.1 - Pi.single i q.2) * Φ q.1 with hG
  let e : (Fin n → ℕ) × ℕ ≃ S :=
    { toFun := fun p => ⟨(p.1 + Pi.single i p.2, p.2), by
        show p.2 ≤ (p.1 + Pi.single i p.2 : Fin n → ℕ) i
        simp⟩
      invFun := fun q => (q.1.1 - Pi.single i q.1.2, q.1.2)
      left_inv := fun p => by
        ext j
        · simp
        · rfl
      right_inv := fun q => by
        obtain ⟨⟨z, c⟩, hq⟩ := q
        have hq' : c ≤ z i := hq
        apply Subtype.ext
        ext j
        · by_cases hj : j = i
          · subst hj; simp [hq']
          · simp [Pi.single_apply, hj]
        · rfl }
  have hFG : ∀ p, F p = G (e p).1 := by
    intro p
    have : p.1 + Pi.single i p.2 - Pi.single i p.2 = p.1 := by
      ext j; simp
    simp only [hF, hG, e, Equiv.coe_fn_mk, this]
    ring
  have hGs : Summable (fun s : S => G s.1) := by
    have : Summable ((fun s : S => G s.1) ∘ e) := hFs.congr (fun p => hFG p)
    exact (e.summable_iff).mp this
  have hInd : Summable (S.indicator G) := summable_subtype_iff_indicator.mp hGs
  have hLHS : rm2Ex (μ + Pi.single i a) Φ = ∑' q, S.indicator G q := by
    rw [hInd.tsum_prod]
    unfold rm2Ex
    apply tsum_congr; intro z
    rw [tsum_eq_sum (s := range (z i + 1)) ?_]
    · rw [rm2P_conv, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro c hc
      have hcS : (z, c) ∈ S := by
        show c ≤ z i
        have := Finset.mem_range.mp hc; omega
      rw [Set.indicator_of_mem hcS]
    · intro c hc
      have hcS : (z, c) ∉ S := by
        show ¬ c ≤ z i
        have := Finset.mem_range.not.mp hc; omega
      exact Set.indicator_of_notMem hcS _
  rw [hLHS, hRHS, ← tsum_subtype S G, ← e.tsum_eq (fun s : S => G s.1)]
  exact tsum_congr (fun p => (hFG p).symm)

end Poisson

/-! ### Second differences of Poisson expectations -/

section Second

variable {n : ℕ}

lemma rm2_tsum_poi_const {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : ∑' c, poissonPmf a c * x = x := by
  rw [tsum_mul_right, (rm2_poi_hasSum ha).tsum_eq, one_mul]

/-- `T_{b,j}Φ(w) − Φ(w) = E[Φ(w + N e_j) − Φ(w)]`. -/
lemma rm2T_sub {b : ℝ} (hb : 0 ≤ b) (j : Fin n) {Φ : (Fin n → ℕ) → ℝ} (hΦ : rm2Lin Φ)
    (w : Fin n → ℕ) :
    rm2T b j Φ w - Φ w = ∑' d, poissonPmf b d * (Φ (w + Pi.single j d) - Φ w) := by
  have h1 := hΦ.summable_line hb w j
  have h2 : Summable (fun d => poissonPmf b d * Φ w) := (rm2_poi_hasSum hb).summable.mul_right _
  simp only [mul_sub]
  rw [h1.tsum_sub h2, rm2_tsum_poi_const hb]
  rfl

/-- Pointwise: the mixed second difference of `T_{a,i}` and `T_{b,j}` is nonpositive. -/
lemma rm2_point {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (i j : Fin n) {Φ : (Fin n → ℕ) → ℝ}
    (hΦ : rm2Lin Φ)
    (hD : ∀ z (c d : ℕ), Φ (z + Pi.single i c + Pi.single j d) - Φ (z + Pi.single i c)
      - Φ (z + Pi.single j d) + Φ z ≤ 0) (z : Fin n → ℕ) :
    rm2T a i (rm2T b j Φ) z - rm2T a i Φ z - rm2T b j Φ z + Φ z ≤ 0 := by
  have hTΦ := rm2T_lin hb j hΦ
  have hΨ : ∀ c : ℕ, (rm2T b j Φ (z + Pi.single i c) - Φ (z + Pi.single i c))
      - (rm2T b j Φ z - Φ z) ≤ 0 := by
    intro c
    rw [rm2T_sub hb j hΦ, rm2T_sub hb j hΦ]
    have sA : Summable (fun d => poissonPmf b d *
        (Φ (z + Pi.single i c + Pi.single j d) - Φ (z + Pi.single i c))) :=
      ((hΦ.summable_line hb (z + Pi.single i c) j).sub
        ((rm2_poi_hasSum hb).summable.mul_right (Φ (z + Pi.single i c)))).congr
        (fun d => by ring)
    have sB : Summable (fun d => poissonPmf b d * (Φ (z + Pi.single j d) - Φ z)) :=
      ((hΦ.summable_line hb z j).sub ((rm2_poi_hasSum hb).summable.mul_right (Φ z))).congr
        (fun d => by ring)
    rw [← sA.tsum_sub sB]
    refine tsum_nonpos (fun d => ?_)
    have h1 := hD z c d
    have h2 := rm2_poi_nonneg hb d
    calc poissonPmf b d * (Φ (z + Pi.single i c + Pi.single j d) - Φ (z + Pi.single i c))
          - poissonPmf b d * (Φ (z + Pi.single j d) - Φ z)
        = poissonPmf b d * (Φ (z + Pi.single i c + Pi.single j d) - Φ (z + Pi.single i c)
          - Φ (z + Pi.single j d) + Φ z) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2 h1
  have s1 := hTΦ.summable_line ha z i
  have s2 := hΦ.summable_line ha z i
  have s3 : Summable (fun c => poissonPmf a c *
      (rm2T b j Φ (z + Pi.single i c) - Φ (z + Pi.single i c))) :=
    (s1.sub s2).congr (fun c => by ring)
  have s4 : Summable (fun c : ℕ => poissonPmf a c * (rm2T b j Φ z - Φ z)) :=
    (rm2_poi_hasSum ha).summable.mul_right _
  have key : ∑' c, poissonPmf a c * (rm2T b j Φ (z + Pi.single i c) - Φ (z + Pi.single i c))
      - ∑' c : ℕ, poissonPmf a c * (rm2T b j Φ z - Φ z) ≤ 0 := by
    rw [← s3.tsum_sub s4]
    refine tsum_nonpos (fun c => ?_)
    have h1 := hΨ c
    have h2 := rm2_poi_nonneg ha c
    rw [← mul_sub]
    exact mul_nonpos_of_nonneg_of_nonpos h2 h1
  rw [rm2_tsum_poi_const ha] at key
  have e1 : rm2T a i (rm2T b j Φ) z - rm2T a i Φ z
      = ∑' c, poissonPmf a c * (rm2T b j Φ (z + Pi.single i c) - Φ (z + Pi.single i c)) := by
    show ∑' c, poissonPmf a c * rm2T b j Φ (z + Pi.single i c)
        - ∑' c, poissonPmf a c * Φ (z + Pi.single i c) = _
    rw [← s1.tsum_sub s2]
    exact tsum_congr (fun c => by ring)
  linarith

lemma rm2_second_diff {μ : Fin n → ℝ} (hμ : ∀ j, 0 ≤ μ j) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (i j : Fin n) {Φ : (Fin n → ℕ) → ℝ} (hΦ : rm2Lin Φ)
    (hD : ∀ z (c d : ℕ), Φ (z + Pi.single i c + Pi.single j d) - Φ (z + Pi.single i c)
      - Φ (z + Pi.single j d) + Φ z ≤ 0) :
    rm2Ex (μ + Pi.single i a + Pi.single j b) Φ - rm2Ex (μ + Pi.single i a) Φ
      - rm2Ex (μ + Pi.single j b) Φ + rm2Ex μ Φ ≤ 0 := by
  classical
  have hμa : ∀ k, 0 ≤ (μ + Pi.single i a : Fin n → ℝ) k := by
    intro k; simp only [Pi.add_apply, Pi.single_apply]; split_ifs <;> linarith [hμ k]
  rw [rm2_super hμa hb j hΦ, rm2_super hμ ha i (rm2T_lin hb j hΦ), rm2_super hμ ha i hΦ,
    rm2_super hμ hb j hΦ]
  unfold rm2Ex
  have s1 := rm2_summable hμ (rm2T_lin ha i (rm2T_lin hb j hΦ))
  have s2 := rm2_summable hμ (rm2T_lin ha i hΦ)
  have s3 := rm2_summable hμ (rm2T_lin hb j hΦ)
  have s4 := rm2_summable hμ hΦ
  rw [← s1.tsum_sub s2, ← (s1.sub s2).tsum_sub s3, ← ((s1.sub s2).sub s3).tsum_add s4]
  refine tsum_nonpos (fun z => ?_)
  have h1 := rm2_point ha hb i j hΦ hD z
  have h2 := rm2P_nonneg hμ z
  show rm2P μ z * rm2T a i (rm2T b j Φ) z - rm2P μ z * rm2T a i Φ z
    - rm2P μ z * rm2T b j Φ z + rm2P μ z * Φ z ≤ 0
  calc rm2P μ z * rm2T a i (rm2T b j Φ) z - rm2P μ z * rm2T a i Φ z
        - rm2P μ z * rm2T b j Φ z + rm2P μ z * Φ z
      = rm2P μ z * (rm2T a i (rm2T b j Φ) z - rm2T a i Φ z - rm2T b j Φ z + Φ z) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2 h1

end Second

/-! ### The service value on integer supplies -/

section Service

variable {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ) (Cap : Fin (m + 1) → ℝ)

/-- Casting a supply vector to real supplies. -/
def rm2c (z : Fin n → ℕ) : Fin n → ℝ := fun j => (z j : ℝ)

lemma rm2c_add_single (z : Fin n → ℕ) (k : Fin n) (c : ℕ) :
    rm2c (z + Pi.single k c) = rm2c z + Pi.single k (c : ℝ) := by
  classical
  funext j
  simp only [rm2c, Pi.add_apply, Nat.cast_add, Pi.single_apply]
  split_ifs <;> simp

lemma rm2_sv_eq (z : Fin n → ℕ) : serviceValue h Cap z = tpVal h Cap (rm2c z) := rfl

lemma rm2_sv_unit (hCap : ∀ i, 0 ≤ Cap i) (z : Fin n → ℕ) (k l : Fin n) :
    serviceValue h Cap (z + Pi.single k 1 + Pi.single l 1) + serviceValue h Cap z
      ≤ serviceValue h Cap (z + Pi.single k 1) + serviceValue h Cap (z + Pi.single l 1) := by
  have hw : ∀ j, 0 ≤ rm2c z j := fun j => Nat.cast_nonneg _
  have := tp_submod h Cap hCap (rm2c z) hw k l
  simp only [rm2_sv_eq h Cap, rm2c_add_single, Nat.cast_one]
  exact this

lemma rm2_sv_step (hCap : ∀ i, 0 ≤ Cap i) (k l : Fin n) :
    ∀ (d : ℕ) (z : Fin n → ℕ),
      serviceValue h Cap (z + Pi.single k 1 + Pi.single l d) - serviceValue h Cap (z + Pi.single l d)
        ≤ serviceValue h Cap (z + Pi.single k 1) - serviceValue h Cap z := by
  intro d
  induction d with
  | zero => intro z; simp only [Pi.single_zero, add_zero]; exact le_refl _
  | succ d ih =>
    intro z
    have hu := rm2_sv_unit h Cap hCap (z + Pi.single l d) k l
    have ih' := ih z
    have e1 : z + Pi.single k 1 + Pi.single l (d + 1)
        = z + Pi.single k 1 + Pi.single l d + Pi.single l 1 := by
      rw [Pi.single_add]; abel
    have e2 : z + Pi.single l (d + 1) = z + Pi.single l d + Pi.single l 1 := by
      rw [Pi.single_add, add_assoc]
    have e3 : z + Pi.single l d + Pi.single k 1 = z + Pi.single k 1 + Pi.single l d := by abel
    rw [e1, e2]
    rw [e3] at hu
    linarith

lemma rm2_sv_msub (hCap : ∀ i, 0 ≤ Cap i) (k l : Fin n) :
    ∀ (c d : ℕ) (z : Fin n → ℕ),
      serviceValue h Cap (z + Pi.single k c + Pi.single l d) - serviceValue h Cap (z + Pi.single k c)
        - serviceValue h Cap (z + Pi.single l d) + serviceValue h Cap z ≤ 0 := by
  intro c
  induction c with
  | zero => intro d z; simp only [Pi.single_zero, add_zero]; linarith
  | succ c ih =>
    intro d z
    have hA := rm2_sv_step h Cap hCap k l d (z + Pi.single k c)
    have hB := ih d z
    have e1 : z + Pi.single k (c + 1) + Pi.single l d
        = z + Pi.single k c + Pi.single k 1 + Pi.single l d := by
      rw [Pi.single_add]; abel
    have e2 : z + Pi.single k (c + 1) = z + Pi.single k c + Pi.single k 1 := by
      rw [Pi.single_add, add_assoc]
    rw [e1, e2]
    linarith

lemma rm2_sv_bound (hCap : ∀ i, 0 ≤ Cap i) (z : Fin n → ℕ) :
    |serviceValue h Cap z| ≤ (∑ j, ∑ i, |h j i|) * ∑ j, (z j : ℝ) := by
  have hH : ∀ j i, |h j i| ≤ ∑ j, ∑ i, |h j i| := fun j i =>
    le_trans (Finset.single_le_sum (f := fun i => |h j i|) (fun i _ => abs_nonneg _) (mem_univ i))
      (Finset.single_le_sum (f := fun j => ∑ i, |h j i|)
        (fun j _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (mem_univ j))
  have hw : ∀ j, 0 ≤ rm2c z j := fun j => Nat.cast_nonneg _
  have hel : ∀ t ∈ tpSet h Cap (rm2c z), |t| ≤ (∑ j, ∑ i, |h j i|) * ∑ j, (z j : ℝ) := by
    rintro t ⟨a, ha, hrow, -, rfl⟩
    have hb : ∑ j, ∑ i, |h j i| * a j i ≤ (∑ j, ∑ i, |h j i|) * ∑ j, (z j : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro j _
      have hrow' : ∑ i, a j i = (z j : ℝ) := hrow j
      rw [← hrow', Finset.mul_sum]
      apply Finset.sum_le_sum; intro i _
      exact mul_le_mul_of_nonneg_right (hH j i) (ha j i)
    calc |∑ j, ∑ i, h j i * a j i| ≤ ∑ j, |∑ i, h j i * a j i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ∑ i, |h j i * a j i| :=
          Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, ∑ i, |h j i| * a j i :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
            rw [abs_mul, abs_of_nonneg (ha j i)]
      _ ≤ _ := hb
  obtain ⟨t0, ht0⟩ := tp_nonempty h Cap hCap (rm2c z) hw
  show |sSup (tpSet h Cap (rm2c z))| ≤ _
  rw [abs_le]
  constructor
  · exact le_trans (abs_le.mp (hel t0 ht0)).1 (le_csSup (tp_bdd h Cap (rm2c z)) ht0)
  · exact csSup_le ⟨t0, ht0⟩ fun t ht => (abs_le.mp (hel t ht)).2

/-- `V'(z) = V(z) + sᵀz`. -/
noncomputable def rm2V (s : Fin n → ℝ) (z : Fin n → ℕ) : ℝ :=
  serviceValue h Cap z + ∑ j, s j * (z j : ℝ)

lemma rm2_lin_single (s : Fin n → ℝ) (z : Fin n → ℕ) (i : Fin n) (c : ℕ) :
    ∑ j, s j * (((z + Pi.single i c : Fin n → ℕ) j : ℕ) : ℝ) = ∑ j, s j * (z j : ℝ) + s i * c := by
  classical
  simp only [Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  congr 1
  simp [Pi.single_apply]

lemma rm2V_msub (hCap : ∀ i, 0 ≤ Cap i) (s : Fin n → ℝ) (i j : Fin n) (z : Fin n → ℕ)
    (c d : ℕ) :
    rm2V h Cap s (z + Pi.single i c + Pi.single j d) - rm2V h Cap s (z + Pi.single i c)
      - rm2V h Cap s (z + Pi.single j d) + rm2V h Cap s z ≤ 0 := by
  have := rm2_sv_msub h Cap hCap i j c d z
  unfold rm2V
  rw [rm2_lin_single s (z + (Pi.single i c : Fin n → ℕ)) j d, rm2_lin_single s z i c,
    rm2_lin_single s z j d]
  linarith

lemma rm2V_lin (hCap : ∀ i, 0 ≤ Cap i) (s : Fin n → ℝ) : rm2Lin (rm2V h Cap s) := by
  refine ⟨0, (∑ j, ∑ i, |h j i|) + ∑ j, |s j|, le_refl 0, by positivity, fun z => ?_⟩
  unfold rm2V
  have h1 := rm2_sv_bound h Cap hCap z
  have h2 : |∑ j, s j * (z j : ℝ)| ≤ (∑ j, |s j|) * ∑ j, (z j : ℝ) := by
    calc |∑ j, s j * (z j : ℝ)| ≤ ∑ j, |s j * (z j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |s j| * (z j : ℝ) :=
          Finset.sum_congr rfl fun j _ => by rw [abs_mul, Nat.abs_cast]
      _ ≤ ∑ j, (∑ k, |s k|) * (z j : ℝ) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (f := fun k => |s k|) (fun k _ => abs_nonneg _) (mem_univ j))
            (Nat.cast_nonneg _)
      _ = _ := by rw [Finset.mul_sum]
  have e : (0 : ℝ) + ((∑ j, ∑ i, |h j i|) + ∑ j, |s j|) * ∑ j, (z j : ℝ)
      = (∑ j, ∑ i, |h j i|) * ∑ j, (z j : ℝ) + (∑ j, |s j|) * ∑ j, (z j : ℝ) := by ring
  rw [e]
  calc |serviceValue h Cap z + ∑ j, s j * (z j : ℝ)|
      ≤ |serviceValue h Cap z| + |∑ j, s j * (z j : ℝ)| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

end Service

/-! ### The expected net revenue -/

section Revenue

variable {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ) (Cap : Fin (m + 1) → ℝ)

lemma rm2_mu_single (q : Fin n → ℝ) (x : Fin n → ℕ) (i : Fin n) :
    (fun j => q j * (((x + Pi.single i 1 : Fin n → ℕ) j : ℕ) : ℝ))
      = (fun j => q j * (x j : ℝ)) + Pi.single i (q i) := by
  classical
  funext j
  simp only [Pi.add_apply, Nat.cast_add, Pi.single_apply]
  split_ifs with hj
  · subst hj; simp; ring
  · simp

lemma rm2_exp_eq (hCap : ∀ i, 0 ≤ Cap i) (p s q : Fin n → ℝ) (hq : ∀ j, 0 ≤ q j)
    (y x : Fin n → ℕ) :
    expNetRevenue h Cap p s q y x
      = (∑ j, p j * ((x j : ℝ) - y j) - ∑ j, s j * (x j : ℝ))
        + rm2Ex (fun j => q j * (x j : ℝ)) (rm2V h Cap s) := by
  have hμ : ∀ j, 0 ≤ q j * (x j : ℝ) := fun j => mul_nonneg (hq j) (Nat.cast_nonneg _)
  have s1 := rm2_summable hμ (rm2V_lin h Cap hCap s)
  have s2 : Summable (fun z => rm2P (fun j => q j * (x j : ℝ)) z * ∑ j, s j * (x j : ℝ)) :=
    (rm2P_hasSum hμ).summable.mul_right _
  have hP := (rm2P_hasSum hμ).tsum_eq
  have e : ∀ z : Fin n → ℕ, (∏ j, poissonPmf (q j * (x j : ℝ)) (z j)) *
      (serviceValue h Cap z - ∑ j, s j * ((x j : ℝ) - z j))
      = rm2P (fun j => q j * (x j : ℝ)) z * rm2V h Cap s z
        - rm2P (fun j => q j * (x j : ℝ)) z * ∑ j, s j * (x j : ℝ) := by
    intro z
    unfold rm2P rm2V
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  unfold expNetRevenue rm2Ex
  rw [tsum_congr e, s1.tsum_sub s2, tsum_mul_right, hP]
  ring

/-- The joint expected net revenue has nonincreasing differences in every pair of coordinates. -/
theorem rm2_goal (hCap : ∀ i, 0 ≤ Cap i) (p s q : Fin n → ℝ) (hq : ∀ j, 0 ≤ q j)
    (y x : Fin n → ℕ) (i j : Fin n) :
    expNetRevenue h Cap p s q y (x + Pi.single i 1 + Pi.single j 1) -
        expNetRevenue h Cap p s q y (x + Pi.single i 1) ≤
      expNetRevenue h Cap p s q y (x + Pi.single j 1) - expNetRevenue h Cap p s q y x := by
  classical
  have hμ : ∀ k, 0 ≤ q k * (x k : ℝ) := fun k => mul_nonneg (hq k) (Nat.cast_nonneg _)
  rw [rm2_exp_eq h Cap hCap p s q hq y (x + Pi.single i 1 + Pi.single j 1),
    rm2_exp_eq h Cap hCap p s q hq y (x + Pi.single i 1),
    rm2_exp_eq h Cap hCap p s q hq y (x + Pi.single j 1),
    rm2_exp_eq h Cap hCap p s q hq y x]
  rw [rm2_mu_single q (x + Pi.single i 1) j, rm2_mu_single q x i, rm2_mu_single q x j]
  have hA : ∀ (x' : Fin n → ℕ) (k : Fin n),
      ∑ j', p j' * ((((x' + Pi.single k 1 : Fin n → ℕ) j' : ℕ) : ℝ) - (y j' : ℝ))
        - ∑ j', s j' * (((x' + Pi.single k 1 : Fin n → ℕ) j' : ℕ) : ℝ)
        = (∑ j', p j' * ((x' j' : ℝ) - y j') - ∑ j', s j' * (x' j' : ℝ)) + (p k - s k) := by
    intro x' k
    have e1 := rm2_lin_single s x' k 1
    have e2 : ∑ j', p j' * ((((x' + Pi.single k 1 : Fin n → ℕ) j' : ℕ) : ℝ) - (y j' : ℝ))
        = ∑ j', p j' * ((x' j' : ℝ) - y j') + p k := by
      have := rm2_lin_single p x' k 1
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [this]; push_cast; ring
    rw [e1, e2]; push_cast; ring
  rw [hA (x + Pi.single i 1) j, hA x i, hA x j]
  have hD := rm2_second_diff hμ (hq i) (hq j) i j (rm2V_lin h Cap hCap s)
    (fun z c d => rm2V_msub h Cap hCap s i j z c d)
  linarith

end Revenue

end RevenueManagement

open RevenueManagement

theorem solution {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ)
    (Cap : Fin (m + 1) → ℝ) (hCap : ∀ i, 0 ≤ Cap i) (p s q : Fin n → ℝ) (hq : ∀ j, 0 ≤ q j)
    (y x : Fin n → ℕ) (i j : Fin n) :
    expNetRevenue h Cap p s q y (x + Pi.single i 1 + Pi.single j 1) -
        expNetRevenue h Cap p s q y (x + Pi.single i 1) ≤
      expNetRevenue h Cap p s q y (x + Pi.single j 1) - expNetRevenue h Cap p s q y x :=
  rm2_goal h Cap hCap p s q hq y x i j

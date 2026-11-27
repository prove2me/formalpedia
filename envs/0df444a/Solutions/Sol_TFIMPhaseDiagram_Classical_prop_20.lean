-- Prove2me | solution 1 for TFIMPhaseDiagram.Classical.prop_20
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:46:53.705421+00:00
-- url     : https://prove2.me/submissions/f28c2c18-0968-404b-bb17-335d5f4a40cb

import Definitions.Def_TFIMPhaseDiagram_Classical_cycles

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical.ChainAux
open TFIMPhaseDiagram.Classical

/-- weighted expectation -/
def wE {Ω : Type} [Fintype Ω] (W f : Ω → ℝ) : ℝ := (∑ x, W x * f x) / ∑ x, W x
def wcov {Ω : Type} [Fintype Ω] (W f g : Ω → ℝ) : ℝ :=
  wE W (fun x => f x * g x) - wE W f * wE W g

lemma covariance_normalize {Ω : Type} [Fintype Ω] (W f g : Ω → ℝ) :
    covariance (normalize W) f g = wcov W f g := by
  unfold covariance normalize wcov wE
  simp only [Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl; intro x _; ring
  · congr 1 <;> (apply Finset.sum_congr rfl; intro x _; ring)

lemma wE_equiv {Ω Ω' : Type} [Fintype Ω] [Fintype Ω'] (e : Ω' ≃ Ω) (W f : Ω → ℝ) :
    wE (W ∘ e) (f ∘ e) = wE W f := by
  unfold wE
  simp only [Function.comp]
  rw [Equiv.sum_comp e (fun x => W x * f x), Equiv.sum_comp e W]

lemma wcov_equiv {Ω Ω' : Type} [Fintype Ω] [Fintype Ω'] (e : Ω' ≃ Ω) (W f g : Ω → ℝ) :
    wcov (W ∘ e) (f ∘ e) (g ∘ e) = wcov W f g := by
  unfold wcov
  rw [wE_equiv, wE_equiv, ← wE_equiv e W (fun x => f x * g x)]
  rfl

lemma wE_smul {Ω : Type} [Fintype Ω] (c : ℝ) (hc : c ≠ 0) (W f : Ω → ℝ) :
    wE (fun x => c * W x) f = wE W f := by
  unfold wE
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ hc]

lemma wcov_smul {Ω : Type} [Fintype Ω] (c : ℝ) (hc : c ≠ 0) (W f g : Ω → ℝ) :
    wcov (fun x => c * W x) f g = wcov W f g := by
  unfold wcov; rw [wE_smul c hc, wE_smul c hc, wE_smul c hc]

lemma wE_le_one {Ω : Type} [Fintype Ω] (W f : Ω → ℝ) (hW : ∀ x, 0 < W x) [Nonempty Ω]
    (hf : ∀ x, |f x| ≤ 1) : |wE W f| ≤ 1 := by
  unfold wE
  have hS : 0 < ∑ x, W x := Finset.sum_pos (fun x _ => hW x) Finset.univ_nonempty
  rw [abs_div, abs_of_pos hS, div_le_one hS]
  calc |∑ x, W x * f x| ≤ ∑ x, |W x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, W x := by
      apply Finset.sum_le_sum; intro x _
      rw [abs_mul, abs_of_pos (hW x)]
      exact mul_le_of_le_one_right (hW x).le (hf x)

lemma var_spin {Ω : Type} [Fintype Ω] [Nonempty Ω] (W f : Ω → ℝ) (hW : ∀ x, 0 < W x)
    (hf : ∀ x, f x = 1 ∨ f x = -1) : |wcov W f f| ≤ 1 := by
  have hsq : wE W (fun x => f x * f x) = 1 := by
    unfold wE
    have hS : 0 < ∑ x, W x := Finset.sum_pos (fun x _ => hW x) Finset.univ_nonempty
    have : ∀ x, W x * (f x * f x) = W x := by
      intro x; rcases hf x with h | h <;> rw [h] <;> ring
    simp only [this]; exact div_self hS.ne'
  have hE := wE_le_one W f hW (fun x => by rcases hf x with h | h <;> rw [h] <;> norm_num)
  unfold wcov; rw [hsq]
  rw [abs_le] at hE ⊢
  constructor <;> nlinarith

/-- The leaf decomposition. -/
lemma leaf {Ω : Type} [Fintype Ω] (R φ : Ω → ℝ) (K w : ℝ) (hφ : ∀ x, φ x = 1 ∨ φ x = -1)
    (g : Ω → ℝ) (hR : ∀ x, 0 < R x) [Nonempty Ω] :
    let W : Bool × Ω → ℝ := fun p => Real.exp (K * spin p.1 * φ p.2 + w * spin p.1) * R p.2
    let R' : Ω → ℝ := fun x => (Real.exp (K * φ x + w) + Real.exp (-(K * φ x + w))) * R x
    let β := (Real.tanh (K + w) - Real.tanh (-K + w)) / 2
    (∀ h : Ω → ℝ, wE W (fun p => h p.2) = wE R' h) ∧
    wcov W (fun p => spin p.1) (fun p => g p.2) = β * wcov R' φ g := by
  intro W R' β
  have hsumW : ∀ h : Ω → ℝ, ∑ p, W p * h p.2 = ∑ x, R' x * h x := by
    intro h
    rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    simp only [W, R', spin, if_true, if_false, Bool.false_eq_true]; ring_nf
  have hsumW' : ∑ p, W p = ∑ x, R' x := by
    have := hsumW (fun _ => 1); simpa using this
  have hE : ∀ h : Ω → ℝ, wE W (fun p => h p.2) = wE R' h := by
    intro h; unfold wE; rw [hsumW h, hsumW']
  refine ⟨hE, ?_⟩
  -- the spin-weighted sums
  set α := (Real.tanh (K + w) + Real.tanh (-K + w)) / 2
  have htanh : ∀ x, (Real.exp (K * φ x + w) - Real.exp (-(K * φ x + w))) * R x =
      (α + β * φ x) * R' x := by
    intro x
    have hc : (Real.exp (K * φ x + w) - Real.exp (-(K * φ x + w))) =
        Real.tanh (K * φ x + w) * (Real.exp (K * φ x + w) + Real.exp (-(K * φ x + w))) := by
      rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
      have : 0 < Real.exp (K * φ x + w) + Real.exp (-(K * φ x + w)) := by positivity
      field_simp
    have ht : Real.tanh (K * φ x + w) = α + β * φ x := by
      rcases hφ x with h | h <;> rw [h] <;> simp only [α, β] <;> ring_nf
    rw [hc, ht]; simp only [R']; ring
  have hsumS : ∀ h : Ω → ℝ, ∑ p, W p * (spin p.1 * h p.2) =
      ∑ x, R' x * ((α + β * φ x) * h x) := by
    intro h
    rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    have := htanh x
    simp only [W, spin, if_true, if_false, Bool.false_eq_true] at this ⊢
    ring_nf; ring_nf at this; linear_combination (h x) * this
  have hS' : 0 < ∑ x, R' x := Finset.sum_pos (fun x _ => by
    simp only [R']; exact mul_pos (by positivity) (hR x)) Finset.univ_nonempty
  have e1 : wE W (fun p => spin p.1 * g p.2) = α * wE R' g + β * wE R' (fun x => φ x * g x) := by
    unfold wE; rw [hsumS g, hsumW', mul_div_assoc', mul_div_assoc', ← add_div]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _; ring
  have e2 : wE W (fun p => spin p.1) = α + β * wE R' φ := by
    have h1 := hsumS (fun _ => 1)
    unfold wE
    rw [show (fun p : Bool × Ω => spin p.1) = fun p => spin p.1 * (fun _ => (1:ℝ)) p.2
      by funext p; ring]
    rw [h1, hsumW', mul_div_assoc', add_div' _ _ _ hS'.ne']
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _; ring
  unfold wcov
  rw [e1, e2, hE g]
  ring


lemma beta_bound (K w : ℝ) :
    |(Real.tanh (K + w) - Real.tanh (-K + w)) / 2| ≤ |Real.tanh K| := by
  have c1 := Real.cosh_pos (K + w); have c2 := Real.cosh_pos (-K + w)
  have cK := Real.cosh_pos K
  have e : (Real.tanh (K + w) - Real.tanh (-K + w)) / 2 =
      Real.sinh K * Real.cosh K / (Real.cosh (K + w) * Real.cosh (-K + w)) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    rw [div_sub_div _ _ c1.ne' c2.ne']
    have : Real.sinh (K + w) * Real.cosh (-K + w) - Real.cosh (K + w) * Real.sinh (-K + w) =
        2 * (Real.sinh K * Real.cosh K) := by
      rw [← Real.sinh_sub, show K + w - (-K + w) = 2 * K by ring, Real.sinh_two_mul]; ring
    rw [this]; field_simp
  have hprod : Real.cosh (K + w) * Real.cosh (-K + w) = Real.cosh K ^ 2 + Real.sinh w ^ 2 := by
    rw [Real.cosh_add, Real.cosh_add, Real.cosh_neg, Real.sinh_neg]
    have h1 := Real.cosh_sq_sub_sinh_sq K
    have h2 := Real.cosh_sq_sub_sinh_sq w
    nlinarith [h1, h2]
  rw [e, Real.tanh_eq_sinh_div_cosh, abs_div, abs_div, abs_mul,
    abs_of_pos cK, abs_of_pos (mul_pos c1 c2), hprod]
  rw [div_le_div_iff₀ (by positivity) cK]
  have : Real.cosh K ^ 2 ≤ Real.cosh K ^ 2 + Real.sinh w ^ 2 := by nlinarith [sq_nonneg (Real.sinh w)]
  calc |Real.sinh K| * Real.cosh K * Real.cosh K = |Real.sinh K| * Real.cosh K ^ 2 := by ring
    _ ≤ |Real.sinh K| * (Real.cosh K ^ 2 + Real.sinh w ^ 2) :=
      mul_le_mul_of_nonneg_left this (abs_nonneg _)

/-- open chain weight with M edges on M+1 sites, written exactly as in `openProb`. -/
def chainW (M : ℕ) (K : Fin M → ℝ) (w : Fin (M+1) → ℝ) (s : Spins (M+1)) : ℝ :=
  Real.exp ((∑ k : Fin M, K k * spin (s k.castSucc) * spin (s k.succ)) + ∑ k, w k * spin (s k))

lemma spin_pm (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b <;> simp [spin]

lemma chainW_cons (M : ℕ) (K : Fin (M+1) → ℝ) (w : Fin (M+2) → ℝ) (b : Bool) (s : Spins (M+1)) :
    chainW (M+1) K w (Fin.cons b s) =
      Real.exp (K 0 * spin b * spin (s 0) + w 0 * spin b) *
        chainW M (fun k => K k.succ) (fun k => w k.succ) s := by
  unfold chainW
  rw [← Real.exp_add]; congr 1
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun k => w k * spin _)]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero, ← Fin.succ_castSucc]
  ring

lemma chainW_field (M : ℕ) (K : Fin M → ℝ) (w : Fin (M+1) → ℝ) (a : ℝ) (s : Spins (M+1)) :
    chainW M K (fun k => if k = 0 then w k + a else w k) s =
      Real.exp (a * spin (s 0)) * chainW M K w s := by
  unfold chainW
  rw [← Real.exp_add]; congr 1
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun k => w k * spin _)]
  simp only [if_true, Fin.succ_ne_zero, if_false]
  ring

lemma chainW_pos (M : ℕ) (K : Fin M → ℝ) (w : Fin (M+1) → ℝ) (s : Spins (M+1)) :
    0 < chainW M K w s := Real.exp_pos _

/-- 2 cosh(K φ + w) as c * exp(a φ) on φ = ±1. -/
lemma cosh_field (K w : ℝ) : ∃ c a : ℝ, 0 < c ∧ ∀ φ : ℝ, (φ = 1 ∨ φ = -1) →
    Real.exp (K * φ + w) + Real.exp (-(K * φ + w)) = c * Real.exp (a * φ) := by
  set A := Real.exp (K * 1 + w) + Real.exp (-(K * 1 + w))
  set B := Real.exp (K * (-1) + w) + Real.exp (-(K * (-1) + w))
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  refine ⟨Real.sqrt (A * B), (1/2) * Real.log (A / B), by positivity, ?_⟩
  rintro φ (rfl | rfl)
  · rw [show 1 / 2 * Real.log (A / B) * 1 = Real.log (Real.sqrt (A / B)) by
      rw [Real.log_sqrt (by positivity)]; ring, Real.exp_log (by positivity),
      ← Real.sqrt_mul (by positivity)]
    rw [show A * B * (A / B) = A ^ 2 by field_simp, Real.sqrt_sq hA.le]
  · rw [show 1 / 2 * Real.log (A / B) * (-1) = Real.log (Real.sqrt (B / A)) by
      rw [Real.log_sqrt (by positivity), Real.log_div hA.ne' hB.ne',
        Real.log_div hB.ne' hA.ne']; ring, Real.exp_log (by positivity),
      ← Real.sqrt_mul (by positivity)]
    rw [show A * B * (B / A) = B ^ 2 by field_simp, Real.sqrt_sq hB.le]


lemma prod_filter_succ {M : ℕ} (f : Fin (M+1) → ℝ) (a b : ℕ) :
    ∏ k ∈ Finset.univ.filter (fun k : Fin (M+1) => a ≤ k.val ∧ k.val < b), f k =
      (if a ≤ 0 ∧ 0 < b then f 0 else 1) *
        ∏ k ∈ Finset.univ.filter (fun k : Fin M => a ≤ k.val + 1 ∧ k.val + 1 < b), f k.succ := by
  rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]
  simp [Fin.val_succ]

theorem chain_cov (M : ℕ) : ∀ (K : Fin M → ℝ) (w : Fin (M+1) → ℝ) (i j : Fin (M+1)), i ≤ j →
    |wcov (chainW M K w) (fun s => spin (s i)) (fun s => spin (s j))| ≤
      |∏ k ∈ Finset.univ.filter (fun k : Fin M => i.val ≤ k.val ∧ k.val < j.val),
        Real.tanh (K k)| := by
  induction M with
  | zero =>
    intro K w i j _
    have hij : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
    subst hij
    rw [Finset.filter_false_of_mem (fun k _ => by omega), Finset.prod_empty, abs_one]
    exact var_spin _ _ (chainW_pos 0 K w) (fun s => spin_pm _)
  | succ M ih =>
    intro K w i j hij
    rcases eq_or_lt_of_le hij with hij | hij
    · subst hij
      rw [Finset.filter_false_of_mem (fun k _ => by omega), Finset.prod_empty, abs_one]
      exact var_spin _ _ (chainW_pos _ K w) (fun s => spin_pm _)
    -- set up the leaf decomposition
    set e := Fin.consEquiv (fun _ : Fin (M+2) => Bool)
    set K' : Fin M → ℝ := fun k => K k.succ
    set w' : Fin (M+1) → ℝ := fun k => w k.succ
    obtain ⟨c, a, hc, hca⟩ := cosh_field (K 0) (w 0)
    set w'' : Fin (M+1) → ℝ := fun k => if k = 0 then w' k + a else w' k
    have hW : (chainW (M+1) K w ∘ e) = fun p : Bool × Spins (M+1) =>
        Real.exp (K 0 * spin p.1 * spin (p.2 0) + w 0 * spin p.1) * chainW M K' w' p.2 := by
      funext p; exact chainW_cons M K w p.1 p.2
    have hR' : (fun x : Spins (M+1) => (Real.exp (K 0 * spin (x 0) + w 0) +
        Real.exp (-(K 0 * spin (x 0) + w 0))) * chainW M K' w' x) =
        fun x => c * chainW M K' w'' x := by
      funext x
      rw [hca _ (spin_pm _), chainW_field]; ring
    have hcov : ∀ F G : Spins (M+2) → ℝ, wcov (chainW (M+1) K w) F G =
        wcov (chainW (M+1) K w ∘ e) (F ∘ e) (G ∘ e) := fun F G => (wcov_equiv e _ F G).symm
    obtain ⟨hleafE, -⟩ := leaf (chainW M K' w') (fun x => spin (x 0)) (K 0) (w 0)
      (fun x => spin_pm _) (fun _ => 0) (chainW_pos M K' w')
    rw [prod_filter_succ]
    -- cases on i
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd hij (lt_irrefl _)
      | succ j =>
        obtain ⟨-, hleaf⟩ := leaf (chainW M K' w') (fun x => spin (x 0)) (K 0) (w 0)
          (fun x => spin_pm _) (fun x => spin (x j)) (chainW_pos M K' w')
        rw [hcov, hW]
        have e1 : ((fun s : Spins (M+2) => spin (s 0)) ∘ e) = fun p => spin p.1 := by
          funext p; simp [e]
        have e2 : ((fun s : Spins (M+2) => spin (s j.succ)) ∘ e) = fun p => spin (p.2 j) := by
          funext p; simp [e]
        rw [e1, e2, hleaf, hR', wcov_smul c hc.ne', abs_mul]
        have hIH := ih K' w'' 0 j (Fin.zero_le _)
        rw [if_pos (by simp), abs_mul]
        have hf : Finset.univ.filter (fun k : Fin M => (0 : Fin (M+2)).val ≤ k.val + 1 ∧
            k.val + 1 < j.succ.val) =
            Finset.univ.filter (fun k : Fin M => (0 : Fin (M+1)).val ≤ k.val ∧ k.val < j.val) := by
          apply Finset.filter_congr; intro k _; simp [Fin.val_succ]
        rw [hf]
        exact mul_le_mul (beta_bound _ _) hIH (abs_nonneg _) (abs_nonneg _)
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j =>
        rw [hcov, hW]
        have e1 : ((fun s : Spins (M+2) => spin (s i.succ)) ∘ e) = fun p => spin (p.2 i) := by
          funext p; simp [e]
        have e2 : ((fun s : Spins (M+2) => spin (s j.succ)) ∘ e) = fun p => spin (p.2 j) := by
          funext p; simp [e]
        rw [e1, e2]
        have hwc : wcov (fun p : Bool × Spins (M+1) =>
            Real.exp (K 0 * spin p.1 * spin (p.2 0) + w 0 * spin p.1) * chainW M K' w' p.2)
            (fun p => spin (p.2 i)) (fun p => spin (p.2 j)) =
            wcov (fun x : Spins (M+1) => (Real.exp (K 0 * spin (x 0) + w 0) +
              Real.exp (-(K 0 * spin (x 0) + w 0))) * chainW M K' w' x)
              (fun x => spin (x i)) (fun x => spin (x j)) := by
          unfold wcov
          rw [hleafE (fun x => spin (x i) * spin (x j)), hleafE (fun x => spin (x i)),
            hleafE (fun x => spin (x j))]
        rw [hwc, hR', wcov_smul c hc.ne']
        have hij' : i ≤ j := by
          rw [Fin.lt_def, Fin.val_succ, Fin.val_succ] at hij; exact Fin.le_def.2 (by omega)
        have hIH := ih K' w'' i j hij'
        have h0 : ¬ (i.succ.val ≤ 0 ∧ 0 < j.succ.val) := by simp
        rw [if_neg h0, one_mul]
        have hf : Finset.univ.filter (fun k : Fin M => i.succ.val ≤ k.val + 1 ∧
            k.val + 1 < j.succ.val) =
            Finset.univ.filter (fun k : Fin M => i.val ≤ k.val ∧ k.val < j.val) := by
          apply Finset.filter_congr; intro k _; simp [Fin.val_succ]
        rw [hf]
        exact hIH


theorem prop20 (M : ℕ) (hM : 1 ≤ M) (K : Fin (M-1) → ℝ) (w : Fin M → ℝ)
    (i j : Fin M) (hij : i ≤ j) :
  |spinCov (openProb K w) i j| ≤
    |∏ k ∈ Finset.univ.filter (fun k : Fin (M-1) => i.val ≤ k.val ∧ k.val < j.val), Real.tanh (K k)| := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hp : openProb K w = normalize (chainW M' K w) := rfl
  unfold spinCov
  rw [hp, covariance_normalize]
  exact chain_cov M' K w i j hij

end TFIMPhaseDiagram.Classical.ChainAux

open TFIMPhaseDiagram.Classical in
theorem solution (M : ℕ) (hM : 1 ≤ M) (K : Fin (M-1) → ℝ) (w : Fin M → ℝ)
    (i j : Fin M) (hij : i ≤ j) :
  |spinCov (openProb K w) i j| ≤
    |∏ k ∈ Finset.univ.filter (fun k : Fin (M-1) => i.val ≤ k.val ∧ k.val < j.val), Real.tanh (K k)| :=
  TFIMPhaseDiagram.Classical.ChainAux.prop20 M hM K w i j hij

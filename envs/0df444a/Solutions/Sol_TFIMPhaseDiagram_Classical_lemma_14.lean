-- Prove2me | solution 1 for TFIMPhaseDiagram.Classical.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:09:34.952819+00:00
-- url     : https://prove2.me/submissions/c8446e95-3a3f-4e6c-8dd6-0a6ca0bc6350

import Theorems.Thm_TFIMPhaseDiagram_Classical_lemma_18

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

lemma sum4 (x : Bool × Bool → ℝ) : ∑ s, x s =
    x (false,false) + x (false,true) + x (true,false) + x (true,true) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]; ring

lemma cov4 (x : Bool × Bool → ℝ) (hS : ∑ s, x s ≠ 0) :
    covariance (normalize x) (fun s => spin s.1) (fun s => spin s.2) =
      4 * (x (false,false) * x (true,true) - x (false,true) * x (true,false)) / (∑ s, x s)^2 := by
  have e1 : covariance (normalize x) (fun s => spin s.1) (fun s => spin s.2) =
      (x (false,false) - x (false,true) - x (true,false) + x (true,true)) / (∑ s, x s) -
      ((x (false,false) + x (false,true) - x (true,false) - x (true,true)) / (∑ s, x s)) *
      ((x (false,false) - x (false,true) + x (true,false) - x (true,true)) / (∑ s, x s)) := by
    simp only [covariance, normalize, Fintype.sum_prod_type, Fintype.sum_bool, spin]
    simp
    ring
  rw [e1, sum4]; rw [sum4] at hS
  field_simp
  ring

lemma tanh_u (J : ℝ) : Real.tanh J = (Real.exp J ^ 2 - 1) / (Real.exp J ^ 2 + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  have := Real.exp_pos J
  field_simp


lemma spin_pm (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b <;> simp [spin]

end TFIMPhaseDiagram.Classical.ChainAux


namespace TFIMPhaseDiagram.Classical.L14Aux
open TFIMPhaseDiagram.Classical TFIMPhaseDiagram.Classical.ChainAux

/-- Schur test for a symmetric matrix on the unit sphere. -/
lemma quad_le {M : ℕ} (C : Fin M → Fin M → ℝ) (hsym : ∀ i j, C i j = C j i) (R : ℝ)
    (hR : ∀ i, ∑ j, |C i j| ≤ R) (x : EuclideanSpace ℝ (Fin M)) (hx : ‖x‖ = 1) :
    ∑ i, ∑ j, x i * C i j * x j ≤ R := by
  have hsq : ∑ i, x i ^ 2 = 1 := by
    have := EuclideanSpace.norm_eq x
    rw [hx] at this
    have h2 : (1:ℝ) ^ 2 = (Real.sqrt (∑ i, ‖x i‖ ^ 2)) ^ 2 := by rw [← this]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))] at h2
    simpa [Real.norm_eq_abs, sq_abs] using h2.symm
  have hterm : ∀ i j, x i * C i j * x j ≤ |C i j| * (x i ^ 2 + x j ^ 2) / 2 := by
    intro i j
    have h1 : x i * C i j * x j ≤ |C i j| * (|x i| * |x j|) := by
      calc x i * C i j * x j ≤ |x i * C i j * x j| := le_abs_self _
        _ = |C i j| * (|x i| * |x j|) := by rw [abs_mul, abs_mul]; ring
    have h2 : |x i| * |x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
      nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
    calc x i * C i j * x j ≤ |C i j| * (|x i| * |x j|) := h1
      _ ≤ |C i j| * ((x i ^ 2 + x j ^ 2) / 2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = |C i j| * (x i ^ 2 + x j ^ 2) / 2 := by ring
  calc ∑ i, ∑ j, x i * C i j * x j ≤ ∑ i, ∑ j, |C i j| * (x i ^ 2 + x j ^ 2) / 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = ∑ i, x i ^ 2 * ∑ j, |C i j| := by
        have e : ∀ i j, |C i j| * (x i ^ 2 + x j ^ 2) / 2 =
            x i ^ 2 * |C i j| / 2 + x j ^ 2 * |C j i| / 2 := by
          intro i j; rw [hsym j i]; ring
        simp_rw [e, Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j => x j ^ 2 * |C j i| / 2), ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ ∑ i, x i ^ 2 * R :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hR i) (sq_nonneg _))
    _ = R := by rw [← Finset.sum_mul, hsq]; ring

lemma finiteCovNorm_le {M : ℕ} (hM : 0 < M) (p : Spins M → ℝ) (R : ℝ)
    (hR : ∀ i, ∑ j, |spinCov p i j| ≤ R) : finiteCovNorm p ≤ R := by
  unfold finiteCovNorm
  apply csSup_le
  · refine ⟨_, EuclideanSpace.single ⟨0, hM⟩ 1, by simp, rfl⟩
  · rintro r ⟨x, hx, rfl⟩
    refine quad_le _ (fun i j => ?_) R hR x hx
    unfold spinCov covariance
    congr 1
    · apply Finset.sum_congr rfl; intro s _; ring
    · ring

/-- the geometric row sum -/
def gd (M : ℕ) (a : ℝ) (d : ℕ) : ℝ := (a ^ d + a ^ (M - d)) / (1 + a ^ M)

lemma tanh_exp (y : ℝ) : Real.tanh y = (1 - Real.exp (-2 * y)) / (1 + Real.exp (-2 * y)) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h1 : Real.exp (-2 * y) = Real.exp (-y) * Real.exp (-y) := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  rw [h1]
  have := Real.exp_pos y
  have := Real.exp_pos (-y)
  field_simp
  nlinarith [h2]

lemma sum_gd (M : ℕ) (hM : 0 < M) (η : ℝ) (hη : 0 < η) :
    ∑ d ∈ Finset.range M, gd M (Real.exp (-2 * η / M)) d = M * alphaMesh M η := by
  set a := Real.exp (-2 * η / M)
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := Real.exp_lt_one_iff.mpr (by
    have : 0 < 2 * η / M := by positivity
    linarith [show -2 * η / M = -(2 * η / M) by ring])
  have haM : a ^ M = Real.exp (-2 * η) := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  have hgeom : (∑ d ∈ Finset.range M, a ^ d) * (1 - a) = 1 - a ^ M := by
    have := geom_sum_mul a M; linarith
  have hrefl : ∑ d ∈ Finset.range M, a ^ (M - d) = a * ∑ d ∈ Finset.range M, a ^ d := by
    rw [← Finset.sum_range_reflect, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d hd
    rw [Finset.mem_range] at hd
    rw [← pow_succ']; congr 1; omega
  have hsum : ∑ d ∈ Finset.range M, gd M a d =
      (1 + a) * (1 - a ^ M) / ((1 - a) * (1 + a ^ M)) := by
    unfold gd
    rw [← Finset.sum_div, Finset.sum_add_distrib, hrefl]
    have h1a : (1 - a) ≠ 0 := by linarith
    have : ∑ d ∈ Finset.range M, a ^ d = (1 - a ^ M) / (1 - a) := by
      field_simp; linarith [hgeom]
    rw [this]
    have : (0:ℝ) < 1 + a ^ M := by positivity
    field_simp
  rw [hsum]
  unfold alphaMesh
  rw [if_neg hη.ne', tanh_exp, tanh_exp, ← haM]
  have ha' : Real.exp (-2 * (η / M)) = a := by simp only [a]; congr 1; ring
  rw [ha']
  have h1a : (0:ℝ) < 1 - a := by linarith
  have : (0:ℝ) < 1 + a ^ M := by positivity
  have : (0:ℝ) < 1 - a ^ M := by
    have : a ^ M < 1 := pow_lt_one₀ ha0.le ha1 hM.ne'
    linarith
  field_simp


lemma spinCov_symm {M : ℕ} (p : Spins M → ℝ) (i j : Fin M) : spinCov p i j = spinCov p j i := by
  unfold spinCov covariance
  congr 1
  · apply Finset.sum_congr rfl; intro s _; ring
  · ring

lemma gd_symm (M : ℕ) (a : ℝ) (d : ℕ) (hd : d ≤ M) : gd M a (M - d) = gd M a d := by
  unfold gd; rw [Nat.sub_sub_self hd, add_comm]

lemma covg_finite (M : ℕ) (hM : 3 ≤ M) (K w : Fin M → ℝ) (b : ℝ) (hb : 0 < b)
    (hK : ∀ k, |K k| ≤ b) (i j : Fin M) :
    |spinCov (cycleProb K (fun k => Field.finite (w k))) i j| ≤ gd M (Real.tanh b) (j - i).val := by
  rcases le_or_gt i j with hij | hij
  · rw [Fin.coe_sub_iff_le.mpr hij]
    have h := TFIMPhaseDiagram.Classical.lemma_18 M hM K w b hb hK i j hij
    exact h.1.trans h.2
  · rw [spinCov_symm, Fin.coe_sub_iff_lt.mpr hij]
    have h := TFIMPhaseDiagram.Classical.lemma_18 M hM K w b hb hK j i hij.le
    have := h.1.trans h.2
    have hd : i.val - j.val ≤ M := by have := i.isLt; omega
    rw [show M + j.val - i.val = M - (i.val - j.val) by have := i.isLt; omega, gd_symm M _ _ hd]
    exact this


open Filter Topology in
lemma wcov_tendsto {Ω : Type} [Fintype Ω] (W : ℝ → Ω → ℝ) (W0 : Ω → ℝ)
    (h : ∀ x, Tendsto (fun t => W t x) atTop (𝓝 (W0 x))) (hS : ∑ x, W0 x ≠ 0) (f g : Ω → ℝ) :
    Tendsto (fun t => wcov (W t) f g) atTop (𝓝 (wcov W0 f g)) := by
  have hsum : ∀ φ : Ω → ℝ, Tendsto (fun t => ∑ x, W t x * φ x) atTop (𝓝 (∑ x, W0 x * φ x)) :=
    fun φ => tendsto_finset_sum _ (fun x _ => (h x).mul_const _)
  have hZ : Tendsto (fun t => ∑ x, W t x) atTop (𝓝 (∑ x, W0 x)) :=
    tendsto_finset_sum _ (fun x _ => h x)
  unfold wcov wE
  exact ((hsum _).div hZ hS).sub (((hsum _).div hZ hS).mul ((hsum _).div hZ hS))

def wt {M : ℕ} (w : Fin M → Field) (t : ℝ) (k : Fin M) : ℝ :=
  match w k with | .finite a => a | .plus => t | .minus => -t
def pen (f : Field) (t : ℝ) : ℝ := match f with | .finite _ => 0 | _ => t
def finE (f : Field) (b : Bool) : ℝ := match f with | .finite a => a * spin b | _ => 0
def mis (f : Field) (b : Bool) : ℝ :=
  match f with | .finite _ => 0 | .plus => if b then 1 else 0 | .minus => if b then 0 else 1

lemma site_id (f : Field) (t : ℝ) (b : Bool) :
    (match f with | .finite a => a | .plus => t | .minus => -t) * spin b - pen f t =
      finE f b - 2 * t * mis f b := by
  cases f <;> cases b <;> simp [pen, finE, mis, spin] <;> ring

lemma mis_nonneg (f : Field) (b : Bool) : 0 ≤ mis f b := by
  cases f <;> cases b <;> simp [mis]

lemma compat_iff {M : ℕ} (w : Fin M → Field) (s : Spins M) :
    compatible w s ↔ ∀ k, mis (w k) (s k) = 0 := by
  unfold compatible
  apply forall_congr'; intro k
  cases h : w k <;> cases s k <;> simp [mis]

open Filter Topology in
lemma covg_general (M : ℕ) (hM : 3 ≤ M) (K : Fin M → ℝ) (w : Fin M → Field)
    (hw : ∃ s, compatible w s) (b : ℝ) (hb : 0 < b)
    (hK : ∀ k, |K k| ≤ b) (i j : Fin M) :
    |spinCov (cycleProb K w) i j| ≤ gd M (Real.tanh b) (j - i).val := by
  set W0 := cycleWeight K w
  set V : ℝ → Spins M → ℝ := fun t s =>
    Real.exp (-(∑ k, pen (w k) t)) * cycleWeight K (fun k => Field.finite (wt w t k)) s
  have hV : ∀ t s, V t s = Real.exp ((∑ k, K k * spin (s k) * spin (s (next k))) +
      fieldEnergy w s - 2 * t * ∑ k, mis (w k) (s k)) := by
    intro t s
    have hc : compatible (fun k => Field.finite (wt w t k)) s := by intro k; trivial
    have hfe2 : fieldEnergy (fun k => Field.finite (wt w t k)) s = ∑ k, wt w t k * spin (s k) := rfl
    simp only [V, cycleWeight, if_pos hc, cycleEnergy, hfe2, ← Real.exp_add]
    congr 1
    have : ∀ k, wt w t k * spin (s k) = finE (w k) (s k) - 2 * t * mis (w k) (s k) + pen (w k) t := by
      intro k; have := site_id (w k) t (s k); unfold wt; linarith
    have hfe : fieldEnergy w s = ∑ k, finE (w k) (s k) := by unfold fieldEnergy finE; rfl
    rw [hfe]
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hlim : ∀ s, Tendsto (fun t => V t s) atTop (𝓝 (W0 s)) := by
    intro s
    simp only [hV]
    by_cases hcs : compatible w s
    · have hm : ∑ k, mis (w k) (s k) = 0 := Finset.sum_eq_zero (fun k _ => (compat_iff w s).1 hcs k)
      simp only [hm, mul_zero, sub_zero]
      have : W0 s = Real.exp ((∑ k, K k * spin (s k) * spin (s (next k))) + fieldEnergy w s) := by
        simp only [W0, cycleWeight, if_pos hcs, cycleEnergy]
      rw [this]; exact tendsto_const_nhds
    · have : W0 s = 0 := by simp only [W0, cycleWeight, if_neg hcs]
      rw [this]
      obtain ⟨k, hk⟩ : ∃ k, mis (w k) (s k) ≠ 0 := by
        by_contra hc; push Not at hc; exact hcs ((compat_iff w s).2 hc)
      have hpos : 0 < ∑ k, mis (w k) (s k) := by
        have h1 : mis (w k) (s k) ≤ ∑ k, mis (w k) (s k) :=
          Finset.single_le_sum (fun k _ => mis_nonneg _ _) (Finset.mem_univ k)
        have := mis_nonneg (w k) (s k)
        exact lt_of_lt_of_le (lt_of_le_of_ne this (Ne.symm hk)) h1
      apply Real.tendsto_exp_atBot.comp
      set E0 := (∑ k, K k * spin (s k) * spin (s (next k))) + fieldEnergy w s
      set m := ∑ k, mis (w k) (s k)
      have h1 : Tendsto (fun t : ℝ => (-(2 * m)) * t) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
      have h2 := tendsto_atBot_add_const_left atTop E0 h1
      convert h2 using 2 with t
      ring
  have hS : ∑ s, W0 s ≠ 0 := by
    obtain ⟨s0, hs0⟩ := hw
    have hnn : ∀ s, 0 ≤ W0 s := fun s => by
      simp only [W0, cycleWeight]; split_ifs <;> positivity
    have : 0 < W0 s0 := by simp only [W0, cycleWeight, if_pos hs0]; positivity
    exact (lt_of_lt_of_le this (Finset.single_le_sum (fun s _ => hnn s) (Finset.mem_univ s0))).ne'
  have hT := wcov_tendsto V W0 hlim hS (fun s => spin (s i)) (fun s => spin (s j))
  have hbound : ∀ t, |wcov (V t) (fun s => spin (s i)) (fun s => spin (s j))| ≤
      gd M (Real.tanh b) (j - i).val := by
    intro t
    have := covg_finite M hM K (wt w t) b hb hK i j
    simp only [V]
    rw [wcov_smul _ (Real.exp_pos _).ne']
    unfold spinCov cycleProb at this
    rwa [covariance_normalize] at this
  unfold spinCov cycleProb
  rw [covariance_normalize]
  exact le_of_tendsto' ((continuous_abs.tendsto _).comp hT) hbound


theorem lemma14 (M : ℕ) (hM : 3 ≤ M) (K : Fin M → ℝ) (w : Fin M → Field)
    (hw : ∃ s, compatible w s) (b η : ℝ) (hb : 0 < b) (hη : 0 < η)
    (hK : ∀ k, |K k| ≤ b) (hrel : Real.tanh b = Real.exp (-2*η/M)) :
  finiteCovNorm (cycleProb K w) / M ≤ alphaMesh M η := by
  have hM0 : 0 < M := by omega
  haveI : NeZero M := ⟨by omega⟩
  have hMr : (0:ℝ) < M := by exact_mod_cast hM0
  have hrow : ∀ i, ∑ j, |spinCov (cycleProb K w) i j| ≤ M * alphaMesh M η := by
    intro i
    calc ∑ j, |spinCov (cycleProb K w) i j| ≤ ∑ j, gd M (Real.tanh b) (j - i).val :=
          Finset.sum_le_sum (fun j _ => covg_general M hM K w hw b hb hK i j)
      _ = ∑ d : Fin M, gd M (Real.tanh b) d.val :=
          Equiv.sum_comp (Equiv.subRight i) (fun d : Fin M => gd M (Real.tanh b) d.val)
      _ = ∑ d ∈ Finset.range M, gd M (Real.tanh b) d :=
          Fin.sum_univ_eq_sum_range (fun d => gd M (Real.tanh b) d) M
      _ = M * alphaMesh M η := by rw [hrel]; exact sum_gd M hM0 η hη
  have := finiteCovNorm_le hM0 (cycleProb K w) _ hrow
  rw [div_le_iff₀ hMr]
  linarith

end TFIMPhaseDiagram.Classical.L14Aux

open TFIMPhaseDiagram.Classical in
theorem solution (M : ℕ) (hM : 3 ≤ M) (K : Fin M → ℝ) (w : Fin M → Field)
    (hw : ∃ s, compatible w s) (b η : ℝ) (hb : 0 < b) (hη : 0 < η)
    (hK : ∀ k, |K k| ≤ b) (hrel : Real.tanh b = Real.exp (-2*η/M)) :
  finiteCovNorm (cycleProb K w) / M ≤ alphaMesh M η :=
  TFIMPhaseDiagram.Classical.L14Aux.lemma14 M hM K w hw b η hb hη hK hrel

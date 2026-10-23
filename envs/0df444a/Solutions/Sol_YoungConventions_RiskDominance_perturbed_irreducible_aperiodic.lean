-- Prove2me | solution 1 for YoungConventions.RiskDominance.perturbed_irreducible_aperiodic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:59:53.816405+00:00
-- url     : https://prove2.me/submissions/e61bc912-59a3-478a-aae6-ee0b3ed068eb

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_AdaptivePlay_IsSuccessor
import Definitions.Def_YoungConventions_RiskDominance_IsBestReplyDistribution
import Definitions.Def_YoungConventions_RiskDominance_IsExperimentation
import Definitions.Def_YoungConventions_RiskDominance_unperturbed
import Definitions.Def_YoungConventions_RiskDominance_perturbed
import Definitions.Def_YoungConventions_RiskDominance_numMistakes
import Definitions.Def_YoungConventions_RiskDominance_IsStationaryDistribution

open Filter Topology


namespace YoungConventions.RiskDominance

open YoungConventions.AdaptivePlay

section Gen

lemma ypa_mpow_nonneg {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℝ)
    (hA : ∀ x y, 0 ≤ A x y) (n : ℕ) : ∀ x y, 0 ≤ (A ^ n) x y := by
  induction n with
  | zero => intro x y; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro x y; rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (ih x z) (hA z y))

lemma ypa_mpow_chain {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℝ)
    (hA : ∀ x y, 0 ≤ A x y) (g : ℕ → X) :
    ∀ n, (∀ j < n, 0 < A (g j) (g (j+1))) → 0 < (A ^ n) (g 0) (g n)
  | 0 => by intro _; simp
  | n+1 => by
    intro hg
    rw [pow_succ, Matrix.mul_apply]
    have h1 := ypa_mpow_chain A hA g n (fun j hj => hg j (by omega))
    have h2 := hg n (by omega)
    calc (0:ℝ) < (A^n) (g 0) (g n) * A (g n) (g (n+1)) := mul_pos h1 h2
    _ ≤ _ := Finset.single_le_sum (f := fun z => (A^n) (g 0) z * A z (g (n+1)))
          (fun z _ => mul_nonneg (ypa_mpow_nonneg A hA n _ _) (hA _ _)) (Finset.mem_univ _)

lemma ypa_stat_exists {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] (P : Matrix X X ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) : ∃ μ, IsStationaryDistribution μ P := by
  have hnn : ∀ x y, 0 ≤ P x y := fun x y => Matrix.nonneg_of_mem_rowStochastic hP
  have hrow := Matrix.sum_row_of_mem_rowStochastic hP
  have hdet : (P - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨1, ?_, ?_⟩
    · intro h; have := congrFun h (Classical.arbitrary X); simp at this
    · rw [Matrix.sub_mulVec, Matrix.one_vecMul_of_mem_rowStochastic hP, Matrix.one_mulVec,
        sub_self]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at hv
  have hv' : ∀ y, ∑ x, v x * P x y = v y := by
    intro y; have := congrFun hv y; simpa [Matrix.vecMul, dotProduct] using this
  set w : X → ℝ := fun x => |v x| with hw
  have key : ∀ y, w y ≤ ∑ x, w x * P x y := by
    intro y
    calc w y = |∑ x, v x * P x y| := by rw [hv' y]
    _ ≤ ∑ x, |v x * P x y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, w x * P x y := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (hnn x y)]
  have hsum : ∑ y, ∑ x, w x * P x y = ∑ y, w y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.mul_sum, hrow x, mul_one]
  have heq : ∀ y, ∑ x, w x * P x y = w y := by
    have h0 : ∑ y, (∑ x, w x * P x y - w y) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sub_nonneg.2 (key y))).1 h0
    intro y; have := this y (Finset.mem_univ _); linarith
  obtain ⟨x0, hx0⟩ := Function.ne_iff.1 hv0
  have hwpos : 0 < ∑ x, w x := by
    calc (0:ℝ) < w x0 := abs_pos.2 hx0
    _ ≤ ∑ x, w x := Finset.single_le_sum (f := w) (fun x _ => abs_nonneg _) (Finset.mem_univ _)
  refine ⟨fun x => w x / ∑ z, w z, fun x => div_nonneg (abs_nonneg _) hwpos.le, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hwpos.ne']
  · funext y
    simp only [Matrix.vecMul, dotProduct]
    rw [← heq y, Finset.sum_div]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring

lemma ypa_stat_pow {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ) (μ : X → ℝ)
    (hμ : Matrix.vecMul μ P = μ) (n : ℕ) : Matrix.vecMul μ (P ^ n) = μ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hμ]

lemma ypa_stat_unique {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ) (n : ℕ)
    (hpos : ∀ x y, 0 < (P ^ n) x y) (μ ν : X → ℝ)
    (hμ : IsStationaryDistribution μ P) (hν : IsStationaryDistribution ν P) : μ = ν := by
  set B := P ^ n with hB
  have hμB : ∀ y, ∑ x, μ x * B x y = μ y := by
    intro y; have := congrFun (ypa_stat_pow P μ hμ.2.2 n) y
    simpa [Matrix.vecMul, dotProduct] using this
  have hνB : ∀ y, ∑ x, ν x * B x y = ν y := by
    intro y; have := congrFun (ypa_stat_pow P ν hν.2.2 n) y
    simpa [Matrix.vecMul, dotProduct] using this
  obtain ⟨x0, hx0⟩ : ∃ x0, 0 < ν x0 := by
    by_contra hc
    push_neg at hc
    have : ∑ x, ν x ≤ 0 := Finset.sum_nonpos (fun x _ => hc x)
    linarith [hν.2.1]
  have hνpos : ∀ y, 0 < ν y := by
    intro y
    rw [← hνB y]
    calc (0:ℝ) < ν x0 * B x0 y := mul_pos hx0 (hpos _ _)
    _ ≤ _ := Finset.single_le_sum (f := fun z => ν z * B z y)
          (fun z _ => mul_nonneg (hν.1 z) (hpos _ _).le) (Finset.mem_univ _)
  obtain ⟨x1, -, hx1⟩ := Finset.exists_min_image Finset.univ (fun x => μ x / ν x)
    ⟨x0, Finset.mem_univ _⟩
  set t := μ x1 / ν x1 with ht
  have hw : ∀ x, 0 ≤ μ x - t * ν x := by
    intro x
    have := hx1 x (Finset.mem_univ _)
    rw [le_div_iff₀ (hνpos x)] at this
    linarith
  have hw1 : μ x1 - t * ν x1 = 0 := by
    rw [ht, div_mul_cancel₀ _ (hνpos x1).ne']; ring
  have hwB : ∑ x, (μ x - t * ν x) * B x x1 = 0 := by
    have : ∑ x, (μ x - t * ν x) * B x x1 = ∑ x, μ x * B x x1 - t * ∑ x, ν x * B x x1 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_); ring
    rw [this, hμB, hνB, hw1]
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => mul_nonneg (hw x) (hpos _ _).le)).1 hwB
  have hz : ∀ x, μ x = t * ν x := by
    intro x
    have := hall x (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h (hpos _ _).ne'
  have ht1 : t = 1 := by
    have h1 := hμ.2.1
    simp_rw [hz] at h1
    rw [← Finset.mul_sum, hν.2.1, mul_one] at h1
    exact h1
  funext x; rw [hz x, ht1, one_mul]

end Gen

section Chain
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] {m : ℕ} [NeZero m]

/-- weight of the experimenting set `J`. -/
noncomputable def ypaW (lam : ι → ℝ) (ε : ℝ) (J : Finset ι) : ℝ :=
  ε ^ J.card * (∏ j ∈ J, lam j) * (∏ j ∈ Jᶜ, (1 - ε * lam j))

lemma ypa_kernel_empty (p q : (i : ι) → History S m → S i → ℝ) :
    experimentKernel ∅ p q = unperturbed p := by
  ext h h'
  simp [experimentKernel, unperturbed]

lemma ypa_full (p q : (i : ι) → History S m → S i → ℝ) (lam : ι → ℝ) (ε : ℝ)
    (h h' : History S m) :
    perturbed p q lam ε h h' = ∑ J : Finset ι, ypaW lam ε J * experimentKernel J p q h h' := by
  rw [← Finset.sum_filter_not_add_sum_filter (Finset.univ) (fun J : Finset ι => J.Nonempty)]
  have : (Finset.univ.filter (fun J : Finset ι => ¬ J.Nonempty)) = {∅} := by
    ext J; simp [Finset.not_nonempty_iff_eq_empty]
  rw [this, Finset.sum_singleton]
  simp [perturbed, ypaW, ypa_kernel_empty]

lemma ypaW_sum (lam : ι → ℝ) (ε : ℝ) : ∑ J : Finset ι, ypaW lam ε J = 1 := by
  have := Fintype.prod_add (fun i => ε * lam i) (fun i => 1 - ε * lam i)
  simp only [add_sub_cancel, Finset.prod_const_one] at this
  rw [this]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  simp [ypaW, Finset.prod_mul_distrib, Finset.prod_const]

lemma ypaW_nonneg (lam : ι → ℝ) (ε : ℝ) (hε : 0 < ε) (hlam : ∀ i, 0 < lam i)
    (hεlam : ∀ i, ε * lam i ≤ 1) (J : Finset ι) : 0 ≤ ypaW lam ε J := by
  unfold ypaW
  refine mul_nonneg (mul_nonneg (pow_nonneg hε.le _) ?_) ?_
  · exact Finset.prod_nonneg (fun j _ => (hlam j).le)
  · exact Finset.prod_nonneg (fun j _ => sub_nonneg.2 (hεlam j))

/-- the successor with newest play `s`. -/
def ypaSucc (h : History S m) (s : (i : ι) → S i) : History S m :=
  fun t => if ht : t.val + 1 < m then h ⟨t.val + 1, ht⟩ else s

lemma ypaSucc_isSucc (h : History S m) (s : (i : ι) → S i) : IsSuccessor h (ypaSucc h s) := by
  intro t ht; simp [ypaSucc, ht]

lemma ypa_newest_succ (h : History S m) (s : (i : ι) → S i) : newest (ypaSucc h s) = s := by
  have : ¬ (m - 1 + 1 < m) := by have := NeZero.pos m; omega
  simp [newest, ypaSucc, this]

lemma ypa_succ_eq (h h' : History S m) (hs : IsSuccessor h h') : h' = ypaSucc h (newest h') := by
  funext t
  by_cases ht : t.val + 1 < m
  · simp [ypaSucc, ht, hs t ht]
  · simp only [ypaSucc, ht, dite_false, newest]
    congr 1; ext; simp; have := t.isLt; omega

open Classical in
lemma ypa_sum_succ (h : History S m) (g : ((i : ι) → S i) → ℝ) :
    ∑ h', (if IsSuccessor h h' then g (newest h') else 0) = ∑ s, g s := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' newest (ypaSucc h) ?_ ?_ ?_ ?_ ?_
  · simp
  · intro s _; simp [ypaSucc_isSucc]
  · intro h' hh'; simp at hh'; exact (ypa_succ_eq h h' hh').symm
  · intro s _; exact ypa_newest_succ h s
  · intro _ _; rfl

lemma ypa_kernel_rowsum (J : Finset ι) (p q : (i : ι) → History S m → S i → ℝ)
    (hp : ∀ i h, ∑ x, p i h x = 1) (hq : ∀ i h, ∑ x, q i h x = 1) (h : History S m) :
    ∑ h', experimentKernel J p q h h' = 1 := by
  unfold experimentKernel
  rw [ypa_sum_succ h (fun s => (∏ j ∈ J, q j h (s j)) * ∏ j ∈ Jᶜ, p j h (s j))]
  let f : (i : ι) → S i → ℝ := fun j x => if j ∈ J then q j h x else p j h x
  have : ∀ s : (i : ι) → S i, (∏ j ∈ J, q j h (s j)) * ∏ j ∈ Jᶜ, p j h (s j)
      = ∏ j, f j (s j) := by
    intro s
    rw [← Finset.prod_mul_prod_compl J (fun j => f j (s j))]
    congr 1
    · apply Finset.prod_congr rfl; intro j hj; simp [f, hj]
    · apply Finset.prod_congr rfl; intro j hj; simp [f, Finset.mem_compl.1 hj]
  simp_rw [this]
  rw [← Fintype.prod_sum]
  apply Finset.prod_eq_one; intro j _; by_cases hj : j ∈ J <;> simp [f, hj, hp, hq]

lemma ypa_kernel_nonneg (J : Finset ι) (p q : (i : ι) → History S m → S i → ℝ)
    (hp : ∀ i h x, 0 ≤ p i h x) (hq : ∀ i h x, 0 ≤ q i h x) (h h' : History S m) :
    0 ≤ experimentKernel J p q h h' := by
  unfold experimentKernel
  split_ifs
  · exact mul_nonneg (Finset.prod_nonneg (fun j _ => hq _ _ _))
      (Finset.prod_nonneg (fun j _ => hp _ _ _))
  · exact le_rfl

/-- the chain of successors from `h` to `h'`. -/
def ypaChain (h h' : History S m) (j : ℕ) : History S m :=
  fun t => if hj : t.val + j < m then h ⟨t.val + j, hj⟩
    else if hj2 : t.val + j - m < m then h' ⟨t.val + j - m, hj2⟩ else h t

lemma ypaChain_zero (h h' : History S m) : ypaChain h h' 0 = h := by
  funext t; simp [ypaChain]

lemma ypaChain_m (h h' : History S m) : ypaChain h h' m = h' := by
  funext t; simp [ypaChain]

lemma ypaChain_succ (h h' : History S m) (j : ℕ) (hj : j < m) :
    IsSuccessor (ypaChain h h' j) (ypaChain h h' (j+1)) := by
  intro t ht
  simp only [ypaChain]
  have e1 : (⟨t.val + 1, ht⟩ : Fin m).val = t.val + 1 := rfl
  by_cases c1 : t.val + (j+1) < m
  · have c2 : t.val + 1 + j < m := by omega
    rw [dif_pos c1, dif_pos c2]; congr 1; ext; simp; omega
  · have c2 : ¬ (t.val + 1 + j < m) := by omega
    have c3 : t.val + (j+1) - m < m := by omega
    have c4 : t.val + 1 + j - m < m := by omega
    rw [dif_neg c1, dif_neg c2, dif_pos c3, dif_pos c4]; congr 1; ext; simp; omega

end Chain

theorem pia_core {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → ((i : ι) → S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (p q : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) (lam : ι → ℝ)
    (hp : IsBestReplyDistribution u k p) (hq : IsExperimentation lam q)
    (ε : ℝ) (hε : 0 < ε) (hεlam : ∀ i, ε * lam i ≤ 1) :
    perturbed p q lam ε ∈ Matrix.rowStochastic ℝ (YoungConventions.AdaptivePlay.History S m) ∧
    (∀ h h' : YoungConventions.AdaptivePlay.History S m, 0 < (perturbed p q lam ε ^ m) h h') ∧
    (∀ h : YoungConventions.AdaptivePlay.History S m, 0 < (perturbed p q lam ε ^ (m + 1)) h h) ∧
    ∃! μ : YoungConventions.AdaptivePlay.History S m → ℝ,
      IsStationaryDistribution μ (perturbed p q lam ε) := by
  set P := perturbed p q lam ε with hPdef
  have hpnn : ∀ i h x, 0 ≤ p i h x := fun i h x => (hp i h).1 x
  have hqnn : ∀ i h x, 0 ≤ q i h x := fun i h x => ((hq.2 i h).1 x).le
  have hWnn := ypaW_nonneg lam ε hε hq.1 hεlam
  have hnn : ∀ h h', 0 ≤ P h h' := by
    intro h h'
    rw [hPdef, ypa_full]
    exact Finset.sum_nonneg (fun J _ => mul_nonneg (hWnn J)
      (ypa_kernel_nonneg J p q hpnn hqnn h h'))
  have hrow : ∀ h, ∑ h', P h h' = 1 := by
    intro h
    simp_rw [hPdef, ypa_full]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp_rw [ypa_kernel_rowsum _ p q (fun i h => (hp i h).2.1) (fun i h => (hq.2 i h).2) h,
      mul_one]
    exact ypaW_sum lam ε
  have hstoch : P ∈ Matrix.rowStochastic ℝ (History S m) :=
    Matrix.mem_rowStochastic_iff_sum.2 ⟨hnn, hrow⟩
  have hsuccpos : ∀ h h', IsSuccessor h h' → 0 < P h h' := by
    intro h h' hs
    rw [hPdef, ypa_full]
    have hW : 0 < ypaW lam ε Finset.univ := by
      unfold ypaW
      simp only [Finset.compl_univ, Finset.prod_empty, mul_one]
      exact mul_pos (pow_pos hε _) (Finset.prod_pos (fun j _ => hq.1 j))
    have hK : 0 < experimentKernel Finset.univ p q h h' := by
      unfold experimentKernel
      rw [if_pos hs]
      simp only [Finset.compl_univ, Finset.prod_empty, mul_one]
      exact Finset.prod_pos (fun j _ => (hq.2 j h).1 _)
    calc (0:ℝ) < ypaW lam ε Finset.univ * experimentKernel Finset.univ p q h h' := mul_pos hW hK
    _ ≤ _ := Finset.single_le_sum (f := fun J => ypaW lam ε J * experimentKernel J p q h h')
          (fun J _ => mul_nonneg (hWnn J) (ypa_kernel_nonneg J p q hpnn hqnn h h'))
          (Finset.mem_univ _)
  have hpowm : ∀ h h', 0 < (P ^ m) h h' := by
    intro h h'
    have := ypa_mpow_chain P hnn (ypaChain h h') m
      (fun j hj => hsuccpos _ _ (ypaChain_succ h h' j hj))
    rwa [ypaChain_zero, ypaChain_m] at this
  let s0 : (i : ι) → S i := fun i => Classical.arbitrary _
  have hNe : Nonempty (History S m) := ⟨fun _ => s0⟩
  refine ⟨hstoch, hpowm, ?_, ?_⟩
  · intro h
    rw [pow_succ', Matrix.mul_apply]
    have h1 := hsuccpos h (ypaSucc h s0) (ypaSucc_isSucc h s0)
    have h2 := hpowm (ypaSucc h s0) h
    calc (0:ℝ) < P h (ypaSucc h s0) * (P ^ m) (ypaSucc h s0) h := mul_pos h1 h2
    _ ≤ _ := Finset.single_le_sum (f := fun z => P h z * (P ^ m) z h)
          (fun z _ => mul_nonneg (hnn _ _) (ypa_mpow_nonneg P hnn m _ _)) (Finset.mem_univ _)
  · obtain ⟨μ, hμ⟩ := ypa_stat_exists P hstoch
    exact ⟨μ, hμ, fun ν hν => ypa_stat_unique P m hpowm ν μ hν hμ⟩

end YoungConventions.RiskDominance

open YoungConventions.RiskDominance


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → ((i : ι) → S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (p q : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) (lam : ι → ℝ)
    (hp : IsBestReplyDistribution u k p) (hq : IsExperimentation lam q)
    (ε : ℝ) (hε : 0 < ε) (hεlam : ∀ i, ε * lam i ≤ 1) :
    perturbed p q lam ε ∈ Matrix.rowStochastic ℝ (YoungConventions.AdaptivePlay.History S m) ∧
    (∀ h h' : YoungConventions.AdaptivePlay.History S m, 0 < (perturbed p q lam ε ^ m) h h') ∧
    (∀ h : YoungConventions.AdaptivePlay.History S m, 0 < (perturbed p q lam ε ^ (m + 1)) h h) ∧
    ∃! μ : YoungConventions.AdaptivePlay.History S m → ℝ, IsStationaryDistribution μ (perturbed p q lam ε) := by
  exact pia_core u k m hk hkm p q lam hp hq ε hε hεlam

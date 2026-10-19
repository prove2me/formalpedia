-- Prove2me | solution 1 for SubsetShrink.Events.eq_28
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T20:45:12.174687+00:00
-- url     : https://prove2.me/submissions/fbe9c36c-6177-4fd3-a206-641bc026d5f2

/-
  DS8 target: SubsetShrink.Events.eq_28
  theorem_id 10d1f6f2-0f54-455e-b5f7-d20708bc6708 (Open milestone of mission
  b3f99725-2ef4-482e-8cc0-ff264fd019ff).

  First conjunct: the finite rearrangement / support bound
      ∑_j u♯_j √log(2p/j) ≤ ‖u‖ √(∑_{j≤s} log(2p/j)),
  proved here from scratch (sortedSum is a max over permutations, the support of
  u∘π has at most s points, Cauchy–Schwarz, and the monotone subset-sum bound).
  Second conjunct reuses the now-Proved platform theorem
  SubsetShrink.Events.sum_log_bound for  ∑_{j≤s} log(2p/j) ≤ s log(2ep/s).
-/
import Mathlib
import Definitions.Def_SubsetShrink_Events_Model
import Theorems.Thm_SubsetShrink_Events_sum_log_bound

open MeasureTheory ProbabilityTheory
open SubsetShrink.Events
open scoped BigOperators

private lemma l2_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ l2 v := Real.sqrt_nonneg _

/-- Permuting the coordinates preserves `l0`. -/
private lemma l0_comp_perm {p : ℕ} (u : Fin p → ℝ) (π : Equiv.Perm (Fin p)) :
    l0 (fun j => u (π j)) = l0 u := by
  unfold l0
  refine Finset.card_bij (fun x _ => π x) ?_ ?_ ?_
  · intro x hx
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
  · intro x _ y _ hxy
    exact π.injective hxy
  · intro y hy
    refine ⟨π.symm y, ?_, ?_⟩
    · simpa [Finset.mem_filter, Equiv.apply_symm_apply] using hy
    · simp

/-- `log (2p/i) ≥ 0` for `1 ≤ i ≤ p`. -/
private lemma log_two_p_div_nonneg {p i : ℕ} (hp : 1 ≤ p) (hi : 1 ≤ i) (hip : i ≤ p) :
    0 ≤ Real.log (2 * (p : ℝ) / (i : ℝ)) := by
  refine Real.log_nonneg ?_
  have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hi)
  rw [le_div_iff₀ hiR]
  have hipR : (i : ℝ) ≤ (p : ℝ) := by exact_mod_cast hip
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp)
  nlinarith

/-- `i ↦ log (2p/i)` is non-increasing on the positive integers. -/
private lemma log_two_p_div_antitone {p i j : ℕ} (hp : 1 ≤ p) (hi : 1 ≤ i) (hij : i ≤ j) :
    Real.log (2 * (p : ℝ) / (j : ℝ)) ≤ Real.log (2 * (p : ℝ) / (i : ℝ)) := by
  have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hi)
  have hjR : (0 : ℝ) < (j : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) (le_trans hi hij))
  have hpos : 0 < 2 * (p : ℝ) / (j : ℝ) := div_pos (by positivity) hjR
  refine Real.log_le_log hpos ?_
  rw [div_le_div_iff₀ hjR hiR]
  have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  exact mul_le_mul_of_nonneg_left hijR (by positivity)

/-- **Finite rearrangement / support bound.**  If `f` is non-increasing and `T` is a
subset of `{1,…,p}`, then `∑_{j∈T} f j` is at most the sum of the `#T` largest
admissible weights `f 1, …, f (#T)`. -/
private lemma sum_le_sum_Icc_card {f : ℕ → ℝ} {p : ℕ}
    (hf : ∀ i j, 1 ≤ i → i ≤ j → f j ≤ f i) (T : Finset ℕ)
    (hT : T ⊆ Finset.Icc 1 p) :
    ∑ j ∈ T, f j ≤ ∑ j ∈ Finset.Icc 1 T.card, f j := by
  revert hT
  induction T using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a T hlt ih =>
      intro hsub
      have ha : a ∈ Finset.Icc 1 p := hsub (Finset.mem_insert_self a T)
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hTsub : T ⊆ Finset.Icc 1 p := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have ih' : ∑ j ∈ T, f j ≤ ∑ j ∈ Finset.Icc 1 T.card, f j := ih hTsub
      have hnot : a ∉ T := fun h => lt_irrefl a (hlt a h)
      have hcard : (insert a T).card = T.card + 1 := Finset.card_insert_of_notMem hnot
      have hTle : T.card ≤ a - 1 := by
        have hsubIco : T ⊆ Finset.Ico 1 a := fun x hx =>
          Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp (hTsub hx)).1, hlt x hx⟩
        have hc := Finset.card_le_card hsubIco
        rwa [Nat.card_Ico] at hc
      have hTa : T.card + 1 ≤ a := by omega
      have hfa : f a ≤ f (T.card + 1) := hf (T.card + 1) a (by omega) hTa
      have hIcc : Finset.Icc 1 (T.card + 1) = insert (T.card + 1) (Finset.Icc 1 T.card) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot2 : T.card + 1 ∉ Finset.Icc 1 T.card := by
        simp only [Finset.mem_Icc]
        omega
      have h1 : ∑ j ∈ insert a T, f j = f a + ∑ j ∈ T, f j := Finset.sum_insert hnot
      have h2 : ∑ j ∈ Finset.Icc 1 (insert a T).card, f j
          = ∑ j ∈ Finset.Icc 1 (T.card + 1), f j := by rw [hcard]
      rw [h1, h2, hIcc, Finset.sum_insert hnot2]
      linarith

/-- Monotone subset-sum bound: a set of at most `s` positive integers has weight sum
at most `∑_{j=1}^{s} f j`, for non-negative non-increasing `f`. -/
private lemma sum_le_sum_Icc_of_card_le {f : ℕ → ℝ} {p s : ℕ}
    (hf : ∀ i j, 1 ≤ i → i ≤ j → f j ≤ f i)
    (hfnn : ∀ i, 1 ≤ i → i ≤ p → 0 ≤ f i)
    {T : Finset ℕ} (hT : T ⊆ Finset.Icc 1 p) (hcard : T.card ≤ s) (hsp : s ≤ p) :
    ∑ j ∈ T, f j ≤ ∑ j ∈ Finset.Icc 1 s, f j := by
  refine le_trans (sum_le_sum_Icc_card hf T hT) ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hcard) ?_
  intro x hx _
  exact hfnn x (Finset.mem_Icc.mp hx).1 (le_trans (Finset.mem_Icc.mp hx).2 hsp)

/-- Cauchy–Schwarz plus the support bound: every permutation sum is bounded by
`‖u‖ √(∑_{j≤s} log(2p/j))`. -/
private lemma perm_sum_le {p s : ℕ} (hs : 1 ≤ s) (hsp : s ≤ p) {u : Fin p → ℝ}
    (hu : l0 u ≤ s) (π : Equiv.Perm (Fin p)) :
    (∑ j : Fin p, |u (π j)| * Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1)))) ≤
      l2 u * Real.sqrt (∑ i ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / i)) := by
  have hp : 1 ≤ p := le_trans hs hsp
  set w : Fin p → ℝ :=
    fun j => Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1))) with hw
  set T : Finset (Fin p) := Finset.univ.filter (fun j => u (π j) ≠ 0) with hT
  have hcast : ∀ j : Fin p, (((j.val + 1 : ℕ)) : ℝ) = (j.val : ℝ) + 1 := by
    intro j
    rw [Nat.cast_add, Nat.cast_one]
  have hw2 : ∀ j : Fin p, w j ^ 2 = Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1)) := by
    intro j
    show Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1))) ^ 2 =
      Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1))
    rw [← hcast j]
    exact Real.sq_sqrt (log_two_p_div_nonneg (p := p) (i := j.val + 1) hp (by omega) (by omega))
  have hTcard : T.card ≤ s := by
    have h1 : T.card = l0 (fun j => u (π j)) := by simp only [hT, l0]
    rw [h1, l0_comp_perm u π]
    exact hu
  have hsum_eq : (∑ j : Fin p, |u (π j)| * w j) = ∑ j ∈ T, |u (π j)| * w j := by
    rw [hT]
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro j _ hj
    have huj : u (π j) = 0 := by
      by_contra h
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
    rw [huj, abs_zero, zero_mul]
  have hA : ∑ j ∈ T, |u (π j)| ^ 2 = (l2 u) ^ 2 := by
    have hsub : ∑ j ∈ T, |u (π j)| ^ 2 = ∑ j ∈ T, (u (π j)) ^ 2 :=
      Finset.sum_congr rfl (fun j _ => sq_abs (u (π j)))
    have herase : ∑ j ∈ T, (u (π j)) ^ 2 = ∑ j : Fin p, (u (π j)) ^ 2 := by
      rw [hT]
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro j _ hj
      have huj : u (π j) = 0 := by
        by_contra h
        exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
      rw [huj]; ring
    have hperm : ∑ j : Fin p, (u (π j)) ^ 2 = ∑ j : Fin p, (u j) ^ 2 :=
      Equiv.sum_comp π (fun j => (u j) ^ 2)
    have hl2 : (l2 u) ^ 2 = ∑ j : Fin p, (u j) ^ 2 := by
      rw [l2, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    rw [hsub, herase, hperm, hl2]
  have hB : ∑ j ∈ T, w j ^ 2 ≤ ∑ i ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / (i : ℝ)) := by
    have hw2T : ∑ j ∈ T, w j ^ 2
        = ∑ j ∈ T, Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1)) :=
      Finset.sum_congr rfl (fun j _ => hw2 j)
    rw [hw2T]
    have hinj : Set.InjOn (fun j : Fin p => j.val + 1) ↑T := by
      intro x _ y _ hxy
      have hxy' : x.val + 1 = y.val + 1 := hxy
      exact Fin.ext (by omega)
    have himgL : ∑ j ∈ T, Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1))
        = ∑ j ∈ T, Real.log (2 * (p : ℝ) / (((j.val + 1 : ℕ)) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hcast j]
    have himg : ∑ i ∈ T.image (fun j : Fin p => j.val + 1),
          Real.log (2 * (p : ℝ) / (i : ℝ))
        = ∑ j ∈ T, Real.log (2 * (p : ℝ) / (((j.val + 1 : ℕ)) : ℝ)) :=
      Finset.sum_image (s := T) (g := fun j : Fin p => j.val + 1) hinj
    rw [himgL, ← himg]
    have himgT : T.image (fun j => j.val + 1) ⊆ Finset.Icc 1 p := by
      intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩
    have himgcard : (T.image (fun j => j.val + 1)).card ≤ s :=
      le_trans Finset.card_image_le hTcard
    exact sum_le_sum_Icc_of_card_le
      (f := fun i : ℕ => Real.log (2 * (p : ℝ) / (i : ℝ)))
      (fun i j hi hij => log_two_p_div_antitone hp hi hij)
      (fun i hi hip => log_two_p_div_nonneg hp hi hip)
      himgT himgcard hsp
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt T (fun j => |u (π j)|) w
  calc (∑ j : Fin p, |u (π j)| * w j)
      = ∑ j ∈ T, |u (π j)| * w j := hsum_eq
    _ ≤ Real.sqrt (∑ j ∈ T, |u (π j)| ^ 2) * Real.sqrt (∑ j ∈ T, w j ^ 2) := hcs
    _ = Real.sqrt ((l2 u) ^ 2) * Real.sqrt (∑ j ∈ T, w j ^ 2) := by rw [hA]
    _ = l2 u * Real.sqrt (∑ j ∈ T, w j ^ 2) := by rw [Real.sqrt_sq (l2_nonneg u)]
    _ ≤ l2 u * Real.sqrt (∑ i ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / (i : ℝ))) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hB) (l2_nonneg u)

theorem solution {p s : ℕ} (hs : 1 ≤ s) (hsp : s ≤ p) (u : Fin p → ℝ) (hu : l0 u ≤ s) :
    sortedSum u ≤ l2 u * Real.sqrt (∑ j ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / j)) ∧
      l2 u * Real.sqrt (∑ j ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / j)) ≤
        Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) * l2 u := by
  constructor
  · show Finset.univ.sup' Finset.univ_nonempty
        (fun π : Equiv.Perm (Fin p) =>
          ∑ j : Fin p, |u (π j)| * Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1)))) ≤
      l2 u * Real.sqrt (∑ j ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / j))
    exact Finset.sup'_le Finset.univ_nonempty _ (fun π _ => perm_sum_le hs hsp hu π)
  · calc l2 u * Real.sqrt (∑ j ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / j))
        = Real.sqrt (∑ j ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / j)) * l2 u :=
          mul_comm _ _
      _ ≤ Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) * l2 u :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (sum_log_bound hs hsp).2) (l2_nonneg u)

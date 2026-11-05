-- Prove2me | solution 1 for StrongConv.prob_norm_adjPerp_ge_of_lt_rhoStair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:19:34.375117+00:00
-- url     : https://prove2.me/submissions/ebb2c2ae-d2e4-4ee1-b1d2-2c824e1ded22

import Mathlib
import Definitions.Def_StrongConv

section
noncomputable section
namespace StrongConv.CitedGraphs
open Filter
/-!
# Blueprint: Kesten, Alon–Boppana (Nilli), Friedman's tangle lower bound

Interfaces for the three cited graph results of CGTvH §8. Every lemma below is `sorry`; the three
published statements are proved from them at the end of this file.
-/
/-! ## Kesten: the 2d-regular tree -/

end StrongConv.CitedGraphs
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs.PartR
open scoped InnerProductSpace
/-- The real vector `f` as a vector of `ℂᴺ`. -/
def toVec {N : ℕ} (f : Fin N → ℝ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun v => (f v : ℂ))

lemma toVec_mem {N : ℕ} (f : Fin N → ℝ) (hf : ∑ v, f v = 0) : toVec f ∈ OnesPerp N := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp only [toVec, onesVec, PiLp.inner_apply]
  simp
  exact_mod_cast hf

lemma permOp_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    (permOp σ x) j = x (σ.symm j) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma inner_permOp {N : ℕ} (σ : Equiv.Perm (Fin N)) (f : Fin N → ℝ) :
    ⟪toVec f, permOp σ (toVec f)⟫_ℂ = ((∑ v, f v * f (σ v) : ℝ) : ℂ) := by
  simp only [PiLp.inner_apply, permOp_apply]
  push_cast
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [toVec]

lemma inner_sModel {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (f : Fin N → ℝ)
    (hx : toVec f ∈ OnesPerp N) (i : Fin d) :
    ⟪(⟨toVec f, hx⟩ : OnesPerp N), (sModel σ i) ⟨toVec f, hx⟩ + star (sModel σ i) ⟨toVec f, hx⟩⟫_ℂ =
      ((2 * ∑ v, f v * f (σ i v) : ℝ) : ℂ) := by
  rw [inner_add_right, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  have h1 : ⟪(⟨toVec f, hx⟩ : OnesPerp N), (sModel σ i) ⟨toVec f, hx⟩⟫_ℂ =
      ((∑ v, f v * f (σ i v) : ℝ) : ℂ) := by
    rw [← inner_permOp]
    rfl
  rw [h1, ← inner_conj_symm, h1]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

theorem rayleigh_le_norm_adjPerp {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (f : Fin N → ℝ)
    (hf : ∑ v, f v = 0) (hf0 : 0 < ∑ v, f v ^ 2) :
    (∑ i, ∑ v, 2 * f v * f (σ i v)) / (∑ v, f v ^ 2) ≤ ‖adjPerp σ‖ := by
  have hx := toVec_mem f hf
  set x : OnesPerp N := ⟨toVec f, hx⟩
  have hinner : ⟪x, adjPerp σ x⟫_ℂ = ((∑ i, ∑ v, 2 * f v * f (σ i v) : ℝ) : ℂ) := by
    rw [adjPerp, FunLike.coe_sum, Finset.sum_apply, inner_sum]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.add_apply, inner_sModel σ f hx i]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    ring
  have hnorm : ‖x‖ ^ 2 = ∑ v, f v ^ 2 := by
    change ‖toVec f‖ ^ 2 = _
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    simp [toVec]
  rw [div_le_iff₀ hf0, ← hnorm]
  calc (∑ i, ∑ v, 2 * f v * f (σ i v)) ≤ ‖⟪x, adjPerp σ x⟫_ℂ‖ := by
        rw [hinner, Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ ‖x‖ * ‖adjPerp σ x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖adjPerp σ‖ * ‖x‖) := by
        gcongr; exact (adjPerp σ).le_opNorm x
    _ = ‖adjPerp σ‖ * ‖x‖ ^ 2 := by ring

end StrongConv.CitedGraphs.PartR
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs
open Filter
/-! ## The permutation model: Rayleigh quotients on `{1_N}⊥` -/
alias rayleigh_le_norm_adjPerp := StrongConv.CitedGraphs.PartR.rayleigh_le_norm_adjPerp

/-! ## Alon–Boppana (Nilli's argument) -/

end StrongConv.CitedGraphs
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs.PartT
open Finset
/-!
# Part T: Friedman's tangle test vector
-/
/-- The profile `j ↦ β^j` for `j ≤ k`, `0` beyond. -/
def psi (β : ℝ) (k j : ℕ) : ℝ := if j ≤ k then β ^ j else 0

lemma psi_anti {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (k : ℕ) {a b : ℕ} (h : a ≤ b) :
    psi β k b ≤ psi β k a := by
  unfold psi
  split_ifs with hb ha ha
  · exact pow_le_pow_of_le_one hβ hβ1 h
  · omega
  · positivity
  · exact le_rfl

lemma sum_fin_ite (d m : ℕ) (hmd : m ≤ d) (x y : ℝ) :
    ∑ i : Fin d, (if (i : ℕ) < m then x else y) = m * x + (d - m : ℕ) * y := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < m then x else y), sum_ite]
  have h1 : (range d).filter (fun i => i < m) = range m := by
    ext i; simp; omega
  have h2 : ((range d).filter (fun i => ¬ i < m)).card = d - m := by
    have : (range d).filter (fun i => ¬ i < m) = Ico m d := by
      ext i; simp; omega
    rw [this, Nat.card_Ico]
  rw [h1, sum_const, sum_const, card_range, h2, nsmul_eq_mul, nsmul_eq_mul]

end StrongConv.CitedGraphs.PartT
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs.PartP
open Finset
/-- Permutations fixing a finset pointwise: `(n - #S)!` of them. -/
lemma card_fix (N : ℕ) (S : Finset (Fin N)) :
    (univ.filter (fun τ : Equiv.Perm (Fin N) => ∀ a ∈ S, τ a = a)).card = (N - S.card).factorial := by
  classical
  have h1 : (univ.filter (fun τ : Equiv.Perm (Fin N) => ∀ a ∈ S, τ a = a)).card =
      Fintype.card {f : Equiv.Perm (Fin N) // ∀ a, ¬ (a ∉ S) → f a = a} := by
    rw [Fintype.card_subtype]
    congr 1
    ext τ
    simp
  rw [h1, ← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∉ S)),
    Fintype.card_perm]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin]
  simp

lemma prod_fin_ite (d m : ℕ) (hmd : m ≤ d) (x y : ℝ) :
    ∏ i : Fin d, (if (i : ℕ) < m then x else y) = x ^ m * y ^ (d - m) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < m then x else y), prod_ite]
  have h1 : (range d).filter (fun i => i < m) = range m := by
    ext i; simp; omega
  have h2 : ((range d).filter (fun i => ¬ i < m)).card = d - m := by
    have : (range d).filter (fun i => ¬ i < m) = Ico m d := by
      ext i; simp; omega
    rw [this, Nat.card_Ico]
  rw [h1, prod_const, prod_const, card_range, h2]

/-- Count of tuples with `σ i` fixing `S` pointwise for `i < m`. -/
lemma card_E (d m N : ℕ) (hmd : m ≤ d) (S : Finset (Fin N)) :
    ((univ.filter (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ∀ i : Fin d, (i : ℕ) < m → ∀ a ∈ S, σ i a = a)).card : ℝ) =
      ((N - S.card).factorial : ℝ) ^ m * (N.factorial : ℝ) ^ (d - m) := by
  classical
  have h : univ.filter (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ∀ i : Fin d, (i : ℕ) < m → ∀ a ∈ S, σ i a = a) =
      Fintype.piFinset (fun i : Fin d =>
        univ.filter (fun τ : Equiv.Perm (Fin N) => (i : ℕ) < m → ∀ a ∈ S, τ a = a)) := by
    ext σ; simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]
  push_cast
  have h2 : ∀ i : Fin d, ((univ.filter (fun τ : Equiv.Perm (Fin N) =>
      (i : ℕ) < m → ∀ a ∈ S, τ a = a)).card : ℝ) =
      if (i : ℕ) < m then ((N - S.card).factorial : ℝ) else (N.factorial : ℝ) := by
    intro i
    split_ifs with hi
    · simp only [hi, true_implies]; exact_mod_cast card_fix N S
    · simp [hi, Fintype.card_perm]
  rw [Finset.prod_congr rfl (fun i _ => h2 i), prod_fin_ite d m hmd]

theorem prob_common_fixed_point_ge (d m N : ℕ) (hm : 1 ≤ m) (hmd : m ≤ d) (hN : 2 ≤ N) :
    1 / (N : ℝ) ^ (m - 1) - 1 / (2 * ((N : ℝ) * (N - 1)) ^ (m - 1)) ≤
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ∃ v, ∀ i : Fin d, (i : ℕ) < m → σ i v = v) := by
  classical
  set X := Fin d → Equiv.Perm (Fin N)
  let E : Fin N → X → Prop := fun v σ => ∀ i : Fin d, (i : ℕ) < m → σ i v = v
  let I : Fin N → X → ℝ := fun v σ => if E v σ then 1 else 0
  let t : X → ℝ := fun σ => ∑ v, I v σ
  -- pointwise Bonferroni
  have hpt : ∀ σ : X, t σ - (t σ ^ 2 - t σ) / 2 ≤ if (∃ v, E v σ) then 1 else 0 := by
    intro σ
    have ht : t σ = ((univ.filter (fun v => E v σ)).card : ℝ) := by
      simp only [t, I]; rw [Finset.sum_boole]
    rw [ht]
    split_ifs with h
    · rcases Nat.lt_or_ge ((univ.filter (fun v => E v σ)).card) 2 with h2 | h2
      · interval_cases hc : (univ.filter (fun v => E v σ)).card <;> norm_num
      · have : (2 : ℝ) ≤ ((univ.filter (fun v => E v σ)).card : ℝ) := by exact_mod_cast h2
        nlinarith
    · push Not at h
      have : (univ.filter (fun v => E v σ)) = ∅ := by
        ext v; simp [h v]
      rw [this]; simp
  -- counts
  set F : ℝ := (N.factorial : ℝ)
  set a : ℝ := ((N - 1).factorial : ℝ) ^ m * F ^ (d - m)
  set b : ℝ := ((N - 2).factorial : ℝ) ^ m * F ^ (d - m)
  have hIa : ∀ v, ∑ σ : X, I v σ * I v σ = a := by
    intro v
    have : ∀ σ : X, I v σ * I v σ = I v σ := by
      intro σ; simp only [I]; split_ifs <;> norm_num
    simp_rw [this]
    simp only [I]
    rw [Finset.sum_boole]
    have := card_E d m N hmd {v}
    simp only [Finset.card_singleton, Finset.mem_singleton, forall_eq] at this
    exact this
  have hIb : ∀ v w, v ≠ w → ∑ σ : X, I v σ * I w σ = b := by
    intro v w hvw
    have : ∀ σ : X, I v σ * I w σ = if (E v σ ∧ E w σ) then 1 else 0 := by
      intro σ; simp only [I]; split_ifs <;> simp_all
    simp_rw [this]
    rw [Finset.sum_boole]
    have := card_E d m N hmd {v, w}
    rw [Finset.card_pair hvw] at this
    refine Eq.trans ?_ this
    congr 2
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq, E]
    constructor
    · rintro ⟨h1, h2⟩ i hi; exact ⟨h1 i hi, h2 i hi⟩
    · intro h; exact ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩
  have hsum_t : ∑ σ : X, t σ = N * a := by
    simp only [t]
    rw [Finset.sum_comm]
    have : ∀ v, ∑ σ : X, I v σ = a := by
      intro v; rw [← hIa v]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [I]; split_ifs <;> norm_num
    simp [this]
  have hsum_t2 : ∑ σ : X, t σ ^ 2 = N * a + N * (N - 1) * b := by
    have : ∀ σ : X, t σ ^ 2 = ∑ v, ∑ w, I v σ * I w σ := by
      intro σ; simp only [t]; rw [sq, Finset.sum_mul_sum]
    simp_rw [this]
    rw [Finset.sum_comm]
    have hrow : ∀ v : Fin N, ∑ σ : X, ∑ w, I v σ * I w σ = a + (N - 1) * b := by
      intro v
      rw [Finset.sum_comm]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), hIa v]
      rw [Finset.sum_congr rfl (fun w hw => hIb v w (Finset.ne_of_mem_erase hw).symm)]
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have : (1 : ℕ) ≤ N := by omega
      push_cast [this]
      ring
    rw [Finset.sum_congr rfl (fun v _ => hrow v)]
    simp
    ring
  -- assemble
  have hcardX : (Fintype.card X : ℝ) = F ^ d := by
    simp [X, F, Fintype.card_perm]
  have hF0 : 0 < F := by positivity
  have hlow : N * a - N * (N - 1) * b / 2 ≤
      ((univ.filter (fun σ : X => ∃ v, E v σ)).card : ℝ) := by
    rw [← Finset.sum_boole]
    calc N * a - N * (N - 1) * b / 2
        = ∑ σ : X, (t σ - (t σ ^ 2 - t σ) / 2) := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_sub_distrib, hsum_t,
            hsum_t2]; ring
      _ ≤ _ := Finset.sum_le_sum (fun σ _ => hpt σ)
  unfold uniformProb
  rw [hcardX]
  have hlow' : N * a - N * (N - 1) * b / 2 ≤ ((univ.filter (fun σ : X =>
      ∃ v, ∀ i : Fin d, (i : ℕ) < m → σ i v = v)).card : ℝ) := hlow
  refine le_trans ?_ (div_le_div_of_nonneg_right (c := F ^ d)
    (a := N * a - N * (N - 1) * b / 2) ?_ (by positivity))
  swap
  · refine le_trans hlow' (le_of_eq ?_)
    rw [Nat.cast_inj]
    congr
  -- arithmetic
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hN1 : (N - 1).factorial * N = N.factorial := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    simp [Nat.factorial_succ]; ring
  have hN2 : (N - 2).factorial * (N * (N - 1)) = N.factorial := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    simp [Nat.factorial_succ]; ring
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hcast1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have eA : ((N - 1).factorial : ℝ) = F / N := by
    rw [eq_div_iff (by positivity)]; simp only [F]; exact_mod_cast hN1
  have eB : ((N - 2).factorial : ℝ) = F / (N * (N - 1)) := by
    have hp : (0 : ℝ) < N * (N - 1) := by nlinarith
    rw [eq_div_iff hp.ne']; simp only [F]
    rw [← hcast1]; exact_mod_cast hN2
  simp only [a, b, eA, eB]
  have hd : d = (k + 1) + (d - (k + 1)) := by omega
  have hp : (0 : ℝ) < N * (N - 1) := by nlinarith
  have hNp : (0 : ℝ) < N := by linarith
  apply le_of_eq
  rw [hd, pow_add F]
  rw [Nat.add_sub_cancel_left]
  generalize hM : (N : ℝ) * (N - 1) = M at hp ⊢
  generalize (N : ℝ) = n at hNp hp ⊢
  have hG : F ^ (d - (k + 1)) ≠ 0 := by positivity
  generalize F ^ (d - (k + 1)) = G at hG ⊢
  rw [div_pow, div_pow]
  field_simp
  ring

end StrongConv.CitedGraphs.PartP
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs
open Filter
alias prob_common_fixed_point_ge := StrongConv.CitedGraphs.PartP.prob_common_fixed_point_ge

/-! ## The three published statements -/

theorem uniformProb_mono {X : Type*} [Fintype X] {E F : X → Prop} (h : ∀ x, E x → F x) :
    uniformProb E ≤ uniformProb F := by
  classical
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact h x hx)

theorem one_le_mStar (d : ℕ) (hd : 1 ≤ d) : 1 ≤ mStar d := by
  unfold mStar
  apply Nat.le_floor
  have h1 : (1 : ℝ) ≤ Real.sqrt (2 * d - 1) := by
    rw [Real.one_le_sqrt]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  push_cast
  linarith

end StrongConv.CitedGraphs
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs
open Finset
variable {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N))
/-!
# BFS levels on the graph of a permutation tuple (shared by Parts N and T)
-/
/-- The end `p = (i, b)` of the vertex `v`: `σ i v` if `b`, `(σ i)⁻¹ v` otherwise. -/
def endv (v : Fin N) (p : Fin d × Bool) : Fin N :=
  if p.2 then σ p.1 v else (σ p.1).symm v

lemma endv_flip (v : Fin N) (p : Fin d × Bool) : endv σ (endv σ v p) (p.1, !p.2) = v := by
  obtain ⟨i, b⟩ := p
  cases b <;> simp [endv]

lemma card_ends : Fintype.card (Fin d × Bool) = 2 * d := by
  simp [Fintype.card_prod]; ring

/-- One BFS step. -/
def nbhd (T : Finset (Fin N)) : Finset (Fin N) :=
  T ∪ T.biUnion (fun v => univ.image (endv σ v))

/-- BFS balls. -/
def ball (S : Finset (Fin N)) : ℕ → Finset (Fin N)
  | 0 => S
  | r + 1 => nbhd σ (ball S r)

end StrongConv.CitedGraphs
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs
open Finset
variable {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N))
variable {σ}
lemma ball_zero (S : Finset (Fin N)) : ball σ S 0 = S := rfl

lemma ball_succ (S : Finset (Fin N)) (r : ℕ) : ball σ S (r + 1) = nbhd σ (ball σ S r) := rfl

lemma ball_subset_succ (S : Finset (Fin N)) (r : ℕ) : ball σ S r ⊆ ball σ S (r + 1) := by
  rw [ball_succ]; exact subset_union_left

lemma ball_mono (S : Finset (Fin N)) {r r' : ℕ} (h : r ≤ r') : ball σ S r ⊆ ball σ S r' :=
  monotone_nat_of_le_succ (fun n => ball_subset_succ S n) h

lemma endv_mem_ball {S : Finset (Fin N)} {r : ℕ} {v : Fin N} (hv : v ∈ ball σ S r)
    (p : Fin d × Bool) : endv σ v p ∈ ball σ S (r + 1) := by
  rw [ball_succ, nbhd]
  apply mem_union_right
  rw [mem_biUnion]
  exact ⟨v, hv, mem_image.2 ⟨p, mem_univ _, rfl⟩⟩

lemma mem_ball_succ {S : Finset (Fin N)} {r : ℕ} {w : Fin N} :
    w ∈ ball σ S (r + 1) ↔ w ∈ ball σ S r ∨ ∃ p, endv σ w p ∈ ball σ S r := by
  constructor
  · intro h
    rw [ball_succ, nbhd, mem_union, mem_biUnion] at h
    rcases h with h | ⟨x, hx, hw⟩
    · exact Or.inl h
    · obtain ⟨p, -, rfl⟩ := mem_image.1 hw
      exact Or.inr ⟨(p.1, !p.2), by rw [endv_flip]; exact hx⟩
  · rintro (h | ⟨p, hp⟩)
    · exact ball_subset_succ S r h
    · have := endv_mem_ball hp (p.1, !p.2)
      rwa [endv_flip] at this

lemma card_nbhd (T : Finset (Fin N)) : (nbhd σ T).card ≤ T.card * (2 * d + 1) := by
  rw [nbhd]
  refine le_trans (card_union_le _ _) ?_
  have : (T.biUnion (fun v => univ.image (endv σ v))).card ≤ T.card * (2 * d) := by
    refine le_trans card_biUnion_le ?_
    refine le_trans (sum_le_sum (fun v _ => card_image_le)) ?_
    rw [sum_const, card_univ, card_ends, smul_eq_mul]
  nlinarith

lemma card_ball (S : Finset (Fin N)) (r : ℕ) : (ball σ S r).card ≤ S.card * (2 * d + 1) ^ r := by
  induction r with
  | zero => simp [ball_zero]
  | succ r ih =>
    rw [ball_succ]
    refine le_trans (card_nbhd _) ?_
    rw [pow_succ, ← mul_assoc]
    exact Nat.mul_le_mul_right _ ih

/-! ## Levels, capped at `K + 1` -/
variable (σ) in
/-- The BFS level of `w` from `S`, capped at `K + 1`. -/
def lev (S : Finset (Fin N)) (K : ℕ) (w : Fin N) : ℕ :=
  Nat.find (⟨K + 1, Or.inr rfl⟩ : ∃ r, w ∈ ball σ S r ∨ r = K + 1)

end StrongConv.CitedGraphs
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs
open Finset
variable {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N))
variable {σ}
variable {S : Finset (Fin N)} {K : ℕ}
lemma lev_le_cap (w : Fin N) : lev σ S K w ≤ K + 1 :=
  Nat.find_min' _ (Or.inr rfl)

lemma lev_le_iff {w : Fin N} {j : ℕ} (hj : j ≤ K) : lev σ S K w ≤ j ↔ w ∈ ball σ S j := by
  unfold lev
  rw [Nat.find_le_iff]
  constructor
  · rintro ⟨r, hr, h | h⟩
    · exact ball_mono S hr h
    · omega
  · intro h; exact ⟨j, le_rfl, Or.inl h⟩

lemma lev_eq_zero_iff {w : Fin N} : lev σ S K w = 0 ↔ w ∈ S := by
  rw [← Nat.le_zero, lev_le_iff (Nat.zero_le K)]; rfl

lemma lev_endv_le (w : Fin N) (p : Fin d × Bool) :
    lev σ S K (endv σ w p) ≤ lev σ S K w + 1 := by
  rcases Nat.lt_or_ge (lev σ S K w) (K + 1) with h | h
  · have hw : w ∈ ball σ S (lev σ S K w) := (lev_le_iff (by omega)).1 le_rfl
    have := endv_mem_ball hw p
    rcases Nat.lt_or_ge (lev σ S K w + 1) (K + 1) with h' | h'
    · exact (lev_le_iff (by omega)).2 this
    · exact le_trans (lev_le_cap _) h'
  · exact le_trans (lev_le_cap _) (by omega)

lemma lev_le_lev_endv (w : Fin N) (p : Fin d × Bool) :
    lev σ S K w ≤ lev σ S K (endv σ w p) + 1 := by
  have := lev_endv_le (σ := σ) (S := S) (K := K) (endv σ w p) (p.1, !p.2)
  rwa [endv_flip] at this

lemma exists_down {w : Fin N} (h1 : 1 ≤ lev σ S K w) (hK : lev σ S K w ≤ K) :
    ∃ p, lev σ S K (endv σ w p) + 1 = lev σ S K w := by
  obtain ⟨j, hj⟩ : ∃ j, lev σ S K w = j + 1 := ⟨lev σ S K w - 1, by omega⟩
  have hw : w ∈ ball σ S (j + 1) := (lev_le_iff (σ := σ) (j := j + 1) (by omega)).1 hj.le
  have hw' : w ∉ ball σ S j := by
    intro h; have := (lev_le_iff (σ := σ) (K := K) (j := j) (by omega)).2 h; omega
  rcases mem_ball_succ.1 hw with h | ⟨p, hp⟩
  · exact absurd h hw'
  · refine ⟨p, ?_⟩
    have h2 := (lev_le_iff (σ := σ) (K := K) (j := j) (by omega)).2 hp
    have h3 := lev_le_lev_endv (σ := σ) (S := S) (K := K) w p
    omega

variable (σ S K) in
/-- The ends of `u` going one level up. -/
def up (u : Fin N) : Finset (Fin d × Bool) :=
  univ.filter (fun p => lev σ S K (endv σ u p) = lev σ S K u + 1)

lemma card_up_le_two_d (u : Fin N) : (up σ S K u).card ≤ 2 * d := by
  refine le_trans (card_filter_le _ _) ?_
  rw [card_univ, card_ends]

lemma card_up_le_of_not_mem {u : Fin N} (p0 : Fin d × Bool) (hp0 : p0 ∉ up σ S K u) :
    (up σ S K u).card ≤ 2 * d - 1 := by
  have : up σ S K u ⊆ univ.erase p0 := by
    intro p hp; rw [mem_erase]; exact ⟨fun h => hp0 (h ▸ hp), mem_univ _⟩
  refine le_trans (card_le_card this) ?_
  rw [card_erase_of_mem (mem_univ _), card_univ, card_ends]

lemma card_up_le {u : Fin N} (h1 : 1 ≤ lev σ S K u) (hK : lev σ S K u ≤ K) :
    (up σ S K u).card ≤ 2 * d - 1 := by
  obtain ⟨p, hp⟩ := exists_down h1 hK
  refine card_up_le_of_not_mem p ?_
  simp only [up, mem_filter, mem_univ, true_and]
  omega

variable (σ S K) in
/-- The level sets. -/
def level (j : ℕ) : Finset (Fin N) := univ.filter (fun u => lev σ S K u = j)

lemma card_level_succ_le {j : ℕ} (hj : j + 1 ≤ K) :
    (level σ S K (j + 1)).card ≤ ∑ u ∈ level σ S K j, (up σ S K u).card := by
  classical
  have hsub : level σ S K (j + 1) ⊆
      (level σ S K j).biUnion (fun u => (up σ S K u).image (endv σ u)) := by
    intro w hw
    simp only [level, mem_filter, mem_univ, true_and] at hw
    obtain ⟨p, hp⟩ := exists_down (σ := σ) (S := S) (K := K) (w := w) (by omega) (by omega)
    rw [mem_biUnion]
    refine ⟨endv σ w p, ?_, ?_⟩
    · simp only [level, mem_filter, mem_univ, true_and]; omega
    · rw [mem_image]
      refine ⟨(p.1, !p.2), ?_, endv_flip σ w p⟩
      simp only [up, mem_filter, mem_univ, true_and]
      rw [endv_flip]; omega
  refine le_trans (card_le_card hsub) (le_trans card_biUnion_le ?_)
  exact sum_le_sum (fun u _ => card_image_le)

lemma card_level_succ_le_mul {j : ℕ} (hj : j + 1 ≤ K) {c : ℕ}
    (hc : ∀ u ∈ level σ S K j, (up σ S K u).card ≤ c) :
    (level σ S K (j + 1)).card ≤ c * (level σ S K j).card := by
  refine le_trans (card_level_succ_le hj) ?_
  refine le_trans (sum_le_sum hc) ?_
  simp [mul_comm]

/-! ## The quadratic form -/
lemma sum_ends (F : Fin d × Bool → ℝ) :
    ∑ p, F p = ∑ i, (F (i, true) + F (i, false)) := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]

variable (σ) in
/-- `Q(f) = ∑ᵥ f v ∑ₚ f (end p of v)`. -/
lemma quad_eq_sum_ends (f : Fin N → ℝ) :
    ∑ i, ∑ v, 2 * f v * f (σ i v) = ∑ v, f v * ∑ p, f (endv σ v p) := by
  simp_rw [sum_ends, mul_sum]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl (fun i _ => ?_)
  have h2 : ∑ v, f v * f ((σ i).symm v) = ∑ v, f (σ i v) * f v := by
    rw [← Equiv.sum_comp (σ i)]; simp
  simp only [endv, if_true, Bool.false_eq_true, if_false, mul_add, sum_add_distrib, h2]
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun v _ => ?_)
  ring

end StrongConv.CitedGraphs
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs.PartT
open Finset
/-- The lower bound `Q(f₀) ≥ ρ ‖f₀‖² - n_k q β^{2k+1}`. -/
theorem tangle_lower {d N m k : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (v : Fin N)
    (hv : ∀ i : Fin d, (i : ℕ) < m → σ i v = v) (hm : 1 ≤ m) (hmd : m ≤ d) (hk : 1 ≤ k)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hβm : (2 * (m : ℝ) - 1) * β = 1) :
    (1 / β + (2 * d - 1) * β) * ∑ u, psi β k (lev σ {v} k u) ^ 2 -
        ((level σ {v} k k).card : ℝ) * ((2 * d - 1) * β ^ (2 * k + 1)) ≤
      ∑ i, ∑ u, 2 * psi β k (lev σ {v} k u) * psi β k (lev σ {v} k (σ i u)) := by
  set q : ℝ := 2 * d - 1 with hq
  set ρ := 1 / β + q * β with hρ
  set f : Fin N → ℝ := fun u => psi β k (lev σ {v} k u) with hf
  have hd : 1 ≤ d := le_trans hm hmd
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hρβ : ρ * β = 1 + q * β ^ 2 := by rw [hρ]; field_simp
  have hcast : ((2 * d - 1 : ℕ) : ℝ) = q := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hfa : ∀ u p, psi β k (lev σ {v} k u + 1) ≤ f (endv σ u p) := by
    intro u p
    exact psi_anti hβ0.le hβ1 k (lev_endv_le u p)
  have hpt : ∀ u, ρ * f u ^ 2 - (if lev σ {v} k u = k then q * β ^ (2 * k + 1) else 0) ≤
      f u * ∑ p, f (endv σ u p) := by
    intro u
    set j := lev σ {v} k u with hj
    rcases Nat.lt_or_ge k j with hjk | hjk
    · have : f u = 0 := by simp only [hf, psi, ← hj]; rw [if_neg (by omega)]
      rw [this, if_neg (by omega)]; simp
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · -- the centre
      have hu : u = v := by
        simpa using (lev_eq_zero_iff (σ := σ) (S := {v}) (K := k)).1 h0
      have hfu : f u = 1 := by simp only [hf, psi, ← hj, h0]; simp
      have hA : ∑ p : Fin d × Bool, (if (p.1 : ℕ) < m then (1 : ℝ) else β) ≤ ∑ p, f (endv σ u p) := by
        refine sum_le_sum (fun p _ => ?_)
        split_ifs with hp
        · have : endv σ u p = v := by
            rw [hu]; obtain ⟨i, b⟩ := p
            have hi := hv i hp
            cases b
            · simp only [endv, Bool.false_eq_true, if_false]
              rw [Equiv.symm_apply_eq]; exact hi.symm
            · simp [endv, hi]
          rw [this]
          have : lev σ {v} k v = 0 := (lev_eq_zero_iff).2 (mem_singleton_self v)
          simp [hf, psi, this]
        · have := hfa u p
          rw [← hj, h0] at this
          simpa [psi, hk] using this
      rw [sum_ends] at hA
      have e : ∑ i : Fin d, ((if ((i, true) : Fin d × Bool).1.val < m then (1 : ℝ) else β) +
          (if ((i, false) : Fin d × Bool).1.val < m then (1 : ℝ) else β)) =
          2 * (m * 1 + ((d - m : ℕ) : ℝ) * β) := by
        rw [← sum_fin_ite d m hmd, mul_sum]
        refine sum_congr rfl (fun i _ => ?_)
        simp only; ring
      rw [e] at hA
      rw [hfu, if_neg (by omega)]
      have hdm : ((d - m : ℕ) : ℝ) = d - m := by rw [Nat.cast_sub hmd]
      rw [hdm] at hA
      -- ρ = 2m + 2(d-m)β
      have hρ' : ρ = 2 * (m * 1 + ((d : ℝ) - m) * β) := by
        have : 1 / β = 2 * (m : ℝ) - 1 := by
          field_simp; linarith
        rw [hρ, this, hq]
        linear_combination hβm
      rw [hρ']
      linarith
    · -- an interior level
      obtain ⟨p0, hp0⟩ := exists_down (σ := σ) (S := {v}) (K := k) (w := u) (by omega) hjk
      obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hfu : f u = β ^ (i + 1) := by simp only [hf, psi, ← hj]; rw [if_pos hjk, hi]
      have hfp0 : f (endv σ u p0) = β ^ i := by
        simp only [hf, psi]; rw [if_pos (by omega), show lev σ {v} k (endv σ u p0) = i by omega]
      have hA : β ^ i + q * psi β k (i + 2) ≤ ∑ p, f (endv σ u p) := by
        rw [← add_sum_erase _ _ (mem_univ p0), hfp0]
        have : ∑ p ∈ univ.erase p0, psi β k (i + 2) ≤ ∑ p ∈ univ.erase p0, f (endv σ u p) :=
          sum_le_sum (fun p _ => by have := hfa u p; rw [← hj, hi] at this; exact this)
        rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, card_ends, nsmul_eq_mul,
          hcast] at this
        linarith
      have hfu0 : 0 ≤ f u := by rw [hfu]; positivity
      have hmul := mul_le_mul_of_nonneg_left hA hfu0
      refine le_trans ?_ hmul
      rw [hfu]
      rcases Nat.lt_or_ge (i + 1) k with hik | hik
      · rw [if_neg (by omega), psi, if_pos (by omega)]
        have : ρ * (β ^ (i + 1)) ^ 2 = β ^ (i + 1) * β ^ i * (ρ * β) := by ring
        rw [this, hρβ]
        apply le_of_eq; ring
      · have hik' : i + 1 = k := by omega
        rw [if_pos (by omega), psi, if_neg (by omega), mul_zero, add_zero]
        have : ρ * (β ^ (i + 1)) ^ 2 = β ^ (i + 1) * β ^ i * (ρ * β) := by ring
        rw [this, hρβ, ← hik']
        apply le_of_eq; ring
  -- sum up
  rw [quad_eq_sum_ends σ f]
  have hsum := sum_le_sum (fun u (_ : u ∈ (univ : Finset (Fin N))) => hpt u)
  rw [sum_sub_distrib, ← mul_sum, sum_ite, sum_const_zero, add_zero, sum_const,
    nsmul_eq_mul] at hsum
  have hl : (level σ {v} k k) = univ.filter (fun x => lev σ {v} k x = k) := rfl
  rw [hl]
  exact hsum

lemma card_level_le {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (v : Fin N) (k : ℕ) :
    ∀ i, i + 1 ≤ k → (level σ {v} k (i + 1)).card ≤ 2 * d * (2 * d - 1) ^ i := by
  intro i
  induction i with
  | zero =>
    intro hk
    have h1 := card_level_succ_le_mul (σ := σ) (S := {v}) (K := k) (j := 0) (c := 2 * d) hk
      (fun u _ => card_up_le_two_d u)
    have h0 : (level σ {v} k 0).card ≤ 1 := by
      have : level σ {v} k 0 ⊆ {v} := by
        intro u hu
        simp only [level, mem_filter, mem_univ, true_and] at hu
        exact (lev_eq_zero_iff (σ := σ) (K := k)).1 hu
      simpa using card_le_card this
    simp only [pow_zero, mul_one]
    nlinarith
  | succ i ih =>
    intro hk
    have h1 := card_level_succ_le_mul (σ := σ) (S := {v}) (K := k) (j := i + 1) (c := 2 * d - 1)
      hk (fun u hu => by
        simp only [level, mem_filter, mem_univ, true_and] at hu
        exact card_up_le (by omega) (by omega))
    calc (level σ {v} k (i + 1 + 1)).card ≤ (2 * d - 1) * (level σ {v} k (i + 1)).card := h1
      _ ≤ (2 * d - 1) * (2 * d * (2 * d - 1) ^ i) := Nat.mul_le_mul_left _ (ih (by omega))
      _ = 2 * d * (2 * d - 1) ^ (i + 1) := by ring

lemma center {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (f₀ : Fin N → ℝ) (c : ℝ) :
    ∑ i, ∑ v, 2 * (f₀ v - c) * (f₀ (σ i v) - c) =
      ∑ i, ∑ v, 2 * f₀ v * f₀ (σ i v) - 4 * d * c * ∑ v, f₀ v + 2 * d * N * c ^ 2 := by
  have h : ∀ i, ∑ v, 2 * (f₀ v - c) * (f₀ (σ i v) - c) =
      ∑ v, 2 * f₀ v * f₀ (σ i v) - 4 * c * ∑ v, f₀ v + 2 * N * c ^ 2 := by
    intro i
    have e1 : ∑ v, f₀ (σ i v) = ∑ v, f₀ v := Equiv.sum_comp (σ i) f₀
    have e : ∀ v, 2 * (f₀ v - c) * (f₀ (σ i v) - c) =
        2 * f₀ v * f₀ (σ i v) - 2 * c * f₀ v - 2 * c * f₀ (σ i v) + 2 * c ^ 2 := by
      intro v; ring
    simp_rw [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, e1, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  simp_rw [h, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem tangle_test_vector (d m : ℕ) (hmd : m ≤ d) (hm : mStar d < m) (α' : ℝ)
    (hα' : α' < rhoStair d m) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ σ : Fin d → Equiv.Perm (Fin N),
      (∃ v, ∀ i : Fin d, (i : ℕ) < m → σ i v = v) →
      ∃ f : Fin N → ℝ, ∑ v, f v = 0 ∧ 0 < ∑ v, f v ^ 2 ∧
        α' * ∑ v, f v ^ 2 ≤ ∑ i, ∑ v, 2 * f v * f (σ i v) := by
  have hm1 : 1 ≤ m := by omega
  have hd : 1 ≤ d := le_trans hm1 hmd
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  set q : ℝ := 2 * d - 1 with hq
  set t : ℝ := 2 * m - 1 with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  have hsqrt : Real.sqrt q < t := by
    have h := hm
    unfold mStar at h
    rw [Nat.floor_lt (by positivity)] at h
    rw [ht]; linarith
  have hqt : q < t ^ 2 := by
    have h1 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
    rw [← h1]
    exact pow_lt_pow_left₀ hsqrt (Real.sqrt_nonneg _) (by norm_num)
  have hρ : rhoStair d m = t + q / t := by
    unfold rhoStair
    rw [if_neg (not_le.2 hsqrt)]
  set β : ℝ := 1 / t with hβ
  have hβ0 : 0 < β := by positivity
  have hβ1 : β ≤ 1 := by rw [hβ, div_le_one (by linarith)]; exact ht1
  have htβ : t * β = 1 := by rw [hβ]; field_simp
  have hρ' : rhoStair d m = 1 / β + q * β := by
    rw [hρ, hβ]; field_simp
  set ε := rhoStair d m - α' with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set r := q * β ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr, hβ, div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]; exact hqt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (4 * d) by positivity) hr1
  set k := n + 1 with hk
  set Bk : ℕ := (2 * d + 1) ^ k with hBk
  set C : ℝ := 2 * d + |α'| with hC
  have hC0 : 0 < C := by rw [hC]; positivity
  refine ⟨⌈2 * C * Bk / ε⌉₊ + Bk + 1, ?_⟩
  intro N hN σ ⟨v, hv⟩
  have hNB : (Bk : ℝ) + 1 ≤ N := by
    have : Bk + 1 ≤ N := by omega
    exact_mod_cast this
  have hNC : 2 * C * Bk / ε ≤ N := by
    have h1 := Nat.le_ceil (2 * C * Bk / ε)
    have h2 : (⌈2 * C * Bk / ε⌉₊ : ℝ) ≤ N := by
      have : ⌈2 * C * Bk / ε⌉₊ ≤ N := by omega
      exact_mod_cast this
    linarith
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℝ) ≤ Bk := by positivity
    linarith
  set f₀ : Fin N → ℝ := fun u => psi β k (lev σ {v} k u) with hf₀
  set A := ∑ u, f₀ u ^ 2 with hA
  set s₀ := ∑ u, f₀ u with hs₀
  set Q₀ := ∑ i, ∑ u, 2 * f₀ u * f₀ (σ i u) with hQ₀
  have hf₀v : f₀ v = 1 := by
    simp only [hf₀, psi]
    rw [(lev_eq_zero_iff (σ := σ) (K := k)).2 (mem_singleton_self v)]; simp
  have hA1 : 1 ≤ A := by
    have := single_le_sum (f := fun u => f₀ u ^ 2) (fun u _ => sq_nonneg _) (mem_univ v)
    simp only [hf₀v] at this; rw [hA]; linarith
  -- the deficit
  have hlow := tangle_lower (k := k) σ v hv hm1 hmd (by omega) β hβ0 hβ1 (by rw [← ht]; exact htβ)
  have hdef : ((level σ {v} k k).card : ℝ) * ((2 * d - 1) * β ^ (2 * k + 1)) ≤ ε / 2 := by
    have hc := card_level_le σ v k n (by omega)
    have hc' : ((level σ {v} k k).card : ℝ) ≤ 2 * d * q ^ n := by
      have hcast : ((2 * d - 1 : ℕ) : ℝ) = q := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [← hcast]; exact_mod_cast hc
    have e : 2 * d * q ^ n * (q * β ^ (2 * k + 1)) = 2 * d * β * r ^ (n + 1) := by
      rw [hr, hk]; ring_nf
    have hrn : r ^ (n + 1) ≤ r ^ n := pow_le_pow_of_le_one hr0 hr1.le (by omega)
    calc ((level σ {v} k k).card : ℝ) * ((2 * d - 1) * β ^ (2 * k + 1))
        ≤ 2 * d * q ^ n * (q * β ^ (2 * k + 1)) := by
          rw [← hq]; gcongr
      _ = 2 * d * β * r ^ (n + 1) := e
      _ ≤ 2 * d * 1 * r ^ n := by gcongr
      _ ≤ 2 * d * (ε / (4 * d)) := by rw [mul_one]; gcongr
      _ = ε / 2 := by field_simp; ring
  rw [← hq, ← hρ'] at hlow
  have hQlow : rhoStair d m * A - ε / 2 * A ≤ Q₀ := by
    have : ε / 2 ≤ ε / 2 * A := by nlinarith
    rw [hA, hQ₀]; linarith
  -- Cauchy–Schwarz on the support
  have hs₀sq : s₀ ^ 2 ≤ Bk * A := by
    have hsub : ∑ u ∈ ball σ {v} k, f₀ u = s₀ := by
      rw [hs₀]
      apply sum_subset (subset_univ _)
      intro u _ hu
      simp only [hf₀, psi]
      rw [if_neg]
      intro h
      exact hu ((lev_le_iff le_rfl).1 h)
    have hcs := sq_sum_le_card_mul_sum_sq (s := ball σ {v} k) (f := f₀)
    have hcard : ((ball σ {v} k).card : ℝ) ≤ Bk := by
      have := card_ball (σ := σ) {v} k
      rw [card_singleton, one_mul] at this
      exact_mod_cast this
    have hsub2 : ∑ u ∈ ball σ {v} k, f₀ u ^ 2 ≤ A :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun u _ _ => sq_nonneg _)
    rw [hsub] at hcs
    calc s₀ ^ 2 ≤ ((ball σ {v} k).card : ℝ) * ∑ u ∈ ball σ {v} k, f₀ u ^ 2 := hcs
      _ ≤ Bk * A := by gcongr
  set c := s₀ / N with hc
  set y := s₀ ^ 2 / N with hy
  have hy0 : 0 ≤ y := by positivity
  have hyB : y ≤ Bk * A / N := by rw [hy]; gcongr
  have hCy : C * y ≤ ε / 2 * A := by
    have h1 : C * (Bk * A / N) ≤ ε / 2 * A := by
      rw [div_le_iff₀ hε0] at hNC
      have hA0 : 0 ≤ A := by linarith
      rw [mul_div_assoc', div_le_iff₀ hNpos]
      have := mul_le_mul_of_nonneg_right hNC hA0
      linarith
    calc C * y ≤ C * (Bk * A / N) := by gcongr
      _ ≤ _ := h1
  refine ⟨fun u => f₀ u - c, ?_, ?_, ?_⟩
  · rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hc]
    field_simp; rw [hs₀]; ring
  · have e : ∑ u, (f₀ u - c) ^ 2 = A - y := by
      have : ∀ u, (f₀ u - c) ^ 2 = f₀ u ^ 2 - 2 * c * f₀ u + c ^ 2 := fun u => by ring
      simp_rw [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [← hA, ← hs₀, hy, hc]; field_simp; ring
    rw [e]
    have : y < A := by
      have h1 : Bk * A / N < A := by
        rw [div_lt_iff₀ hNpos]
        have hA0 : 0 ≤ A := by linarith
        have := mul_le_mul_of_nonneg_left hNB hA0
        linarith
      linarith
    linarith
  · have e : ∑ u, (f₀ u - c) ^ 2 = A - y := by
      have : ∀ u, (f₀ u - c) ^ 2 = f₀ u ^ 2 - 2 * c * f₀ u + c ^ 2 := fun u => by ring
      simp_rw [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [← hA, ← hs₀, hy, hc]; field_simp; ring
    rw [e, center σ f₀ c, ← hQ₀, ← hs₀]
    have eq : 4 * d * c * s₀ - 2 * d * N * c ^ 2 = 2 * d * y := by
      rw [hc, hy]; field_simp; ring
    have hab : -(α' * y) ≤ |α'| * y := by
      have := mul_le_mul_of_nonneg_right (neg_abs_le α') hy0
      linarith
    have hε' : rhoStair d m = α' + ε := by rw [hε]; ring
    rw [hC] at hCy
    have key : Q₀ - 4 * d * c * s₀ + 2 * d * N * c ^ 2 = Q₀ - 2 * d * y := by linarith [eq]
    rw [key]
    have hA0 : 0 ≤ A := by linarith
    have h3 : rhoStair d m * A = α' * A + ε * A := by rw [hε']; ring
    linarith

end StrongConv.CitedGraphs.PartT
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs
open Filter
/-! ## Friedman's tangle -/
alias tangle_test_vector := StrongConv.CitedGraphs.PartT.tangle_test_vector

theorem prob_norm_adjPerp_ge_of_lt_rhoStair_dev (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (hm : mStar d < m)
    (hmd : m ≤ d) (α' : ℝ) (hα' : α' < rhoStair d m) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (1 - η) / (N : ℝ) ^ (m - 1) ≤
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => α' ≤ ‖adjPerp σ‖) := by
  obtain ⟨N₀, hN₀⟩ := tangle_test_vector d m hmd hm α' hα'
  have hm2 : 2 ≤ m := by have := one_le_mStar d (by omega); omega
  filter_upwards [eventually_ge_atTop (max N₀ (max 2 (⌈1 / (2 * η)⌉₊ + 1)))] with N hN
  have hN0 : N₀ ≤ N := le_of_max_le_left hN
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) (le_of_max_le_right hN)
  have hNη : ⌈1 / (2 * η)⌉₊ + 1 ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hN)
  have hP := prob_common_fixed_point_ge d m N (by omega) hmd hN2
  have hmono : uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ∃ v, ∀ i : Fin d, (i : ℕ) < m → σ i v = v) ≤
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => α' ≤ ‖adjPerp σ‖) := by
    apply uniformProb_mono
    intro σ hσ
    obtain ⟨f, hf, hf0, hq⟩ := hN₀ N hN0 σ hσ
    have hR := rayleigh_le_norm_adjPerp σ f hf hf0
    rw [div_le_iff₀ hf0] at hR
    have : α' * ∑ v, f v ^ 2 ≤ ‖adjPerp σ‖ * ∑ v, f v ^ 2 := le_trans hq hR
    exact le_of_mul_le_mul_right this hf0
  refine le_trans ?_ (le_trans hP hmono)
  -- arithmetic
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have hceil : 1 / (2 * η) ≤ (N : ℝ) - 1 := by
    have h1 : (⌈1 / (2 * η)⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hNη
    have h2 := Nat.le_ceil (1 / (2 * η))
    linarith
  set k := m - 1 with hk
  have hk1 : 1 ≤ k := by omega
  have hNk : (N : ℝ) - 1 ≤ ((N : ℝ) - 1) ^ k := by
    calc (N : ℝ) - 1 = ((N : ℝ) - 1) ^ 1 := (pow_one _).symm
      _ ≤ ((N : ℝ) - 1) ^ k := pow_le_pow_right₀ hN1 hk1
  have hpos : 0 < (N : ℝ) ^ k := by positivity
  have hpos1 : 0 < ((N : ℝ) - 1) ^ k := by positivity
  rw [mul_pow]
  have key : 1 / (2 * ((N : ℝ) ^ k * ((N : ℝ) - 1) ^ k)) ≤ η / (N : ℝ) ^ k := by
    rw [div_le_div_iff₀ (by positivity) hpos]
    have : 1 ≤ η * (2 * ((N : ℝ) - 1) ^ k) := by
      have h3 : 1 / (2 * η) ≤ ((N : ℝ) - 1) ^ k := le_trans hceil hNk
      rw [div_le_iff₀ (by positivity)] at h3
      linarith
    nlinarith
  have : (1 - η) / (N : ℝ) ^ k = 1 / (N : ℝ) ^ k - η / (N : ℝ) ^ k := by ring
  rw [this]
  linarith

end StrongConv.CitedGraphs
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs
open Finset
variable {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N))
variable {σ}
variable {S : Finset (Fin N)} {K : ℕ}

end StrongConv.CitedGraphs
end
end
open StrongConv Filter in
theorem solution (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (hm : mStar d < m)
    (hmd : m ≤ d) (α' : ℝ) (hα' : α' < rhoStair d m) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (1 - η) / (N : ℝ) ^ (m - 1) ≤
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => α' ≤ ‖adjPerp σ‖) :=
  StrongConv.CitedGraphs.prob_norm_adjPerp_ge_of_lt_rhoStair_dev d hd m hm hmd α' hα' η hη

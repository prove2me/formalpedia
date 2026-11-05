-- Prove2me | solution 1 for StrongConv.norm_adjPerp_ge_alonBoppana
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:18:36.838719+00:00
-- url     : https://prove2.me/submissions/a87d6043-a73f-4e73-b851-eeb5054d2e50

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

end StrongConv.CitedGraphs
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs.PartN
open Finset
/-!
# Part N: Nilli's two-edge test vector
-/
/-- The radial profile `j ↦ (2d-1)^{-j/2}` for `j ≤ k`, `0` beyond. -/
def phi (d k j : ℕ) : ℝ := if j ≤ k then (1 / Real.sqrt (2 * d - 1)) ^ j else 0

end StrongConv.CitedGraphs.PartN
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs
open Filter
/-! ## Friedman's tangle -/

/-! ## The three published statements -/

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

lemma nbhd_mono {T T' : Finset (Fin N)} (h : T ⊆ T') : nbhd σ T ⊆ nbhd σ T' := by
  unfold nbhd
  exact union_subset_union h (biUnion_subset_biUnion_of_subset_left _ h)

lemma ball_subset_ball {S T : Finset (Fin N)} (h : S ⊆ T) (r : ℕ) : ball σ S r ⊆ ball σ T r := by
  induction r with
  | zero => exact h
  | succ r ih => exact nbhd_mono ih

lemma ball_ball (S : Finset (Fin N)) (a b : ℕ) : ball σ (ball σ S a) b = ball σ S (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih => rw [ball_succ, ih]; rfl

lemma mem_ball_trans {S : Finset (Fin N)} {a b : ℕ} {x y : Fin N} (hx : x ∈ ball σ S a)
    (hy : y ∈ ball σ {x} b) : y ∈ ball σ S (a + b) := by
  rw [← ball_ball]
  exact ball_subset_ball (singleton_subset_iff.2 hx) b hy

lemma mem_ball_symm {x y : Fin N} {r : ℕ} (h : y ∈ ball σ {x} r) : x ∈ ball σ {y} r := by
  induction r generalizing y with
  | zero => simp [ball_zero] at h ⊢; exact h.symm
  | succ r ih =>
    rcases mem_ball_succ.1 h with h | ⟨p, hp⟩
    · exact ball_subset_succ _ r (ih h)
    · have h1 := ih hp
      -- `endv y p ∈ ball {y} 1`
      have h2 : endv σ y p ∈ ball σ {y} 1 := endv_mem_ball (by simp [ball_zero]) p
      have := mem_ball_trans h2 h1
      rwa [add_comm] at this

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
namespace StrongConv.CitedGraphs.PartN
open Finset
/-- The test function around `S`. -/
def gfun {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (S : Finset (Fin N)) (k : ℕ) (v : Fin N) :
    ℝ := phi d k (lev σ S k v)

lemma real_ineq (s : ℝ) (hs : 1 ≤ s) (k : ℕ) (x : ℕ → ℝ) (hx0 : ∀ j, 0 ≤ x j)
    (hmono : ∀ j ≤ k, x k ≤ x j) :
    2 * s * (1 - 1 / ((k : ℝ) + 1)) * (∑ j ∈ range k, x j + x k) ≤
      (s ^ 2 + 1) * (∑ j ∈ range k, x j + x k) -
        ((s - 1) ^ 2 * ∑ j ∈ range k, x j + s ^ 2 * x k) := by
  set X := ∑ j ∈ range k, x j
  have hX : (k : ℝ) * x k ≤ X := by
    have : ∑ j ∈ range k, x k ≤ X := sum_le_sum (fun j hj => hmono j (by
      rw [mem_range] at hj; omega))
    simpa using this
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hxk := hx0 k
  have e : 2 * s * (1 - 1 / ((k : ℝ) + 1)) * (X + x k) =
      2 * s * (X + x k) - 2 * s * (X + x k) / ((k : ℝ) + 1) := by
    field_simp
  rw [e]
  have h2 : (2 * s - 1) * x k ≤ 2 * s * (X + x k) / ((k : ℝ) + 1) := by
    rw [le_div_iff₀ hk]
    nlinarith
  nlinarith

end StrongConv.CitedGraphs.PartN
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

lemma card_up_le_of_mem {u : Fin N} (hu : u ∈ S) (p0 : Fin d × Bool) (hp0 : endv σ u p0 ∈ S) :
    (up σ S K u).card ≤ 2 * d - 1 := by
  refine card_up_le_of_not_mem p0 ?_
  simp only [up, mem_filter, mem_univ, true_and]
  rw [lev_eq_zero_iff.2 hu, lev_eq_zero_iff.2 hp0]
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

lemma sum_lev (F : ℕ → ℝ) :
    ∑ u, F (lev σ S K u) = ∑ j ∈ range (K + 2), ((level σ S K j).card : ℝ) * F j := by
  rw [← sum_fiberwise_of_maps_to' (s := univ) (t := range (K + 2)) (g := lev σ S K)
    (fun u _ => by rw [mem_range]; have := lev_le_cap (σ := σ) (S := S) (K := K) u; omega) F]
  refine sum_congr rfl (fun j _ => ?_)
  rw [sum_const, nsmul_eq_mul]
  rfl

/-! ## The quadratic form -/
lemma sum_ends (F : Fin d × Bool → ℝ) :
    ∑ p, F p = ∑ i, (F (i, true) + F (i, false)) := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]

variable (σ) in
lemma diff_sq_sum (f : Fin N → ℝ) :
    ∑ i, ∑ v, (f v - f (σ i v)) ^ 2 =
      2 * d * ∑ v, f v ^ 2 - ∑ i, ∑ v, 2 * f v * f (σ i v) := by
  have h1 : ∀ i, ∑ v, (f v - f (σ i v)) ^ 2 =
      2 * ∑ v, f v ^ 2 - ∑ v, 2 * f v * f (σ i v) := by
    intro i
    have : ∑ v, f (σ i v) ^ 2 = ∑ v, f v ^ 2 := Equiv.sum_comp (σ i) (fun v => f v ^ 2)
    have e : ∀ v, (f v - f (σ i v)) ^ 2 = f v ^ 2 + f (σ i v) ^ 2 - 2 * f v * f (σ i v) := by
      intro v; ring
    simp_rw [e, sum_sub_distrib, sum_add_distrib, this]
    ring
  simp_rw [h1, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Charging each level-changing term to its lower endpoint. -/
lemma diff_sq_lev (φ : ℕ → ℝ) :
    ∑ i, ∑ v, (φ (lev σ S K v) - φ (lev σ S K (σ i v))) ^ 2 =
      ∑ u, ((up σ S K u).card : ℝ) * (φ (lev σ S K u) - φ (lev σ S K u + 1)) ^ 2 := by
  set w : ℕ → ℝ := fun j => (φ j - φ (j + 1)) ^ 2
  have hpt : ∀ i v, (φ (lev σ S K v) - φ (lev σ S K (σ i v))) ^ 2 =
      (if lev σ S K (σ i v) = lev σ S K v + 1 then w (lev σ S K v) else 0) +
      (if lev σ S K v = lev σ S K (σ i v) + 1 then w (lev σ S K (σ i v)) else 0) := by
    intro i v
    have h1 := lev_endv_le (σ := σ) (S := S) (K := K) v (i, true)
    have h2 := lev_le_lev_endv (σ := σ) (S := S) (K := K) v (i, true)
    simp only [endv, if_true] at h1 h2
    rcases Nat.lt_trichotomy (lev σ S K (σ i v)) (lev σ S K v) with h | h | h
    · have e : lev σ S K v = lev σ S K (σ i v) + 1 := by omega
      rw [if_neg (by omega), if_pos e, e]; simp only [w]; ring
    · rw [if_neg (by omega), if_neg (by omega), h]; simp
    · have e : lev σ S K (σ i v) = lev σ S K v + 1 := by omega
      rw [if_pos e, if_neg (by omega), e]; simp [w]
  simp_rw [hpt, sum_add_distrib]
  have h2 : ∀ i, ∑ v, (if lev σ S K v = lev σ S K (σ i v) + 1 then w (lev σ S K (σ i v)) else 0)
      = ∑ u, (if lev σ S K ((σ i).symm u) = lev σ S K u + 1 then w (lev σ S K u) else 0) := by
    intro i
    conv_rhs => rw [← Equiv.sum_comp (σ i)]
    simp
  simp_rw [h2]
  rw [← sum_add_distrib, sum_congr rfl (fun i _ => (sum_add_distrib).symm), sum_comm]
  refine sum_congr rfl (fun u _ => ?_)
  have : ((up σ S K u).card : ℝ) = ∑ p, (if lev σ S K (endv σ u p) = lev σ S K u + 1
      then (1 : ℝ) else 0) := by
    rw [sum_boole]; rfl
  rw [this, sum_mul, sum_ends]
  refine sum_congr rfl (fun i _ => ?_)
  simp only [endv, if_true, Bool.false_eq_true, if_false]
  split_ifs <;> simp [w]

end StrongConv.CitedGraphs
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs.PartN
open Finset
theorem nilli_one {d N : ℕ} (hd : 1 ≤ d) (σ : Fin d → Equiv.Perm (Fin N)) (k : ℕ)
    (S : Finset (Fin N)) (hS : ∀ x ∈ S, ∃ p, endv σ x p ∈ S) :
    2 * Real.sqrt (2 * d - 1) * (1 - 1 / ((k : ℝ) + 1)) * ∑ v, gfun σ S k v ^ 2 ≤
      ∑ i, ∑ v, 2 * gfun σ S k v * gfun σ S k (σ i v) := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set s := Real.sqrt (2 * d - 1) with hs_def
  have hq0 : (0 : ℝ) ≤ 2 * d - 1 := by linarith
  have hss : s ^ 2 = 2 * d - 1 := Real.sq_sqrt hq0
  have hs1 : 1 ≤ s := by
    rw [hs_def, Real.one_le_sqrt]; linarith
  have hs0 : 0 < s := by linarith
  set β := 1 / s with hβ
  have hβ0 : 0 ≤ β := by positivity
  set φ : ℕ → ℝ := phi d k with hφ
  have hφle : ∀ j, j ≤ k → φ j = β ^ j := fun j hj => by simp [hφ, phi, hj, hβ, hs_def]
  have hφgt : ∀ j, k < j → φ j = 0 := fun j hj => by simp [hφ, phi, show ¬ j ≤ k by omega]
  have hg : ∀ v, gfun σ S k v = φ (lev σ S k v) := fun v => rfl
  have hcast : ((2 * d - 1 : ℕ) : ℝ) = 2 * d - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  -- the quadratic form
  rw [← sub_nonneg]
  have hQ := diff_sq_sum σ (gfun σ S k)
  have hD := diff_sq_lev (σ := σ) (S := S) (K := k) φ
  simp only [hg] at hQ ⊢
  set Q := ∑ i, ∑ v, 2 * φ (lev σ S k v) * φ (lev σ S k (σ i v))
  -- upper bound for the difference sum
  have hDle : ∑ i, ∑ v, (φ (lev σ S k v) - φ (lev σ S k (σ i v))) ^ 2 ≤
      ∑ u, (2 * (d : ℝ) - 1) * (φ (lev σ S k u) - φ (lev σ S k u + 1)) ^ 2 := by
    rw [hD]
    refine sum_le_sum (fun u _ => ?_)
    rcases Nat.lt_or_ge k (lev σ S k u) with h | h
    · rw [hφgt _ h, hφgt _ (by omega)]; simp
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [← hcast]
      apply Nat.cast_le.2
      rcases Nat.eq_zero_or_pos (lev σ S k u) with h0 | h0
      · have hu : u ∈ S := lev_eq_zero_iff.1 h0
        obtain ⟨p, hp⟩ := hS u hu
        exact card_up_le_of_mem hu p hp
      · exact card_up_le h0 h
  -- levels
  set n : ℕ → ℝ := fun j => ((level σ S k j).card : ℝ) with hn
  have hsum1 := sum_lev (σ := σ) (S := S) (K := k) (fun j => φ j ^ 2)
  have hsum2 := sum_lev (σ := σ) (S := S) (K := k)
    (fun j => (2 * (d : ℝ) - 1) * (φ j - φ (j + 1)) ^ 2)
  -- monotonicity
  set x : ℕ → ℝ := fun j => n j * (β ^ j) ^ 2 with hx
  have hx0 : ∀ j, 0 ≤ x j := fun j => by simp only [hx, hn]; positivity
  have hstep : ∀ j, j + 1 ≤ k → x (j + 1) ≤ x j := by
    intro j hj
    have hc : (level σ S k (j + 1)).card ≤ (2 * d - 1) * (level σ S k j).card := by
      apply card_level_succ_le_mul hj
      intro u hu
      simp only [level, mem_filter, mem_univ, true_and] at hu
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · have hu' : u ∈ S := (lev_eq_zero_iff (σ := σ) (K := k)).1 (by omega)
        obtain ⟨p, hp⟩ := hS u hu'
        exact card_up_le_of_mem hu' p hp
      · exact card_up_le (σ := σ) (S := S) (K := k) (u := u) (by omega) (by omega)
    have hc' : n (j + 1) ≤ (2 * d - 1) * n j := by
      simp only [hn]; rw [← hcast]; exact_mod_cast hc
    simp only [hx]
    have hβ2 : (2 * (d : ℝ) - 1) * β ^ 2 = 1 := by
      rw [← hss, hβ]; field_simp
    have hnj : 0 ≤ n j := by simp only [hn]; positivity
    calc n (j + 1) * (β ^ (j + 1)) ^ 2 = n (j + 1) * (β ^ j) ^ 2 * β ^ 2 := by ring
      _ ≤ (2 * d - 1) * n j * (β ^ j) ^ 2 * β ^ 2 := by gcongr
      _ = n j * (β ^ j) ^ 2 * ((2 * d - 1) * β ^ 2) := by ring
      _ = n j * (β ^ j) ^ 2 := by rw [hβ2, mul_one]
  have hmono : ∀ j ≤ k, x k ≤ x j := by
    have : ∀ t, t ≤ k → x k ≤ x (k - t) := by
      intro t
      induction t with
      | zero => intro _; simp
      | succ t ih =>
        intro ht
        have := hstep (k - (t + 1)) (by omega)
        rw [show k - (t + 1) + 1 = k - t by omega] at this
        exact le_trans (ih (by omega)) this
    intro j hj
    have := this (k - j) (by omega)
    rwa [show k - (k - j) = j by omega] at this
  have hR := real_ineq s hs1 k x hx0 hmono
  -- rewrite the sums
  have e1 : ∑ v, φ (lev σ S k v) ^ 2 = ∑ j ∈ range k, x j + x k := by
    rw [hsum1, sum_range_succ, sum_range_succ, hφgt (k + 1) (by omega)]
    simp only [hx, hφle k le_rfl]
    rw [sum_congr rfl (fun j hj => by rw [hφle j (by rw [mem_range] at hj; omega)])]
    ring
  have e2 : ∑ u, (2 * (d : ℝ) - 1) * (φ (lev σ S k u) - φ (lev σ S k u + 1)) ^ 2 =
      (s - 1) ^ 2 * ∑ j ∈ range k, x j + s ^ 2 * x k := by
    rw [hsum2, sum_range_succ, sum_range_succ, hφgt (k + 1) (by omega), hφgt (k + 1 + 1) (by omega),
      hφle k le_rfl, mul_sum]
    have hsβ : s * β = 1 := by rw [hβ]; field_simp
    rw [sum_congr rfl (fun j hj => by
      rw [hφle j (by rw [mem_range] at hj; omega), hφle (j + 1) (by rw [mem_range] at hj; omega)])]
    simp only [hx]
    rw [← hss]
    have : ∀ j, n j * (s ^ 2 * (β ^ j - β ^ (j + 1)) ^ 2) = (s - 1) ^ 2 * (n j * (β ^ j) ^ 2) := by
      intro j
      have : s ^ 2 * (β ^ j - β ^ (j + 1)) ^ 2 = (β ^ j) ^ 2 * (s - s * β) ^ 2 := by ring
      rw [this, hsβ]; ring
    rw [sum_congr rfl (fun j _ => this j)]
    ring
  rw [e1] at hQ ⊢
  rw [e2] at hDle
  rw [hss] at hR hDle
  linarith

lemma gfun_nonneg {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (S : Finset (Fin N)) (k : ℕ)
    (v : Fin N) : 0 ≤ gfun σ S k v := by
  unfold gfun phi; split_ifs <;> positivity

lemma gfun_of_mem {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) {S : Finset (Fin N)} (k : ℕ)
    {v : Fin N} (hv : v ∈ S) : gfun σ S k v = 1 := by
  unfold gfun phi; rw [(lev_eq_zero_iff (σ := σ) (K := k)).2 hv]; simp

lemma mem_ball_of_gfun_ne {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (S : Finset (Fin N))
    (k : ℕ) {v : Fin N} (hv : gfun σ S k v ≠ 0) : v ∈ ball σ S k := by
  unfold gfun phi at hv
  split_ifs at hv with h
  · exact (lev_le_iff le_rfl).1 h
  · exact absurd rfl hv

lemma pair_subset_ball {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (i0 : Fin d) (u : Fin N) :
    ({u, σ i0 u} : Finset (Fin N)) ⊆ ball σ {u} 1 := by
  intro x hx
  rw [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ball_subset_succ _ 0 (by simp [ball_zero])
  · exact endv_mem_ball (p := (i0, true)) (by simp [ball_zero])

lemma pair_closed {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (i0 : Fin d) (u : Fin N) :
    ∀ x ∈ ({u, σ i0 u} : Finset (Fin N)), ∃ p, endv σ x p ∈ ({u, σ i0 u} : Finset (Fin N)) := by
  intro x hx
  rw [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨(i0, true), by simp [endv]⟩
  · exact ⟨(i0, false), by simp [endv]⟩

theorem nilli_test_vector {d N : ℕ} (hd : 1 ≤ d) (σ : Fin d → Equiv.Perm (Fin N)) (k : ℕ)
    (hN : (2 * d + 1) ^ (2 * k + 4) ≤ N) :
    ∃ f : Fin N → ℝ, ∑ v, f v = 0 ∧ 0 < ∑ v, f v ^ 2 ∧
      2 * Real.sqrt (2 * d - 1) * (1 - 1 / ((k : ℝ) + 1)) * ∑ v, f v ^ 2 ≤
        ∑ i, ∑ v, 2 * f v * f (σ i v) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  set i0 : Fin d := ⟨0, by omega⟩
  set u : Fin N := ⟨0, hNpos⟩
  -- a far vertex
  obtain ⟨w, hw⟩ : ∃ w, w ∉ ball σ {u} (2 * k + 3) := by
    by_contra h
    push Not at h
    have h1 : (univ : Finset (Fin N)).card ≤ (ball σ {u} (2 * k + 3)).card :=
      card_le_card (fun x _ => h x)
    have h2 := card_ball (σ := σ) {u} (2 * k + 3)
    rw [card_singleton, one_mul, card_univ, Fintype.card_fin] at *
    have h3 : (2 * d + 1) ^ (2 * k + 3) < (2 * d + 1) ^ (2 * k + 4) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  set S₁ : Finset (Fin N) := {u, σ i0 u}
  set S₂ : Finset (Fin N) := {w, σ i0 w}
  set g₁ := gfun σ S₁ k
  set g₂ := gfun σ S₂ k
  have far : ∀ x y, g₁ x ≠ 0 → g₂ y ≠ 0 → y ∈ ball σ {x} 1 → False := by
    intro x y hx hy hxy
    have hx' : x ∈ ball σ {u} (1 + k) := by
      rw [← ball_ball]
      exact ball_subset_ball (pair_subset_ball σ i0 u) k (mem_ball_of_gfun_ne σ S₁ k hx)
    have hy' : y ∈ ball σ {w} (1 + k) := by
      rw [← ball_ball]
      exact ball_subset_ball (pair_subset_ball σ i0 w) k (mem_ball_of_gfun_ne σ S₂ k hy)
    have h1 := mem_ball_trans hx' hxy
    have h2 := mem_ball_trans h1 (mem_ball_symm hy')
    exact hw (ball_mono _ (by omega) h2)
  have hz1 : ∀ v, g₁ v * g₂ v = 0 := by
    intro v; by_contra h
    rcases mul_ne_zero_iff.1 h with ⟨h1, h2⟩
    exact far v v h1 h2 (ball_subset_succ _ 0 (by simp [ball_zero]))
  have hz2 : ∀ i v, g₁ v * g₂ (σ i v) = 0 := by
    intro i v; by_contra h
    rcases mul_ne_zero_iff.1 h with ⟨h1, h2⟩
    exact far v (σ i v) h1 h2 (endv_mem_ball (p := (i, true)) (by simp [ball_zero]))
  have hz3 : ∀ i v, g₂ v * g₁ (σ i v) = 0 := by
    intro i v; by_contra h
    rcases mul_ne_zero_iff.1 h with ⟨h1, h2⟩
    have : v ∈ ball σ {σ i v} 1 := by
      have := endv_mem_ball (σ := σ) (S := {σ i v}) (r := 0) (v := σ i v)
        (by simp [ball_zero]) (i, false)
      simpa [endv] using this
    exact far (σ i v) v h2 h1 this
  have hu1 : g₁ u = 1 := gfun_of_mem σ k (by simp [S₁])
  have hw1 : g₂ w = 1 := gfun_of_mem σ k (by simp [S₂])
  have hsum2 : 0 < ∑ v, g₂ v := by
    have := single_le_sum (f := g₂) (fun v _ => gfun_nonneg σ S₂ k v) (mem_univ w)
    rw [hw1] at this; linarith
  have hsq1 : 1 ≤ ∑ v, g₁ v ^ 2 := by
    have := single_le_sum (f := fun v => g₁ v ^ 2) (fun v _ => sq_nonneg _) (mem_univ u)
    simp only [hu1] at this; linarith
  have hsq2 : 0 ≤ ∑ v, g₂ v ^ 2 := sum_nonneg (fun v _ => sq_nonneg _)
  have hN1 := nilli_one hd σ k S₁ (pair_closed σ i0 u)
  have hN2 := nilli_one hd σ k S₂ (pair_closed σ i0 w)
  set c := (∑ v, g₁ v) / (∑ v, g₂ v)
  refine ⟨fun v => g₁ v - c * g₂ v, ?_, ?_, ?_⟩
  · rw [sum_sub_distrib, ← mul_sum]
    simp only [c]; field_simp; ring
  · have e : ∑ v, (g₁ v - c * g₂ v) ^ 2 = ∑ v, g₁ v ^ 2 + c ^ 2 * ∑ v, g₂ v ^ 2 := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl (fun v _ => ?_)
      have := hz1 v
      linear_combination (-2 * c) * this
    rw [e]; positivity
  · have e : ∑ v, (g₁ v - c * g₂ v) ^ 2 = ∑ v, g₁ v ^ 2 + c ^ 2 * ∑ v, g₂ v ^ 2 := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl (fun v _ => ?_)
      have := hz1 v
      linear_combination (-2 * c) * this
    have eQ : ∑ i, ∑ v, 2 * (g₁ v - c * g₂ v) * (g₁ (σ i v) - c * g₂ (σ i v)) =
        ∑ i, ∑ v, 2 * g₁ v * g₁ (σ i v) + c ^ 2 * ∑ i, ∑ v, 2 * g₂ v * g₂ (σ i v) := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl (fun i _ => ?_)
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl (fun v _ => ?_)
      linear_combination (-2 * c) * hz2 i v + (-2 * c) * hz3 i v
    rw [e, eQ]
    have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
    have := mul_le_mul_of_nonneg_left hN2 hc2
    nlinarith

end StrongConv.CitedGraphs.PartN
end
end

section
noncomputable section
namespace StrongConv.CitedGraphs
open Filter
/-! ## Alon–Boppana (Nilli's argument) -/
alias nilli_test_vector := StrongConv.CitedGraphs.PartN.nilli_test_vector

theorem norm_adjPerp_ge_alonBoppana_dev :
    ∃ C : ℝ, ∀ d N : ℕ, 1 ≤ d → 2 ≤ N → ∀ σ : Fin d → Equiv.Perm (Fin N),
      (1 - C * Real.log (2 * d) / Real.log N) * (2 * Real.sqrt (2 * d - 1)) ≤ ‖adjPerp σ‖ := by
  refine ⟨20, fun d N hd hN σ => ?_⟩
  set s := 2 * Real.sqrt (2 * d - 1) with hs
  have hs0 : 0 ≤ s := by positivity
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hl2 : 0 < Real.log (2 * d) := Real.log_pos (by linarith)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  set b := 2 * d + 1 with hb
  have hb1 : 1 < b := by omega
  set t := Nat.log b N with ht
  have hbt : b ^ t ≤ N := Nat.pow_log_le_self b (by omega)
  have hbt1 : N < b ^ (t + 1) := Nat.lt_pow_succ_log_self hb1 N
  -- log N < (t+1) log b ≤ 2 (t+1) log (2d)
  have hlogb : Real.log (b : ℝ) ≤ 2 * Real.log (2 * d) := by
    have hb' : ((b : ℕ) : ℝ) = 2 * d + 1 := by rw [hb]; push_cast; ring
    have : Real.log (b : ℝ) ≤ Real.log ((2 * (d : ℝ)) ^ 2) := by
      apply Real.log_le_log (by positivity)
      rw [hb']
      nlinarith
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hlogN : Real.log N < (t + 1) * (2 * Real.log (2 * d)) := by
    have h1 : Real.log N < Real.log ((b : ℝ) ^ (t + 1)) := by
      apply Real.log_lt_log (by linarith)
      exact_mod_cast hbt1
    rw [Real.log_pow] at h1
    push_cast at h1
    have : (0 : ℝ) ≤ t + 1 := by positivity
    nlinarith
  have hnorm0 : 0 ≤ ‖adjPerp σ‖ := norm_nonneg _
  by_cases ht4 : t < 4
  · have htr : (t : ℝ) + 1 ≤ 4 := by exact_mod_cast ht4
    have : 1 - 20 * Real.log (2 * d) / Real.log N ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hlN]
      nlinarith
    nlinarith
  · push_neg at ht4
    set k := (t - 4) / 2 with hk
    have hk2 : 2 * k + 4 ≤ t := by omega
    have hkt : t ≤ 2 * k + 5 := by omega
    have hNk : (2 * d + 1) ^ (2 * k + 4) ≤ N :=
      le_trans (Nat.pow_le_pow_right (by omega) hk2) hbt
    obtain ⟨f, hf, hf0, hq⟩ := nilli_test_vector hd σ k hNk
    have hR := rayleigh_le_norm_adjPerp σ f hf hf0
    rw [div_le_iff₀ hf0] at hR
    have h1 : s * (1 - 1 / ((k : ℝ) + 1)) ≤ ‖adjPerp σ‖ :=
      le_of_mul_le_mul_right (le_trans hq hR) hf0
    refine le_trans ?_ h1
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hs0
    have hktr : (t : ℝ) + 1 ≤ 10 * ((k : ℝ) + 1) := by
      have : (t : ℝ) ≤ 2 * k + 5 := by exact_mod_cast hkt
      linarith
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have : 1 / ((k : ℝ) + 1) ≤ 20 * Real.log (2 * d) / Real.log N := by
      rw [div_le_div_iff₀ hk1 hlN]
      nlinarith
    linarith

end StrongConv.CitedGraphs
end
end
open StrongConv in
theorem solution :
    ∃ C : ℝ, ∀ d N : ℕ, 1 ≤ d → 2 ≤ N → ∀ σ : Fin d → Equiv.Perm (Fin N),
      (1 - C * Real.log (2 * d) / Real.log N) * (2 * Real.sqrt (2 * d - 1)) ≤ ‖adjPerp σ‖ :=
  StrongConv.CitedGraphs.norm_adjPerp_ge_alonBoppana_dev

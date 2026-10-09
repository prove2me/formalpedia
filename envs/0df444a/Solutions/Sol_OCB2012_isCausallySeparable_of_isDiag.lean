-- Prove2me | solution 1 for OCB2012.isCausallySeparable_of_isDiag
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:22:51.325392+00:00
-- url     : https://prove2.me/submissions/f8ee3d9f-72ab-4250-bc76-8c069ea608a5

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012Sol
open OCB2012

/-- Changing a function at one point changes a sum `∑ i, F i (f i)` only in that term. -/
lemma sum_update_sub {α β M : Type*} [Fintype α] [DecidableEq α] [AddCommGroup M]
    (F : α → β → M) (f : α → β) (i : α) (a b : β) :
    ∑ i', F i' (Function.update f i a i') - ∑ i', F i' (Function.update f i b i') =
      F i a - F i b := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'; simp [Function.update_of_ne hi']
  · simp

/-- The CJ matrix of the deterministic classical channel `i ↦ f i` (diagonal in the pointer
basis). -/
def detCJ {x1 x2 : Type*} [DecidableEq x1] [DecidableEq x2] (f : x1 → x2) :
    Matrix (x1 × x2) (x1 × x2) ℂ :=
  diagonal fun p => if p.2 = f p.1 then 1 else 0

lemma detCJ_cptp {x1 x2 : Type*} [Fintype x1] [Fintype x2] [DecidableEq x1] [DecidableEq x2]
    (f : x1 → x2) : IsCPTP_CJ (detCJ f) := by
  refine ⟨posSemidef_diagonal_iff.mpr fun p => ?_, ?_⟩
  · split_ifs <;> simp
  · ext i i'
    simp only [ptrace₂, detCJ, of_apply, diagonal_apply, Prod.mk.injEq, one_apply]
    by_cases h : i = i'
    · subst h; simp
    · simp [h]

lemma ptrace₂_diag_sum {x1 x2 : Type*} [Fintype x1] [Fintype x2] [DecidableEq x1]
    {M : Matrix (x1 × x2) (x1 × x2) ℂ} (hM : IsCPTP_CJ M) (i : x1) :
    ∑ j, M (i, j) (i, j) = 1 := by
  have := congrFun (congrFun hM.2 i) i
  simpa [ptrace₂] using this

variable {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2] [Fintype b1] [Fintype b2]
  [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]

/-- Probabilities for a diagonal `W` only see the diagonals of the local CJ matrices. -/
lemma prob_diagonal (d : (a1 × a2) × (b1 × b2) → ℂ) (MA : Matrix (a1 × a2) (a1 × a2) ℂ)
    (MB : Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob (diagonal d) MA MB =
      ∑ i, ∑ j, ∑ k, ∑ l, d ((i, j), (k, l)) * (MA (i, j) (i, j) * MB (k, l) (k, l)) := by
  simp only [prob, trace, diag, diagonal_mul, kroneckerMap_apply, Fintype.sum_prod_type]

/-- A diagonal matrix `diag u(i,j,k) ⊗ 𝟙^{B2}` of the form `𝟙^{B2} ⊗ W^{A1A2B1}`. -/
def diagBA (u : a1 → a2 → b1 → ℝ) : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ :=
  diagonal fun x => (u x.1.1 x.1.2 x.2.1 : ℂ)

/-- A diagonal matrix `diag v(i,k,l) ⊗ 𝟙^{A2}` of the form `𝟙^{A2} ⊗ W^{A1B1B2}`. -/
def diagAB (v : a1 → b1 → b2 → ℝ) : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ :=
  diagonal fun x => (v x.1.1 x.2.1 x.2.2 : ℂ)

lemma diagBA_form (u : a1 → a2 → b1 → ℝ) : IsNoSignalBtoA (diagBA (b2 := b2) u) := by
  refine ⟨diagonal fun y => (u y.1.1 y.1.2 y.2 : ℂ), ?_⟩
  ext r c
  simp only [diagBA, diagonal_apply, of_apply]
  obtain ⟨⟨r1, r2⟩, r3, r4⟩ := r
  obtain ⟨⟨c1, c2⟩, c3, c4⟩ := c
  simp only [Prod.mk.injEq]
  by_cases h4 : r4 = c4 <;> simp [h4]

lemma diagAB_form (v : a1 → b1 → b2 → ℝ) : IsNoSignalAtoB (diagAB (a2 := a2) v) := by
  refine ⟨diagonal fun y => (v y.1 y.2.1 y.2.2 : ℂ), ?_⟩
  ext r c
  simp only [diagAB, diagonal_apply, of_apply]
  obtain ⟨⟨r1, r2⟩, r3, r4⟩ := r
  obtain ⟨⟨c1, c2⟩, c3, c4⟩ := c
  simp only [Prod.mk.injEq]
  by_cases h2 : r2 = c2 <;> simp [h2]

/-- Normalization of `diagBA u` on CPTP maps, when `∑ₖ u(i,j,k)` does not depend on `j`. -/
lemma prob_diagBA (u : a1 → a2 → b1 → ℝ) (j0 : a2) (hu : ∀ i j, ∑ k, u i j k = ∑ k, u i j0 k)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ)
    (hA : IsCPTP_CJ MA) (hB : IsCPTP_CJ MB) :
    prob (diagBA u) MA MB = ((∑ i, ∑ k, u i j0 k : ℝ) : ℂ) := by
  rw [diagBA, prob_diagonal]
  calc ∑ i, ∑ j, ∑ k, ∑ l, (u i j k : ℂ) * (MA (i, j) (i, j) * MB (k, l) (k, l))
      = ∑ i, ∑ j, MA (i, j) (i, j) * ∑ k, (u i j k : ℂ) * ∑ l, MB (k, l) (k, l) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
    _ = ∑ i, ∑ j, MA (i, j) (i, j) * ((∑ k, u i j0 k : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [ptrace₂_diag_sum hB, mul_one]
        rw [← hu i j]; push_cast; rfl
    _ = ∑ i, ((∑ k, u i j0 k : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, ptrace₂_diag_sum hA, one_mul]
    _ = _ := by push_cast; rfl

/-- Normalization of `diagAB v` on CPTP maps, when `∑ᵢ v(i,k,l)` does not depend on `l`. -/
lemma prob_diagAB (v : a1 → b1 → b2 → ℝ) (l0 : b2) (hv : ∀ k l, ∑ i, v i k l = ∑ i, v i k l0)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ)
    (hA : IsCPTP_CJ MA) (hB : IsCPTP_CJ MB) :
    prob (diagAB v) MA MB = ((∑ k, ∑ i, v i k l0 : ℝ) : ℂ) := by
  rw [diagAB, prob_diagonal]
  calc ∑ i, ∑ j, ∑ k, ∑ l, (v i k l : ℂ) * (MA (i, j) (i, j) * MB (k, l) (k, l))
      = ∑ i, (∑ j, MA (i, j) (i, j)) * ∑ k, ∑ l, (v i k l : ℂ) * MB (k, l) (k, l) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
    _ = ∑ i, ∑ k, ∑ l, (v i k l : ℂ) * MB (k, l) (k, l) := by
        simp only [ptrace₂_diag_sum hA, one_mul]
    _ = ∑ k, ∑ l, MB (k, l) (k, l) * ∑ i, (v i k l : ℂ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ k, ∑ l, MB (k, l) (k, l) * ((∑ i, v i k l0 : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [← hv k l]; push_cast; rfl
    _ = ∑ k, ((∑ i, v i k l0 : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_mul, ptrace₂_diag_sum hB, one_mul]
    _ = _ := by push_cast; rfl

end OCB2012Sol

namespace OCB2012Sol
open OCB2012

variable {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2] [Fintype b1] [Fintype b2]
  [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]

lemma diagBA_process (j0 : a2) (u : a1 → a2 → b1 → ℝ) (h0 : ∀ i j k, 0 ≤ u i j k)
    (hu : ∀ i j, ∑ k, u i j k = ∑ k, u i j0 k) (h1 : ∑ i, ∑ k, u i j0 k = 1) :
    IsProcessMatrix (diagBA (b2 := b2) u) :=
  ⟨posSemidef_diagonal_iff.mpr fun x => Complex.zero_le_real.mpr (h0 _ _ _),
    fun MA MB hA hB => by rw [prob_diagBA u j0 hu MA MB hA hB, h1, Complex.ofReal_one]⟩

lemma diagAB_process (l0 : b2) (v : a1 → b1 → b2 → ℝ) (h0 : ∀ i k l, 0 ≤ v i k l)
    (hv : ∀ k l, ∑ i, v i k l = ∑ i, v i k l0) (h1 : ∑ k, ∑ i, v i k l0 = 1) :
    IsProcessMatrix (diagAB (a2 := a2) v) :=
  ⟨posSemidef_diagonal_iff.mpr fun x => Complex.zero_le_real.mpr (h0 _ _ _),
    fun MA MB hA hB => by rw [prob_diagAB v l0 hv MA MB hA hB, h1, Complex.ofReal_one]⟩

end OCB2012Sol

open OCB2012 OCB2012Sol in
theorem solution {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (hW : IsProcessMatrix W) (hdiag : W.IsDiag) :
    IsCausallySeparable W := by
  -- Degenerate dimensions: all matrices on an empty index type coincide.
  by_cases hne : Nonempty a1 ∧ Nonempty a2 ∧ Nonempty b1 ∧ Nonempty b2
  swap
  · have : IsEmpty ((a1 × a2) × (b1 × b2)) := by
      simp only [not_and_or, not_nonempty_iff] at hne
      rcases hne with h | h | h | h <;> infer_instance
    exact ⟨1, zero_le_one, le_rfl, W, W, hW, ⟨0, Subsingleton.elim _ _⟩, hW,
      ⟨0, Subsingleton.elim _ _⟩, Subsingleton.elim _ _⟩
  obtain ⟨ha1, ha2, hb1, hb2⟩ := hne
  obtain ⟨j0⟩ := id ha2
  obtain ⟨l0⟩ := id hb2
  -- The diagonal entries `w(i,j,k,l) ≥ 0` of `W`.
  set w : a1 → a2 → b1 → b2 → ℝ := fun i j k l => (W ((i, j), (k, l)) ((i, j), (k, l))).re
  have hw0 : ∀ i j k l, 0 ≤ w i j k l := fun i j k l =>
    (Complex.le_def.mp (hW.1.diag_nonneg (i := ((i, j), (k, l))))).1
  have hWd : W = diagonal fun x => (w x.1.1 x.1.2 x.2.1 x.2.2 : ℂ) := by
    conv_lhs => rw [← hdiag.diagonal_diag]
    congr 1; funext x; exact (hW.1.1.coe_re_apply_self x).symm
  -- Deterministic local strategies: `∑_{i,k} w(i, f i, k, g k) = 1`.
  have hS : ∀ (f : a1 → a2) (g : b1 → b2), ∑ i, ∑ k, w i (f i) k (g k) = 1 := by
    intro f g
    have h := hW.2 _ _ (detCJ_cptp f) (detCJ_cptp g)
    rw [hWd, prob_diagonal] at h
    simp only [detCJ, diagonal_apply_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact_mod_cast h
  -- Single-point variations of `f` and of `g`.
  have hSV1 : ∀ (g : b1 → b2) i j j', ∑ k, (w i j k (g k) - w i j' k (g k)) = 0 := by
    intro g i j j'
    have := sum_update_sub (fun i' a => ∑ k, w i' a k (g k)) (fun _ => j0) i j j'
    simp only [hS, sub_self] at this
    rw [Finset.sum_sub_distrib]; linarith
  have hSV2 : ∀ (f : a1 → a2) k l l', ∑ i, (w i (f i) k l - w i (f i) k l') = 0 := by
    intro f k l l'
    have := sum_update_sub (fun k' b => ∑ i, w i (f i) k' b) (fun _ => l0) k l l'
    have hS' : ∀ g : b1 → b2, ∑ k', ∑ i, w i (f i) k' (g k') = 1 := fun g => by
      rw [Finset.sum_comm]; exact hS f g
    simp only [hS', sub_self] at this
    rw [Finset.sum_sub_distrib]; linarith
  -- `w(i,j,k,l) - w(i,j',k,l)` does not depend on `l`.
  have hdd : ∀ i j j' k l l', w i j k l + w i j' k l' = w i j' k l + w i j k l' := by
    intro i j j' k l l'
    have := sum_update_sub (fun k' b => w i j k' b - w i j' k' b) (fun _ => l0) k l l'
    simp only [hSV1, sub_self] at this
    linarith
  -- Shift by the minimum over `j` (Eqs. (38)–(43)).
  have hmin : ∀ i k, ∃ js, ∀ j, w i js k l0 ≤ w i j k l0 :=
    fun i k => Finite.exists_min (fun j => w i j k l0)
  choose js hjs using hmin
  set u : a1 → a2 → b1 → ℝ := fun i j k => w i j k l0 - w i (js i k) k l0 with hu_def
  set v : a1 → b1 → b2 → ℝ := fun i k l => w i (js i k) k l with hv_def
  have hu0 : ∀ i j k, 0 ≤ u i j k := fun i j k => sub_nonneg.mpr (hjs i k j)
  have hv0 : ∀ i k l, 0 ≤ v i k l := fun _ _ _ => hw0 _ _ _ _
  have huv : ∀ i j k l, w i j k l = u i j k + v i k l := by
    intro i j k l
    have := hdd i j (js i k) k l l0
    simp only [hu_def, hv_def]; linarith
  have hu : ∀ i j, ∑ k, u i j k = ∑ k, u i j0 k := by
    intro i j
    have := hSV1 (fun _ => l0) i j j0
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hu_def]; ring
  have hv : ∀ k l, ∑ i, v i k l = ∑ i, v i k l0 := by
    intro k l
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    exact hSV2 (fun i => js i k) k l l0
  set q := ∑ i, ∑ k, u i j0 k with hq_def
  have hq : q + ∑ k, ∑ i, v i k l0 = 1 := by
    have := hS (fun _ => j0) (fun _ => l0)
    simp only [huv, Finset.sum_add_distrib] at this
    rw [Finset.sum_comm (f := fun k i => v i k l0)]; exact this
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hu0 _ _ _
  have hq1 : 0 ≤ ∑ k, ∑ i, v i k l0 :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => hv0 _ _ _
  have hWuv : W = diagBA u + diagAB v := by
    rw [hWd, diagBA, diagAB, diagonal_add]
    congr 1; funext x; rw [huv]; push_cast; ring
  -- The maximally mixed process, which has both one-way forms.
  have hcard : (0 : ℝ) < Fintype.card a1 * Fintype.card b1 := by
    have := Fintype.card_pos (α := a1); have := Fintype.card_pos (α := b1); positivity
  set c : ℝ := 1 / (Fintype.card a1 * Fintype.card b1)
  have hc1 : ∑ _i : a1, ∑ _k : b1, c = 1 := by
    have := hcard.ne'
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, c]; field_simp
  have hc1' : ∑ _k : b1, ∑ _i : a1, c = 1 := by rw [Finset.sum_comm]; exact hc1
  have mixBA := diagBA_process (b2 := b2) j0 (fun _ _ _ => c) (fun _ _ _ => by positivity)
    (fun _ _ => rfl) hc1
  have mixAB := diagAB_process (a2 := a2) l0 (fun _ _ _ => c) (fun _ _ _ => by positivity)
    (fun _ _ => rfl) hc1'
  by_cases hqz : q = 0
  · -- `u = 0`, so `W = diagAB v` has no signalling from Alice to Bob.
    have hu_zero : ∀ i j k, u i j k = 0 := by
      intro i j k
      have hi : ∑ k, u i j0 k = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        Finset.sum_nonneg fun k _ => hu0 _ _ _).mp hqz i (Finset.mem_univ _)
      rw [← hu i j] at hi
      exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hu0 _ _ _).mp hi k (Finset.mem_univ _)
    refine ⟨0, le_rfl, zero_le_one, _, _, mixBA, diagBA_form _, diagAB_process l0 v hv0 hv
      (by linarith), diagAB_form v, ?_⟩
    rw [hWuv]
    have : diagBA (b2 := b2) u = 0 := by
      ext x y; simp [diagBA, diagonal_apply, hu_zero]
    rw [this]; simp
  by_cases hq1' : q = 1
  · -- `v = 0`, so `W = diagBA u` has no signalling from Bob to Alice.
    have hv_zero : ∀ i k l, v i k l = 0 := by
      intro i k l
      have h0 : ∑ k, ∑ i, v i k l0 = 0 := by linarith
      have hk : ∑ i, v i k l0 = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
        Finset.sum_nonneg fun i _ => hv0 _ _ _).mp h0 k (Finset.mem_univ _)
      rw [← hv k l] at hk
      exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hv0 _ _ _).mp hk i (Finset.mem_univ _)
    refine ⟨1, zero_le_one, le_rfl, _, _, diagBA_process j0 u hu0 hu (by rw [← hq_def, hq1']),
      diagBA_form u, mixAB, diagAB_form _, ?_⟩
    rw [hWuv]
    have : diagAB (a2 := a2) v = 0 := by
      ext x y; simp [diagAB, diagonal_apply, hv_zero]
    rw [this]; simp
  -- Generic case `0 < q < 1`: normalize both parts.
  have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
  have hq1pos : 0 < 1 - q := by
    have : q ≤ 1 := by linarith
    exact sub_pos.mpr (lt_of_le_of_ne this hq1')
  refine ⟨q, hq0, by linarith, diagBA (fun i j k => u i j k / q),
    diagAB (fun i k l => v i k l / (1 - q)), ?_, diagBA_form _, ?_, diagAB_form _, ?_⟩
  · refine diagBA_process j0 _ (fun i j k => div_nonneg (hu0 i j k) hqpos.le)
      (fun i j => by simp only [← Finset.sum_div, hu i j]) ?_
    simp only [← Finset.sum_div, ← hq_def]; field_simp
  · refine diagAB_process l0 _ (fun i k l => div_nonneg (hv0 i k l) hq1pos.le)
      (fun k l => by simp only [← Finset.sum_div, hv k l]) ?_
    simp only [← Finset.sum_div]; rw [div_eq_one_iff_eq hq1pos.ne']; linarith
  · rw [hWuv, diagBA, diagAB, diagBA, diagAB, ← diagonal_smul, ← diagonal_smul, diagonal_add,
      diagonal_add]
    congr 1; funext x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    have h1q : (1 : ℂ) - q ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub]; exact_mod_cast hq1pos.ne'
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
    push_cast
    field_simp

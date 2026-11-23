-- Prove2me | solution 1 for QAlgorithms.Papers.RoadmapL03.keyl_squaredRisk_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T12:44:10.685896+00:00
-- url     : https://prove2.me/submissions/ccf084a8-37fc-4f70-94bb-42cbb2431a7f

import Mathlib
import Definitions.Def_QAlgorithms_Defs_KeylTomography
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_TomographyOutcomes
import Theorems.Thm_KWSpectrum_Estimator_eq_17
import Theorems.Thm_KWSpectrum_Estimator_eq_2_4_projections
import Theorems.Thm_KWSpectrum_Estimator_eq_20
import Theorems.Thm_QAlgorithms_Papers_RoadmapL03_keyl_haar_generalizedPower
-- ===== KS1 =====

set_option autoImplicit false
open scoped BigOperators Matrix

noncomputable section

namespace KeylS

/-- multilinear expansion of a determinant whose columns are sums -/
lemma det_sum_cols {R : Type*} [CommRing R] {m : ℕ} (S : Fin m → Finset ℕ) (g : Fin m → ℕ → Fin m → R) :
    (Matrix.of fun i j => ∑ k ∈ S j, g j k i).det =
      ∑ K ∈ Fintype.piFinset S, (Matrix.of fun i j => g j (K j) i).det := by
  simp only [Matrix.det_apply, Matrix.of_apply]
  simp_rw [Finset.prod_univ_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.smul_sum]

/-- alternant with exponent vector `e` -/
def alt {R : Type*} [CommRing R] {m : ℕ} (e : Fin m → ℕ) (x : Fin m → R) : R :=
  (Matrix.of fun i j => x i ^ e j).det

/-- the column-operation matrix -/
def colOp {R : Type*} [CommRing R] {d : ℕ} (c : Fin d → R) : Matrix (Fin (d+1)) (Fin (d+1)) R :=
  fun k j => if k = j then 1 else if h : j.val < d ∧ k.val = j.val + 1 then -c ⟨j.val, h.1⟩ else 0

lemma colOp_diag {R : Type*} [CommRing R] {d : ℕ} (c : Fin d → R) (j : Fin (d+1)) :
    colOp c j j = 1 := by simp [colOp]

lemma colOp_sub {R : Type*} [CommRing R] {d : ℕ} (c : Fin d → R) (j : Fin (d+1)) (h : j.val < d) :
    colOp c ⟨j.val + 1, by omega⟩ j = -c ⟨j.val, h⟩ := by
  unfold colOp
  rw [if_neg (by intro e; have := congrArg Fin.val e; simp at this), dif_pos ⟨h, rfl⟩]

lemma colOp_zero {R : Type*} [CommRing R] {d : ℕ} (c : Fin d → R) (k j : Fin (d+1)) (hk : k ≠ j)
    (hk' : k.val ≠ j.val + 1) : colOp c k j = 0 := by
  unfold colOp
  rw [if_neg hk, dif_neg (fun h => hk' h.2)]

lemma det_colOp {R : Type*} [CommRing R] {d : ℕ} (c : Fin d → R) : (colOp c).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [colOp_diag]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    have : (i : ℕ) < j := hij'
    exact colOp_zero c i j (fun e => by rw [e] at this; exact lt_irrefl _ this) (by omega)

lemma mul_colOp {R : Type*} [CommRing R] {d : ℕ} (c : Fin d → R)
    (M : Matrix (Fin (d+1)) (Fin (d+1)) R) (i : Fin (d+1)) (j : Fin (d+1)) :
    (M * colOp c) i j = if h : j.val < d then M i j - c ⟨j.val, h⟩ * M i ⟨j.val + 1, by omega⟩
      else M i j := by
  rw [Matrix.mul_apply]
  by_cases h : j.val < d
  · rw [dif_pos h]
    have hne : j ≠ ⟨j.val + 1, by omega⟩ := by
      intro e; have := congrArg Fin.val e; simp at this
    rw [Finset.sum_eq_add_of_mem j ⟨j.val + 1, by omega⟩ (Finset.mem_univ _) (Finset.mem_univ _) hne
      (fun k _ hk => by
        rw [colOp_zero c k j hk.1 (fun h' => hk.2 (Fin.ext h')), mul_zero])]
    rw [colOp_diag, colOp_sub c j h]
    ring
  · rw [dif_neg h]
    rw [Finset.sum_eq_single j]
    · rw [colOp_diag, mul_one]
    · intro k _ hk
      rw [colOp_zero c k j hk (fun h' => by have := k.isLt; omega), mul_zero]
    · intro h'; exact absurd (Finset.mem_univ _) h'

lemma factor_entry {R : Type*} [CommRing R] (x t : R) (a b : ℕ) (hab : b ≤ a) :
    x ^ a - t ^ (a - b) * x ^ b = (x - t) * ∑ k ∈ Finset.range (a - b), x ^ (b + k) * t ^ (a - b - 1 - k) := by
  have h := geom_sum₂_mul x t (a - b)
  have ha : x ^ a = x ^ b * x ^ (a - b) := by rw [← pow_add]; congr 1; omega
  calc x ^ a - t ^ (a - b) * x ^ b = x ^ b * (x ^ (a - b) - t ^ (a - b)) := by rw [ha]; ring
    _ = x ^ b * ((∑ i ∈ Finset.range (a - b), x ^ i * t ^ (a - b - 1 - i)) * (x - t)) := by rw [h]
    _ = (x - t) * ∑ k ∈ Finset.range (a - b), x ^ (b + k) * t ^ (a - b - 1 - k) := by
        rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [pow_add]; ring

/-- branching of alternants along the last variable -/
lemma alt_branch {R : Type*} [CommRing R] {d : ℕ} (l : Fin (d+1) → ℕ)
    (hl : ∀ j : Fin d, l j.succ < l j.castSucc) (x : Fin (d+1) → R) :
    alt l x = (∏ i : Fin d, (x i.castSucc - x (Fin.last d))) *
      ∑ p ∈ Fintype.piFinset (fun j : Fin d => Finset.Ico (l j.succ) (l j.castSucc)),
        x (Fin.last d) ^ (l (Fin.last d) + ∑ j, (l j.castSucc - p j - 1)) * alt p (x ∘ Fin.castSucc) := by
  set t := x (Fin.last d) with ht
  set c : Fin d → R := fun j => t ^ (l j.castSucc - l j.succ) with hc
  set M : Matrix (Fin (d+1)) (Fin (d+1)) R := Matrix.of fun i j => x i ^ l j with hM
  have h1 : alt l x = (M * colOp c).det := by
    rw [Matrix.det_mul, det_colOp, mul_one]; rfl
  rw [h1, Matrix.det_succ_row _ (Fin.last d), Fin.sum_univ_castSucc]
  have hzero : ∀ j : Fin d, (M * colOp c) (Fin.last d) j.castSucc = 0 := by
    intro j
    rw [mul_colOp, dif_pos (by simp)]
    simp only [hM, Matrix.of_apply, hc, Fin.val_castSucc]
    have hj : (⟨j.val + 1, by omega⟩ : Fin (d+1)) = j.succ := Fin.ext rfl
    rw [hj, ← ht, ← pow_add]
    have := hl j
    rw [show l j.castSucc - l j.succ + l j.succ = l j.castSucc by omega]
    simp
  simp only [hzero, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  have hlast : (M * colOp c) (Fin.last d) (Fin.last d) = t ^ l (Fin.last d) := by
    rw [mul_colOp, dif_neg (by simp)]
    rfl
  rw [hlast, Fin.succAbove_last]
  have hsign : (-1 : R) ^ ((Fin.last d : ℕ) + (Fin.last d : ℕ)) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]; simp
  rw [hsign, one_mul]
  -- the minor
  have hminor : ((M * colOp c).submatrix Fin.castSucc Fin.castSucc).det =
      (∏ i : Fin d, (x i.castSucc - t)) * (Matrix.of fun i j =>
        ∑ k ∈ Finset.range (l (Fin.castSucc j) - l (Fin.succ j)),
          x (Fin.castSucc i) ^ (l (Fin.succ j) + k) *
            t ^ (l (Fin.castSucc j) - l (Fin.succ j) - 1 - k) : Matrix (Fin d) (Fin d) R).det := by
    rw [← Matrix.det_mul_column]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    rw [mul_colOp, dif_pos (by simp)]
    simp only [hM, Matrix.of_apply, hc, Fin.val_castSucc]
    have hj : (⟨j.val + 1, by omega⟩ : Fin (d+1)) = j.succ := Fin.ext rfl
    rw [hj]
    exact factor_entry _ _ _ _ (hl j).le
  rw [hminor]
  rw [det_sum_cols (fun j => Finset.range (l j.castSucc - l j.succ))
    (fun j k i => x i.castSucc ^ (l j.succ + k) * t ^ (l j.castSucc - l j.succ - 1 - k))]
  rw [mul_comm (t ^ _), mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_nbij' (fun K j => l j.succ + K j) (fun p j => p j - l j.succ) ?_ ?_ ?_ ?_ ?_
  · intro K hK
    simp only [Fintype.mem_piFinset, Finset.mem_range] at hK
    simp only [Fintype.mem_piFinset, Finset.mem_Ico]
    intro j; have := hK j; constructor <;> omega
  · intro p hp
    simp only [Fintype.mem_piFinset, Finset.mem_Ico] at hp
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro j; have := hp j; omega
  · intro K _; funext j; simp
  · intro p hp
    simp only [Fintype.mem_piFinset, Finset.mem_Ico] at hp
    funext j; have := hp j; simp only; omega
  · intro K hK
    simp only [Fintype.mem_piFinset, Finset.mem_range] at hK
    have hdet : (Matrix.of fun i j => x i.castSucc ^ (l j.succ + K j) *
        t ^ (l j.castSucc - l j.succ - 1 - K j)).det =
        (∏ j, t ^ (l j.castSucc - l j.succ - 1 - K j)) * alt (fun j => l j.succ + K j) (x ∘ Fin.castSucc) := by
      unfold alt
      rw [← Matrix.det_mul_row]
      congr 1; ext i j; simp only [Matrix.of_apply, Function.comp_apply]; ring
    rw [hdet, Finset.prod_pow_eq_pow_sum]
    have hexp : ∑ j, (l j.castSucc - l j.succ - 1 - K j) = ∑ j, (l j.castSucc - (l j.succ + K j) - 1) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have := hK j
      omega
    rw [hexp, pow_add]
    ring

end KeylS

-- ===== KS2 =====

set_option autoImplicit false
open scoped BigOperators

noncomputable section

namespace KeylS

/-- semistandard condition on a Young diagram -/
def SS {d : ℕ} (μ : YoungDiagram) (T : μ.cells → Fin d) : Prop :=
  ∀ a b : μ.cells,
    (a.val.1 = b.val.1 → a.val.2 < b.val.2 → T a ≤ T b) ∧
    (a.val.2 = b.val.2 → a.val.1 < b.val.1 → T a < T b)

open Classical in
/-- the semistandard fillings -/
def ssytF (d : ℕ) (μ : YoungDiagram) : Finset (μ.cells → Fin d) := Finset.univ.filter (SS μ)

/-- evaluation of the Schur polynomial -/
def sev {R : Type*} [CommRing R] (d : ℕ) (μ : YoungDiagram) (x : Fin d → R) : R :=
  ∑ T ∈ ssytF d μ, ∏ a : μ.cells, x (T a)

/-- the Young diagram with prescribed (antitone) row lengths -/
def dg {d : ℕ} (q : Fin d → ℕ) (hq : Antitone q) : YoungDiagram where
  cells := Finset.univ.biUnion (fun i : Fin d => (Finset.range (q i)).map
    ⟨fun j => ((i : ℕ), j), fun a b h => (Prod.mk.inj h).2⟩)
  isLowerSet := by
    intro b a hab hb
    simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
      Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hb ⊢
    obtain ⟨i, j, hj, rfl⟩ := hb
    have h1 : a.1 ≤ i := hab.1
    have h2 : a.2 ≤ j := hab.2
    refine ⟨⟨a.1, by omega⟩, a.2, ?_, rfl⟩
    have := hq (show (⟨a.1, by omega⟩ : Fin d) ≤ i from h1)
    omega

lemma mem_dg {d : ℕ} (q : Fin d → ℕ) (hq : Antitone q) (c : ℕ × ℕ) :
    c ∈ dg q hq ↔ ∃ h : c.1 < d, c.2 < q ⟨c.1, h⟩ := by
  show c ∈ (dg q hq).cells ↔ _
  simp only [dg, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk, Finset.mem_range]
  constructor
  · rintro ⟨i, j, hj, rfl⟩
    exact ⟨i.isLt, hj⟩
  · rintro ⟨h, h2⟩
    exact ⟨⟨c.1, h⟩, c.2, h2, rfl⟩

lemma dg_rowLen {d : ℕ} (q : Fin d → ℕ) (hq : Antitone q) (i : Fin d) :
    (dg q hq).rowLen i = q i := by
  apply le_antisymm
  · by_contra h
    push_neg at h
    have : ((i : ℕ), q i) ∈ dg q hq := YoungDiagram.mem_iff_lt_rowLen.2 h
    obtain ⟨_, h2⟩ := (mem_dg q hq _).1 this
    simp at h2
  · by_contra h
    push_neg at h
    have : ((i : ℕ), (dg q hq).rowLen i) ∈ dg q hq := (mem_dg q hq _).2 ⟨i.isLt, by simpa using h⟩
    exact lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.1 this)

lemma dg_card {d : ℕ} (q : Fin d → ℕ) (hq : Antitone q) : (dg q hq).card = ∑ i, q i := by
  show (dg q hq).cells.card = _
  simp only [dg]
  rw [Finset.card_biUnion]
  · simp
  · intro i₁ _ i₂ _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hc hc'
    obtain ⟨_, _, rfl⟩ := hc
    obtain ⟨_, _, h⟩ := hc'
    exact hij (Fin.ext (Prod.mk.inj h).1.symm)

lemma dg_colLen {d : ℕ} (q : Fin d → ℕ) (hq : Antitone q) : (dg q hq).colLen 0 ≤ d := by
  by_contra h
  push_neg at h
  have : (d, 0) ∈ dg q hq := YoungDiagram.mem_iff_lt_colLen.2 h
  obtain ⟨h1, _⟩ := (mem_dg q hq _).1 this
  exact lt_irrefl _ h1

/-- downward closed finite sets of naturals are initial segments -/
lemma mem_iff_lt_card_of_down (S : Finset ℕ) (hS : ∀ a b, b ≤ a → a ∈ S → b ∈ S) (j : ℕ) :
    j ∈ S ↔ j < S.card := by
  constructor
  · intro hj
    have : Finset.range (j+1) ⊆ S := fun k hk => hS j k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hj
    have := Finset.card_le_card this
    simp at this; omega
  · intro hj
    by_contra hn
    have : S ⊆ Finset.range j := by
      intro k hk
      rw [Finset.mem_range]
      by_contra hk'
      push_neg at hk'
      exact hn (hS k j hk' hk)
    have := Finset.card_le_card this
    simp at this; omega

open Classical in
/-- the number of entries `< d` in row `i` -/
def cntR {d : ℕ} (μ : YoungDiagram) (T : μ.cells → Fin (d+1)) (i : ℕ) : ℕ :=
  ((Finset.range (μ.rowLen i)).filter (fun j => ∃ h : (i, j) ∈ μ, (T ⟨(i, j), h⟩).val < d)).card

lemma cntR_spec {d : ℕ} (μ : YoungDiagram) (T : μ.cells → Fin (d+1)) (hT : SS μ T) (c : μ.cells) :
    (T c).val < d ↔ c.val.2 < cntR μ T c.val.1 := by
  classical
  unfold cntR
  rw [← mem_iff_lt_card_of_down]
  · simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact ⟨YoungDiagram.mem_iff_lt_rowLen.1 c.2, c.2, h⟩
    · rintro ⟨_, h, h2⟩
      exact h2
  · intro a b hba ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    obtain ⟨ha1, h, h2⟩ := ha
    have hb : (c.val.1, b) ∈ μ := μ.up_left_mem le_rfl hba h
    refine ⟨by omega, hb, ?_⟩
    rcases lt_or_eq_of_le hba with hlt | heq
    · exact lt_of_le_of_lt ((hT ⟨_, hb⟩ ⟨_, h⟩).1 rfl hlt) h2
    · subst heq; exact h2

lemma cntR_le {d : ℕ} (μ : YoungDiagram) (T : μ.cells → Fin (d+1)) (i : ℕ) :
    cntR μ T i ≤ μ.rowLen i := by
  classical
  unfold cntR
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- entries in row `r` are at least `r` -/
lemma row_ge {d : ℕ} (μ : YoungDiagram) (T : μ.cells → Fin (d+1)) (hT : SS μ T) :
    ∀ (r : ℕ) (j : ℕ) (h : (r, j) ∈ μ), r ≤ (T ⟨(r, j), h⟩).val := by
  intro r
  induction r with
  | zero => intro j h; exact Nat.zero_le _
  | succ r ih =>
    intro j h
    have h' : (r, j) ∈ μ := μ.up_left_mem (Nat.le_succ r) le_rfl h
    have := (hT ⟨_, h'⟩ ⟨_, h⟩).2 rfl (Nat.lt_succ_self r)
    have := ih j h'
    have : (T ⟨(r, j), h'⟩).val < (T ⟨(r+1, j), h⟩).val := by exact_mod_cast ‹_›
    omega

lemma last_row {d : ℕ} (μ : YoungDiagram) (T : μ.cells → Fin (d+1)) (hT : SS μ T) (c : μ.cells)
    (hc : c.val.1 = d) : T c = Fin.last d := by
  have h := row_ge μ T hT c.val.1 c.val.2 c.2
  have e : (⟨(c.val.1, c.val.2), c.2⟩ : μ.cells) = c := rfl
  rw [e] at h
  apply Fin.ext
  have := (T c).isLt
  rw [Fin.val_last]
  omega

lemma cntR_ge {d : ℕ} (μ : YoungDiagram) (T : μ.cells → Fin (d+1)) (hT : SS μ T) (i : ℕ) :
    μ.rowLen (i+1) ≤ cntR μ T i := by
  by_contra h
  push_neg at h
  have hm : (i+1, cntR μ T i) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.2 h
  have hm' : (i, cntR μ T i) ∈ μ := μ.up_left_mem (Nat.le_succ i) le_rfl hm
  have h1 := (hT ⟨_, hm'⟩ ⟨_, hm⟩).2 rfl (Nat.lt_succ_self i)
  have h2 : (T ⟨(i, cntR μ T i), hm'⟩).val < d := by
    have := (T ⟨(i+1, cntR μ T i), hm⟩).isLt
    have : (T ⟨(i, cntR μ T i), hm'⟩).val < (T ⟨(i+1, cntR μ T i), hm⟩).val := by exact_mod_cast h1
    omega
  have := (cntR_spec μ T hT ⟨_, hm'⟩).1 h2
  exact lt_irrefl _ this

/-- interlacing row vectors -/
def IL (d : ℕ) (μ : YoungDiagram) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i : Fin d => Finset.Icc (μ.rowLen (i+1)) (μ.rowLen i))

lemma il_anti {d : ℕ} {μ : YoungDiagram} {q : Fin d → ℕ} (hq : q ∈ IL d μ) : Antitone q := by
  intro i i' hii
  simp only [IL, Fintype.mem_piFinset, Finset.mem_Icc] at hq
  rcases lt_or_eq_of_le hii with h | h
  · have h1 := (hq i').2
    have h2 := (hq i).1
    have : μ.rowLen i' ≤ μ.rowLen (i + 1) := μ.rowLen_anti _ _ (by exact h)
    omega
  · rw [h]

lemma dg_sub {d : ℕ} {μ : YoungDiagram} {q : Fin d → ℕ} (hq : q ∈ IL d μ) (c : ℕ × ℕ)
    (hc : c ∈ dg q (il_anti hq)) : c ∈ μ := by
  obtain ⟨h1, h2⟩ := (mem_dg q (il_anti hq) c).1 hc
  simp only [IL, Fintype.mem_piFinset, Finset.mem_Icc] at hq
  have := (hq ⟨c.1, h1⟩).2
  exact YoungDiagram.mem_iff_lt_rowLen.2 (by simp at this; omega)

/-- restriction of a tableau to the cells with entries `< d` -/
def toSmall {d : ℕ} {μ : YoungDiagram} {q : Fin d → ℕ} (hq : q ∈ IL d μ) (T : μ.cells → Fin (d+1)) :
    (dg q (il_anti hq)).cells → Fin d := fun a =>
  if h : (T ⟨a.val, dg_sub hq a.val a.2⟩).val < d then ⟨_, h⟩
  else ⟨0, by obtain ⟨h1, _⟩ := (mem_dg q (il_anti hq) a.val).1 a.2; omega⟩

/-- extension of a tableau by the letter `d` -/
def toBig {d : ℕ} {μ : YoungDiagram} {q : Fin d → ℕ} (hq : q ∈ IL d μ)
    (T : (dg q (il_anti hq)).cells → Fin d) : μ.cells → Fin (d+1) := fun c =>
  if h : c.val ∈ dg q (il_anti hq) then Fin.castSucc (T ⟨c.val, h⟩) else Fin.last d

lemma row_le_d {d : ℕ} {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ d + 1) (c : μ.cells) : c.val.1 ≤ d := by
  have h1 : c.val.1 < μ.colLen c.val.2 := YoungDiagram.mem_iff_lt_colLen.1 c.2
  have h2 : μ.colLen c.val.2 ≤ μ.colLen 0 := μ.colLen_anti 0 c.val.2 (Nat.zero_le _)
  omega

lemma lt_d_of_mem {d : ℕ} {μ : YoungDiagram} {q : Fin d → ℕ} (hq : q ∈ IL d μ)
    (T : μ.cells → Fin (d+1)) (hT : SS μ T) (hc : ∀ i : Fin d, cntR μ T i = q i)
    (c : μ.cells) (h : c.val ∈ dg q (il_anti hq)) : (T c).val < d := by
  obtain ⟨h1, h2⟩ := (mem_dg q (il_anti hq) c.val).1 h
  rw [cntR_spec μ T hT c, show cntR μ T c.val.1 = q ⟨c.val.1, h1⟩ from hc ⟨c.val.1, h1⟩]
  exact h2

lemma eq_last_of_not_mem {d : ℕ} {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ d + 1) {q : Fin d → ℕ}
    (hq : q ∈ IL d μ) (T : μ.cells → Fin (d+1)) (hT : SS μ T) (hc : ∀ i : Fin d, cntR μ T i = q i)
    (c : μ.cells) (h : c.val ∉ dg q (il_anti hq)) : T c = Fin.last d := by
  rcases lt_or_eq_of_le (row_le_d hμ c) with h1 | h1
  · have h2 : ¬ (c.val.2 < q ⟨c.val.1, h1⟩) := fun h2 => h ((mem_dg q (il_anti hq) c.val).2 ⟨h1, h2⟩)
    rw [← hc ⟨c.val.1, h1⟩] at h2
    have h3 : ¬ (T c).val < d := fun h3 => h2 ((cntR_spec μ T hT c).1 h3)
    apply Fin.ext
    have := (T c).isLt
    simp only [Fin.val_last]
    omega
  · exact last_row μ T hT c h1

lemma toSmall_val {d : ℕ} {μ : YoungDiagram} {q : Fin d → ℕ} (hq : q ∈ IL d μ)
    (T : μ.cells → Fin (d+1)) (hT : SS μ T) (hc : ∀ i : Fin d, cntR μ T i = q i)
    (a : (dg q (il_anti hq)).cells) :
    (toSmall hq T a).val = (T ⟨a.val, dg_sub hq a.val a.2⟩).val := by
  unfold toSmall
  rw [dif_pos (lt_d_of_mem hq T hT hc ⟨a.val, dg_sub hq a.val a.2⟩ a.2)]

lemma toSmall_ss {d : ℕ} {μ : YoungDiagram} {q : Fin d → ℕ} (hq : q ∈ IL d μ)
    (T : μ.cells → Fin (d+1)) (hT : SS μ T) (hc : ∀ i : Fin d, cntR μ T i = q i) :
    SS (dg q (il_anti hq)) (toSmall hq T) := by
  intro a b
  have ha := toSmall_val hq T hT hc a
  have hb := toSmall_val hq T hT hc b
  have hab := hT ⟨a.val, dg_sub hq a.val a.2⟩ ⟨b.val, dg_sub hq b.val b.2⟩
  constructor
  · intro h1 h2
    have := hab.1 h1 h2
    rw [Fin.le_iff_val_le_val, ha, hb]
    exact this
  · intro h1 h2
    have := hab.2 h1 h2
    rw [Fin.lt_iff_val_lt_val, ha, hb]
    exact this

lemma toBig_ss {d : ℕ} {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ d + 1) {q : Fin d → ℕ} (hq : q ∈ IL d μ)
    (T : (dg q (il_anti hq)).cells → Fin d) (hT : SS (dg q (il_anti hq)) T) :
    SS μ (toBig hq T) := by
  intro a b
  constructor
  · intro h1 h2
    unfold toBig
    by_cases hb : b.val ∈ dg q (il_anti hq)
    · have ha : a.val ∈ dg q (il_anti hq) :=
        (dg q (il_anti hq)).isLowerSet (show a.val ≤ b.val from ⟨le_of_eq h1, h2.le⟩) hb
      rw [dif_pos ha, dif_pos hb, Fin.castSucc_le_castSucc_iff]
      exact (hT ⟨a.val, ha⟩ ⟨b.val, hb⟩).1 h1 h2
    · rw [dif_neg hb]; exact Fin.le_last _
  · intro h1 h2
    unfold toBig
    have ha : a.val ∈ dg q (il_anti hq) := by
      have hbd := row_le_d hμ b
      have had : a.val.1 < d := by omega
      refine (mem_dg q (il_anti hq) a.val).2 ⟨had, ?_⟩
      simp only [IL, Fintype.mem_piFinset, Finset.mem_Icc] at hq
      have h3 := (hq ⟨a.val.1, had⟩).1
      have h4 : b.val.2 < μ.rowLen b.val.1 := YoungDiagram.mem_iff_lt_rowLen.1 b.2
      have h5 : μ.rowLen b.val.1 ≤ μ.rowLen (a.val.1 + 1) := μ.rowLen_anti _ _ (by omega)
      simp only at h3
      omega
    rw [dif_pos ha]
    by_cases hb : b.val ∈ dg q (il_anti hq)
    · rw [dif_pos hb, Fin.castSucc_lt_castSucc_iff]
      exact (hT ⟨a.val, ha⟩ ⟨b.val, hb⟩).2 h1 h2
    · rw [dif_neg hb]; exact Fin.castSucc_lt_last _

lemma cnt_toBig {d : ℕ} {μ : YoungDiagram} {q : Fin d → ℕ} (hq : q ∈ IL d μ)
    (T : (dg q (il_anti hq)).cells → Fin d) (i : Fin d) : cntR μ (toBig hq T) i = q i := by
  classical
  unfold cntR
  have hqi : q i ≤ μ.rowLen i := by
    simp only [IL, Fintype.mem_piFinset, Finset.mem_Icc] at hq; exact (hq i).2
  have : (Finset.range (μ.rowLen i)).filter (fun j => ∃ h : ((i : ℕ), j) ∈ μ,
      (toBig hq T ⟨((i : ℕ), j), h⟩).val < d) = Finset.range (q i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, h, h2⟩
      unfold toBig at h2
      by_cases hm : ((i : ℕ), j) ∈ dg q (il_anti hq)
      · obtain ⟨_, h3⟩ := (mem_dg q (il_anti hq) _).1 hm
        simpa using h3
      · rw [dif_neg hm] at h2; simp at h2
    · intro hj
      have hm : ((i : ℕ), j) ∈ dg q (il_anti hq) := (mem_dg q (il_anti hq) _).2 ⟨i.isLt, by simpa using hj⟩
      refine ⟨by omega, dg_sub hq _ hm, ?_⟩
      unfold toBig
      rw [dif_pos hm]
      simp
  rw [this, Finset.card_range]

lemma toBig_toSmall {d : ℕ} {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ d + 1) {q : Fin d → ℕ}
    (hq : q ∈ IL d μ) (T : μ.cells → Fin (d+1)) (hT : SS μ T) (hc : ∀ i : Fin d, cntR μ T i = q i) :
    toBig hq (toSmall hq T) = T := by
  funext c
  unfold toBig
  by_cases h : c.val ∈ dg q (il_anti hq)
  · rw [dif_pos h]
    apply Fin.ext
    rw [Fin.val_castSucc, toSmall_val hq T hT hc]
  · rw [dif_neg h, eq_last_of_not_mem hμ hq T hT hc c h]

lemma toSmall_toBig {d : ℕ} {μ : YoungDiagram} {q : Fin d → ℕ} (hq : q ∈ IL d μ)
    (T : (dg q (il_anti hq)).cells → Fin d) : toSmall hq (toBig hq T) = T := by
  funext a
  simp [toSmall, toBig, a.2]

lemma weight_split {R : Type*} [CommRing R] {d : ℕ} {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ d + 1)
    {q : Fin d → ℕ} (hq : q ∈ IL d μ) (T : μ.cells → Fin (d+1)) (hT : SS μ T)
    (hc : ∀ i : Fin d, cntR μ T i = q i) (x : Fin (d+1) → R) :
    ∏ c : μ.cells, x (T c) =
      (∏ a : (dg q (il_anti hq)).cells, (x ∘ Fin.castSucc) (toSmall hq T a)) *
        x (Fin.last d) ^ (μ.card - ∑ i, q i) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun c : μ.cells => c.val ∈ dg q (il_anti hq))]
  have hcard : (Finset.univ.filter (fun c : μ.cells => c.val ∈ dg q (il_anti hq))).card =
      (dg q (il_anti hq)).card := by
    show _ = (dg q (il_anti hq)).cells.card
    rw [← Finset.card_attach (s := (dg q (il_anti hq)).cells)]
    refine Finset.card_bij' (fun c hc => ⟨c.val, (Finset.mem_filter.1 hc).2⟩)
      (fun a _ => ⟨a.val, dg_sub hq a.val a.2⟩) (fun _ _ => Finset.mem_attach _ _)
      (fun a _ => by simp [a.2]) (fun _ _ => rfl) (fun _ _ => rfl)
  congr 1
  · refine Finset.prod_bij' (fun c hc => ⟨c.val, (Finset.mem_filter.1 hc).2⟩)
      (fun a _ => ⟨a.val, dg_sub hq a.val a.2⟩) (fun _ _ => Finset.mem_univ _)
      (fun a _ => by simp [a.2]) (fun _ _ => rfl) (fun _ _ => rfl) ?_
    intro c hcm
    simp only [Function.comp_apply]
    congr 1
    apply Fin.ext
    rw [Fin.val_castSucc, toSmall_val hq T hT hc]
  · rw [Finset.prod_congr rfl (fun c hcm => by
      rw [eq_last_of_not_mem hμ hq T hT hc c (Finset.mem_filter.1 hcm).2]), Finset.prod_const]
    congr 1
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset μ.cells))
      (fun c : μ.cells => c.val ∈ dg q (il_anti hq))
    rw [hcard, dg_card, Finset.card_univ] at h1
    have h2 : Fintype.card μ.cells = μ.card := by
      rw [Fintype.card_coe]
    omega

/-- **horizontal strip branching** of Schur polynomials -/
theorem sev_branch {R : Type*} [CommRing R] (d : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ d + 1)
    (x : Fin (d+1) → R) :
    sev (d+1) μ x = ∑ q ∈ IL d μ, (if hq : Antitone q then sev d (dg q hq) (x ∘ Fin.castSucc) else 0) *
      x (Fin.last d) ^ (μ.card - ∑ i, q i) := by
  classical
  unfold sev
  have hmaps : ∀ T ∈ ssytF (d+1) μ, (fun i : Fin d => cntR μ T i) ∈ IL d μ := by
    intro T hT
    have hT' : SS μ T := (Finset.mem_filter.1 hT).2
    simp only [IL, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    exact ⟨cntR_ge μ T hT' i, cntR_le μ T i⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [dif_pos (il_anti hq), Finset.sum_mul]
  refine Finset.sum_nbij' (fun T => toSmall hq T) (fun T' => toBig hq T') ?_ ?_ ?_ ?_ ?_
  · intro T hT
    simp only [Finset.mem_filter, ssytF, Finset.mem_univ, true_and] at hT ⊢
    exact toSmall_ss hq T hT.1 (fun i => congrFun hT.2 i)
  · intro T' hT'
    simp only [Finset.mem_filter, ssytF, Finset.mem_univ, true_and] at hT' ⊢
    exact ⟨toBig_ss hμ hq T' hT', funext (fun i => cnt_toBig hq T' i)⟩
  · intro T hT
    simp only [Finset.mem_filter, ssytF, Finset.mem_univ, true_and] at hT
    exact toBig_toSmall hμ hq T hT.1 (fun i => congrFun hT.2 i)
  · intro T' _
    exact toSmall_toBig hq T'
  · intro T hT
    simp only [Finset.mem_filter, ssytF, Finset.mem_univ, true_and] at hT
    exact weight_split hμ hq T hT.1 (fun i => congrFun hT.2 i) x

end KeylS

-- ===== KS3 =====

set_option autoImplicit false
open scoped BigOperators

noncomputable section

namespace KeylS

/-- the staircase exponent -/
def dl (d : ℕ) : Fin d → ℕ := fun j => d - 1 - j

lemma rows_anti (d : ℕ) (μ : YoungDiagram) : Antitone (fun i : Fin d => μ.rowLen i) :=
  fun i i' h => μ.rowLen_anti _ _ (Fin.le_iff_val_le_val.1 h)

lemma diagram_eq_dg (d : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ d) :
    μ = dg (fun i : Fin d => μ.rowLen i) (rows_anti d μ) := by
  ext c
  show c ∈ μ ↔ c ∈ dg _ _
  rw [mem_dg]
  constructor
  · intro hc
    have h1 : c.1 < μ.colLen c.2 := YoungDiagram.mem_iff_lt_colLen.1 hc
    have h2 : μ.colLen c.2 ≤ μ.colLen 0 := μ.colLen_anti 0 c.2 (Nat.zero_le _)
    exact ⟨by omega, YoungDiagram.mem_iff_lt_rowLen.1 hc⟩
  · rintro ⟨_, h2⟩
    exact YoungDiagram.mem_iff_lt_rowLen.2 h2

lemma card_eq_sum_rows (d : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ d) :
    μ.card = ∑ i : Fin d, μ.rowLen i := by
  conv_lhs => rw [diagram_eq_dg d μ hμ]
  rw [dg_card]

lemma sev_zero {R : Type*} [CommRing R] (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ 0) (x : Fin 0 → R) :
    sev 0 μ x = 1 := by
  classical
  have hempty : ∀ c : μ.cells, False := by
    intro c
    have h1 : c.val.1 < μ.colLen c.val.2 := YoungDiagram.mem_iff_lt_colLen.1 c.2
    have h2 : μ.colLen c.val.2 ≤ μ.colLen 0 := μ.colLen_anti 0 c.val.2 (Nat.zero_le _)
    omega
  have : IsEmpty μ.cells := ⟨hempty⟩
  unfold sev ssytF
  have : (Finset.univ.filter (SS (d := 0) μ)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro T _ a
    exact (hempty a).elim
  rw [this]
  simp

lemma alt_zero {R : Type*} [CommRing R] (e : Fin 0 → ℕ) (x : Fin 0 → R) : alt e x = 1 := by
  unfold alt
  simp

lemma alt_dl_succ {R : Type*} [CommRing R] (d : ℕ) (x : Fin (d+1) → R) :
    alt (dl (d+1)) x = (∏ i : Fin d, (x i.castSucc - x (Fin.last d))) * alt (dl d) (x ∘ Fin.castSucc) := by
  rw [alt_branch (dl (d+1)) (fun j => by simp [dl]; omega) x]
  congr 1
  have hbox : Fintype.piFinset (fun j : Fin d => Finset.Ico (dl (d+1) j.succ) (dl (d+1) j.castSucc)) =
      {dl d} := by
    ext p
    simp only [Fintype.mem_piFinset, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · intro h; funext j; have := h j; simp [dl] at this ⊢; omega
    · rintro rfl j; simp [dl]; omega
  rw [hbox, Finset.sum_singleton]
  have : dl (d+1) (Fin.last d) + ∑ j : Fin d, (dl (d+1) j.castSucc - dl d j - 1) = 0 := by
    simp only [dl, Fin.val_last, Fin.val_castSucc]
    rw [Finset.sum_eq_zero (fun j _ => by omega)]
    omega
  rw [this, pow_zero, one_mul]

/-- **bialternant formula** for semistandard-tableau Schur polynomials -/
theorem bialt {R : Type*} [CommRing R] (d : ℕ) :
    ∀ (μ : YoungDiagram), μ.colLen 0 ≤ d → ∀ x : Fin d → R,
      sev d μ x * alt (dl d) x = alt (fun j => μ.rowLen j + dl d j) x := by
  induction d with
  | zero =>
    intro μ hμ x
    rw [sev_zero μ hμ, alt_zero, alt_zero, one_mul]
  | succ d ih =>
    intro μ hμ x
    rw [sev_branch d μ hμ x, alt_dl_succ]
    rw [alt_branch (fun j => μ.rowLen j + dl (d+1) j) (fun j => by
      have := μ.rowLen_anti (j : ℕ) ((j : ℕ) + 1) (Nat.le_succ _)
      simp only [dl, Fin.val_succ, Fin.val_castSucc]
      omega) x]
    set t := x (Fin.last d) with ht
    set P := ∏ i : Fin d, (x i.castSucc - t) with hP
    have hL : (∑ q ∈ IL d μ, (if hq : Antitone q then sev d (dg q hq) (x ∘ Fin.castSucc) else 0) *
        t ^ (μ.card - ∑ i, q i)) * (P * alt (dl d) (x ∘ Fin.castSucc)) =
        P * ∑ q ∈ IL d μ, t ^ (μ.card - ∑ i, q i) * alt (fun j => q j + dl d j) (x ∘ Fin.castSucc) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun q hq => ?_)
      rw [dif_pos (il_anti hq)]
      have h := ih (dg q (il_anti hq)) (dg_colLen _ _) (x ∘ Fin.castSucc)
      have hr : (fun j : Fin d => (dg q (il_anti hq)).rowLen j + dl d j) = fun j => q j + dl d j := by
        funext j; rw [dg_rowLen]
      rw [hr] at h
      rw [← h]
      ring
    rw [hL]
    congr 1
    have hcard := card_eq_sum_rows (d+1) μ hμ
    rw [Fin.sum_univ_castSucc] at hcard
    refine Finset.sum_nbij' (fun q j => q j + dl d j) (fun p j => p j - dl d j) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [IL, Fintype.mem_piFinset, Finset.mem_Icc] at hq
      simp only [Fintype.mem_piFinset, Finset.mem_Ico]
      intro j
      have := hq j
      simp only [dl, Fin.val_succ, Fin.val_castSucc] at this ⊢
      omega
    · intro p hp
      simp only [Fintype.mem_piFinset, Finset.mem_Ico] at hp
      simp only [IL, Fintype.mem_piFinset, Finset.mem_Icc]
      intro j
      have := hp j
      simp only [dl, Fin.val_succ, Fin.val_castSucc] at this ⊢
      omega
    · intro q hq
      funext j; simp
    · intro p hp
      simp only [Fintype.mem_piFinset, Finset.mem_Ico] at hp
      funext j
      have := hp j
      simp only [dl, Fin.val_succ, Fin.val_castSucc] at this ⊢
      omega
    · intro q hq
      simp only [IL, Fintype.mem_piFinset, Finset.mem_Icc] at hq
      congr 2
      have hsum : ∑ j : Fin d, (μ.rowLen ((j.castSucc : Fin (d+1)) : ℕ) + dl (d+1) j.castSucc -
          (q j + dl d j) - 1) = ∑ j : Fin d, (μ.rowLen (j : ℕ) - q j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [dl, Fin.val_castSucc]
        omega
      have hsum2 : ∑ j : Fin d, (μ.rowLen (j : ℕ) - q j) + ∑ j : Fin d, q j =
          ∑ j : Fin d, μ.rowLen (j : ℕ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have := (hq j).2
        omega
      rw [hsum]
      simp only [dl, Fin.val_last, Fin.val_castSucc] at hcard ⊢
      omega

end KeylS

-- ===== KS4 =====

set_option autoImplicit false
open scoped BigOperators

noncomputable section

namespace KeylS

variable {d : ℕ}

/-- polynomial alternant -/
def Al (e : Fin d → ℕ) : MvPolynomial (Fin d) ℝ :=
  (Matrix.of fun i j => (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ e j).det

lemma Al_eval (e : Fin d → ℕ) (x : Fin d → ℝ) : MvPolynomial.eval x (Al e) = alt e x := by
  unfold Al alt
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

lemma alt_eq_zero {R : Type*} [CommRing R] (e : Fin d → ℕ) (x : Fin d → R) {a b : Fin d} (hab : a ≠ b)
    (he : e a = e b) : alt e x = 0 := by
  unfold alt
  exact Matrix.det_zero_of_column_eq hab (fun i => by simp [he])

lemma Al_eq_zero (e : Fin d → ℕ) {a b : Fin d} (hab : a ≠ b) (he : e a = e b) : Al e = 0 :=
  alt_eq_zero (R := MvPolynomial (Fin d) ℝ) e MvPolynomial.X hab he

/-- the polynomial Schur function -/
def sP (μ : YoungDiagram) : MvPolynomial (Fin d) ℝ := sev d μ MvPolynomial.X

lemma sP_eval (μ : YoungDiagram) (x : Fin d → ℝ) : MvPolynomial.eval x (sP (d := d) μ) = sev d μ x := by
  unfold sP sev
  simp [map_sum, map_prod]

lemma bialtP (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ d) :
    sP μ * Al (dl d) = Al (fun j => μ.rowLen j + dl d j) :=
  bialt d μ hμ MvPolynomial.X

/-- Jacobi's trick: multiplication of an alternant by the first power sum -/
lemma alt_pieri {R : Type*} [CommRing R] (e : Fin d → ℕ) (x : Fin d → R) :
    (∑ i, x i) * alt e x = ∑ k, alt (e + Pi.single k 1) x := by
  unfold alt
  simp only [Matrix.det_apply, Matrix.of_apply]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [← Finset.smul_sum, mul_smul_comm]
  congr 1
  have h1 : ∑ i, x i = ∑ k, x (σ k) := (Equiv.sum_comp σ x).symm
  rw [h1, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hk : ∏ i, x (σ i) ^ (e + Pi.single k 1 : Fin d → ℕ) i = x (σ k) * ∏ i, x (σ i) ^ e i := by
    have h2 : ∀ i, x (σ i) ^ (e + Pi.single k 1 : Fin d → ℕ) i =
        x (σ i) ^ e i * (if i = k then x (σ i) else 1) := by
      intro i
      by_cases h : i = k
      · subst h; simp [pow_succ]
      · simp [Pi.single_eq_of_ne h, h]
    rw [Finset.prod_congr rfl (fun i _ => h2 i), Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k]
    simp only [Finset.mem_univ, if_true]
    ring
  rw [hk]

lemma Al_pieri (e : Fin d → ℕ) :
    (∑ i, (MvPolynomial.X i : MvPolynomial (Fin d) ℝ)) * Al e = ∑ k, Al (e + Pi.single k 1) :=
  alt_pieri (R := MvPolynomial (Fin d) ℝ) e MvPolynomial.X

/-- exponent vector as a finsupp -/
def fs (m : Fin d → ℕ) : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm m

lemma prod_X_pow_perm (e : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) :
    ∏ j, (MvPolynomial.X (σ j) : MvPolynomial (Fin d) ℝ) ^ e j =
      MvPolynomial.monomial (fs (fun i => e (σ.symm i))) 1 := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun i => by simp)]
  rw [← Equiv.prod_comp σ (fun i => (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ (fs (fun i => e (σ.symm i))) i)]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp [fs]

lemma Al_expand (e : Fin d → ℕ) :
    Al e = ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℝ) •
      MvPolynomial.monomial (fs (fun i => e (σ.symm i))) (1 : ℝ) := by
  unfold Al
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [Matrix.of_apply]
  rw [prod_X_pow_perm]
  rw [Units.smul_def]
  norm_cast

lemma perm_eq_one_of_strictAnti {e : Fin d → ℕ} (he : StrictAnti e) (τ : Equiv.Perm (Fin d))
    (h : StrictAnti (fun i => e (τ i))) : τ = 1 := by
  have hm : StrictMono τ := by
    intro a b hab
    have := h hab
    exact he.lt_iff_gt.1 this
  have hm' : StrictMono τ.symm := by
    intro a b hab
    by_contra hc
    push_neg at hc
    rcases lt_or_eq_of_le hc with hc | hc
    · have := hm hc; simp at this; exact absurd hab (not_lt.2 this.le)
    · have := congrArg τ hc; simp at this; exact absurd hab (by rw [this]; exact lt_irrefl _)
  ext i
  have h1 := hm.id_le i
  have h2 := hm'.id_le (τ i)
  simp at h1 h2
  exact congrArg Fin.val (le_antisymm h2 h1)

lemma coeff_Al {e m : Fin d → ℕ} (he : StrictAnti e) (hm : StrictAnti m) :
    MvPolynomial.coeff (fs m) (Al e) = if e = m then 1 else 0 := by
  rw [Al_expand, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, smul_eq_mul]
  rw [Finset.sum_eq_single 1]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_symm,
      Equiv.Perm.coe_one, id_eq]
    by_cases h : e = m
    · subst h; simp
    · rw [if_neg h]
      split_ifs with h'
      · exfalso; apply h; funext i; have := congrArg (fun f => f i) h'; simpa [fs] using this
      · exact if_neg h'
  · intro σ _ hσ
    rw [if_neg, mul_zero]
    intro h'
    have hfun : (fun i => e (σ.symm i)) = m := by
      funext i
      have := congrArg (fun f => f i) h'
      simpa [fs] using this
    apply hσ
    have := perm_eq_one_of_strictAnti he σ.symm (by rw [hfun]; exact hm)
    rw [← inv_inv σ, ← Equiv.Perm.inv_def] at this
    simpa using this
  · intro h; exact absurd (Finset.mem_univ _) h

/-- the operator `Σ ∂_i` -/
def Ed (d : ℕ) : Derivation ℝ (MvPolynomial (Fin d) ℝ) (MvPolynomial (Fin d) ℝ) :=
  ∑ i, MvPolynomial.pderiv i

/-- the Euler operators `θ_i = X_i ∂_i` -/
def th (i : Fin d) : Derivation ℝ (MvPolynomial (Fin d) ℝ) (MvPolynomial (Fin d) ℝ) :=
  (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) • MvPolynomial.pderiv i

lemma fs_sub_single (v : Fin d → ℕ) (i : Fin d) :
    fs v - Finsupp.single i 1 = fs (v - Pi.single i 1) := by
  ext j
  simp only [fs, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_equivFunOnFinite_symm]
  by_cases h : j = i
  · subst h; simp
  · simp [Finsupp.single_apply, Ne.symm h]

lemma der_sum_apply {ι : Type*} (S : Finset ι)
    (D : ι → Derivation ℝ (MvPolynomial (Fin d) ℝ) (MvPolynomial (Fin d) ℝ)) (p : MvPolynomial (Fin d) ℝ) :
    (∑ i ∈ S, D i) p = ∑ i ∈ S, D i p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Derivation.zero_apply]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

lemma Ed_monomial (v : Fin d → ℕ) (c : ℝ) :
    Ed d (MvPolynomial.monomial (fs v) c) =
      ∑ i, MvPolynomial.monomial (fs (v - Pi.single i 1)) (c * v i) := by
  unfold Ed
  rw [der_sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MvPolynomial.pderiv_monomial, fs_sub_single]
  rfl

lemma Ed_Al (e : Fin d → ℕ) : Ed d (Al e) = ∑ j, (e j : ℝ) • Al (e - Pi.single j 1) := by
  rw [Al_expand, map_sum]
  simp_rw [Al_expand, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [(Ed d).map_smul, Ed_monomial, Finset.smul_sum]
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [MvPolynomial.smul_monomial]
  have hm : fs ((fun i => e (σ.symm i)) - Pi.single (σ j) 1) =
      fs (fun i => (e - Pi.single j 1 : Fin d → ℕ) (σ.symm i)) := by
    congr 1
    funext i
    by_cases h : i = σ j
    · subst h; simp
    · have h' : σ.symm i ≠ j := fun e => h (by rw [← e]; simp)
      simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
  rw [hm]
  congr 1
  simp [smul_eq_mul]
  ring

lemma Ed_Al_dl : Ed d (Al (dl d)) = 0 := by
  rw [Ed_Al]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  by_cases hj : j.val + 1 < d
  · rw [Al_eq_zero (dl d - Pi.single j 1) (a := j) (b := ⟨j.val + 1, hj⟩)
      (fun e => by have := congrArg Fin.val e; simp at this) (by
        have h1 : (⟨j.val + 1, hj⟩ : Fin d) ≠ j := fun e => by have := congrArg Fin.val e; simp at this
        simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h1, dl]
        omega), smul_zero]
  · have : dl d j = 0 := by simp only [dl]; omega
    rw [this]; simp

lemma th_apply (i : Fin d) (p : MvPolynomial (Fin d) ℝ) :
    th i p = MvPolynomial.X i * MvPolynomial.pderiv i p := by
  simp [th, Derivation.smul_apply, smul_eq_mul]

lemma th_monomial (i : Fin d) (v : Fin d → ℕ) (c : ℝ) :
    th i (MvPolynomial.monomial (fs v) c) = MvPolynomial.monomial (fs v) (c * v i) := by
  rw [th_apply, MvPolynomial.pderiv_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
  by_cases h : v i = 0
  · simp [fs, h]
  · have he : Finsupp.single i 1 + (fs v - Finsupp.single i 1) = fs v := by
      ext j
      simp only [fs, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.coe_equivFunOnFinite_symm]
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hj]
    rw [he]
    simp [fs]

/-- the second-order operator `Σ θ_i²` -/
def D2 (p : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ := ∑ i, th i (th i p)

lemma D2_Al (e : Fin d → ℕ) : D2 (Al e) = (∑ j, ((e j : ℝ)) ^ 2) • Al e := by
  unfold D2
  rw [Al_expand]
  simp only [map_sum, Derivation.map_smul, th_monomial]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [← Finset.smul_sum, smul_comm]
  congr 1
  rw [MvPolynomial.smul_monomial, ← map_sum]
  congr 1
  have h := Equiv.sum_comp σ.symm (fun j => ((e j : ℝ)) ^ 2)
  simp only [one_mul, smul_eq_mul, mul_one]
  rw [← h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [sq]

/-- `Σ X_i θ_i` -/
def Xth (p : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ := ∑ i, MvPolynomial.X i * th i p

lemma Xth_Al (e : Fin d → ℕ) : Xth (Al e) = ∑ j, (e j : ℝ) • Al (e + Pi.single j 1) := by
  unfold Xth
  rw [Al_expand]
  simp only [map_sum, Derivation.map_smul, th_monomial, Finset.mul_sum, mul_smul_comm]
  conv_lhs => rw [Finset.sum_comm]
  simp_rw [Al_expand, Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, smul_comm]
  simp only [MvPolynomial.smul_monomial]
  have hm : Finsupp.single (σ j) 1 + fs (fun i => e (σ.symm i)) =
      fs (fun i => (e + Pi.single j 1 : Fin d → ℕ) (σ.symm i)) := by
    ext i
    simp only [fs, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_equivFunOnFinite_symm]
    by_cases h : i = σ j
    · subst h; simp; ring
    · have h' : σ.symm i ≠ j := fun e => h (by rw [← e]; simp)
      simp [Finsupp.single_apply, Ne.symm h, Pi.single_eq_of_ne h']
  rw [hm]
  congr 1
  simp [smul_eq_mul]

lemma D2_mul (F G : MvPolynomial (Fin d) ℝ) :
    D2 (F * G) = D2 F * G + 2 * ∑ i, th i F * th i G + F * D2 G := by
  unfold D2
  simp only [Derivation.leibniz, smul_eq_mul, map_add]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- power sums -/
def p1 (d : ℕ) : MvPolynomial (Fin d) ℝ := ∑ i, MvPolynomial.X i
def p2 (d : ℕ) : MvPolynomial (Fin d) ℝ := ∑ i, MvPolynomial.X i ^ 2

lemma th_X (i j : Fin d) : th i (MvPolynomial.X j : MvPolynomial (Fin d) ℝ) =
    if i = j then MvPolynomial.X i else 0 := by
  rw [th_apply, MvPolynomial.pderiv_X]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Pi.single_eq_of_ne (Ne.symm h)]

lemma th_p1 (i : Fin d) : th i (p1 d) = MvPolynomial.X i := by
  unfold p1
  rw [map_sum, Finset.sum_eq_single i]
  · rw [th_X, if_pos rfl]
  · intro j _ hj; rw [th_X, if_neg (Ne.symm hj)]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma th_p1_pow (i : Fin d) (n : ℕ) :
    th i (p1 d ^ n) = (n : MvPolynomial (Fin d) ℝ) * p1 d ^ (n - 1) * MvPolynomial.X i := by
  rw [Derivation.leibniz_pow, th_p1, nsmul_eq_mul, smul_eq_mul, mul_assoc]

lemma D2_p1_pow (n : ℕ) :
    D2 (p1 d ^ n) = ((n * (n - 1) : ℕ) : MvPolynomial (Fin d) ℝ) * p1 d ^ (n - 2) * p2 d +
      (n : MvPolynomial (Fin d) ℝ) * p1 d ^ n := by
  unfold D2
  simp_rw [th_p1_pow]
  have h1 : ∀ i : Fin d, th i ((n : MvPolynomial (Fin d) ℝ) * p1 d ^ (n - 1) * MvPolynomial.X i) =
      (n : MvPolynomial (Fin d) ℝ) * (((n - 1 : ℕ) : MvPolynomial (Fin d) ℝ) * p1 d ^ (n - 1 - 1) *
        MvPolynomial.X i * MvPolynomial.X i + p1 d ^ (n - 1) * MvPolynomial.X i) := by
    intro i
    rw [Derivation.leibniz, Derivation.leibniz, th_X, if_pos rfl, th_p1_pow]
    have : th i (n : MvPolynomial (Fin d) ℝ) = 0 := by
      rw [show (n : MvPolynomial (Fin d) ℝ) = MvPolynomial.C (n : ℝ) by simp]
      exact (th i).map_algebraMap _
    rw [this]
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring
  simp_rw [h1]
  have e1 : ∑ x : Fin d, ((n - 1 : ℕ) : MvPolynomial (Fin d) ℝ) * p1 d ^ (n - 1 - 1) *
      MvPolynomial.X x * MvPolynomial.X x = ((n - 1 : ℕ) : MvPolynomial (Fin d) ℝ) * p1 d ^ (n - 1 - 1) * p2 d := by
    unfold p2; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _ => by ring)
  have e2 : ∑ x : Fin d, p1 d ^ (n - 1) * MvPolynomial.X x = p1 d ^ (n - 1) * p1 d := by
    unfold p1; rw [Finset.mul_sum]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, e1, e2]
  rcases n with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [show m + 1 - 2 = m - 1 by omega, ← pow_succ]
    push_cast
    ring

lemma Xth_Al_dl : Xth (Al (dl d)) = ((d - 1 : ℕ) : ℝ) • (p1 d * Al (dl d)) := by
  rcases d with _ | d
  · simp [Xth, p1]
  · rw [Xth_Al, p1, Al_pieri]
    rw [Finset.sum_eq_single (0 : Fin (d+1)), Finset.smul_sum, Finset.sum_eq_single (0 : Fin (d+1))]
    · simp [dl]
    · intro k _ hk
      have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
      rw [Al_eq_zero _ (a := k) (b := ⟨k.val - 1, by omega⟩)
        (fun e => by have := congrArg Fin.val e; simp at this; omega) (by
          have h1 : (⟨k.val - 1, by omega⟩ : Fin (d+1)) ≠ k := fun e => by
            have := congrArg Fin.val e; simp at this; omega
          simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h1, dl]
          omega), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro k _ hk
      have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
      rw [Al_eq_zero _ (a := k) (b := ⟨k.val - 1, by omega⟩)
        (fun e => by have := congrArg Fin.val e; simp at this; omega) (by
          have h1 : (⟨k.val - 1, by omega⟩ : Fin (d+1)) ≠ k := fun e => by
            have := congrArg Fin.val e; simp at this; omega
          simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h1, dl]
          omega), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma D2_main (n : ℕ) :
    D2 (p1 d ^ n * Al (dl d)) =
      (((n * (n - 1) : ℕ) : MvPolynomial (Fin d) ℝ) * p1 d ^ (n - 2) * p2 d +
        (((n + 2 * n * (d - 1) : ℕ) : ℝ) + ∑ j, ((dl d j : ℝ)) ^ 2) • p1 d ^ n) * Al (dl d) := by
  rw [D2_mul, D2_p1_pow, D2_Al]
  simp_rw [th_p1_pow]
  have h2 : ∑ i : Fin d, (n : MvPolynomial (Fin d) ℝ) * p1 d ^ (n - 1) * MvPolynomial.X i * th i (Al (dl d)) =
      (n : MvPolynomial (Fin d) ℝ) * p1 d ^ (n - 1) * Xth (Al (dl d)) := by
    unfold Xth; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)
  rw [h2, Xth_Al_dl]
  rcases n with _ | m
  · simp
  · rw [show m + 1 - 1 = m by omega]
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    push_cast
    rw [pow_succ]
    simp only [map_add, map_mul, map_natCast, map_sum, map_pow, MvPolynomial.C_1, map_ofNat]
    ring

/-- homogeneity at `1`: Euler's identity -/
lemma eval_Ed_prod {ι : Type*} (S : Finset ι) (g : ι → Fin d) :
    MvPolynomial.eval (fun _ => (1 : ℝ)) (Ed d (∏ a ∈ S, MvPolynomial.X (g a))) = S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Derivation.map_one_eq_zero]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, Finset.card_insert_of_notMem ha]
    have hX : Ed d (MvPolynomial.X (g a) : MvPolynomial (Fin d) ℝ) = 1 := by
      unfold Ed
      rw [der_sum_apply, Finset.sum_eq_single (g a)]
      · simp
      · intro i _ hi; rw [MvPolynomial.pderiv_X]; simp [Pi.single_eq_of_ne (Ne.symm hi)]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [smul_eq_mul, map_add, map_mul, hX, map_one, MvPolynomial.eval_X, ih, map_prod]
    simp

lemma eval_Ed_sP (μ : YoungDiagram) :
    MvPolynomial.eval (fun _ => (1 : ℝ)) (Ed d (sP (d := d) μ)) =
      μ.card * MvPolynomial.eval (fun _ => (1 : ℝ)) (sP (d := d) μ) := by
  unfold sP sev
  rw [map_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [eval_Ed_prod]
  simp only [map_prod, MvPolynomial.eval_X, Finset.prod_const_one, mul_one, Finset.card_univ]
  congr 1
  rw [Fintype.card_coe]

lemma Al_ne_zero : Al (dl d) ≠ 0 := by
  intro h
  have := coeff_Al (e := dl d) (m := dl d) (fun i j hij => by simp only [dl]; omega)
    (fun i j hij => by simp only [dl]; omega)
  rw [h, if_pos rfl] at this
  simp at this

/-- the row vector of a diagram -/
def rw' (d : ℕ) (μ : YoungDiagram) : Fin d → ℕ := fun i => μ.rowLen i

lemma anti_add_single (r : Fin d → ℕ) (hr : Antitone r) (k : Fin d)
    (hk : (k : ℕ) = 0 ∨ ∃ h : (k : ℕ) - 1 < d, r k < r ⟨(k : ℕ) - 1, h⟩) :
    Antitone (r + Pi.single k 1) := by
  intro a b hab
  simp only [Pi.add_apply]
  have h1 : r b ≤ r a := hr hab
  by_cases hb : b = k
  · subst hb
    by_cases ha : a = b
    · subst ha; exact le_rfl
    · have hlt : (a : ℕ) < b := lt_of_le_of_ne hab (fun e => ha (Fin.ext e))
      rcases hk with hk | ⟨h, hk⟩
      · omega
      · have h2 : r ⟨(b : ℕ) - 1, h⟩ ≤ r a := hr (show a ≤ ⟨(b : ℕ) - 1, h⟩ from by
          rw [Fin.le_iff_val_le_val]; simp; omega)
        simp [Pi.single_eq_of_ne ha]; omega
  · by_cases ha : a = k
    · subst ha; simp [Pi.single_eq_of_ne hb]; omega
    · simp [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb, h1]

/-- Pieri rule for Schur polynomials -/
lemma sP_pieri (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ d) :
    p1 d * sP μ = ∑ k : Fin d, if h : Antitone (rw' d μ + Pi.single k 1) then
      sP (dg (rw' d μ + Pi.single k 1) h) else 0 := by
  apply mul_right_cancel₀ (Al_ne_zero (d := d))
  rw [mul_assoc, bialtP μ hμ, p1, Al_pieri, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs with h
  · rw [bialtP _ (dg_colLen _ _)]
    congr 1
    funext j
    rw [dg_rowLen]
    simp [rw', add_comm, add_assoc]
  · rw [zero_mul]
    have hr : Antitone (rw' d μ) := rows_anti d μ
    have hk : (k : ℕ) ≠ 0 := fun hk0 => h (anti_add_single _ hr k (Or.inl hk0))
    have hk1 : (k : ℕ) - 1 < d := by omega
    have heq : rw' d μ k = rw' d μ ⟨(k : ℕ) - 1, hk1⟩ := by
      by_contra hne
      have h2 : rw' d μ k ≤ rw' d μ ⟨(k : ℕ) - 1, hk1⟩ := hr (by rw [Fin.le_iff_val_le_val]; simp)
      exact h (anti_add_single _ hr k (Or.inr ⟨hk1, lt_of_le_of_ne h2 hne⟩))
    have hne : (⟨(k : ℕ) - 1, hk1⟩ : Fin d) ≠ k := fun e => by
      have := congrArg Fin.val e; simp at this; omega
    refine Al_eq_zero _ (a := k) (b := ⟨(k : ℕ) - 1, hk1⟩) (Ne.symm hne) ?_
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, dl]
    simp only [rw'] at heq
    omega

lemma anti_sub_single (r : Fin d → ℕ) (hr : Antitone r) (k : Fin d) (hk1 : 1 ≤ r k)
    (hk : (k : ℕ) + 1 = d ∨ ∃ h : (k : ℕ) + 1 < d, r ⟨(k : ℕ) + 1, h⟩ < r k) :
    Antitone (r - Pi.single k 1) := by
  intro a b hab
  simp only [Pi.sub_apply]
  have h1 : r b ≤ r a := hr hab
  by_cases ha : a = k
  · subst ha
    by_cases hb : b = a
    · subst hb; exact le_rfl
    · have hlt : (a : ℕ) < b := lt_of_le_of_ne hab (fun e => hb (Fin.ext e.symm))
      rcases hk with hk | ⟨h, hk⟩
      · have := b.isLt; omega
      · have h2 : r b ≤ r ⟨(a : ℕ) + 1, h⟩ := hr (show (⟨(a : ℕ) + 1, h⟩ : Fin d) ≤ b from by
          rw [Fin.le_iff_val_le_val]; simp; omega)
        simp [Pi.single_eq_of_ne hb]; omega
  · by_cases hb : b = k
    · subst hb; simp [Pi.single_eq_of_ne ha]; omega
    · simp [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb, h1]

/-- the operator `Σ ∂_i` on Schur polynomials removes one box -/
lemma Ed_sP (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ d) :
    Ed d (sP μ) = ∑ j : Fin d, if h : Antitone (rw' d μ - Pi.single j 1) ∧ 1 ≤ rw' d μ j then
      ((rw' d μ j + dl d j : ℕ) : ℝ) • sP (dg (rw' d μ - Pi.single j 1) h.1) else 0 := by
  apply mul_right_cancel₀ (Al_ne_zero (d := d))
  have h1 : Ed d (sP μ) * Al (dl d) = Ed d (sP μ * Al (dl d)) := by
    rw [Derivation.leibniz, Ed_Al_dl, smul_zero, zero_add, smul_eq_mul, mul_comm]
  rw [h1, bialtP μ hμ, Ed_Al, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hr : Antitone (rw' d μ) := rows_anti d μ
  split_ifs with h
  · rw [smul_mul_assoc, bialtP _ (dg_colLen _ _)]
    congr 2
    funext j
    rw [dg_rowLen]
    by_cases hj : j = k
    · subst hj; simp [rw']; have := h.2; simp [rw'] at this; omega
    · simp [rw', Pi.single_eq_of_ne hj]
  · rw [zero_mul]
    by_cases hk1 : 1 ≤ rw' d μ k
    · -- not antitone after removal: equal next row
      have hlt : (k : ℕ) + 1 < d := by
        by_contra hc
        exact h ⟨anti_sub_single _ hr k hk1 (Or.inl (by have := k.isLt; omega)), hk1⟩
      have heq : rw' d μ ⟨(k : ℕ) + 1, hlt⟩ = rw' d μ k := by
        by_contra hne
        have h2 : rw' d μ ⟨(k : ℕ) + 1, hlt⟩ ≤ rw' d μ k := hr (by rw [Fin.le_iff_val_le_val]; simp)
        exact h ⟨anti_sub_single _ hr k hk1 (Or.inr ⟨hlt, lt_of_le_of_ne h2 hne⟩), hk1⟩
      have hne : (⟨(k : ℕ) + 1, hlt⟩ : Fin d) ≠ k := fun e => by
        have := congrArg Fin.val e; simp at this
      rw [Al_eq_zero _ (a := k) (b := ⟨(k : ℕ) + 1, hlt⟩) (Ne.symm hne) (by
        simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, dl]
        simp only [rw'] at heq hk1
        omega), smul_zero]
    · push_neg at hk1
      have hk0 : rw' d μ k = 0 := by omega
      by_cases hlt : (k : ℕ) + 1 < d
      · have h3 : rw' d μ ⟨(k : ℕ) + 1, hlt⟩ ≤ rw' d μ k := hr (by rw [Fin.le_iff_val_le_val]; simp)
        have hne : (⟨(k : ℕ) + 1, hlt⟩ : Fin d) ≠ k := fun e => by
          have := congrArg Fin.val e; simp at this
        rw [Al_eq_zero _ (a := k) (b := ⟨(k : ℕ) + 1, hlt⟩) (Ne.symm hne) (by
          simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, dl]
          simp only [rw'] at h3 hk0
          omega), smul_zero]
      · have : (μ.rowLen (k : ℕ) + dl d k : ℕ) = 0 := by
          simp only [rw'] at hk0; simp only [dl]; omega
        rw [show ((μ.rowLen (k : ℕ) + dl d k : ℕ) : ℝ) = 0 by exact_mod_cast this]
        simp

end KeylS

-- ===== KS5 =====

set_option autoImplicit false
open scoped BigOperators Matrix

noncomputable section

namespace KeylS
open QAlgorithms QAlgorithms.Schur

variable {d n : ℕ}

/-- dimension of the Specht module -/
def fP (lam : Partition d n) : ℝ := (Module.finrank ℂ (spechtSpace lam) : ℝ)

/-- row vector of a partition -/
def rv (lam : Partition d n) : Fin d → ℕ := rw' d lam.val

lemma rv_anti (lam : Partition d n) : Antitone (rv lam) := rows_anti d lam.val

lemma schurPoly_eq (lam : Partition d n) : schurPolynomial lam = sP lam.val := by
  unfold schurPolynomial sP sev ssytF
  rfl

lemma eval_schur (lam : Partition d n) (x : Fin d → ℝ) :
    MvPolynomial.eval x (schurPolynomial lam) = sev d lam.val x := by
  rw [schurPoly_eq, sP_eval]

lemma schurDim_sev (lam : Partition d n) : schurDimension lam = sev d lam.val (fun _ => 1) := by
  unfold schurDimension; rw [eval_schur]

lemma sum_rv (lam : Partition d n) : ∑ i, rv lam i = n := by
  unfold rv rw'
  rw [← card_eq_sum_rows d lam.val lam.property.2]
  exact lam.property.1

lemma trace_piKron_diag (x : Fin d → ℂ) :
    (piKron n (Matrix.diagonal x)).trace = (∑ i, x i) ^ n := by
  simp only [Matrix.trace, Matrix.diag, piKron, Matrix.of_apply, Matrix.diagonal_apply_eq]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (i : Fin d) => x i)]
  simp

lemma rowv_anti (n : ℕ) : Antitone (fun i : Fin d => if (i : ℕ) = 0 then n else 0) := by
  intro a b hab
  by_cases hb : (b : ℕ) = 0
  · have : (a : ℕ) = 0 := by have : (a : ℕ) ≤ b := hab; omega
    simp [hb, this]
  · simp [hb]

/-- a single-row partition -/
def rowP (hd : 0 < d) (n : ℕ) : Partition d n :=
  ⟨dg (fun i : Fin d => if (i : ℕ) = 0 then n else 0) (rowv_anti n),
    by
      rw [dg_card, Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
      · simp
      · intro b _ hb; have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h); simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h,
    dg_colLen _ _⟩

/-- **C0**: `Σ_λ dim Sp_λ · s_λ(x) = (Σ x)^n` -/
theorem C0 (hd : 0 < d) (x : Fin d → ℝ) :
    ∑ lam : Partition d n, fP lam * sev d lam.val x = (∑ i, x i) ^ n := by
  apply Complex.ofReal_injective
  push_cast
  have key : ∀ lam : Partition d n, (fP lam : ℂ) * ((sev d lam.val x : ℝ) : ℂ) =
      (piKron n (Matrix.diagonal (fun i => (x i : ℂ))) * isotypicProjector lam).trace := by
    intro lam
    rw [KWSpectrum.Estimator.eq_17]
    have h20 := KWSpectrum.Estimator.eq_20 lam 1 (one_mem _) x
    rw [Matrix.one_mul, star_one, Matrix.mul_one] at h20
    rw [h20, eval_schur, fP, mul_comm]
    push_cast
    ring
  simp_rw [key]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum,
    (KWSpectrum.Estimator.eq_2_4_projections (rowP hd n)).2.2.2.2.1, Matrix.mul_one,
    trace_piKron_diag]

lemma C0P (hd : 0 < d) :
    ∑ lam : Partition d n, fP lam • sP (d := d) lam.val = p1 d ^ n := by
  apply MvPolynomial.funext
  intro x
  simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, sP_eval, map_pow, p1,
    MvPolynomial.eval_X]
  exact C0 hd x

lemma dg_congr {q q' : Fin d → ℕ} (hq : Antitone q) (hq' : Antitone q') (h : q = q') :
    dg q hq = dg q' hq' := by subst h; rfl

lemma part_ext {m : ℕ} (μ ν : Partition d m) (h : rv μ = rv ν) : μ = ν := by
  apply Subtype.ext
  rw [diagram_eq_dg d μ.val μ.property.2, diagram_eq_dg d ν.val ν.property.2]
  exact dg_congr _ _ h

/-- adding a box in row `k` -/
def addP (lam : Partition d n) (k : Fin d) (h : Antitone (rv lam + Pi.single k 1)) : Partition d (n+1) :=
  ⟨dg (rv lam + Pi.single k 1) h, by
    rw [dg_card]
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_rv]
    simp, dg_colLen _ _⟩

lemma rv_addP (lam : Partition d n) (k : Fin d) (h : Antitone (rv lam + Pi.single k 1)) :
    rv (addP lam k h) = rv lam + Pi.single k 1 := by
  funext i
  exact dg_rowLen (rv lam + Pi.single k 1) h i

/-- removing a box in row `j` -/
def remP (μ : Partition d (n+1)) (j : Fin d) (h : Antitone (rv μ - Pi.single j 1) ∧ 1 ≤ rv μ j) :
    Partition d n :=
  ⟨dg (rv μ - Pi.single j 1) h.1, by
    rw [dg_card]
    have h1 := sum_rv μ
    have h3 : ∀ i, (rv μ - Pi.single j 1 : Fin d → ℕ) i + (if i = j then 1 else 0) = rv μ i := by
      intro i
      by_cases hi : i = j
      · subst hi; simp; have := h.2; omega
      · simp [Pi.single_eq_of_ne hi, hi]
    have h2 : ∑ i, (rv μ - Pi.single j 1 : Fin d → ℕ) i + 1 = ∑ i, rv μ i := by
      rw [← Finset.sum_congr rfl (fun i _ => h3 i), Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp
    omega, dg_colLen _ _⟩

lemma rv_remP (μ : Partition d (n+1)) (j : Fin d) (h : Antitone (rv μ - Pi.single j 1) ∧ 1 ≤ rv μ j) :
    rv (remP μ j h) = rv μ - Pi.single j 1 := by
  funext i
  exact dg_rowLen (rv μ - Pi.single j 1) h.1 i

lemma sev_addP (lam : Partition d n) (k : Fin d) (h : Antitone (rv lam + Pi.single k 1)) (x : Fin d → ℝ) :
    sev d (addP lam k h).val x = sev d (dg (rw' d lam.val + Pi.single k 1) h) x := rfl

/-- Pieri rule, evaluated -/
lemma pieri_eval (lam : Partition d n) (x : Fin d → ℝ) :
    ∑ k : Fin d, (if h : Antitone (rv lam + Pi.single k 1) then sev d (addP lam k h).val x else 0) =
      (∑ i, x i) * sev d lam.val x := by
  have := congrArg (MvPolynomial.eval x) (sP_pieri lam.val lam.property.2)
  simp only [map_mul, map_sum, p1, MvPolynomial.eval_X, sP_eval] at this
  rw [this]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold rv
  split_ifs with h
  · simp only [sP_eval]; rfl
  · simp

/-- the exponent vector of a partition -/
def lv (lam : Partition d n) : Fin d → ℕ := fun j => rv lam j + dl d j

lemma lv_strictAnti (lam : Partition d n) : StrictAnti (lv lam) := by
  intro a b hab
  have := rv_anti lam hab.le
  simp only [lv, dl]
  have : (a : ℕ) < b := hab
  omega

lemma sP_Al (lam : Partition d n) : sP (d := d) lam.val * Al (dl d) = Al (lv lam) :=
  bialtP lam.val lam.property.2

open Classical in
lemma coeff_Al_part {m : ℕ} (μ ν : Partition d m) :
    MvPolynomial.coeff (fs (lv ν)) (Al (lv μ)) = if μ = ν then 1 else 0 := by
  rw [coeff_Al (lv_strictAnti μ) (lv_strictAnti ν)]
  by_cases h : μ = ν
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro hl
    apply h
    apply part_ext
    funext i
    have := congrFun hl i
    simp only [lv] at this
    omega

lemma rv_add_sub (r : Fin d → ℕ) (k : Fin d) : r + Pi.single k 1 - Pi.single k 1 = r := by
  funext i; by_cases h : i = k
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

lemma rv_sub_add (r : Fin d → ℕ) (k : Fin d) (hk : 1 ≤ r k) : r - Pi.single k 1 + Pi.single k 1 = r := by
  funext i; by_cases h : i = k
  · subst h; simp; omega
  · simp [Pi.single_eq_of_ne h]

open Classical in
/-- **C3**: branching rule for the dimensions of Specht modules -/
theorem C3 (hd : 0 < d) (μ : Partition d (n+1)) :
    fP μ = ∑ j : Fin d, if h : Antitone (rv μ - Pi.single j 1) ∧ 1 ≤ rv μ j then fP (remP μ j h) else 0 := by
  have eq1 : ∑ μ' : Partition d (n+1), fP μ' • Al (lv μ') =
      ∑ lam : Partition d n, ∑ k : Fin d, if h : Antitone (rv lam + Pi.single k 1) then
        fP lam • Al (lv (addP lam k h)) else 0 := by
    have hL : ∑ μ' : Partition d (n+1), fP μ' • Al (lv μ') =
        (∑ μ' : Partition d (n+1), fP μ' • sP (d := d) μ'.val) * Al (dl d) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun μ' _ => ?_)
      rw [smul_mul_assoc, sP_Al]
    rw [hL, C0P hd, pow_succ, mul_comm (p1 d ^ n), mul_assoc, ← C0P hd, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun lam _ => ?_)
    rw [smul_mul_assoc, mul_smul_comm, ← mul_assoc, sP_pieri lam.val lam.property.2, Finset.sum_mul,
      Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : Antitone (rv lam + Pi.single k 1)
    · have h' : Antitone (rw' d lam.val + Pi.single k 1) := h
      rw [dif_pos h', dif_pos h]
      exact congrArg (fP lam • ·) (sP_Al (addP lam k h))
    · have h' : ¬ Antitone (rw' d lam.val + Pi.single k 1) := h
      rw [dif_neg h', dif_neg h]
      simp
  have hc := congrArg (MvPolynomial.coeff (fs (lv μ))) eq1
  simp only [MvPolynomial.coeff_sum, apply_dite (MvPolynomial.coeff (fs (lv μ))),
    MvPolynomial.coeff_zero, MvPolynomial.coeff_smul, coeff_Al_part, smul_eq_mul, mul_ite, mul_one,
    mul_zero] at hc
  rw [Finset.sum_ite_eq' Finset.univ μ, if_pos (Finset.mem_univ _)] at hc
  rw [hc, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs with hv
  · rw [Finset.sum_eq_single (remP μ k hv)]
    · have hA : Antitone (rv (remP μ k hv) + Pi.single k 1) := by
        rw [rv_remP, rv_sub_add _ k hv.2]; exact rv_anti μ
      rw [dif_pos hA, if_pos]
      apply part_ext
      rw [rv_addP, rv_remP, rv_sub_add _ k hv.2]
    · intro lam _ hne
      split_ifs with h1 h2
      · exfalso; apply hne
        apply part_ext
        rw [rv_remP, ← h2, rv_addP, rv_add_sub]
      · rfl
      · rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero (fun lam _ => ?_)
    split_ifs with h1 h2
    · exfalso; apply hv
      have hr : rv μ = rv lam + Pi.single k 1 := by rw [← h2, rv_addP]
      refine ⟨?_, ?_⟩
      · rw [hr, rv_add_sub]; exact rv_anti lam
      · rw [hr]; simp
    · rfl
    · rfl

lemma D2_sum_smul {ι : Type*} (S : Finset ι) (c : ι → ℝ) (A : ι → MvPolynomial (Fin d) ℝ) :
    D2 (∑ i ∈ S, c i • A i) = ∑ i ∈ S, c i • D2 (A i) := by
  unfold D2
  simp only [map_sum, Derivation.map_smul]
  rw [Finset.sum_comm]
  simp_rw [Finset.smul_sum]

/-- the shifted power sum `p₂*(λ) = Σ_j (λ_j² - (2j+1) λ_j)` -/
def p2s (lam : Partition d n) : ℝ := ∑ j : Fin d, (((rv lam j : ℝ)) ^ 2 - (2 * (j : ℝ) + 1) * rv lam j)

/-- **C1**: the Schur–Weyl average of the shifted power sum -/
theorem C1 (hd : 0 < d) (α : Fin d → ℝ) (hα : ∑ i, α i = 1) :
    ∑ lam : Partition d n, fP lam * sev d lam.val α * p2s lam = (n * (n - 1) : ℕ) * ∑ i, α i ^ 2 := by
  -- polynomial identity
  have hpoly : ∑ lam : Partition d n, fP lam • ((∑ j, ((lv lam j : ℝ)) ^ 2) • sP (d := d) lam.val) =
      ((n * (n - 1) : ℕ) : MvPolynomial (Fin d) ℝ) * p1 d ^ (n - 2) * p2 d +
        (((n + 2 * n * (d - 1) : ℕ) : ℝ) + ∑ j, ((dl d j : ℝ)) ^ 2) • p1 d ^ n := by
    apply mul_right_cancel₀ (Al_ne_zero (d := d))
    have hC : (∑ lam : Partition d n, fP lam • sP (d := d) lam.val) * Al (dl d) =
        ∑ lam : Partition d n, fP lam • Al (lv lam) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun lam _ => ?_)
      rw [smul_mul_assoc, sP_Al]
    rw [← D2_main, ← C0P hd, hC, D2_sum_smul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun lam _ => ?_)
    rw [smul_mul_assoc, smul_mul_assoc, sP_Al, D2_Al]
  have hev := congrArg (MvPolynomial.eval α) hpoly
  simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, sP_eval, map_add,
    map_pow, map_natCast, p1, p2, MvPolynomial.eval_X, hα, one_pow, mul_one] at hev
  have hC0 := C0 (n := n) hd α
  rw [hα, one_pow] at hC0
  have hl : ∀ lam : Partition d n, ∑ j, ((lv lam j : ℝ)) ^ 2 =
      p2s lam + (2 * d - 1) * n + ∑ j, ((dl d j : ℝ)) ^ 2 := by
    intro lam
    have hs : ∑ j, (rv lam j : ℝ) = n := by exact_mod_cast sum_rv lam
    unfold p2s lv
    have hj : ∀ j : Fin d, ((dl d j : ℕ) : ℝ) = (d : ℝ) - 1 - j := by
      intro j; simp only [dl]; have := j.isLt; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    simp only [Nat.cast_add, hj]
    rw [← hs, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [hl] at hev
  have hexp : ∀ lam : Partition d n, fP lam * ((p2s lam + (2 * d - 1) * n + ∑ j, ((dl d j : ℝ)) ^ 2) *
      sev d lam.val α) = fP lam * sev d lam.val α * p2s lam +
        ((2 * d - 1) * n + ∑ j, ((dl d j : ℝ)) ^ 2) * (fP lam * sev d lam.val α) := by
    intro lam; ring
  simp_rw [hexp] at hev
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hC0, mul_one] at hev
  have hd1 : ((n + 2 * n * (d - 1) : ℕ) : ℝ) = (2 * d - 1) * n := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
  rw [hd1] at hev
  by_cases hn : n ≤ 1
  · have : n * (n - 1) = 0 := by interval_cases n <;> simp
    rw [this] at hev ⊢
    push_cast at hev ⊢
    linarith
  · push_cast at hev ⊢
    linarith

lemma rv_zero (lam : Partition d 0) : rv lam = 0 := by
  have h := sum_rv lam
  funext i
  have := Finset.single_le_sum (fun j _ => Nat.zero_le (rv lam j)) (Finset.mem_univ i)
  simp only [Pi.zero_apply]
  omega

lemma part0_eq (lam μ : Partition d 0) : lam = μ := part_ext lam μ (by rw [rv_zero, rv_zero])

lemma sev_part0 (lam : Partition d 0) (x : Fin d → ℝ) : sev d lam.val x = 1 := by
  classical
  have hempty : ∀ c : lam.val.cells, False := by
    rintro ⟨v, hv⟩
    have h1 : lam.val.cells.card = 0 := lam.property.1
    rw [Finset.card_eq_zero] at h1
    rw [h1] at hv
    simp at hv
  have : IsEmpty lam.val.cells := ⟨hempty⟩
  unfold sev ssytF
  have hf : (Finset.univ.filter (SS (d := d) lam.val)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro T _ a
    exact (hempty a).elim
  rw [hf]
  simp

lemma fP_zero (hd : 0 < d) (lam : Partition d 0) : fP lam = 1 := by
  have h := C0 (n := 0) hd (fun _ => 0)
  rw [Finset.sum_eq_single lam (fun b _ hb => absurd (part0_eq b lam) hb)
    (fun h => absurd (Finset.mem_univ _) h), sev_part0, mul_one, pow_zero] at h
  exact h

/-- removing a box decreases the exponent `l_j` by one -/
lemma prod_fact_remP (μ : Partition d (n+1)) (j : Fin d) (h : Antitone (rv μ - Pi.single j 1) ∧ 1 ≤ rv μ j) :
    ∏ i, ((lv μ i).factorial : ℝ) = (lv μ j : ℝ) * ∏ i, ((lv (remP μ j h) i).factorial : ℝ) := by
  have hlv : ∀ i, lv (remP μ j h) i = if i = j then lv μ i - 1 else lv μ i := by
    intro i
    simp only [lv, rv_remP]
    by_cases hi : i = j
    · subst hi; simp; have := h.2; omega
    · simp [Pi.single_eq_of_ne hi, hi]
  have e1 : ∏ i, ((lv μ i).factorial : ℝ) = ((lv μ j).factorial : ℝ) *
      ∏ i ∈ Finset.univ.erase j, ((lv μ i).factorial : ℝ) :=
    (Finset.mul_prod_erase _ (fun i => ((lv μ i).factorial : ℝ)) (Finset.mem_univ j)).symm
  have e2 : ∏ i, ((lv (remP μ j h) i).factorial : ℝ) = ((lv (remP μ j h) j).factorial : ℝ) *
      ∏ i ∈ Finset.univ.erase j, ((lv (remP μ j h) i).factorial : ℝ) :=
    (Finset.mul_prod_erase _ (fun i => ((lv (remP μ j h) i).factorial : ℝ)) (Finset.mem_univ j)).symm
  have e3 : ∏ i ∈ Finset.univ.erase j, ((lv (remP μ j h) i).factorial : ℝ) =
      ∏ i ∈ Finset.univ.erase j, ((lv μ i).factorial : ℝ) :=
    Finset.prod_congr rfl (fun i hi => by rw [hlv i, if_neg (Finset.ne_of_mem_erase hi)])
  rw [e1, e2, e3, hlv j, if_pos rfl]
  have h1 : 1 ≤ lv μ j := by simp only [lv]; have := h.2; omega
  rw [show (lv μ j).factorial = lv μ j * (lv μ j - 1).factorial by
    conv_lhs => rw [show lv μ j = (lv μ j - 1) + 1 by omega]
    rw [Nat.factorial_succ]; congr 1; omega]
  push_cast
  ring

/-- the factorial formula relating `dim Sp_λ` and `dim V_λ` -/
theorem fact_formula (hd : 0 < d) : ∀ (n : ℕ) (lam : Partition d n),
    fP lam * ∏ j, ((lv lam j).factorial : ℝ) =
      (∏ j, ((dl d j).factorial : ℝ)) * (n.factorial : ℝ) * schurDimension lam := by
  intro n
  induction n with
  | zero =>
    intro lam
    rw [fP_zero hd lam, schurDim_sev, sev_part0, Nat.factorial_zero]
    have : lv lam = dl d := by funext j; simp [lv, rv_zero]
    rw [this]; ring
  | succ n ih =>
    intro μ
    -- the removal identity at the point 1
    have hE := congrArg (MvPolynomial.eval (fun _ => (1 : ℝ))) (Ed_sP (d := d) μ.val μ.property.2)
    rw [eval_Ed_sP, μ.property.1] at hE
    simp only [map_sum, apply_dite (MvPolynomial.eval (fun _ => (1 : ℝ))), map_zero,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, sP_eval] at hE
    rw [C3 hd μ, Finset.sum_mul]
    have hterm : ∀ j : Fin d, (if h : Antitone (rv μ - Pi.single j 1) ∧ 1 ≤ rv μ j then
        fP (remP μ j h) else 0) * ∏ i, ((lv μ i).factorial : ℝ) =
        (∏ j, ((dl d j).factorial : ℝ)) * (n.factorial : ℝ) *
          (if h : Antitone (rv μ - Pi.single j 1) ∧ 1 ≤ rv μ j then
            ((rw' d μ.val j + dl d j : ℕ) : ℝ) * sev d (dg (rw' d μ.val - Pi.single j 1) h.1) (fun _ => 1)
            else 0) := by
      intro j
      split_ifs with h
      · rw [prod_fact_remP μ j h]
        rw [show fP (remP μ j h) * ((lv μ j : ℝ) * ∏ i, ((lv (remP μ j h) i).factorial : ℝ)) =
          (lv μ j : ℝ) * (fP (remP μ j h) * ∏ i, ((lv (remP μ j h) i).factorial : ℝ)) by ring]
        rw [ih (remP μ j h), schurDim_sev]
        show (lv μ j : ℝ) * ((∏ j, ((dl d j).factorial : ℝ)) * (n.factorial : ℝ) *
            sev d (dg (rv μ - Pi.single j 1) h.1) (fun _ => 1)) = _
        simp only [lv, rv, Nat.cast_add]
        ring
      · simp
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum]
    have hE' : ∑ j : Fin d, (if h : Antitone (rw' d μ.val - Pi.single j 1) ∧ 1 ≤ rw' d μ.val j then
        ((rw' d μ.val j + dl d j : ℕ) : ℝ) * sev d (dg (rw' d μ.val - Pi.single j 1) h.1) (fun _ => 1) else 0) =
        ((n + 1 : ℕ) : ℝ) * sev d μ.val (fun _ => 1) := by
      rw [← hE]
    rw [show (∑ j : Fin d, (if h : Antitone (rv μ - Pi.single j 1) ∧ 1 ≤ rv μ j then
        ((rw' d μ.val j + dl d j : ℕ) : ℝ) * sev d (dg (rw' d μ.val - Pi.single j 1) h.1) (fun _ => 1)
        else 0)) = ((n + 1 : ℕ) : ℝ) * sev d μ.val (fun _ => 1) from hE', schurDim_sev, Nat.factorial_succ]
    push_cast
    ring

/-- **C4**: the content ratio -/
theorem C4 (hd : 0 < d) (lam : Partition d n) (k : Fin d) (h : Antitone (rv lam + Pi.single k 1)) :
    fP lam * schurDimension (addP lam k h) * (n + 1 : ℝ) =
      schurDimension lam * ((lv lam k : ℝ) + 1) * fP (addP lam k h) := by
  have h1 := fact_formula hd n lam
  have h2 := fact_formula hd (n+1) (addP lam k h)
  have hl : ∏ j, ((lv (addP lam k h) j).factorial : ℝ) = ((lv lam k : ℝ) + 1) * ∏ j, ((lv lam j).factorial : ℝ) := by
    have hlv : ∀ i, lv (addP lam k h) i = if i = k then lv lam i + 1 else lv lam i := by
      intro i
      simp only [lv, rv_addP]
      by_cases hi : i = k
      · subst hi; simp; ring
      · simp [Pi.single_eq_of_ne hi, hi]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ (fun i =>
      ((lv lam i).factorial : ℝ)) (Finset.mem_univ k)]
    rw [Finset.prod_congr rfl (fun i hi => by rw [hlv i, if_neg (Finset.ne_of_mem_erase hi)])]
    rw [hlv k, if_pos rfl, Nat.factorial_succ]
    push_cast
    ring
  rw [hl] at h2
  have hpos : (0 : ℝ) < ∏ j, ((lv lam j).factorial : ℝ) :=
    Finset.prod_pos (fun j _ => by exact_mod_cast Nat.factorial_pos _)
  apply mul_right_cancel₀ hpos.ne'
  rw [Nat.factorial_succ] at h2
  push_cast at h2
  calc fP lam * schurDimension (addP lam k h) * (n + 1 : ℝ) * ∏ j, ((lv lam j).factorial : ℝ)
      = (fP lam * ∏ j, ((lv lam j).factorial : ℝ)) * schurDimension (addP lam k h) * (n + 1 : ℝ) := by ring
    _ = (∏ j, ((dl d j).factorial : ℝ)) * (n.factorial : ℝ) * schurDimension lam *
          schurDimension (addP lam k h) * (n + 1 : ℝ) := by rw [h1]
    _ = schurDimension lam * (fP (addP lam k h) * (((lv lam k : ℝ) + 1) * ∏ j, ((lv lam j).factorial : ℝ))) := by
          rw [h2]; ring
    _ = _ := by ring

end KeylS

-- ===== KR1 =====

set_option autoImplicit false
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

namespace KeylR
open QAlgorithms QAlgorithms.Schur KeylS

variable {d : ℕ}

/-- leading principal submatrix -/
def lead (Z : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) (hm : m ≤ d) : Matrix (Fin m) (Fin m) ℂ :=
  Z.submatrix (fun i => (⟨i.val, by omega⟩ : Fin d)) (fun i => (⟨i.val, by omega⟩ : Fin d))

lemma lead_psd {Z : Matrix (Fin d) (Fin d) ℂ} (hZ : Z.PosSemidef) (m : ℕ) (hm : m ≤ d) :
    (lead Z m hm).PosSemidef := hZ.submatrix _

lemma psd_ker {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosSemidef) (x : Fin m → ℂ)
    (hx : star x ⬝ᵥ (A *ᵥ x) = 0) : A *ᵥ x = 0 := by
  obtain ⟨M, hM⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have h1 : star x ⬝ᵥ (A *ᵥ x) = star (M *ᵥ x) ⬝ᵥ (M *ᵥ x) := by
    rw [hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
      Matrix.star_eq_conjTranspose]
  rw [h1] at hx
  have h2 : M *ᵥ x = 0 := dotProduct_star_self_eq_zero.1 hx
  rw [hM, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]

/-- **Fischer's inequality** for leading principal minors -/
lemma fischer {Z : Matrix (Fin d) (Fin d) ℂ} (hZ : Z.PosSemidef) (k : ℕ) (hk : k < d) :
    (lead Z (k+1) hk).det ≤ (lead Z k hk.le).det * Z ⟨k, hk⟩ ⟨k, hk⟩ := by
  set A := lead Z (k+1) hk with hAdef
  set B := lead Z k hk.le with hBdef
  have hA : A.PosSemidef := lead_psd hZ _ _
  have hB : B.PosSemidef := lead_psd hZ _ _
  set vc : Matrix (Fin k) (Fin 1) ℂ := Matrix.of fun i _ => Z ⟨i, by omega⟩ ⟨k, hk⟩ with hvc
  set vr : Matrix (Fin 1) (Fin k) ℂ := Matrix.of fun _ j => Z ⟨k, hk⟩ ⟨j, by omega⟩ with hvr
  set C1 : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => Z ⟨k, hk⟩ ⟨k, hk⟩ with hC1
  have hblk : A.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks B vc vr C1 := by
    ext (i | i) (j | j)
    · simp [hAdef, hBdef, lead, finSumFinEquiv_apply_left]
    · simp [hAdef, hvc, lead, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
    · simp [hAdef, hvr, lead, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
    · simp [hAdef, hC1, lead, finSumFinEquiv_apply_right]
  have hdetA : A.det = (Matrix.fromBlocks B vc vr C1).det := by
    rw [← hblk, Matrix.det_submatrix_equiv_self]
  have hBnn : 0 ≤ B.det := hB.det_nonneg
  by_cases hdet : B.det = 0
  · have hA0 : A.det = 0 := by
      obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
      let wt : Fin (k+1) → ℂ := fun i => if h : i.val < k then w ⟨i, h⟩ else 0
      have hwt : wt ≠ 0 := by
        intro h
        apply hw0
        funext i
        have := congrFun h (Fin.castSucc i)
        simpa [wt] using this
      have hq : star wt ⬝ᵥ (A *ᵥ wt) = 0 := by
        have hAw : ∀ (i : Fin (k+1)) (hi : i.val < k), (A *ᵥ wt) i = (B *ᵥ w) ⟨i, hi⟩ := by
          intro i hi
          simp only [Matrix.mulVec, dotProduct, hAdef, hBdef, lead, Matrix.submatrix_apply]
          rw [Fin.sum_univ_castSucc]
          simp [wt]
        rw [dotProduct, Fin.sum_univ_castSucc]
        simp only [wt, Pi.star_apply]
        rw [dif_neg (by simp)]
        simp only [star_zero, zero_mul, add_zero]
        refine Finset.sum_eq_zero (fun i _ => ?_)
        rw [dif_pos (by simp), hAw _ (by simp), hw]
        simp
      exact Matrix.exists_mulVec_eq_zero_iff.1 ⟨wt, hwt, psd_ker hA wt hq⟩
    rw [hA0, hdet, zero_mul]
  · haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.2 hdet)
    rw [hdetA, Matrix.det_fromBlocks₁₁, Matrix.det_unique (C1 - vr * ⅟B * vc)]
    have hq : 0 ≤ (vr * ⅟B * vc) default default := by
      rw [Matrix.invOf_eq_nonsing_inv]
      have hinv : B⁻¹.PosSemidef := hB.inv
      set v : Fin k → ℂ := fun i => vc i 0 with hv
      have : (vr * B⁻¹ * vc) default default = star v ⬝ᵥ (B⁻¹ *ᵥ v) := by
        simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, hvr, hvc, hv, Matrix.of_apply,
          Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [show star (Z ⟨(i : ℕ), by omega⟩ ⟨k, hk⟩) = Z ⟨k, hk⟩ ⟨(i : ℕ), by omega⟩ from hZ.1.apply _ _]
        ring
      rw [this]
      exact hinv.dotProduct_mulVec_nonneg v
    have : (C1 - vr * ⅟B * vc) default default = Z ⟨k, hk⟩ ⟨k, hk⟩ - (vr * ⅟B * vc) default default := by
      simp [hC1]
    rw [this, mul_sub]
    have : 0 ≤ B.det * (vr * ⅟B * vc) default default := mul_nonneg hBnn hq
    exact sub_le_self _ this

lemma genP_eq {n : ℕ} (lam : Partition d n) (Z : Matrix (Fin d) (Fin d) ℂ) :
    Tomography.keylGeneralizedPower lam Z =
      ∏ m : Fin d, (lead Z (m.val+1) m.isLt).det ^ (lam.val.rowLen m - lam.val.rowLen (m+1)) := rfl

lemma rowLen_d {n : ℕ} (lam : Partition d n) : lam.val.rowLen d = 0 := by
  by_contra h
  have : (d, 0) ∈ lam.val := YoungDiagram.mem_iff_lt_rowLen.2 (Nat.pos_of_ne_zero h)
  have := YoungDiagram.mem_iff_lt_colLen.1 this
  have := lam.property.2
  omega

lemma rowLen_addP {n : ℕ} (lam : Partition d n) (k : Fin d) (h : Antitone (rv lam + Pi.single k 1))
    (m : ℕ) : (addP lam k h).val.rowLen m = lam.val.rowLen m + (if m = k then 1 else 0) := by
  by_cases hm : m < d
  · have := congrFun (rv_addP lam k h) ⟨m, hm⟩
    simp only [rv, rw', Pi.add_apply] at this
    rw [this]
    by_cases hmk : m = k
    · have : (⟨m, hm⟩ : Fin d) = k := Fin.ext hmk
      rw [this, if_pos hmk]; simp
    · have : (⟨m, hm⟩ : Fin d) ≠ k := fun e => hmk (congrArg Fin.val e)
      rw [Pi.single_eq_of_ne this, if_neg hmk]
  · have h1 : ∀ {n' : ℕ} (μ : Partition d n'), μ.val.rowLen m = 0 := by
      intro n' μ
      have := μ.val.rowLen_anti d m (by omega)
      rw [rowLen_d] at this; omega
    rw [h1 (addP lam k h), h1 lam, if_neg (fun e => hm (by rw [e]; exact k.isLt))]

lemma lead_det_congr (Z : Matrix (Fin d) (Fin d) ℂ) {m m' : ℕ} (hm : m ≤ d) (hm' : m' ≤ d) (h : m = m') :
    (lead Z m hm).det = (lead Z m' hm').det := by subst h; rfl

lemma prod_pow_add_ite {M : Type*} [CommMonoid M] (a : Fin d → M) (f : Fin d → ℕ) (j : Fin d) :
    ∏ m, a m ^ (f m + if m = j then 1 else 0) = (∏ m, a m ^ f m) * a j := by
  rw [Finset.prod_congr rfl (fun m _ => pow_add (a m) (f m) _), Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Fischer bound** for generalized powers -/
lemma genP_add_le {n : ℕ} (lam : Partition d n) (k : Fin d) (h : Antitone (rv lam + Pi.single k 1))
    {Z : Matrix (Fin d) (Fin d) ℂ} (hZ : Z.PosSemidef) :
    Tomography.keylGeneralizedPower (addP lam k h) Z ≤ Z k k * Tomography.keylGeneralizedPower lam Z := by
  set a : Fin d → ℂ := fun m => (lead Z (m.val+1) m.isLt).det with ha
  have ha0 : ∀ m, 0 ≤ a m := fun m => (lead_psd hZ _ _).det_nonneg
  set e : Fin d → ℕ := fun m => lam.val.rowLen m - lam.val.rowLen (m+1) with he
  set e' : Fin d → ℕ := fun m => (addP lam k h).val.rowLen m - (addP lam k h).val.rowLen (m+1) with he'
  have hL : Tomography.keylGeneralizedPower lam Z = ∏ m, a m ^ e m := rfl
  have hL' : Tomography.keylGeneralizedPower (addP lam k h) Z = ∏ m, a m ^ e' m := rfl
  have hanti := rv_anti lam
  by_cases hk0 : (k : ℕ) = 0
  · -- adding to the first row
    have hee : ∀ m, e' m = e m + if m = k then 1 else 0 := by
      intro m
      simp only [he, he', rowLen_addP]
      by_cases hm : m = k
      · subst hm
        have h1 : (m : ℕ) + 1 ≠ m := by omega
        simp [h1]
        have := lam.val.rowLen_anti m (m+1) (by omega)
        omega
      · have h1 : (m : ℕ) ≠ k := fun e => hm (Fin.ext e)
        have h2 : (m : ℕ) + 1 ≠ k := by omega
        simp [h1, h2, hm]
    have e1 : ∏ m, a m ^ e' m = (∏ m, a m ^ e m) * a k := by
      rw [Finset.prod_congr rfl (fun m _ => by rw [hee m])]
      exact prod_pow_add_ite a e k
    rw [hL', e1, ← hL]
    have hak : a k = Z k k := by
      have hd1 : 1 ≤ d := by have := k.isLt; omega
      have h1 : a k = (lead Z 1 hd1).det := lead_det_congr Z _ _ (by omega)
      rw [h1, Matrix.det_unique]
      have hkk : k = ⟨0, by omega⟩ := Fin.ext hk0
      rw [hkk]
      rfl
    rw [hak, mul_comm]
  · have hk1 : (k : ℕ) - 1 < d := by omega
    set k' : Fin d := ⟨(k : ℕ) - 1, hk1⟩ with hk'
    have hne : k' ≠ k := fun e => by have := congrArg Fin.val e; simp [hk'] at this; omega
    -- the row above is strictly longer
    have hgt : lam.val.rowLen k < lam.val.rowLen k' := by
      have := h (show k' ≤ k from by rw [Fin.le_iff_val_le_val]; simp [hk'])
      simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, rv, rw', add_zero] at this
      omega
    set f : Fin d → ℕ := fun m => e m - if m = k' then 1 else 0 with hf
    have hef : ∀ m, e m = f m + if m = k' then 1 else 0 := by
      intro m
      simp only [hf, he]
      by_cases hm : m = k'
      · subst hm
        have h1 : (k' : ℕ) + 1 = k := by simp [hk']; omega
        rw [if_pos rfl, h1]
        omega
      · simp [hm]
    have hef' : ∀ m, e' m = f m + if m = k then 1 else 0 := by
      intro m
      simp only [hf, he, he', rowLen_addP]
      by_cases hm : m = k
      · subst hm
        have h1 : (m : ℕ) + 1 ≠ m := by omega
        simp [h1, Ne.symm hne]
        have := lam.val.rowLen_anti m (m+1) (by omega)
        omega
      · by_cases hm' : m = k'
        · subst hm'
          have h1 : (k' : ℕ) + 1 = k := by simp [hk']; omega
          have h2 : (k' : ℕ) ≠ k := fun e => hne (Fin.ext e)
          simp [h1, h2, hm]
          omega
        · have h1 : (m : ℕ) ≠ k := fun e => hm (Fin.ext e)
          have h2 : (m : ℕ) + 1 ≠ k := by
            intro e; apply hm'; apply Fin.ext; simp [hk']; omega
          simp [h1, h2, hm, hm']
    have e1 : ∏ m, a m ^ e' m = (∏ m, a m ^ f m) * a k := by
      rw [Finset.prod_congr rfl (fun m _ => by rw [hef' m])]
      exact prod_pow_add_ite a f k
    have e2 : ∏ m, a m ^ e m = (∏ m, a m ^ f m) * a k' := by
      rw [Finset.prod_congr rfl (fun m _ => by rw [hef m])]
      exact prod_pow_add_ite a f k'
    rw [hL', e1, hL, e2]
    have hR : 0 ≤ ∏ m, a m ^ f m := Finset.prod_nonneg (fun m _ => pow_nonneg (ha0 m) _)
    have hfis : a k ≤ a k' * Z k k := by
      have := fischer hZ (k : ℕ) k.isLt
      have hak' : a k' = (lead Z (k : ℕ) k.isLt.le).det :=
        lead_det_congr Z _ _ (by simp [hk']; omega)
      rw [hak']
      exact this
    calc (∏ m, a m ^ f m) * a k ≤ (∏ m, a m ^ f m) * (a k' * Z k k) :=
          mul_le_mul_of_nonneg_left hfis hR
      _ = Z k k * ((∏ m, a m ^ f m) * a k') := by ring

end KeylR

-- ===== KR2 =====

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder

noncomputable section

namespace KeylR
open QAlgorithms QAlgorithms.Schur KeylS

variable {d : ℕ}

lemma piKron_one'' {n : ℕ} : piKron n (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma polyRep_one {n : ℕ} (lam : Partition d n) :
    polynomialRepresentation lam 1 = LinearMap.id := by
  ext v
  simp only [polynomialRepresentation, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply,
    piKron_one'']
  have : Matrix.toEuclideanLin (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (v : EuclideanSpace ℂ (Fin n → Fin d)) = v := by
    simp [Matrix.toLpLin_apply]
  simp [this]

lemma finrank_eq_schurDim {n : ℕ} (lam : Partition d n) :
    ((Module.finrank ℂ (schurModule lam) : ℕ) : ℂ) = ((schurDimension lam : ℝ) : ℂ) := by
  have h := KWSpectrum.Estimator.eq_20 lam 1 (one_mem _) (fun _ => 1)
  have h1 : (1 : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun _ => ((1 : ℝ) : ℂ)) * star 1 = 1 := by simp
  rw [h1, polyRep_one, LinearMap.trace_id] at h
  rw [h]
  rfl

lemma schurDim_pos {n : ℕ} (lam : Partition d n) : 0 < schurDimension lam := by
  classical
  rw [schurDim_sev]
  unfold sev
  simp only [Finset.prod_const_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hT : (fun c : lam.val.cells => (⟨c.val.1, by
      have h1 : c.val.1 < lam.val.colLen c.val.2 := YoungDiagram.mem_iff_lt_colLen.1 c.2
      have h2 : lam.val.colLen c.val.2 ≤ lam.val.colLen 0 := lam.val.colLen_anti 0 _ (Nat.zero_le _)
      have := lam.property.2
      omega⟩ : Fin d)) ∈ ssytF d lam.val := by
    simp only [ssytF, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a b
    constructor
    · intro h1 _; rw [Fin.le_iff_val_le_val]; simp [h1]
    · intro _ h2; rw [Fin.lt_iff_val_lt_val]; simpa using h2
  have : 0 < (ssytF d lam.val).card := Finset.card_pos.2 ⟨_, hT⟩
  exact_mod_cast this

lemma spec (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsDensityMatrix ρ) :
    ∃ (V : Matrix (Fin d) (Fin d) ℂ) (α : Fin d → ℝ), V ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
      (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1 ∧ ρ = V * Matrix.diagonal (fun i => (α i : ℂ)) * star V := by
  have hH := hρ.1.1
  refine ⟨hH.eigenvectorUnitary, hH.eigenvalues, hH.eigenvectorUnitary.2,
    fun i => hρ.1.eigenvalues_nonneg i, ?_, ?_⟩
  · have := hH.trace_eq_sum_eigenvalues
    rw [hρ.2] at this
    have h2 : ((∑ i, hH.eigenvalues i : ℝ) : ℂ) = 1 := by push_cast; exact this.symm
    exact_mod_cast h2
  · conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl

lemma chi_rho {n : ℕ} (lam : Partition d n) (V : Matrix (Fin d) (Fin d) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (α : Fin d → ℝ) :
    LinearMap.trace ℂ (schurModule lam)
        (polynomialRepresentation lam (V * Matrix.diagonal (fun i => (α i : ℂ)) * star V)) =
      ((sev d lam.val α : ℝ) : ℂ) := by
  rw [KWSpectrum.Estimator.eq_20 lam V hV α, eval_schur]

section haar
set_option backward.isDefEq.respectTransparency.types false
open scoped Matrix.Norms.Elementwise

abbrev UG (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

lemma integC {g : UG d → ℂ} (hg : Continuous g) : Integrable g (unitaryHaar d) := by
  unfold unitaryHaar
  exact integrableOn_univ.1 (hg.continuousOn.integrableOn_compact isCompact_univ)

lemma integRe {g : UG d → ℝ} (hg : Continuous g) : Integrable g (unitaryHaar d) := by
  unfold unitaryHaar
  exact integrableOn_univ.1 (hg.continuousOn.integrableOn_compact isCompact_univ)

instance haar_prob' : IsProbabilityMeasure (unitaryHaar d) := by
  unfold unitaryHaar
  exact ⟨Measure.haarMeasure_self⟩

lemma conjU_cont (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Continuous (fun U : UG d => star (U : Matrix (Fin d) (Fin d) ℂ) * ρ * (U : Matrix (Fin d) (Fin d) ℂ)) := by
  have h1 : Continuous (fun U : UG d => (U : Matrix (Fin d) (Fin d) ℂ)) := continuous_subtype_val
  exact ((continuous_star.comp h1).mul continuous_const).mul h1

lemma genP_cont {n : ℕ} (lam : Partition d n) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Continuous (fun U : UG d => Tomography.keylGeneralizedPower lam
      (star (U : Matrix (Fin d) (Fin d) ℂ) * ρ * (U : Matrix (Fin d) (Fin d) ℂ))) := by
  unfold Tomography.keylGeneralizedPower
  refine continuous_finsetProd _ (fun k _ => ?_)
  refine Continuous.pow ?_ _
  exact ((conjU_cont ρ).matrix_submatrix _ _).matrix_det

/-- Haar average of the real part of the generalized power at a density matrix -/
lemma haar_re {n : ℕ} (lam : Partition d n) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix (Fin d) (Fin d) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (α : Fin d → ℝ)
    (hρV : ρ = V * Matrix.diagonal (fun i => (α i : ℂ)) * star V) :
    ∫ U, (Tomography.keylGeneralizedPower lam
      (star (U : Matrix (Fin d) (Fin d) ℂ) * ρ * (U : Matrix (Fin d) (Fin d) ℂ))).re ∂(unitaryHaar d) =
      sev d lam.val α / schurDimension lam := by
  have h1 := QAlgorithms.Papers.RoadmapL03.keyl_haar_generalizedPower lam ρ
  have hre := integral_re (𝕜 := ℂ) (μ := unitaryHaar d) (integC (genP_cont lam ρ))
  simp only [RCLike.re_to_complex] at hre
  rw [hre, h1, hρV, chi_rho lam V hV α, finrank_eq_schurDim]
  rw [← Complex.ofReal_div, Complex.ofReal_re]

end haar

end KeylR

-- ===== KR3 =====

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder

noncomputable section

namespace KeylR
open QAlgorithms QAlgorithms.Schur KeylS

variable {d : ℕ}

lemma frob_sq (M : Matrix (Fin d) (Fin d) ℂ) : frobNorm M ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  unfold frobNorm
  rw [@Matrix.frobenius_norm_def]
  have hnn : 0 ≤ ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

lemma sum_normsq_eq_trace (M : Matrix (Fin d) (Fin d) ℂ) :
    ∑ i, ∑ j, ‖M i j‖ ^ 2 = (Mᴴ * M).trace.re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.mul_re]

/-- expansion of the Frobenius error of a rotated diagonal estimate -/
lemma frob_expand (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (c : Fin d → ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.IsHermitian) :
    frobNorm (U * Matrix.diagonal (fun i => (c i : ℂ)) * star U - ρ) ^ 2 =
      ∑ i, c i ^ 2 - 2 * ∑ i, c i * ((star U * ρ * U) i i).re + (ρ * ρ).trace.re := by
  rw [frob_sq, sum_normsq_eq_trace]
  set D := Matrix.diagonal (fun i => (c i : ℂ)) with hD
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hDH : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]; congr 1; funext i; simp [Complex.conj_ofReal]
  have hMH : (U * D * star U - ρ)ᴴ = U * D * star U - ρ := by
    rw [Matrix.conjTranspose_sub, hρ.eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, hDH, Matrix.mul_assoc]
  rw [hMH]
  have h1 : ((U * D * star U) * (U * D * star U)).trace = ∑ i, ((c i ^ 2 : ℝ) : ℂ) := by
    rw [show (U * D * star U) * (U * D * star U) = U * (D * (star U * U) * D) * star U by
      simp only [Matrix.mul_assoc], hUU, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      hUU, Matrix.one_mul, hD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    push_cast; simp [sq]
  have h2 : (U * D * star U * ρ).trace = ∑ i, (c i : ℂ) * (star U * ρ * U) i i := by
    rw [show U * D * star U * ρ = U * (D * (star U * ρ)) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, Matrix.mul_assoc]
    simp only [Matrix.trace, Matrix.diag, hD, Matrix.diagonal_mul]
  have h3 : (ρ * (U * D * star U)).trace = (U * D * star U * ρ).trace := Matrix.trace_mul_comm _ _
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_sub, h1, h3, h2]
  simp only [Complex.sub_re, Complex.re_sum, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

lemma trace_rho_sq (V : Matrix (Fin d) (Fin d) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (α : Fin d → ℝ) :
    ((V * Matrix.diagonal (fun i => (α i : ℂ)) * star V) * (V * Matrix.diagonal (fun i => (α i : ℂ)) * star V)).trace.re =
      ∑ i, α i ^ 2 := by
  have hVV : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
  rw [show (V * Matrix.diagonal (fun i => (α i : ℂ)) * star V) * (V * Matrix.diagonal (fun i => (α i : ℂ)) * star V) =
      V * (Matrix.diagonal (fun i => (α i : ℂ)) * (star V * V) * Matrix.diagonal (fun i => (α i : ℂ))) * star V by
    simp only [Matrix.mul_assoc], hVV, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hVV,
    Matrix.one_mul, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.ofReal_mul, Complex.ofReal_re]; ring

lemma conj_psd (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (U : Matrix (Fin d) (Fin d) ℂ) :
    (star U * ρ * U).PosSemidef := by
  have := hρ.conjTranspose_mul_mul_same U
  rwa [← Matrix.star_eq_conjTranspose] at this

lemma genP_nonneg' {n : ℕ} (lam : Partition d n) {Z : Matrix (Fin d) (Fin d) ℂ} (hZ : Z.PosSemidef) :
    0 ≤ Tomography.keylGeneralizedPower lam Z := by
  rw [genP_eq]
  exact Finset.prod_nonneg (fun m _ => pow_nonneg (lead_psd hZ _ _).det_nonneg _)

lemma re_mul_of_nonneg {a b : ℂ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a * b).re = a.re * b.re := by
  have h1 := (Complex.nonneg_iff.1 ha).2
  have h2 := (Complex.nonneg_iff.1 hb).2
  rw [Complex.mul_re, ← h1, ← h2]; ring

/-- the pointwise Fischer bound in real form -/
lemma fischer_re {n : ℕ} (lam : Partition d n) (k : Fin d) (h : Antitone (rv lam + Pi.single k 1))
    {Z : Matrix (Fin d) (Fin d) ℂ} (hZ : Z.PosSemidef) :
    (Tomography.keylGeneralizedPower (addP lam k h) Z).re ≤
      (Z k k).re * (Tomography.keylGeneralizedPower lam Z).re := by
  have h1 := genP_add_le lam k h hZ
  have hzz : 0 ≤ Z k k := hZ.diag_nonneg
  rw [← re_mul_of_nonneg hzz (genP_nonneg' lam hZ)]
  exact (Complex.le_def.1 h1).1

section bound
set_option backward.isDefEq.respectTransparency.types false
open scoped Matrix.Norms.Elementwise

variable (hd : 0 < d) {n : ℕ} (hn : 0 < n) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsDensityMatrix ρ)
  (V : Matrix (Fin d) (Fin d) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (α : Fin d → ℝ)
  (hρV : ρ = V * Matrix.diagonal (fun i => (α i : ℂ)) * star V)

/-- the conjugated state -/
abbrev Zc (U : UG d) : Matrix (Fin d) (Fin d) ℂ :=
  star (U : Matrix (Fin d) (Fin d) ℂ) * ρ * (U : Matrix (Fin d) (Fin d) ℂ)

lemma Zc_entry_cont (i : Fin d) : Continuous (fun U : UG d => (Zc ρ U i i).re) :=
  Complex.continuous_re.comp ((continuous_apply i).comp ((continuous_apply i).comp (conjU_cont ρ)))

lemma genPre_cont {m : ℕ} (lam : Partition d m) :
    Continuous (fun U : UG d => (Tomography.keylGeneralizedPower lam (Zc ρ U)).re) :=
  Complex.continuous_re.comp (genP_cont lam ρ)

include hρ hV hρV in
lemma frob_est (lam : Partition d n) (U : UG d) :
    frobNorm (Schur.estimate hd hn lam U - ρ) ^ 2 =
      ∑ i : Fin d, ((lam.val.rowLen (i : ℕ) : ℝ) / n) ^ 2 -
        2 * ∑ i : Fin d, ((lam.val.rowLen (i : ℕ) : ℝ) / n) * (Zc ρ U i i).re + ∑ i, α i ^ 2 := by
  unfold Schur.estimate Schur.normalizedDiagram Schur.normalizedRows
  rw [frob_expand _ U.2 _ ρ hρ.1.1]
  congr 1
  rw [hρV, trace_rho_sq V hV α]

include hρ hV hρV in
/-- the risk contribution of one shape -/
lemma int_bound (lam : Partition d n) :
    ∫ U, frobNorm (Schur.estimate hd hn lam U - ρ) ^ 2 *
        (fP lam * schurDimension lam * (Tomography.keylGeneralizedPower lam (Zc ρ U)).re) ∂(unitaryHaar d) ≤
      fP lam * sev d lam.val α * (∑ i : Fin d, ((lam.val.rowLen (i : ℕ) : ℝ) / n) ^ 2 + ∑ i, α i ^ 2) -
        2 * (fP lam * schurDimension lam) * ∑ i : Fin d,
          (if h : Antitone (rv lam + Pi.single i 1) then
            ((lam.val.rowLen (i : ℕ) : ℝ) / n) * (sev d (addP lam i h).val α / schurDimension (addP lam i h))
            else 0) := by
  set K := fP lam * schurDimension lam with hK
  have hK0 : 0 ≤ K := mul_nonneg (by unfold fP; positivity) (schurDim_pos lam).le
  set c : Fin d → ℝ := fun i => (lam.val.rowLen i : ℝ) / n with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => by simp only [hc]; positivity
  set p2 := ∑ i, α i ^ 2 with hp2
  set Δr : UG d → ℝ := fun U => (Tomography.keylGeneralizedPower lam (Zc ρ U)).re with hΔr
  have hΔc : Continuous Δr := genPre_cont ρ lam
  have hpsd : ∀ U : UG d, (Zc ρ U).PosSemidef := fun U => conj_psd ρ hρ.1 _
  -- the comparison function
  set H : UG d → ℝ := fun U => K * (∑ i, c i ^ 2 + p2) * Δr U - 2 * K * ∑ i : Fin d,
    (if h : Antitone (rv lam + Pi.single i 1) then
      c i * (Tomography.keylGeneralizedPower (addP lam i h) (Zc ρ U)).re else 0) with hH
  have hle : ∀ U : UG d, frobNorm (Schur.estimate hd hn lam U - ρ) ^ 2 * (K * Δr U) ≤ H U := by
    intro U
    rw [frob_est hd hn ρ hρ V hV α hρV lam U]
    simp only [hH]
    have hterm : ∀ i : Fin d, (if h : Antitone (rv lam + Pi.single i 1) then
        c i * (Tomography.keylGeneralizedPower (addP lam i h) (Zc ρ U)).re else 0) ≤
        c i * ((Zc ρ U i i).re * Δr U) := by
      intro i
      split_ifs with h
      · exact mul_le_mul_of_nonneg_left (fischer_re lam i h (hpsd U)) (hc0 i)
      · exact mul_nonneg (hc0 i) (mul_nonneg (Complex.nonneg_iff.1 (hpsd U).diag_nonneg).1
          (Complex.nonneg_iff.1 (genP_nonneg' lam (hpsd U))).1)
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    have : (∑ i, c i ^ 2 - 2 * ∑ i, c i * (Zc ρ U i i).re + p2) * (K * Δr U) =
        K * (∑ i, c i ^ 2 + p2) * Δr U - 2 * K * ∑ i, c i * ((Zc ρ U i i).re * Δr U) := by
      have hB : ∑ i, c i * ((Zc ρ U i i).re * Δr U) = (∑ i, c i * (Zc ρ U i i).re) * Δr U := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [hB]; ring
    rw [this]
    nlinarith
  have hFeq : (fun U : UG d => frobNorm (Schur.estimate hd hn lam U - ρ) ^ 2 * (K * Δr U)) =
      fun U => (∑ i, c i ^ 2 - 2 * ∑ i, c i * (Zc ρ U i i).re + p2) * (K * Δr U) := by
    funext U; rw [frob_est hd hn ρ hρ V hV α hρV lam U]
  have hFc : Continuous (fun U : UG d => frobNorm (Schur.estimate hd hn lam U - ρ) ^ 2 * (K * Δr U)) := by
    rw [hFeq]
    refine Continuous.mul ?_ (continuous_const.mul hΔc)
    refine (continuous_const.sub (continuous_const.mul (continuous_finsetSum _ (fun i _ =>
      continuous_const.mul (Zc_entry_cont ρ i))))).add continuous_const
  have hdc : ∀ i : Fin d, Continuous (fun U : UG d =>
      (if h : Antitone (rv lam + Pi.single i 1) then
        c i * (Tomography.keylGeneralizedPower (addP lam i h) (Zc ρ U)).re else 0)) := by
    intro i
    split_ifs with h
    · exact continuous_const.mul (genPre_cont ρ (addP lam i h))
    · exact continuous_const
  have hHc : Continuous H :=
    ((continuous_const.mul hΔc).sub (continuous_const.mul (continuous_finsetSum _ (fun i _ => hdc i))))
  have hstep := integral_mono (integRe hFc) (integRe hHc) hle
  refine le_trans hstep (le_of_eq ?_)
  simp only [hH]
  rw [integral_sub, integral_const_mul, integral_const_mul, integral_finsetSum]
  rotate_left
  · intro i _; exact integRe (hdc i)
  · exact integRe (continuous_const.mul hΔc)
  · exact integRe (continuous_const.mul (continuous_finsetSum _ (fun i _ => hdc i)))
  have hΔint : ∫ U, Δr U ∂(unitaryHaar d) = sev d lam.val α / schurDimension lam :=
    haar_re lam ρ V hV α hρV
  rw [hΔint]
  have hterm : ∀ i : Fin d, ∫ U, (if h : Antitone (rv lam + Pi.single i 1) then
      c i * (Tomography.keylGeneralizedPower (addP lam i h) (Zc ρ U)).re else 0) ∂(unitaryHaar d) =
      if h : Antitone (rv lam + Pi.single i 1) then
        c i * (sev d (addP lam i h).val α / schurDimension (addP lam i h)) else 0 := by
    intro i
    split_ifs with h
    · rw [integral_const_mul, haar_re (addP lam i h) ρ V hV α hρV]
    · simp
  simp_rw [hterm]
  have hD : schurDimension lam ≠ 0 := (schurDim_pos lam).ne'
  simp only [hK, hc, hp2]
  field_simp

end bound

end KeylR

-- ===== KR4 =====

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder

noncomputable section

namespace KeylR
open QAlgorithms QAlgorithms.Schur KeylS

variable {d : ℕ}

/-- Chebyshev's sum inequality on `Fin d` -/
lemma cheb (w μ : Fin d → ℝ) (hw : Monotone w) (hμ : Antitone μ) :
    (d : ℝ) * ∑ k, w k * μ k ≤ (∑ k, w k) * ∑ k, μ k := by
  have hav : Antivary w μ := by
    intro i j hij
    apply hw
    by_contra h
    push_neg at h
    exact absurd (hμ h.le) (not_le.2 hij)
  have := hav.card_smul_sum_le_sum_smul_sum
  simp only [Fintype.card_fin, nsmul_eq_mul, smul_eq_mul] at this
  exact this

lemma rv_real_anti {n : ℕ} (lam : Partition d n) : Antitone (fun k : Fin d => (rv lam k : ℝ)) :=
  fun a b h => by show (rv lam b : ℝ) ≤ rv lam a; exact_mod_cast rv_anti lam h

lemma sum_rv_real {n : ℕ} (lam : Partition d n) : ∑ k, (rv lam k : ℝ) = n := by
  exact_mod_cast sum_rv lam

lemma sum_odd (d : ℕ) : ∑ k : Fin d, (2 * (k : ℝ) + 1) = (d : ℝ) ^ 2 := by
  induction d with
  | zero => simp
  | succ d ih => rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last] at ih ⊢; rw [ih]; push_cast; ring

lemma sum_lin (d : ℕ) : ∑ k : Fin d, ((d : ℝ) + k - 1) = 3 * (d : ℝ) * (d - 1) / 2 := by
  have h : ∑ k : Fin d, (k : ℝ) = (d : ℝ) * (d - 1) / 2 := by
    induction d with
    | zero => simp
    | succ d ih => rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last] at ih ⊢; rw [ih]; push_cast; ring
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h]
  simp
  ring

/-- `Σ_k (2k+1) λ_k ≤ n d` -/
lemma odd_weight_le (hd : 0 < d) {n : ℕ} (lam : Partition d n) :
    ∑ k : Fin d, (2 * (k : ℝ) + 1) * rv lam k ≤ n * d := by
  have h := cheb (fun k : Fin d => 2 * (k : ℝ) + 1) (fun k => (rv lam k : ℝ))
    (fun a b hab => by
      show 2 * ((a : ℕ) : ℝ) + 1 ≤ 2 * ((b : ℕ) : ℝ) + 1
      have : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
      linarith) (rv_real_anti lam)
  rw [sum_odd, sum_rv_real] at h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  nlinarith

/-- `Σ_k (d + k - 1) μ_k ≤ (3/2)(d-1) m` -/
lemma lin_weight_le (hd : 0 < d) {m : ℕ} (μ : Partition d m) :
    ∑ k : Fin d, ((d : ℝ) + k - 1) * rv μ k ≤ 3 * ((d : ℝ) - 1) / 2 * m := by
  have h := cheb (fun k : Fin d => (d : ℝ) + k - 1) (fun k => (rv μ k : ℝ))
    (fun a b hab => by
      show (d : ℝ) + ((a : ℕ) : ℝ) - 1 ≤ (d : ℝ) + ((b : ℕ) : ℝ) - 1
      have : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
      linarith) (rv_real_anti μ)
  rw [sum_lin, sum_rv_real] at h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : (d : ℝ) * ∑ k : Fin d, ((d : ℝ) + k - 1) * rv μ k ≤ (d : ℝ) * (3 * ((d : ℝ) - 1) / 2 * m) := by
    linarith
  exact le_of_mul_le_mul_left this hd'

open Classical in
/-- reindexing pairs `(λ, k)` with `λ + e_k` a partition by pairs `(μ, k)` with `μ - e_k` a partition -/
lemma reindex {n : ℕ} (G : Fin d → Partition d n → Partition d (n+1) → ℝ) :
    ∑ lam : Partition d n, ∑ k : Fin d,
        (if h : Antitone (rv lam + Pi.single k 1) then G k lam (addP lam k h) else 0) =
      ∑ μ : Partition d (n+1), ∑ k : Fin d,
        (if h : Antitone (rv μ - Pi.single k 1) ∧ 1 ≤ rv μ k then G k (remP μ k h) μ else 0) := by
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Partition d (n+1))))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_dite, Finset.sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  refine Finset.sum_bij' (fun x _ => ⟨addP x.1 k (Finset.mem_filter.1 x.2).2, ?_⟩)
    (fun y _ => ⟨remP y.1 k (Finset.mem_filter.1 y.2).2, ?_⟩) ?_ ?_ ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h := (Finset.mem_filter.1 x.2).2
    rw [rv_addP, rv_add_sub]
    exact ⟨rv_anti _, by simp⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h := (Finset.mem_filter.1 y.2).2
    rw [rv_remP, rv_sub_add _ k h.2]
    exact rv_anti _
  · intro x _; exact Finset.mem_attach _ _
  · intro y _; exact Finset.mem_attach _ _
  · intro x _
    apply Subtype.ext
    apply part_ext
    rw [rv_remP, rv_addP, rv_add_sub]
  · intro y _
    apply Subtype.ext
    apply part_ext
    rw [rv_addP, rv_remP, rv_sub_add _ k (Finset.mem_filter.1 y.2).2.2]
  · intro x _
    have he : remP (addP x.1 k (Finset.mem_filter.1 x.2).2) k (by
        rw [rv_addP, rv_add_sub]; exact ⟨rv_anti _, by simp⟩) = x.1 := by
      apply part_ext; rw [rv_remP, rv_addP, rv_add_sub]
    simp only
    rw [he]

section comb
variable (hd : 0 < d) (α : Fin d → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∑ i, α i = 1)

include hα0 in
lemma sev_nonneg {μ : YoungDiagram} : 0 ≤ sev d μ α := by
  unfold sev
  exact Finset.sum_nonneg (fun T _ => Finset.prod_nonneg (fun a _ => hα0 _))

include hd hα1 in
lemma L1 {n : ℕ} : ∑ lam : Partition d n, fP lam * sev d lam.val α = 1 := by
  rw [C0 hd α, hα1, one_pow]

lemma fP_nonneg {n : ℕ} (lam : Partition d n) : 0 ≤ fP lam := by unfold fP; positivity

lemma sq_sum_eq {n : ℕ} (lam : Partition d n) :
    ∑ i : Fin d, ((rv lam i : ℝ)) ^ 2 = p2s lam + ∑ k : Fin d, (2 * (k : ℝ) + 1) * rv lam k := by
  unfold p2s
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => by ring)

include hd hα0 hα1 in
/-- `E Σ λ_i² ≤ n(n-1) p₂ + n d` -/
lemma L2 {n : ℕ} : ∑ lam : Partition d n, fP lam * sev d lam.val α * ∑ i : Fin d, ((rv lam i : ℝ)) ^ 2 ≤
    (n * (n - 1) : ℕ) * ∑ i, α i ^ 2 + n * d := by
  have h1 := C1 (n := n) hd α hα1
  have h2 := L1 hd α hα1 (n := n)
  calc ∑ lam : Partition d n, fP lam * sev d lam.val α * ∑ i : Fin d, ((rv lam i : ℝ)) ^ 2
      = ∑ lam : Partition d n, (fP lam * sev d lam.val α * p2s lam +
          fP lam * sev d lam.val α * ∑ k : Fin d, (2 * (k : ℝ) + 1) * rv lam k) := by
        refine Finset.sum_congr rfl (fun lam _ => ?_); rw [sq_sum_eq]; ring
    _ ≤ ∑ lam : Partition d n, (fP lam * sev d lam.val α * p2s lam +
          fP lam * sev d lam.val α * (n * d)) := by
        refine Finset.sum_le_sum (fun lam _ => ?_)
        have := odd_weight_le hd lam
        have hnn : 0 ≤ fP lam * sev d lam.val α := mul_nonneg (fP_nonneg lam) (sev_nonneg α hα0)
        nlinarith
    _ = _ := by rw [Finset.sum_add_distrib, h1, ← Finset.sum_mul, h2, one_mul]

include hα1 in
lemma L4 {n : ℕ} (lam : Partition d n) :
    ∑ k : Fin d, (if h : Antitone (rv lam + Pi.single k 1) then sev d (addP lam k h).val α else 0) =
      sev d lam.val α := by
  rw [pieri_eval, hα1, one_mul]

include hd in
/-- weighted transfer from level `n` pairs to level `n+1` -/
lemma transfer {n : ℕ} (hfun : Partition d (n+1) → ℝ) :
    ∑ lam : Partition d n, ∑ k : Fin d, (if h : Antitone (rv lam + Pi.single k 1) then
      fP lam * sev d (addP lam k h).val α * hfun (addP lam k h) else 0) =
    ∑ μ : Partition d (n+1), fP μ * sev d μ.val α * hfun μ := by
  rw [reindex (fun k lam μ => fP lam * sev d μ.val α * hfun μ)]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [C3 hd μ, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs <;> simp

lemma sq_addP {n : ℕ} (lam : Partition d n) (k : Fin d) (h : Antitone (rv lam + Pi.single k 1)) :
    ∑ i : Fin d, ((rv (addP lam k h) i : ℝ)) ^ 2 = ∑ i : Fin d, ((rv lam i : ℝ)) ^ 2 + 2 * rv lam k + 1 := by
  rw [rv_addP]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
    ← Finset.sum_erase_add _ (fun i : Fin d => ((rv lam i : ℝ)) ^ 2) (Finset.mem_univ k)]
  rw [Finset.sum_congr rfl (fun i hi => by rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi), add_zero])]
  simp only [Pi.add_apply, Pi.single_eq_same]
  push_cast; ring

lemma odd_addP {n : ℕ} (lam : Partition d n) (k : Fin d) (h : Antitone (rv lam + Pi.single k 1)) :
    ∑ i : Fin d, (2 * (i : ℝ) + 1) * rv (addP lam k h) i =
      ∑ i : Fin d, (2 * (i : ℝ) + 1) * rv lam i + (2 * k + 1) := by
  rw [rv_addP]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
    ← Finset.sum_erase_add _ (fun i : Fin d => (2 * ((i : ℕ) : ℝ) + 1) * rv lam i) (Finset.mem_univ k)]
  rw [Finset.sum_congr rfl (fun i hi => by rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi), add_zero])]
  simp only [Pi.add_apply, Pi.single_eq_same]
  push_cast; ring

/-- sum of squared row lengths -/
def sqR {m : ℕ} (μ : Partition d m) : ℝ := ∑ i : Fin d, ((rv μ i : ℝ)) ^ 2
/-- odd-weighted row sum -/
def oddR {m : ℕ} (μ : Partition d m) : ℝ := ∑ i : Fin d, (2 * ((i : ℕ) : ℝ) + 1) * rv μ i

include hd hα0 hα1 in
/-- **B1**: `Σ fP_λ λ_k s_{λ+e_k}(α) ≥ n p₂` -/
lemma B1 {n : ℕ} : (n : ℝ) * ∑ i, α i ^ 2 ≤ ∑ lam : Partition d n, ∑ k : Fin d,
    (if h : Antitone (rv lam + Pi.single k 1) then fP lam * (rv lam k : ℝ) * sev d (addP lam k h).val α else 0) := by
  have hE1 := transfer hd α (n := n) (fun μ => sqR μ)
  have hE2 := transfer hd α (n := n) (fun μ => oddR μ)
  -- pieri sums
  have hP : ∀ (g : Partition d n → ℝ), ∑ lam : Partition d n, ∑ k : Fin d,
      (if h : Antitone (rv lam + Pi.single k 1) then fP lam * sev d (addP lam k h).val α * g lam else 0) =
      ∑ lam : Partition d n, fP lam * sev d lam.val α * g lam := by
    intro g
    refine Finset.sum_congr rfl (fun lam _ => ?_)
    rw [← L4 α hα1 lam, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs <;> ring
  set K1 := ∑ lam : Partition d n, ∑ k : Fin d,
    (if h : Antitone (rv lam + Pi.single k 1) then fP lam * sev d (addP lam k h).val α * (k : ℝ) else 0) with hK1
  set B := ∑ lam : Partition d n, ∑ k : Fin d,
    (if h : Antitone (rv lam + Pi.single k 1) then fP lam * (rv lam k : ℝ) * sev d (addP lam k h).val α else 0) with hB
  have hK1nn : 0 ≤ K1 := Finset.sum_nonneg (fun lam _ => Finset.sum_nonneg (fun k _ => by
    split_ifs
    · exact mul_nonneg (mul_nonneg (fP_nonneg _) (sev_nonneg α hα0)) (by positivity)
    · exact le_rfl))
  have hA1 : ∑ lam : Partition d n, ∑ k : Fin d,
      (if h : Antitone (rv lam + Pi.single k 1) then fP lam * sev d (addP lam k h).val α * sqR (addP lam k h) else 0) =
      ∑ lam : Partition d n, fP lam * sev d lam.val α * sqR lam + 2 * B + 1 := by
    have : ∀ lam : Partition d n, ∀ k : Fin d,
        (if h : Antitone (rv lam + Pi.single k 1) then fP lam * sev d (addP lam k h).val α * sqR (addP lam k h) else 0) =
        (if h : Antitone (rv lam + Pi.single k 1) then fP lam * sev d (addP lam k h).val α * sqR lam else 0) +
        2 * (if h : Antitone (rv lam + Pi.single k 1) then fP lam * (rv lam k : ℝ) * sev d (addP lam k h).val α else 0) +
        (if h : Antitone (rv lam + Pi.single k 1) then fP lam * sev d (addP lam k h).val α * 1 else 0) := by
      intro lam k
      split_ifs with h
      · simp only [sqR]; rw [sq_addP]; ring
      · ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hP, hP (fun _ => 1)]
    simp only [mul_one]
    rw [L1 hd α hα1]
  have hA2 : ∑ lam : Partition d n, ∑ k : Fin d,
      (if h : Antitone (rv lam + Pi.single k 1) then fP lam * sev d (addP lam k h).val α * oddR (addP lam k h) else 0) =
      ∑ lam : Partition d n, fP lam * sev d lam.val α * oddR lam + 2 * K1 + 1 := by
    have : ∀ lam : Partition d n, ∀ k : Fin d,
        (if h : Antitone (rv lam + Pi.single k 1) then fP lam * sev d (addP lam k h).val α * oddR (addP lam k h) else 0) =
        (if h : Antitone (rv lam + Pi.single k 1) then fP lam * sev d (addP lam k h).val α * oddR lam else 0) +
        2 * (if h : Antitone (rv lam + Pi.single k 1) then fP lam * sev d (addP lam k h).val α * (k : ℝ) else 0) +
        (if h : Antitone (rv lam + Pi.single k 1) then fP lam * sev d (addP lam k h).val α * 1 else 0) := by
      intro lam k
      split_ifs with h
      · simp only [oddR]; rw [odd_addP]; ring
      · ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hP, hP (fun _ => 1)]
    simp only [mul_one]
    rw [L1 hd α hα1]
  have hC1n := C1 (n := n) hd α hα1
  have hC1n1 := C1 (n := n+1) hd α hα1
  have hpq : ∀ {m : ℕ} (μ : Partition d m), p2s μ = sqR μ - oddR μ := by
    intro m μ; simp only [sqR, oddR]; rw [sq_sum_eq]; ring
  have e1 : ∑ μ : Partition d (n+1), fP μ * sev d μ.val α * sqR μ - ∑ μ : Partition d (n+1), fP μ * sev d μ.val α * oddR μ =
      ((n + 1) * (n + 1 - 1) : ℕ) * ∑ i, α i ^ 2 := by
    rw [← Finset.sum_sub_distrib, ← hC1n1]
    refine Finset.sum_congr rfl (fun μ _ => ?_); rw [hpq]; ring
  have e0 : ∑ lam : Partition d n, fP lam * sev d lam.val α * sqR lam - ∑ lam : Partition d n, fP lam * sev d lam.val α * oddR lam =
      (n * (n - 1) : ℕ) * ∑ i, α i ^ 2 := by
    rw [← Finset.sum_sub_distrib, ← hC1n]
    refine Finset.sum_congr rfl (fun lam _ => ?_); rw [hpq]; ring
  rw [hE1] at hA1
  rw [hE2] at hA2
  have hp2 : 0 ≤ ∑ i, α i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rcases n with _ | n
  · simp only [Nat.cast_zero, zero_mul]
    exact Finset.sum_nonneg (fun lam _ => Finset.sum_nonneg (fun k _ => by
      split_ifs
      · exact mul_nonneg (mul_nonneg (fP_nonneg _) (by positivity)) (sev_nonneg α hα0)
      · exact le_rfl))
  · push_cast at e1 e0 ⊢
    nlinarith

lemma corner_le {m : ℕ} (μ : Partition d m) (k : Fin d) :
    (if h : Antitone (rv μ - Pi.single k 1) ∧ 1 ≤ rv μ k then
      ((rv μ k : ℝ) - 1) * ((rv μ k : ℝ) + d - 1 - k) else 0) ≤
    ((rv μ k : ℝ)) ^ 2 - (2 * (k : ℝ) + 1) * rv μ k + ((d : ℝ) + k - 1) * rv μ k := by
  have hk : (k : ℝ) + 1 ≤ d := by have := k.isLt; exact_mod_cast this
  split_ifs with h
  · nlinarith
  · by_cases h0 : rv μ k = 0
    · rw [h0]; simp
    · have h1 : (1 : ℝ) ≤ rv μ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
      nlinarith

include hd hα0 hα1 in
/-- **B2**: the dimension-weighted cross term -/
lemma B2 {n : ℕ} : ∑ lam : Partition d n, ∑ k : Fin d,
    (if h : Antitone (rv lam + Pi.single k 1) then
      fP lam * (rv lam k : ℝ) * sev d (addP lam k h).val α * (schurDimension (addP lam k h) / schurDimension lam)
      else 0) ≤ (n : ℝ) * ∑ i, α i ^ 2 + 3 * ((d : ℝ) - 1) / 2 := by
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  -- content ratio
  have hterm : ∀ lam : Partition d n, ∀ k : Fin d,
      (if h : Antitone (rv lam + Pi.single k 1) then
        fP lam * (rv lam k : ℝ) * sev d (addP lam k h).val α * (schurDimension (addP lam k h) / schurDimension lam)
        else 0) =
      (if h : Antitone (rv lam + Pi.single k 1) then
        (fun k lam μ => (rv lam k : ℝ) * ((lv lam k : ℝ) + 1) * (fP μ * sev d μ.val α) / (n + 1)) k lam (addP lam k h)
        else 0) := by
    intro lam k
    split_ifs with h
    · have hc := C4 hd lam k h
      have hD := schurDim_pos lam
      simp only
      field_simp
      linear_combination (rv lam k : ℝ) * sev d (addP lam k h).val α * hc
    · rfl
  simp_rw [hterm]
  rw [reindex (fun k lam μ => (rv lam k : ℝ) * ((lv lam k : ℝ) + 1) * (fP μ * sev d μ.val α) / (n + 1))]
  have hμ : ∀ μ : Partition d (n+1), ∑ k : Fin d,
      (if h : Antitone (rv μ - Pi.single k 1) ∧ 1 ≤ rv μ k then
        (rv (remP μ k h) k : ℝ) * ((lv (remP μ k h) k : ℝ) + 1) * (fP μ * sev d μ.val α) / (n + 1) else 0) ≤
      (fP μ * sev d μ.val α) / (n + 1) * (p2s μ + 3 * ((d : ℝ) - 1) / 2 * (n + 1 : ℕ)) := by
    intro μ
    have hnn : 0 ≤ (fP μ * sev d μ.val α) / (n + 1) :=
      div_nonneg (mul_nonneg (fP_nonneg μ) (sev_nonneg α hα0)) hn1.le
    have h1 : ∀ k : Fin d, (if h : Antitone (rv μ - Pi.single k 1) ∧ 1 ≤ rv μ k then
        (rv (remP μ k h) k : ℝ) * ((lv (remP μ k h) k : ℝ) + 1) * (fP μ * sev d μ.val α) / (n + 1) else 0) =
        (fP μ * sev d μ.val α) / (n + 1) *
          (if h : Antitone (rv μ - Pi.single k 1) ∧ 1 ≤ rv μ k then
            ((rv μ k : ℝ) - 1) * ((rv μ k : ℝ) + d - 1 - k) else 0) := by
      intro k
      split_ifs with h
      · have e1 : (rv (remP μ k h) k : ℝ) = (rv μ k : ℝ) - 1 := by
          rw [rv_remP]; simp only [Pi.sub_apply, Pi.single_eq_same]
          rw [Nat.cast_sub h.2]; simp
        have e2 : ((lv (remP μ k h) k : ℝ) + 1) = (rv μ k : ℝ) + d - 1 - k := by
          simp only [lv, dl, rv_remP, Pi.sub_apply, Pi.single_eq_same]
          have := k.isLt
          rw [Nat.cast_add, Nat.cast_sub h.2, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
          simp; ring
        rw [e1, e2]; ring
      · simp
    simp_rw [h1]
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hnn
    calc ∑ k : Fin d, (if h : Antitone (rv μ - Pi.single k 1) ∧ 1 ≤ rv μ k then
          ((rv μ k : ℝ) - 1) * ((rv μ k : ℝ) + d - 1 - k) else 0)
        ≤ ∑ k : Fin d, (((rv μ k : ℝ)) ^ 2 - (2 * (k : ℝ) + 1) * rv μ k + ((d : ℝ) + k - 1) * rv μ k) :=
          Finset.sum_le_sum (fun k _ => corner_le μ k)
      _ = p2s μ + ∑ k : Fin d, ((d : ℝ) + k - 1) * rv μ k := by
          unfold p2s; rw [← Finset.sum_add_distrib]
      _ ≤ p2s μ + 3 * ((d : ℝ) - 1) / 2 * (n + 1 : ℕ) := by
          have := lin_weight_le hd μ; linarith
  refine le_trans (Finset.sum_le_sum (fun μ _ => hμ μ)) (le_of_eq ?_)
  have hC1 := C1 (n := n+1) hd α hα1
  have hL1 := L1 hd α hα1 (n := n+1)
  have : ∑ μ : Partition d (n+1), (fP μ * sev d μ.val α) / (n + 1) * (p2s μ + 3 * ((d : ℝ) - 1) / 2 * (n + 1 : ℕ)) =
      (∑ μ : Partition d (n+1), fP μ * sev d μ.val α * p2s μ) / (n + 1) +
        3 * ((d : ℝ) - 1) / 2 * (∑ μ : Partition d (n+1), fP μ * sev d μ.val α) := by
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    field_simp
    push_cast
    ring
  rw [this, hC1, hL1]
  push_cast
  field_simp

end comb

end KeylR

-- ===== KR5 =====

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder

noncomputable section

namespace KeylR
open QAlgorithms QAlgorithms.Schur KeylS

variable {d : ℕ}

lemma amgm (a D D' : ℝ) (ha : 0 ≤ a) (hD : 0 < D) (hD' : 0 < D') :
    2 * a - a * (D' / D) ≤ a * (D / D') := by
  have hx : D / D' + D' / D - 2 = (D - D') ^ 2 / (D * D') := by field_simp; ring
  have hx0 : 0 ≤ (D - D') ^ 2 / (D * D') := by positivity
  nlinarith

lemma rhs_eq (f D r S D' m : ℝ) :
    2 * (f * D) * (r / m * (S / D')) = 2 / m * (f * r * S * (D / D')) := by ring

section final
set_option backward.isDefEq.respectTransparency.types false
open scoped Matrix.Norms.Elementwise

variable (hd : 0 < d) {n : ℕ} (hn : 0 < n) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsDensityMatrix ρ)

lemma est_cont (lam : Partition d n) :
    Continuous (fun U : UG d => frobNorm (Schur.estimate hd hn lam U - ρ) ^ 2) := by
  have : (fun U : UG d => frobNorm (Schur.estimate hd hn lam U - ρ) ^ 2) =
      fun U => ∑ i, ∑ j, ‖(Schur.estimate hd hn lam U - ρ) i j‖ ^ 2 := by
    funext U; rw [frob_sq]
  rw [this]
  have hU : Continuous (fun U : UG d => (U : Matrix (Fin d) (Fin d) ℂ)) := continuous_subtype_val
  have hM : Continuous (fun U : UG d => Schur.estimate hd hn lam U - ρ) := by
    unfold Schur.estimate
    exact ((hU.mul continuous_const).mul (continuous_star.comp hU)).sub continuous_const
  refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
  exact ((continuous_apply j).comp ((continuous_apply i).comp hM)).norm.pow 2

include hρ in
/-- the risk as a finite sum of real integrals -/
lemma risk_eq : Tomography.keylSquaredRisk hd hn ρ hρ = ENNReal.ofReal (∑ lam : Partition d n,
    ∫ U, frobNorm (Schur.estimate hd hn lam U - ρ) ^ 2 *
      (fP lam * schurDimension lam * (Tomography.keylGeneralizedPower lam (Zc ρ U)).re) ∂(unitaryHaar d)) := by
  set Gr : Partition d n → UG d → ℝ := fun lam U =>
    fP lam * schurDimension lam * (Tomography.keylGeneralizedPower lam (Zc ρ U)).re with hGr
  set Fr : Partition d n → UG d → ℝ := fun lam U => frobNorm (Schur.estimate hd hn lam U - ρ) ^ 2 with hFr
  have hGc : ∀ lam, Continuous (Gr lam) := fun lam => continuous_const.mul (genPre_cont ρ lam)
  have hFc : ∀ lam, Continuous (Fr lam) := fun lam => est_cont hd hn ρ lam
  have hGn : ∀ lam U, 0 ≤ Gr lam U := by
    intro lam U
    refine mul_nonneg (mul_nonneg (fP_nonneg lam) (schurDim_pos lam).le) ?_
    exact (Complex.nonneg_iff.1 (genP_nonneg' lam (conj_psd ρ hρ.1 _))).1
  have hFn : ∀ lam U, 0 ≤ Fr lam U := fun lam U => sq_nonneg _
  have hgm : Measurable (fun o : Partition d n × UG d => ENNReal.ofReal (Gr o.1 o.2)) :=
    measurable_from_prod_countable_right (fun lam => ENNReal.measurable_ofReal.comp (hGc lam).measurable)
  have hfm : Measurable (fun o : Partition d n × UG d => ENNReal.ofReal (Fr o.1 o.2)) :=
    measurable_from_prod_countable_right (fun lam => ENNReal.measurable_ofReal.comp (hFc lam).measurable)
  unfold Tomography.keylSquaredRisk Tomography.keylJointLaw
  show ∫⁻ o, ENNReal.ofReal (Fr o.1 o.2) ∂(Measure.count.prod (unitaryHaar d)).withDensity
    (fun o => ENNReal.ofReal (Gr o.1 o.2)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hgm hfm]
  have hmul : ∀ o : Partition d n × UG d,
      ((fun o : Partition d n × UG d => ENNReal.ofReal (Gr o.1 o.2)) *
        (fun o : Partition d n × UG d => ENNReal.ofReal (Fr o.1 o.2))) o =
      ENNReal.ofReal (Fr o.1 o.2 * Gr o.1 o.2) := by
    intro o
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hGn _ _), mul_comm]
  simp_rw [hmul]
  have hmeas : Measurable (fun o : Partition d n × UG d => ENNReal.ofReal (Fr o.1 o.2 * Gr o.1 o.2)) :=
    measurable_from_prod_countable_right (fun lam =>
      ENNReal.measurable_ofReal.comp ((hFc lam).mul (hGc lam)).measurable)
  rw [lintegral_prod _ hmeas.aemeasurable, lintegral_fintype]
  simp only [Measure.count_singleton, mul_one]
  rw [ENNReal.ofReal_sum_of_nonneg (fun lam _ => integral_nonneg (fun U => mul_nonneg (hFn lam U) (hGn lam U)))]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  have hint : Integrable (fun U => Fr lam U * Gr lam U) (unitaryHaar d) := integRe ((hFc lam).mul (hGc lam))
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun U => mul_nonneg (hFn lam U) (hGn lam U)))).symm

include hρ in
/-- the real form of the risk bound -/
theorem real_bound : ∑ lam : Partition d n,
    ∫ U, frobNorm (Schur.estimate hd hn lam U - ρ) ^ 2 *
      (fP lam * schurDimension lam * (Tomography.keylGeneralizedPower lam (Zc ρ U)).re) ∂(unitaryHaar d) ≤
      ((4 : ℝ) * d - 3) / n := by
  obtain ⟨V, α, hV, hα0, hα1, hρV⟩ := spec ρ hρ
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set p2 := ∑ i, α i ^ 2 with hp2
  have hp2n : 0 ≤ p2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  refine le_trans (Finset.sum_le_sum (fun lam _ => int_bound hd hn ρ hρ V hV α hρV lam)) ?_
  -- rewrite the bound
  set B1s := ∑ lam : Partition d n, ∑ k : Fin d,
    (if h : Antitone (rv lam + Pi.single k 1) then fP lam * (rv lam k : ℝ) * sev d (addP lam k h).val α else 0)
    with hB1s
  set B2s := ∑ lam : Partition d n, ∑ k : Fin d,
    (if h : Antitone (rv lam + Pi.single k 1) then
      fP lam * (rv lam k : ℝ) * sev d (addP lam k h).val α * (schurDimension (addP lam k h) / schurDimension lam)
      else 0) with hB2s
  have hB1 : (n : ℝ) * p2 ≤ B1s := B1 hd α hα0 hα1
  have hB2 : B2s ≤ (n : ℝ) * p2 + 3 * ((d : ℝ) - 1) / 2 := B2 hd α hα0 hα1
  have hL1 := L1 hd α hα1 (n := n)
  have hL2 := L2 hd α hα0 hα1 (n := n)
  -- termwise AM-GM
  have hterm : ∀ lam : Partition d n, ∀ i : Fin d,
      (2 / (n : ℝ)) * (2 * (if h : Antitone (rv lam + Pi.single i 1) then
          fP lam * (rv lam i : ℝ) * sev d (addP lam i h).val α else 0) -
        (if h : Antitone (rv lam + Pi.single i 1) then
          fP lam * (rv lam i : ℝ) * sev d (addP lam i h).val α *
            (schurDimension (addP lam i h) / schurDimension lam) else 0)) ≤
      2 * (fP lam * schurDimension lam) *
        (if h : Antitone (rv lam + Pi.single i 1) then
          ((lam.val.rowLen (i : ℕ) : ℝ) / n) * (sev d (addP lam i h).val α / schurDimension (addP lam i h))
          else 0) := by
    intro lam i
    split_ifs with h
    · have ha : 0 ≤ fP lam * (rv lam i : ℝ) * sev d (addP lam i h).val α :=
        mul_nonneg (mul_nonneg (fP_nonneg lam) (Nat.cast_nonneg _)) (sev_nonneg α hα0)
      exact (mul_le_mul_of_nonneg_left (amgm _ _ _ ha (schurDim_pos lam) (schurDim_pos (addP lam i h)))
        (div_nonneg zero_le_two hnr.le)).trans (rhs_eq (fP lam) (schurDimension lam) (rv lam i : ℝ)
          (sev d (addP lam i h).val α) (schurDimension (addP lam i h)) (n : ℝ)).symm.le
    · simp
  have hcross : (2 / (n : ℝ)) * (2 * B1s - B2s) ≤ ∑ lam : Partition d n, 2 * (fP lam * schurDimension lam) *
      ∑ i : Fin d, (if h : Antitone (rv lam + Pi.single i 1) then
          ((lam.val.rowLen (i : ℕ) : ℝ) / n) * (sev d (addP lam i h).val α / schurDimension (addP lam i h))
          else 0) := by
    have heq : (2 / (n : ℝ)) * (2 * B1s - B2s) = ∑ lam : Partition d n, ∑ i : Fin d,
        (2 / (n : ℝ)) * (2 * (if h : Antitone (rv lam + Pi.single i 1) then
          fP lam * (rv lam i : ℝ) * sev d (addP lam i h).val α else 0) -
        (if h : Antitone (rv lam + Pi.single i 1) then
          fP lam * (rv lam i : ℝ) * sev d (addP lam i h).val α *
            (schurDimension (addP lam i h) / schurDimension lam) else 0)) := by
      rw [hB1s, hB2s, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun lam _ => ?_)
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [heq]
    refine Finset.sum_le_sum (fun lam _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hterm lam i)
  set E := ∑ lam : Partition d n, fP lam * sev d lam.val α * ∑ i : Fin d, ((rv lam i : ℝ)) ^ 2 with hE
  have hfirst : ∑ lam : Partition d n, fP lam * sev d lam.val α *
      (∑ i : Fin d, ((lam.val.rowLen (i : ℕ) : ℝ) / n) ^ 2 + p2) = E / (n : ℝ) ^ 2 + p2 := by
    calc _ = ∑ lam : Partition d n, ((fP lam * sev d lam.val α * ∑ i : Fin d, ((rv lam i : ℝ)) ^ 2) / (n : ℝ) ^ 2
          + fP lam * sev d lam.val α * p2) := by
          refine Finset.sum_congr rfl (fun lam _ => ?_)
          have : ∑ i : Fin d, ((lam.val.rowLen (i : ℕ) : ℝ) / n) ^ 2 =
              (∑ i : Fin d, ((rv lam i : ℝ)) ^ 2) / (n : ℝ) ^ 2 := by
            rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun i _ => ?_); rw [div_pow]; rfl
          rw [this]; ring
      _ = E / (n : ℝ) ^ 2 + (∑ lam : Partition d n, fP lam * sev d lam.val α) * p2 := by
          rw [Finset.sum_add_distrib, hE, Finset.sum_div, Finset.sum_mul]
      _ = E / (n : ℝ) ^ 2 + p2 := by rw [hL1, one_mul]
  rw [Finset.sum_sub_distrib, hfirst]
  have hL2' : E ≤ (n : ℝ) * (n - 1) * p2 + n * d := by
    have h1 : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * (n - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
    have := hL2; rw [h1] at this; exact this
  have hX : (n : ℝ) * p2 - 3 * ((d : ℝ) - 1) / 2 ≤ 2 * B1s - B2s := by linarith
  have key : E + (n : ℝ) ^ 2 * p2 - 2 * n * (2 * B1s - B2s) ≤ n * (4 * d - 3) := by
    nlinarith [mul_le_mul_of_nonneg_left hX hnr.le]
  have hle : E / (n : ℝ) ^ 2 + p2 - (2 / (n : ℝ)) * (2 * B1s - B2s) ≤ ((4 : ℝ) * d - 3) / n := by
    rw [show E / (n : ℝ) ^ 2 + p2 - (2 / (n : ℝ)) * (2 * B1s - B2s) =
      (E + (n : ℝ) ^ 2 * p2 - 2 * n * (2 * B1s - B2s)) / (n : ℝ) ^ 2 by field_simp]
    rw [div_le_div_iff₀ (by positivity) hnr]
    nlinarith [mul_le_mul_of_nonneg_left key hnr.le]
  linarith

include hρ in
theorem K3 : Tomography.keylSquaredRisk hd hn ρ hρ ≤ ENNReal.ofReal (((4 : ℝ) * d - 3) / n) := by
  rw [risk_eq]
  exact ENNReal.ofReal_le_ofReal (real_bound hd hn ρ hρ)

end final

end KeylR

-- ===== final =====
section solution_sec
open QAlgorithms

theorem solution (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (density : IsDensityMatrix rho) :
    Tomography.keylSquaredRisk hd hn rho density ≤ ENNReal.ofReal (((4 : ℝ) * d - 3) / n) :=
  KeylR.K3 hd hn rho density

end solution_sec

-- Prove2me | solution 1 for ReLUBinaryDepth.ProductTradeoff.Supplement.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T12:02:44.996525+00:00
-- url     : https://prove2.me/submissions/8bcdda78-9f12-48cc-b329-28d0d32dbd89

import Mathlib
import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Network
import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Supplement_Layered
import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Supplement_ThresholdCircuit

section
set_option autoImplicit false

namespace ReLUBinaryDepth.Dev.Muroga

open Finset

/-- Dot product with a fixed vector as a linear functional. -/
noncomputable def dotL {κ : Type} [Fintype κ] (d : κ → ℝ) : (κ → ℝ) →ₗ[ℝ] ℝ where
  toFun v := dotProduct v d
  map_add' := fun u v => add_dotProduct u v d
  map_smul' := fun c v => smul_dotProduct c v d

theorem step {Y κ : Type} [Fintype Y] [DecidableEq Y] [Fintype κ] [DecidableEq κ]
    (r : Y → κ → ℝ)
    (hker : ∀ d : κ → ℝ, (∀ y, dotProduct (r y) d = 0) → d = 0)
    (z : κ → ℝ) (hz : ∀ y, 1 ≤ dotProduct (r y) z)
    (S : Finset Y) (hS : S.card < Fintype.card κ)
    (hind : LinearIndepOn ℝ r (S : Set Y))
    (htight : ∀ y ∈ S, dotProduct (r y) z = 1) :
    ∃ (z' : κ → ℝ) (y0 : Y), y0 ∉ S ∧ (∀ y, 1 ≤ dotProduct (r y) z') ∧
      LinearIndepOn ℝ r ((insert y0 S : Finset Y) : Set Y) ∧
      ∀ y ∈ insert y0 S, dotProduct (r y) z' = 1 := by
  -- a direction orthogonal to S
  let L : (κ → ℝ) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun d y => dotProduct (r y) d
      map_add' := fun u v => by funext y; simp [dotProduct_add]
      map_smul' := fun c v => by funext y; simp [dotProduct_smul] }
  have hne : LinearMap.ker L ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simpa using hS
  obtain ⟨d, hdk, hd0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hdS : ∀ y ∈ S, dotProduct (r y) d = 0 := by
    intro y hy
    have := congrFun (LinearMap.mem_ker.1 hdk) ⟨y, hy⟩
    simpa [L] using this
  have hex : ∃ y, dotProduct (r y) d ≠ 0 := by
    by_contra h
    push Not at h
    exact hd0 (hker d h)
  -- choose sign so that some row decreases
  obtain ⟨d, hdS, hneg⟩ : ∃ d : κ → ℝ, (∀ y ∈ S, dotProduct (r y) d = 0) ∧
      ∃ y, dotProduct (r y) d < 0 := by
    obtain ⟨y, hy⟩ := hex
    rcases lt_or_gt_of_ne hy with h | h
    · exact ⟨d, hdS, y, h⟩
    · refine ⟨-d, fun y hy => ?_, y, ?_⟩
      · simp [dotProduct_neg, hdS y hy]
      · simpa [dotProduct_neg] using h
  classical
  let B : Finset Y := univ.filter (fun y => dotProduct (r y) d < 0)
  have hB : B.Nonempty := by
    obtain ⟨y, hy⟩ := hneg
    exact ⟨y, by simp [B, hy]⟩
  let ρ : Y → ℝ := fun y => (dotProduct (r y) z - 1) / (-(dotProduct (r y) d))
  obtain ⟨y0, hy0B, hy0min⟩ := Finset.exists_min_image B ρ hB
  have hy0neg : dotProduct (r y0) d < 0 := by simpa [B] using hy0B
  have hy0S : y0 ∉ S := by
    intro h
    have := hdS y0 h
    linarith
  have hρ0 : 0 ≤ ρ y0 := by
    apply div_nonneg
    · linarith [hz y0]
    · linarith
  refine ⟨z + ρ y0 • d, y0, hy0S, ?_, ?_, ?_⟩
  · intro y
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    by_cases hy : dotProduct (r y) d < 0
    · have hyB : y ∈ B := by simp [B, hy]
      have h1 := hy0min y hyB
      have h2 : ρ y0 * (-(dotProduct (r y) d)) ≤ dotProduct (r y) z - 1 := by
        have := (le_div_iff₀ (by linarith : 0 < -(dotProduct (r y) d))).1 h1
        exact this
      linarith
    · push Not at hy
      have := mul_nonneg hρ0 hy
      linarith [hz y]
  · rw [coe_insert, linearIndepOn_insert (by simpa using hy0S)]
    refine ⟨hind, ?_⟩
    intro hmem
    have hle : Submodule.span ℝ (r '' (S : Set Y)) ≤ LinearMap.ker (dotL d) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      simpa [dotL] using hdS y hy
    have := hle hmem
    simp only [LinearMap.mem_ker, dotL, LinearMap.coe_mk, AddHom.coe_mk] at this
    linarith
  · intro y hy
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · have hne : dotProduct (r y) d ≠ 0 := hy0neg.ne
      have : ρ y * (-(dotProduct (r y) d)) = dotProduct (r y) z - 1 := by
        simp only [ρ]
        field_simp
      linarith
    · rw [hdS y hy, htight y hy]; ring

theorem vertex {Y κ : Type} [Fintype Y] [DecidableEq Y] [Fintype κ] [DecidableEq κ]
    (r : Y → κ → ℝ)
    (hker : ∀ d : κ → ℝ, (∀ y, dotProduct (r y) d = 0) → d = 0)
    (z0 : κ → ℝ) (hz0 : ∀ y, 1 ≤ dotProduct (r y) z0) :
    ∃ (z : κ → ℝ) (S : Finset Y), (∀ y, 1 ≤ dotProduct (r y) z) ∧
      S.card = Fintype.card κ ∧ LinearIndepOn ℝ r (S : Set Y) ∧
      ∀ y ∈ S, dotProduct (r y) z = 1 := by
  have key : ∀ k : ℕ, k ≤ Fintype.card κ → ∃ (z : κ → ℝ) (S : Finset Y),
      (∀ y, 1 ≤ dotProduct (r y) z) ∧ S.card = k ∧ LinearIndepOn ℝ r (S : Set Y) ∧
      ∀ y ∈ S, dotProduct (r y) z = 1 := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨z0, ∅, hz0, by simp, by simp, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨z, S, hz, hc, hi, ht⟩ := ih (by omega)
      obtain ⟨z', y0, hy0, hz', hi', ht'⟩ := step r hker z hz S (by omega) hi ht
      exact ⟨z', insert y0 S, hz', by rw [Finset.card_insert_of_notMem hy0, hc], hi', ht'⟩
  exact key _ le_rfl |>.imp fun z h => (h.imp fun S h => h)

theorem matrix_of_vertex {Y κ : Type} [Fintype Y] [DecidableEq Y] [Fintype κ] [DecidableEq κ]
    (ri : Y → κ → ℤ)
    (hker : ∀ d : κ → ℝ, (∀ y, dotProduct (fun j => (ri y j : ℝ)) d = 0) → d = 0)
    (z0 : κ → ℝ) (hz0 : ∀ y, 1 ≤ dotProduct (fun j => (ri y j : ℝ)) z0) :
    ∃ z : κ → ℝ, (∀ y, 1 ≤ dotProduct (fun j => (ri y j : ℝ)) z) ∧
      ∃ M : Matrix κ κ ℤ, M.det ≠ 0 ∧ (∀ i, ∃ y, M i = ri y) ∧
        ∀ i, ∑ j, (M i j : ℝ) * z j = 1 := by
  obtain ⟨z, S, hz, hc, hi, ht⟩ := vertex (fun y j => (ri y j : ℝ)) hker z0 hz0
  refine ⟨z, hz, ?_⟩
  have hcard : Fintype.card κ = Fintype.card S := by simp [hc]
  let e : κ ≃ S := Fintype.equivOfCardEq hcard
  refine ⟨Matrix.of fun i => ri (e i).1, ?_, fun i => ⟨(e i).1, rfl⟩, fun i => ?_⟩
  · intro h0
    have hli : LinearIndependent ℝ (fun i : κ => (fun j => (ri (e i).1 j : ℝ))) :=
      (hi.linearIndependent).comp e e.injective
    have hu : IsUnit (Matrix.of fun i j => ((ri (e i).1 j : ℤ) : ℝ)) :=
      Matrix.linearIndependent_rows_iff_isUnit.1 hli
    have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hu
    have : (Matrix.of fun i j => ((ri (e i).1 j : ℤ) : ℝ)).det = 0 := by
      have := (Int.castRingHom ℝ).map_det (Matrix.of fun i => ri (e i).1)
      simp only [eq_intCast] at this
      rw [h0] at this
      simp only [RingHom.mapMatrix_apply] at this
      exact this.symm.trans Int.cast_zero
    rw [this] at hdet
    exact not_isUnit_zero hdet
  · have := ht (e i).1 (e i).2
    simpa [dotProduct] using this

theorem cramer_int {κ : Type} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℤ) (z : κ → ℝ)
    (h : ∀ i, ∑ j, (M i j : ℝ) * z j = 1) (k : κ) :
    (M.det : ℝ) * z k = ((M.updateCol k (fun _ => 1)).det : ℝ) := by
  set A : Matrix κ κ ℝ := M.map (Int.cast : ℤ → ℝ) with hA
  have hAz : A.mulVec z = fun _ => 1 := by
    funext i
    simpa [Matrix.mulVec, dotProduct, hA] using h i
  have h1 := congrArg (fun v => A.adjugate.mulVec v) hAz
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
  have h2 := congrFun h1 k
  have h3 : A.adjugate.mulVec (fun _ => (1 : ℝ)) = Matrix.cramer A (fun _ => 1) := by
    rw [Matrix.cramer_eq_adjugate_mulVec]
  rw [h3, Matrix.cramer_apply] at h2
  have hdA : A.det = (M.det : ℝ) := by
    have := (Int.castRingHom ℝ).map_det M
    simpa [RingHom.mapMatrix_apply, hA] using this.symm
  have hu : A.updateCol k (fun _ => 1) = (Int.castRingHom ℝ).mapMatrix (M.updateCol k (fun _ => 1)) := by
    ext i j
    by_cases hj : j = k
    · subst hj; simp [Matrix.updateCol_apply, hA]
    · simp [Matrix.updateCol_apply, hA, hj]
  have hdu : (A.updateCol k (fun _ => 1)).det = ((M.updateCol k (fun _ => 1)).det : ℝ) := by
    rw [hu, ← RingHom.map_det]; simp
  rw [← hdu, ← h2, hdA]
  simp

theorem det_bound {κ : Type} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℤ)
    (h : ∀ i j, |M i j| ≤ 1) : |M.det| ≤ ((Fintype.card κ ^ Fintype.card κ : ℕ) : ℤ) := by
  have := Matrix.det_le (abv := AbsoluteValue.abs) (A := M) (x := (1 : ℤ)) (fun i j => h i j)
  simp only [AbsoluteValue.abs_apply, one_pow, nsmul_eq_mul, mul_one] at this
  refine this.trans ?_
  exact_mod_cast Nat.factorial_le_pow _

theorem muroga {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (t : ℝ) :
    ∃ (a' : ι → ℤ) (t' : ℤ),
      (∀ j, |a' j| ≤ (((Fintype.card ι + 1) ^ (Fintype.card ι + 1) : ℕ) : ℤ)) ∧
      |t'| ≤ (((Fintype.card ι + 1) ^ (Fintype.card ι + 1) : ℕ) : ℤ) ∧
      ∀ y : ι → Bool,
        (t ≤ ∑ j, a j * (if y j then (1 : ℝ) else 0)) ↔
        (t' ≤ ∑ j, a' j * (if y j then (1 : ℤ) else 0)) := by
  classical
  let A : (ι → Bool) → ℝ := fun y => ∑ j, a j * (if y j then (1 : ℝ) else 0)
  let σ : (ι → Bool) → ℤ := fun y => if t ≤ A y then 1 else -1
  have hσ : ∀ y, σ y = 1 ∨ σ y = -1 := by
    intro y; simp only [σ]; split_ifs <;> simp
  let ri : (ι → Bool) → Option ι → ℤ := fun y k =>
    σ y * k.elim (-1) (fun j => if y j then 1 else 0)
  have hri : ∀ y k, |ri y k| ≤ 1 := by
    intro y k
    have h1 : |σ y| = 1 := by rcases hσ y with h | h <;> simp [h]
    have h2 : |k.elim (-1) (fun j => if y j then (1 : ℤ) else 0)| ≤ 1 := by
      cases k with
      | none => simp
      | some j => by_cases hj : y j <;> simp [hj]
    simp only [ri, abs_mul, h1, one_mul]
    exact h2
  have hrow : ∀ (y : ι → Bool) (z : Option ι → ℝ),
      dotProduct (fun k => (ri y k : ℝ)) z =
        (σ y : ℝ) * (∑ j, (if y j then (1 : ℝ) else 0) * z (some j) - z none) := by
    intro y z
    simp only [dotProduct, Fintype.sum_option, ri]
    simp only [Option.elim_none, Option.elim_some, Int.cast_mul, Int.cast_neg, Int.cast_one]
    rw [mul_sub, Finset.mul_sum]
    have : ∀ j, ((σ y : ℝ) * ((if y j then (1 : ℤ) else 0 : ℤ) : ℝ)) * z (some j)
        = (σ y : ℝ) * ((if y j then (1 : ℝ) else 0) * z (some j)) := by
      intro j; by_cases hj : y j <;> simp [hj]
    simp only [this]
    ring
  have hσne : ∀ y, (σ y : ℝ) ≠ 0 := by
    intro y; rcases hσ y with h | h <;> simp [h]
  have hσne0 : ∀ y, σ y ≠ 0 := by
    intro y; rcases hσ y with h | h <;> simp [h]
  have hker : ∀ d : Option ι → ℝ, (∀ y, dotProduct (fun k => (ri y k : ℝ)) d = 0) → d = 0 := by
    intro d hd
    have h0 := hd (fun _ => false)
    rw [hrow] at h0
    simp at h0
    have hnone : d none = 0 := by
      rcases h0 with h | h
      · first | exact absurd h (hσne _) | (exfalso; apply hσne0 _ h)
      · exact h
    funext k
    cases k with
    | none => exact hnone
    | some j =>
      have h1 := hd (fun i => decide (i = j))
      rw [hrow] at h1
      simp [hnone] at h1
      rcases h1 with h | h
      · first | exact absurd h (hσne _) | (exfalso; apply hσne0 _ h)
      · exact h
  -- margin
  obtain ⟨δ, hδ, hδN⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ y, A y < t → A y - t ≤ -δ := by
    by_cases hN : (univ.filter (fun y => A y < t)).Nonempty
    · obtain ⟨y0, hy0, hmax⟩ := Finset.exists_max_image _ A hN
      have hy0' : A y0 < t := by simpa using hy0
      refine ⟨t - A y0, by linarith, fun y hy => ?_⟩
      have := hmax y (by simpa using hy)
      linarith
    · refine ⟨1, one_pos, fun y hy => ?_⟩
      exact absurd ⟨y, by simpa using hy⟩ hN
  let z0 : Option ι → ℝ := fun k => k.elim ((2 / δ) * t - 1) (fun j => (2 / δ) * a j)
  have hz0 : ∀ y, 1 ≤ dotProduct (fun k => (ri y k : ℝ)) z0 := by
    intro y
    rw [hrow]
    have hs : ∑ j, (if y j then (1 : ℝ) else 0) * z0 (some j) = (2 / δ) * A y := by
      simp only [z0, Option.elim_some, A, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hs]
    simp only [z0, Option.elim_none]
    by_cases ht : t ≤ A y
    · have : σ y = 1 := by simp [σ, ht]
      rw [this]
      have : 0 ≤ (2 / δ) * (A y - t) := mul_nonneg (by positivity) (by linarith)
      push_cast
      nlinarith
    · have : σ y = -1 := by simp [σ, ht]
      rw [this]
      push Not at ht
      have h1 := hδN y ht
      have : (2 / δ) * (A y - t) ≤ -2 := by
        have : (2 / δ) * (A y - t) ≤ (2 / δ) * (-δ) := mul_le_mul_of_nonneg_left h1 (by positivity)
        have h2 : (2 / δ) * (-δ) = -2 := by field_simp
        linarith
      push_cast
      nlinarith
  obtain ⟨z, hz, M, hdet, hMrow, hMz⟩ := matrix_of_vertex ri hker z0 hz0
  have hM : ∀ i j, |M i j| ≤ 1 := by
    intro i j
    obtain ⟨y, hy⟩ := hMrow i
    rw [hy]; exact hri y j
  let w : Option ι → ℤ := fun k => (M.updateCol k (fun _ => 1)).det
  have hw : ∀ k, |w k| ≤ (((Fintype.card ι + 1) ^ (Fintype.card ι + 1) : ℕ) : ℤ) := by
    intro k
    have := det_bound (M.updateCol k (fun _ => 1)) (by
      intro i j
      by_cases hj : j = k
      · subst hj; simp
      · simpa [Matrix.updateCol_apply, hj] using hM i j)
    simpa [Fintype.card_option] using this
  have hcz : ∀ k, (M.det : ℝ) * z k = w k := fun k => cramer_int M z hMz k
  let s : ℤ := if 0 < M.det then 1 else -1
  have hs1 : |s| = 1 := by simp only [s]; split_ifs <;> simp
  have hD : 0 < s * M.det := by
    simp only [s]
    split_ifs with h
    · simpa using h
    · have : M.det < 0 := lt_of_le_of_ne (not_lt.1 h) hdet
      linarith
  have hDr : (0 : ℝ) < ((s * M.det : ℤ) : ℝ) := by exact_mod_cast hD
  have hsw : ∀ k, ((s * w k : ℤ) : ℝ) = ((s * M.det : ℤ) : ℝ) * z k := by
    intro k
    rw [Int.cast_mul, Int.cast_mul, ← hcz k]; ring
  refine ⟨fun j => s * w (some j), s * w none, fun j => ?_, ?_, fun y => ?_⟩
  · simp only [abs_mul, hs1, one_mul]; exact hw _
  · simp only [abs_mul, hs1, one_mul]; exact hw _
  · have hX : (((∑ j, s * w (some j) * (if y j then (1 : ℤ) else 0) : ℤ) : ℝ)
        - ((s * w none : ℤ) : ℝ)) =
        ((s * M.det : ℤ) : ℝ) * (∑ j, (if y j then (1 : ℝ) else 0) * z (some j) - z none) := by
      rw [hsw none, Int.cast_sum, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      have := hsw (some j)
      rw [Int.cast_mul, this]
      by_cases hj : y j <;> simp [hj]
    have e : (s * w none ≤ ∑ j, s * w (some j) * (if y j then (1 : ℤ) else 0)) ↔
        0 ≤ ((s * M.det : ℤ) : ℝ) *
          (∑ j, (if y j then (1 : ℝ) else 0) * z (some j) - z none) := by
      rw [← hX, sub_nonneg, Int.cast_le]
    rw [e, mul_nonneg_iff_of_pos_left hDr]
    have hy := hz y
    rw [hrow] at hy
    by_cases ht : t ≤ A y
    · have h1 : σ y = 1 := by simp [σ, ht]
      rw [h1] at hy
      simp only [Int.cast_one, one_mul] at hy
      exact ⟨fun _ => by linarith, fun _ => ht⟩
    · have h1 : σ y = -1 := by simp [σ, ht]
      rw [h1] at hy
      simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] at hy
      refine ⟨fun h => absurd h ht, fun h => ?_⟩
      linarith

end ReLUBinaryDepth.Dev.Muroga
end

section
set_option autoImplicit false

namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.Compile

open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement

theorem foldl_take_succ {α β : Type} (L : List β) (f : List α → β → List α) (k : ℕ)
    (hk : k < L.length) :
    (L.take (k+1)).foldl (fun v l => v ++ f v l) [] =
      (L.take k).foldl (fun v l => v ++ f v l) [] ++
        f ((L.take k).foldl (fun v l => v ++ f v l) []) L[k] := by
  simp only [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

def ind (b : Bool) : ℤ := if b then 1 else 0

theorem bit_eq_ind (b : Bool) : bit b = ((ind b : ℤ) : ℝ) := by
  cases b <;> simp [bit, ind]

theorem ind_01 (b : Bool) : ind b = 0 ∨ ind b = 1 := by
  cases b <;> simp [ind]

noncomputable def zr (r : ℝ) : ℤ := ⌊r⌋

theorem zr_cast (r : ℝ) (h : ∃ a : ℤ, r = a) : ((zr r : ℤ) : ℝ) = r := by
  obtain ⟨a, rfl⟩ := h
  simp [zr]

theorem abs_zr_le (r : ℝ) (W : ℕ) (h : ∃ a : ℤ, r = a ∧ |a| ≤ W) : |zr r| ≤ W := by
  obtain ⟨a, rfl, ha⟩ := h
  simpa [zr] using ha

noncomputable section Circuit

variable {n : ℕ}

def LL (C : RealThresholdCircuit n) : List (List (ThresholdGate n)) := C.layers ++ [[C.output]]

def vs (C : RealThresholdCircuit n) (x : Cube n) (m : ℕ) : List Bool :=
  ((LL C).take m).foldl (fun v layer => v ++ layer.map (fun g => g.eval x v)) []

def cnt (C : RealThresholdCircuit n) (m : ℕ) : ℕ := (((LL C).take m).map List.length).sum

theorem LL_length (C : RealThresholdCircuit n) : (LL C).length = C.layers.length + 1 := by
  simp [LL]

theorem vs_succ (C : RealThresholdCircuit n) (x : Cube n) (m : ℕ) (hm : m < (LL C).length) :
    vs C x (m+1) = vs C x m ++ ((LL C)[m]).map (fun g => g.eval x (vs C x m)) := by
  unfold vs
  exact foldl_take_succ (LL C) (fun v l => l.map (fun g => g.eval x v)) m hm

theorem cnt_succ (C : RealThresholdCircuit n) (m : ℕ) (hm : m < (LL C).length) :
    cnt C (m+1) = cnt C m + ((LL C)[m]).length := by
  unfold cnt
  simp only [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some,
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]

theorem vs_length (C : RealThresholdCircuit n) (x : Cube n) :
    ∀ m, m ≤ (LL C).length → (vs C x m).length = cnt C m := by
  intro m
  induction m with
  | zero => intro _; simp [vs, cnt]
  | succ m ih =>
    intro hm
    rw [vs_succ C x m (by omega), cnt_succ C m (by omega)]
    simp [ih (by omega)]

theorem cnt_le (C : RealThresholdCircuit n) :
    ∀ m, m ≤ (LL C).length → cnt C m ≤ cnt C (LL C).length := by
  intro m
  induction' h : (LL C).length - m with d ih generalizing m
  · intro hm
    have : m = (LL C).length := by omega
    rw [this]
  · intro hm
    have h1 := cnt_succ C m (by omega)
    have := ih (m+1) (by omega) (by omega)
    omega

theorem cnt_full (C : RealThresholdCircuit n) : cnt C (LL C).length = C.size := by
  unfold cnt RealThresholdCircuit.size
  rw [List.take_length]
  simp [LL]

theorem cnt_layers (C : RealThresholdCircuit n) : cnt C C.layers.length = C.size - 1 := by
  unfold cnt RealThresholdCircuit.size LL
  rw [List.take_left' rfl]
  omega

theorem vs_layers (C : RealThresholdCircuit n) (x : Cube n) :
    vs C x C.layers.length = C.values x := by
  unfold vs LL RealThresholdCircuit.values
  rw [List.take_left' rfl]

theorem vs_last (C : RealThresholdCircuit n) (x : Cube n) :
    vs C x (C.layers.length + 1) = C.values x ++ [C.eval x] := by
  rw [vs_succ C x _ (by rw [LL_length]; omega), vs_layers]
  have : (LL C)[C.layers.length]'(by rw [LL_length]; omega) = [C.output] := by
    simp [LL]
  rw [this]
  simp [RealThresholdCircuit.eval]

def dflt : ThresholdGate n := ⟨0, fun _ => 0, fun _ => 0⟩

def gateAt (C : RealThresholdCircuit n) (m i : ℕ) : ThresholdGate n :=
  ((LL C).getD m []).getD i dflt

theorem vs_getElem (C : RealThresholdCircuit n) (x : Cube n) (m : ℕ) (hm : m < (LL C).length)
    (q : ℕ) (hq1 : cnt C m ≤ q) (hq2 : q < cnt C (m+1)) :
    ((vs C x (m+1)).map ind).getD q 0 = ind ((gateAt C m (q - cnt C m)).eval x (vs C x m)) := by
  have hc := cnt_succ C m hm
  have hl := vs_length C x m (by omega)
  have hi : q - cnt C m < ((LL C)[m]).length := by omega
  have hg : gateAt C m (q - cnt C m) = ((LL C)[m])[q - cnt C m] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hm, hi]
  rw [vs_succ C x m hm, hg]
  rw [List.map_append, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hl]; omega)]
  simp [hl, List.getElem?_eq_getElem hi]

def Yst (x : Cube n) (v : List Bool) (c : ℕ) : ℤ :=
  if h : c < n then ind (x ⟨c, h⟩) else (v.map ind).getD (c - n) 0

theorem Yst_01 (x : Cube n) (v : List Bool) (c : ℕ) : Yst x v c = 0 ∨ Yst x v c = 1 := by
  unfold Yst
  split_ifs
  · exact ind_01 _
  · rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_map]
    cases v[c - n]? with
    | none => simp
    | some a => simpa using ind_01 a

/-- weights of a gate over coordinates -/
noncomputable def wg (g : ThresholdGate n) (c : ℕ) : ℤ :=
  if h : c < n then zr (g.inputWeight ⟨c, h⟩) else zr (g.previousWeight (c - n))

def Okay (W : ℕ) (g : ThresholdGate n) : Prop :=
  (∃ b : ℤ, g.threshold = b ∧ |b| ≤ W) ∧
  (∀ i, ∃ a : ℤ, g.inputWeight i = a ∧ |a| ≤ W) ∧
  (∀ j, ∃ p : ℤ, g.previousWeight j = p ∧ |p| ≤ W)

theorem gate_ind (W : ℕ) (g : ThresholdGate n) (hg : Okay W g) (x : Cube n) (v : List Bool)
    (S : ℕ) (hS : v.length ≤ S) :
    ind (g.eval x v) =
      if 0 ≤ (∑ c ∈ Finset.range (n + S), wg g c * Yst x v c) - zr g.threshold then 1 else 0 := by
  obtain ⟨⟨b, hb, _⟩, hi, hp⟩ := hg
  have hiz : ∀ i, ((zr (g.inputWeight i) : ℤ) : ℝ) = g.inputWeight i := fun i =>
    zr_cast _ (by obtain ⟨a, ha, _⟩ := hi i; exact ⟨a, ha⟩)
  have hpz : ∀ j, ((zr (g.previousWeight j) : ℤ) : ℝ) = g.previousWeight j := fun j =>
    zr_cast _ (by obtain ⟨a, ha, _⟩ := hp j; exact ⟨a, ha⟩)
  have hbz : ((zr g.threshold : ℤ) : ℝ) = g.threshold := zr_cast _ ⟨b, hb⟩
  -- integer value of the sum
  have hsum : (∑ i, g.inputWeight i * bit (x i)) + ∑ j : Fin v.length, g.previousWeight j.val * bit v[j]
      = ((∑ c ∈ Finset.range (n + S), wg g c * Yst x v c : ℤ) : ℝ) := by
    rw [Finset.sum_range_add]
    push_cast
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range (fun c => ((wg g c : ℤ) : ℝ) * ((Yst x v c : ℤ) : ℝ)) n]
      apply Finset.sum_congr rfl
      intro i _
      simp [wg, Yst, hiz, bit_eq_ind]
    · obtain ⟨d, rfl⟩ : ∃ d, S = v.length + d := ⟨S - v.length, by omega⟩
      rw [Finset.sum_range_add]
      have h0 : (∑ j ∈ Finset.range d, ((wg g (n + (v.length + j)) : ℤ) : ℝ) *
          ((Yst x v (n + (v.length + j)) : ℤ) : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have : Yst x v (n + (v.length + j)) = 0 := by
          simp [Yst, List.getD_eq_getElem?_getD]
        simp [this]
      rw [h0, add_zero, ← Fin.sum_univ_eq_sum_range
        (fun j => ((wg g (n + j) : ℤ) : ℝ) * ((Yst x v (n + j) : ℤ) : ℝ)) v.length]
      apply Finset.sum_congr rfl
      intro j _
      have : Yst x v (n + j.val) = ind v[j] := by
        simp [Yst, List.getD_eq_getElem?_getD]
      simp [wg, this, hpz, bit_eq_ind]
  unfold ind ThresholdGate.eval
  rw [hsum]
  generalize zr g.threshold = t at hbz ⊢
  generalize (∑ c ∈ Finset.range (n + S), wg g c * Yst x v c) = Sz
  rw [← hbz]
  simp only [decide_eq_true_eq]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; apply h2
    have := Int.cast_le.mp (by simpa using h1 : ((t : ℤ) : ℝ) ≤ ((Sz : ℤ) : ℝ))
    omega
  · exfalso; apply h1
    have : t ≤ Sz := by omega
    exact_mod_cast this
  · rfl

end Circuit


noncomputable section Net

variable {n : ℕ}

def TT (C : RealThresholdCircuit n) : ℕ := n + C.size

def sw (C : RealThresholdCircuit n) (m p : ℕ) : ℕ → ℤ :=
  if p < n ∨ p - n < cnt C m then (fun c => if c = p then 1 else 0)
  else if p - n < cnt C (m+1) then wg (gateAt C m (p - n - cnt C m))
  else fun _ => 0

def st (C : RealThresholdCircuit n) (m p : ℕ) : ℤ :=
  if p < n ∨ p - n < cnt C m then 1
  else if p - n < cnt C (m+1) then zr (gateAt C m (p - n - cnt C m)).threshold
  else 1

def zz (C : RealThresholdCircuit n) (x : Cube n) (m p : ℕ) : ℤ :=
  (∑ c ∈ Finset.range (TT C), sw C m p c * Yst x (vs C x m) c) - st C m p

theorem Yst_carry (C : RealThresholdCircuit n) (x : Cube n) (m : ℕ) (hm : m < (LL C).length)
    (p : ℕ) (h : p < n ∨ p - n < cnt C m) :
    Yst x (vs C x (m+1)) p = Yst x (vs C x m) p := by
  unfold Yst
  by_cases hp : p < n
  · simp [hp]
  · have h' : p - n < cnt C m := by tauto
    have hl := vs_length C x m (by omega)
    simp only [hp, dif_neg, not_false_eq_true]
    rw [vs_succ C x m hm, List.map_append, List.getD_append _ _ _ _ (by simp [hl, h'])]

theorem Yst_zero (C : RealThresholdCircuit n) (x : Cube n) (m : ℕ) (hm : m ≤ (LL C).length)
    (p : ℕ) (hp : n ≤ p) (h : cnt C m ≤ p - n) : Yst x (vs C x m) p = 0 := by
  have hl := vs_length C x m hm
  unfold Yst
  rw [dif_neg (by omega)]
  apply List.getD_eq_default
  simp [hl, h]

theorem step (W : ℕ) (C : RealThresholdCircuit n) (hok : ∀ m i, Okay W (gateAt C m i))
    (x : Cube n) (m : ℕ) (hm : m < (LL C).length) (p : ℕ) (hp : p < TT C) :
    (if 0 ≤ zz C x m p then (1 : ℤ) else 0) = Yst x (vs C x (m+1)) p := by
  unfold zz
  by_cases h1 : p < n ∨ p - n < cnt C m
  · have hs : st C m p = 1 := by simp [st, h1]
    have hsum : (∑ c ∈ Finset.range (TT C), sw C m p c * Yst x (vs C x m) c) = Yst x (vs C x m) p := by
      have : sw C m p = fun c => if c = p then 1 else 0 := by simp [sw, h1]
      rw [this]
      simp [ite_mul, Finset.sum_ite_eq', hp]
    rw [hs, hsum, Yst_carry C x m hm p h1]
    rcases Yst_01 x (vs C x m) p with h | h <;> simp [h]
  · have h1' : n ≤ p ∧ cnt C m ≤ p - n := by omega
    by_cases h2 : p - n < cnt C (m+1)
    · have hs : st C m p = zr (gateAt C m (p - n - cnt C m)).threshold := by simp [st, h1, h2]
      have hw : sw C m p = wg (gateAt C m (p - n - cnt C m)) := by simp [sw, h1, h2]
      rw [hs, hw]
      have hS : (vs C x m).length ≤ C.size := by
        rw [vs_length C x m (by omega)]
        have := cnt_le C m (by omega)
        rwa [cnt_full] at this
      have := gate_ind W (gateAt C m (p - n - cnt C m)) (hok m _) x (vs C x m) C.size hS
      unfold TT
      rw [← this]
      unfold Yst
      rw [dif_neg (by omega)]
      exact (vs_getElem C x m hm (p - n) h1'.2 h2).symm
    · have hs : st C m p = 1 := by simp [st, h1, h2]
      have hw : sw C m p = fun _ => 0 := by simp [sw, h1, h2]
      rw [hs, hw, Yst_zero C x (m+1) (by omega) p h1'.1 (by omega)]
      simp


theorem read_sum (v : List ℝ) (off T : ℕ) (hlen : v.length = off + T) (f : ℕ → ℝ) :
    ∑ j : Fin v.length, (if off ≤ j.val ∧ j.val < off + T then f (j.val - off) else 0) * v[j] =
      ∑ c ∈ Finset.range T, f c * v.getD (off + c) 0 := by
  have h1 : ∀ j : Fin v.length, (if off ≤ j.val ∧ j.val < off + T then f (j.val - off) else 0) * v[j] =
      (if off ≤ j.val ∧ j.val < off + T then f (j.val - off) else 0) * v.getD j.val 0 := by
    intro j
    simp [List.getD_eq_getElem?_getD]
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => (if off ≤ j ∧ j < off + T then f (j - off) else 0) * v.getD j 0) v.length]
  rw [hlen, Finset.sum_range_add]
  have h0 : (∑ c ∈ Finset.range off, (if off ≤ c ∧ c < off + T then f (c - off) else 0) * v.getD c 0) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    have := Finset.mem_range.mp hc
    have : ¬ (off ≤ c ∧ c < off + T) := by omega
    simp [this]
  rw [h0, zero_add]
  apply Finset.sum_congr rfl
  intro c hc
  have := Finset.mem_range.mp hc
  have h2 : off ≤ off + c ∧ off + c < off + T := by omega
  simp [h2]

theorem sum_two (v : List ℝ) (a : ℕ) (ha : a + 1 < v.length) :
    ∑ j : Fin v.length, (if j.val = a then (1:ℝ) else if j.val = a + 1 then -1 else 0) * v[j] =
      v.getD a 0 - v.getD (a+1) 0 := by
  have h1 : ∀ j : Fin v.length, (if j.val = a then (1:ℝ) else if j.val = a + 1 then -1 else 0) * v[j] =
      (if j.val = a then v.getD a 0 else 0) - (if j.val = a + 1 then v.getD (a+1) 0 else 0) := by
    intro j
    have key : v[j] = v.getD j.val 0 := by simp [List.getD_eq_getElem?_getD]
    rw [key]
    by_cases h : j.val = a
    · have : j.val ≠ a + 1 := by omega
      rw [h]; simp [this]
    · by_cases h' : j.val = a + 1
      · rw [h']; simp [h]
      · simp [h, h']
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_sub_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j = a then v.getD a 0 else 0) v.length,
    Fin.sum_univ_eq_sum_range (fun j => if j = a + 1 then v.getD (a+1) 0 else 0) v.length]
  have h2 : a < v.length := by omega
  simp [h2, ha]

theorem gadget (z : ℤ) :
    relu (relu ((z : ℝ) + 1) - relu (z : ℝ)) = ((if 0 ≤ z then (1 : ℤ) else 0 : ℤ) : ℝ) := by
  by_cases h : 0 ≤ z
  · have h0 : (0 : ℝ) ≤ z := by exact_mod_cast h
    simp only [relu, if_pos h]
    have e1 : max 0 ((z : ℝ) + 1) = z + 1 := max_eq_right (by linarith)
    have e2 : max 0 (z : ℝ) = z := max_eq_right h0
    rw [e1, e2]
    simp
  · have h1 : z + 1 ≤ 0 := by omega
    have h0 : (z : ℝ) + 1 ≤ 0 := by exact_mod_cast h1
    have h2 : (z : ℝ) ≤ 0 := by linarith
    simp only [relu, if_neg h]
    rw [max_eq_left h0, max_eq_left h2]
    simp

def Aunit (C : RealThresholdCircuit n) (m p s : ℕ) : AffineGate n where
  bias := ((if s = 0 then 1 - st C m p else - st C m p : ℤ) : ℝ)
  inputWeight := fun i => if m = 0 then ((sw C m p i.val : ℤ) : ℝ) else 0
  previousWeight := fun j =>
    if m ≠ 0 ∧ 3 * TT C * (m - 1) + 2 * TT C ≤ j ∧ j < 3 * TT C * (m - 1) + 2 * TT C + TT C
    then ((sw C m p (j - (3 * TT C * (m - 1) + 2 * TT C)) : ℤ) : ℝ) else 0

def Bunit (C : RealThresholdCircuit n) (m p : ℕ) : AffineGate n where
  bias := 0
  inputWeight := fun _ => 0
  previousWeight := fun j =>
    if j = 3 * TT C * m + 2 * p then 1 else if j = 3 * TT C * m + 2 * p + 1 then -1 else 0

def Alay (C : RealThresholdCircuit n) (m : ℕ) : List (AffineGate n) :=
  List.ofFn (fun j : Fin (2 * TT C) => Aunit C m (j.val / 2) (j.val % 2))

def Blay (C : RealThresholdCircuit n) (m : ℕ) : List (AffineGate n) :=
  List.ofFn (fun p : Fin (TT C) => Bunit C m p.val)

def NL (C : RealThresholdCircuit n) : List (List (AffineGate n)) :=
  (List.range (2 * (LL C).length - 1)).map
    (fun j => if j % 2 = 0 then Alay C (j / 2) else Blay C (j / 2))

def Net (C : RealThresholdCircuit n) : Network n :=
  ⟨NL C, Bunit C ((LL C).length - 1) (TT C - 1), true⟩

def NV (C : RealThresholdCircuit n) (x : Cube n) (j : ℕ) : List ℝ :=
  ((NL C).take j).foldl (fun v layer => v ++ layer.map (fun g => relu (g.eval x v))) []

theorem NL_length (C : RealThresholdCircuit n) : (NL C).length = 2 * (LL C).length - 1 := by
  simp [NL]

theorem LL_pos (C : RealThresholdCircuit n) : 1 ≤ (LL C).length := by
  rw [LL_length]; omega

theorem NV_succ (C : RealThresholdCircuit n) (x : Cube n) (j : ℕ) (hj : j < (NL C).length) :
    NV C x (j+1) = NV C x j ++ ((NL C)[j]).map (fun g => relu (g.eval x (NV C x j))) := by
  unfold NV
  exact foldl_take_succ (NL C) (fun v l => l.map (fun g => relu (g.eval x v))) j hj

theorem NL_even (C : RealThresholdCircuit n) (m : ℕ) (hm : 2 * m < (NL C).length) :
    (NL C)[2 * m] = Alay C m := by
  simp [NL]

theorem NL_odd (C : RealThresholdCircuit n) (m : ℕ) (hm : 2 * m + 1 < (NL C).length) :
    (NL C)[2 * m + 1] = Blay C m := by
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  simp [NL, h1, h2]

theorem Alay_length (C : RealThresholdCircuit n) (m : ℕ) : (Alay C m).length = 2 * TT C := by
  simp [Alay]

theorem Blay_length (C : RealThresholdCircuit n) (m : ℕ) : (Blay C m).length = TT C := by
  simp [Blay]

def Inv (C : RealThresholdCircuit n) (x : Cube n) (m : ℕ) : Prop :=
  (NV C x (2 * m)).length = 3 * TT C * m ∧
  (m ≠ 0 → ∀ c < TT C, (NV C x (2 * m)).getD (3 * TT C * (m - 1) + 2 * TT C + c) 0 =
    ((Yst x (vs C x m) c : ℤ) : ℝ))

theorem NV_A_len (C : RealThresholdCircuit n) (x : Cube n) (m : ℕ) (hm : m < (LL C).length)
    (hI : (NV C x (2 * m)).length = 3 * TT C * m) :
    NV C x (2 * m + 1) = NV C x (2 * m) ++ (Alay C m).map (fun g => relu (g.eval x (NV C x (2 * m)))) ∧
    (NV C x (2 * m + 1)).length = 3 * TT C * m + 2 * TT C := by
  have h : 2 * m < (NL C).length := by rw [NL_length]; have := LL_pos C; omega
  have e := NV_succ C x (2 * m) h
  rw [NL_even C m h] at e
  refine ⟨e, ?_⟩
  rw [e]
  simp [hI, Alay_length]

theorem NV_B_len (C : RealThresholdCircuit n) (x : Cube n) (m : ℕ) (hm : m + 1 < (LL C).length)
    (hI : (NV C x (2 * m + 1)).length = 3 * TT C * m + 2 * TT C) :
    NV C x (2 * m + 2) = NV C x (2 * m + 1) ++ (Blay C m).map (fun g => relu (g.eval x (NV C x (2 * m + 1)))) ∧
    (NV C x (2 * m + 2)).length = 3 * TT C * (m + 1) := by
  have h : 2 * m + 1 < (NL C).length := by rw [NL_length]; omega
  have e := NV_succ C x (2 * m + 1) h
  rw [NL_odd C m h] at e
  refine ⟨e, ?_⟩
  rw [e]
  simp [hI, Blay_length]
  ring

theorem Aval (W : ℕ) (C : RealThresholdCircuit n) (hok : ∀ m i, Okay W (gateAt C m i))
    (x : Cube n) (m : ℕ) (hm : m < (LL C).length) (hI : Inv C x m) (p s : ℕ) (hs : s < 2) :
    (Aunit C m p s).eval x (NV C x (2 * m)) =
      ((zz C x m p : ℤ) : ℝ) + (if s = 0 then 1 else 0) := by
  have key : (∑ i, (if m = 0 then ((sw C m p i.val : ℤ) : ℝ) else 0) * bit (x i)) +
      ∑ j : Fin (NV C x (2 * m)).length,
        (Aunit C m p s).previousWeight j.val * (NV C x (2 * m))[j] =
      ((∑ c ∈ Finset.range (TT C), sw C m p c * Yst x (vs C x m) c : ℤ) : ℝ) := by
    by_cases h0 : m = 0
    · subst h0
      have hnv : NV C x (2 * 0) = [] := by simp [NV]
      have hvs : vs C x 0 = [] := by simp [vs]
      have : ∀ j : Fin (NV C x (2 * 0)).length, False := by
        intro j; rw [hnv] at j; exact j.elim0
      have hz : (∑ j : Fin (NV C x (2 * 0)).length,
        (Aunit C 0 p s).previousWeight j.val * (NV C x (2 * 0))[j]) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact (this j).elim
      rw [hz, add_zero]
      unfold TT
      rw [Finset.sum_range_add]
      push_cast
      have hz2 : (∑ j ∈ Finset.range C.size, ((sw C 0 p (n + j) : ℤ) : ℝ) *
          ((Yst x (vs C x 0) (n + j) : ℤ) : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have : Yst x (vs C x 0) (n + j) = 0 := by simp [Yst, hvs]
        simp [this]
      rw [hz2, add_zero]
      rw [← Fin.sum_univ_eq_sum_range
        (fun c => ((sw C 0 p c : ℤ) : ℝ) * ((Yst x (vs C x 0) c : ℤ) : ℝ)) n]
      apply Finset.sum_congr rfl
      intro i _
      simp [Yst, bit_eq_ind]
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hlen : (NV C x (2 * (m' + 1))).length = (3 * TT C * (m' + 1 - 1) + 2 * TT C) + TT C := by
        rw [hI.1]; simp; ring
      have hinp : (∑ i : Fin n, (if m' + 1 = 0 then ((sw C (m' + 1) p i.val : ℤ) : ℝ) else 0) * bit (x i)) = 0 := by
        simp
      rw [hinp, zero_add]
      have hpw : ∀ j : Fin (NV C x (2 * (m' + 1))).length,
          (Aunit C (m'+1) p s).previousWeight j.val * (NV C x (2 * (m' + 1)))[j] =
          (if 3 * TT C * (m' + 1 - 1) + 2 * TT C ≤ j.val ∧ j.val < 3 * TT C * (m' + 1 - 1) + 2 * TT C + TT C
            then ((sw C (m' + 1) p (j.val - (3 * TT C * (m' + 1 - 1) + 2 * TT C)) : ℤ) : ℝ) else 0) *
            (NV C x (2 * (m' + 1)))[j] := by
        intro j; simp [Aunit]
      rw [Finset.sum_congr rfl (fun j _ => hpw j)]
      rw [read_sum _ _ _ hlen (fun c => ((sw C (m' + 1) p c : ℤ) : ℝ))]
      push_cast
      apply Finset.sum_congr rfl
      intro c hc
      have h := hI.2 (by omega) c (Finset.mem_range.mp hc)
      simp only [Nat.add_sub_cancel] at h
      rw [h]
  unfold AffineGate.eval
  rw [add_assoc]
  have hb : (Aunit C m p s).bias = ((if s = 0 then 1 - st C m p else - st C m p : ℤ) : ℝ) := rfl
  have hiw : ∀ i, (Aunit C m p s).inputWeight i = if m = 0 then ((sw C m p i.val : ℤ) : ℝ) else 0 := fun i => rfl
  simp only [hb, hiw]
  rw [key]
  unfold zz
  by_cases hs0 : s = 0
  · simp [hs0]; ring
  · simp [hs0]; ring

theorem Bval (W : ℕ) (C : RealThresholdCircuit n) (hok : ∀ m i, Okay W (gateAt C m i))
    (x : Cube n) (m : ℕ) (hm : m < (LL C).length) (hI : Inv C x m) (p : ℕ) (hp : p < TT C) :
    relu ((Bunit C m p).eval x (NV C x (2 * m + 1))) = ((Yst x (vs C x (m+1)) p : ℤ) : ℝ) := by
  obtain ⟨hA, hAl⟩ := NV_A_len C x m hm hI.1
  have hsum : ∑ j : Fin (NV C x (2 * m + 1)).length,
      (Bunit C m p).previousWeight j.val * (NV C x (2 * m + 1))[j] =
      (NV C x (2 * m + 1)).getD (3 * TT C * m + 2 * p) 0 -
        (NV C x (2 * m + 1)).getD (3 * TT C * m + 2 * p + 1) 0 := by
    rw [← sum_two (NV C x (2 * m + 1)) (3 * TT C * m + 2 * p) (by omega)]
    rfl
  have hget : ∀ s, s < 2 → (NV C x (2 * m + 1)).getD (3 * TT C * m + 2 * p + s) 0 =
      relu (((zz C x m p : ℤ) : ℝ) + (if s = 0 then 1 else 0)) := by
    intro s hs
    rw [hA, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [hI.1]; omega), List.getElem?_map]
    have hidx : 3 * TT C * m + 2 * p + s - (NV C x (2 * m)).length = 2 * p + s := by
      rw [hI.1]; omega
    rw [hidx]
    have hlt : 2 * p + s < (Alay C m).length := by rw [Alay_length]; omega
    rw [List.getElem?_eq_getElem hlt]
    simp only [Option.map_some, Option.getD_some]
    have e1 : (2 * p + s) / 2 = p := by omega
    have e2 : (2 * p + s) % 2 = s := by omega
    have : (Alay C m)[2 * p + s] = Aunit C m p s := by simp [Alay, e1, e2]
    rw [this, Aval W C hok x m hm hI p s hs]
  have e0 : (NV C x (2 * m + 1)).getD (3 * TT C * m + 2 * p) 0 =
      relu (((zz C x m p : ℤ) : ℝ) + 1) := by
    have h := hget 0 (by norm_num)
    rw [if_pos rfl] at h
    exact h
  have e1 : (NV C x (2 * m + 1)).getD (3 * TT C * m + 2 * p + 1) 0 =
      relu ((zz C x m p : ℤ) : ℝ) := by
    have h := hget 1 (by norm_num)
    rw [if_neg (by norm_num), add_zero] at h
    exact h
  have hev : (Bunit C m p).eval x (NV C x (2 * m + 1)) =
      relu (((zz C x m p : ℤ) : ℝ) + 1) - relu ((zz C x m p : ℤ) : ℝ) := by
    unfold AffineGate.eval
    have hb : (Bunit C m p).bias = 0 := rfl
    have hi : ∀ i, (Bunit C m p).inputWeight i = 0 := fun i => rfl
    simp only [hb, hi, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
    rw [hsum, e0, e1]
  rw [hev, gadget, step W C hok x m hm p hp]


theorem inv_all (W : ℕ) (C : RealThresholdCircuit n) (hok : ∀ m i, Okay W (gateAt C m i))
    (x : Cube n) : ∀ m, m < (LL C).length → Inv C x m := by
  intro m
  induction m with
  | zero => intro _; exact ⟨by simp [NV], fun h => absurd rfl h⟩
  | succ m ih =>
    intro hm1
    have hm : m < (LL C).length := by omega
    have hI := ih hm
    obtain ⟨hA, hAl⟩ := NV_A_len C x m hm hI.1
    obtain ⟨hB, hBl⟩ := NV_B_len C x m hm1 hAl
    have e : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [Inv, e]
    refine ⟨hBl, fun _ c hc => ?_⟩
    simp only [Nat.add_sub_cancel]
    rw [hB, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [hAl]; omega), List.getElem?_map]
    have hidx : 3 * TT C * m + 2 * TT C + c - (NV C x (2 * m + 1)).length = c := by
      rw [hAl]; omega
    rw [hidx]
    have hlt : c < (Blay C m).length := by rw [Blay_length]; exact hc
    rw [List.getElem?_eq_getElem hlt]
    simp only [Option.map_some, Option.getD_some]
    have : (Blay C m)[c] = Bunit C m c := by simp [Blay]
    rw [this]
    exact Bval W C hok x m hm hI c hc

theorem Yst_out (C : RealThresholdCircuit n) (x : Cube n) :
    Yst x (vs C x (C.layers.length + 1)) (TT C - 1) = ind (C.eval x) := by
  have hl := vs_length C x C.layers.length (by rw [LL_length]; omega)
  have hc := cnt_layers C
  rw [vs_layers] at hl
  have hsz : 1 ≤ C.size := by unfold RealThresholdCircuit.size; omega
  unfold Yst TT
  rw [dif_neg (by omega), vs_last, List.map_append,
    List.getD_append_right _ _ _ _ (by simp [hl]; omega)]
  have : n + C.size - 1 - n - (List.map ind (C.values x)).length = 0 := by
    simp [hl]; omega
  rw [this]
  simp

theorem net_eval (W : ℕ) (C : RealThresholdCircuit n) (hok : ∀ m i, Okay W (gateAt C m i))
    (x : Cube n) : (Net C).eval x = ((ind (C.eval x) : ℤ) : ℝ) := by
  have hD : (LL C).length = C.layers.length + 1 := LL_length C
  have hm : (LL C).length - 1 < (LL C).length := by omega
  have hI := inv_all W C hok x _ hm
  have hv : (Net C).values x = NV C x (2 * ((LL C).length - 1) + 1) := by
    unfold Network.values NV
    have : 2 * ((LL C).length - 1) + 1 = (NL C).length := by rw [NL_length]; omega
    rw [this, List.take_length]
    rfl
  have hT : TT C - 1 < TT C := by
    unfold TT; have : 1 ≤ C.size := by unfold RealThresholdCircuit.size; omega
    omega
  have := Bval W C hok x _ hm hI _ hT
  have e : (LL C).length - 1 + 1 = C.layers.length + 1 := by omega
  rw [e, Yst_out] at this
  unfold Network.eval
  rw [hv]
  simp only [Net, if_true]
  exact this

theorem lo_succ (C : RealThresholdCircuit n) (k : ℕ) (hk : k < (NL C).length) :
    layerOffset (Net C) (k+1) = layerOffset (Net C) k + ((NL C)[k]).length := by
  unfold layerOffset
  simp only [Net]
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

theorem lo_two (C : RealThresholdCircuit n) : ∀ r, 2 * r + 1 ≤ (NL C).length →
    layerOffset (Net C) (2 * r) = 3 * TT C * r ∧
    layerOffset (Net C) (2 * r + 1) = 3 * TT C * r + 2 * TT C := by
  intro r
  induction r with
  | zero =>
    intro h
    have h0 : layerOffset (Net C) 0 = 0 := by simp [layerOffset]
    have h1 := lo_succ C 0 (by omega)
    have h2 := NL_even C 0 (by omega)
    simp only [Nat.mul_zero, Nat.zero_add] at h2 ⊢
    rw [h1, h2, Alay_length, h0]
    simp
  | succ r ih =>
    intro h
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have e : 2 * (r + 1) = 2 * r + 1 + 1 := by ring
    have h1 := lo_succ C (2 * r + 1) (by omega)
    rw [NL_odd C r (by omega), Blay_length] at h1
    have h3 := lo_succ C (2 * (r + 1)) (by omega)
    rw [NL_even C (r + 1) (by omega), Alay_length] at h3
    have h4 : layerOffset (Net C) (2 * (r + 1)) = 3 * TT C * (r + 1) := by
      rw [e, h1, ih2]; ring
    refine ⟨h4, ?_⟩
    rw [h3, h4]

theorem Bunit_support (C : RealThresholdCircuit n) (m p : ℕ) (hp : p < TT C) (j : ℕ)
    (h : (Bunit C m p).previousWeight j ≠ 0) :
    3 * TT C * m ≤ j ∧ j < 3 * TT C * m + 2 * TT C := by
  simp only [Bunit] at h
  by_cases h1 : j = 3 * TT C * m + 2 * p
  · omega
  · by_cases h2 : j = 3 * TT C * m + 2 * p + 1
    · omega
    · simp [h1, h2] at h

theorem Aunit_support (C : RealThresholdCircuit n) (m' p s : ℕ) (j : ℕ)
    (h : (Aunit C (m'+1) p s).previousWeight j ≠ 0) :
    3 * TT C * m' + 2 * TT C ≤ j ∧ j < 3 * TT C * (m' + 1) := by
  simp only [Aunit, Nat.add_sub_cancel] at h
  by_cases hc : (m' + 1 ≠ 0 ∧ 3 * TT C * m' + 2 * TT C ≤ j ∧ j < 3 * TT C * m' + 2 * TT C + TT C)
  · have : 3 * TT C * (m' + 1) = 3 * TT C * m' + 2 * TT C + TT C := by ring
    omega
  · rw [if_neg hc] at h
    exact (h rfl).elim

theorem mem_NL (C : RealThresholdCircuit n) (l : List (AffineGate n)) (hl : l ∈ NL C) :
    ∃ r, l = Alay C r ∨ l = Blay C r := by
  simp only [NL, List.mem_map, List.mem_range] at hl
  obtain ⟨j, _, hj⟩ := hl
  split_ifs at hj
  · exact ⟨j / 2, Or.inl hj.symm⟩
  · exact ⟨j / 2, Or.inr hj.symm⟩

theorem NL_getElem (C : RealThresholdCircuit n) (k : ℕ) (hk : k < (NL C).length) :
    ((NL C)[k] = Alay C (k / 2) ∧ k % 2 = 0) ∨ ((NL C)[k] = Blay C (k / 2) ∧ k % 2 = 1) := by
  by_cases h : k % 2 = 0
  · left
    refine ⟨?_, h⟩
    have e : k = 2 * (k / 2) := by omega
    have := NL_even C (k / 2) (by omega)
    simpa [← e] using this
  · right
    refine ⟨?_, by omega⟩
    have e : k = 2 * (k / 2) + 1 := by omega
    have := NL_odd C (k / 2) (by omega)
    simpa [← e] using this

theorem net_layered (C : RealThresholdCircuit n) : IsLayered (Net C) := by
  have hT : ∀ (g : AffineGate n), TT C - 1 < TT C → True := fun _ _ => trivial
  constructor
  · intro k hk hk0 g hg
    have hk' : k < (NL C).length := hk
    have hgk : g ∈ (NL C)[k] := hg
    rcases NL_getElem C k hk' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hgk
      obtain ⟨j, hj⟩ : ∃ j : Fin (2 * TT C), Aunit C (k / 2) (j.val / 2) (j.val % 2) = g := by
        simpa [Alay, List.mem_ofFn] using hgk
      subst hj
      obtain ⟨r, hr⟩ : ∃ r, k / 2 = r + 1 := ⟨k / 2 - 1, by omega⟩
      rw [hr]
      have hk2 : k - 1 = 2 * r + 1 := by omega
      have hk3 : k = 2 * (r + 1) := by omega
      refine ⟨fun i => by simp [Aunit], fun j' hj' => ?_⟩
      have := Aunit_support C r _ _ j' hj'
      rw [hk2]
      rw [hk3]
      have a1 := (lo_two C r (by omega)).2
      have a2 := (lo_two C (r + 1) (by omega)).1
      omega
    · obtain ⟨r, hkr⟩ : ∃ r, k = 2 * r + 1 := ⟨k / 2, by omega⟩
      subst hkr
      have e1 : (2 * r + 1) / 2 = r := by omega
      rw [e1] at h1
      rw [h1] at hgk
      obtain ⟨j, hj⟩ : ∃ j : Fin (TT C), Bunit C r j.val = g := by
        simpa [Blay, List.mem_ofFn] using hgk
      subst hj
      refine ⟨fun i => rfl, fun j' hj' => ?_⟩
      have := Bunit_support C r j.val j.isLt j' hj'
      have a1 := (lo_two C r (by omega)).1
      have a2 := (lo_two C r (by omega)).2
      simp only [Nat.add_sub_cancel]
      omega
  · intro _
    refine ⟨fun i => rfl, fun j hj => ?_⟩
    have hD := LL_pos C
    have hT1 : 1 ≤ TT C := by
      unfold TT; have : 1 ≤ C.size := by unfold RealThresholdCircuit.size; omega
      omega
    have := Bunit_support C ((LL C).length - 1) (TT C - 1) (by omega) j hj
    have hlen : (Net C).layers.length = 2 * ((LL C).length - 1) + 1 := by
      show (NL C).length = _
      rw [NL_length]; omega
    rw [hlen]
    have a1 := (lo_two C ((LL C).length - 1) (by rw [NL_length]; omega)).1
    have a2 := (lo_two C ((LL C).length - 1) (by rw [NL_length]; omega)).2
    simp only [Nat.add_sub_cancel]
    omega


theorem getD_mem_or {α : Type} (l : List α) (i : ℕ) (d : α) : l.getD i d = d ∨ l.getD i d ∈ l := by
  by_cases h : i < l.length
  · right
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · left
    exact List.getD_eq_default _ _ (by omega)

theorem okay_gateAt (W : ℕ) (C : RealThresholdCircuit n)
    (hint : ∀ g : ThresholdGate n, g ∈ C.output :: C.layers.flatten → Okay W g) (m i : ℕ) :
    Okay W (gateAt C m i) := by
  have hd : Okay W (dflt : ThresholdGate n) :=
    ⟨⟨0, by simp [dflt], by simp⟩, fun _ => ⟨0, by simp [dflt], by simp⟩,
      fun _ => ⟨0, by simp [dflt], by simp⟩⟩
  unfold gateAt
  rcases getD_mem_or (LL C) m [] with h | h
  · rw [h]
    simpa using hd
  · rcases getD_mem_or ((LL C).getD m []) i dflt with h2 | h2
    · rw [h2]; exact hd
    generalize (LL C).getD m [] = l at h h2
    apply hint
    · simp only [LL, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨_, h, h2⟩)
      · rw [h] at h2 ⊢
        rw [List.mem_singleton.1 h2]
        exact List.mem_cons_self

def GoodG (W : ℕ) (g : AffineGate n) : Prop :=
  (∃ b : ℤ, g.bias = b ∧ |b| ≤ (W : ℤ) + 1) ∧
  (∀ i, ∃ a : ℤ, g.inputWeight i = a ∧ |a| ≤ (W : ℤ) + 1) ∧
  (∀ j, ∃ p : ℤ, g.previousWeight j = p ∧ |p| ≤ (W : ℤ) + 1)

theorem bits_of_good (W Bits : ℕ) (hBits : W + 2 < 2 ^ Bits) (g : AffineGate n) (hg : GoodG W g)
    (mm : ℕ) : AffineGate.HasBitWeights Bits mm g := by
  have hB : (W : ℤ) + 2 < 2 ^ Bits := by exact_mod_cast hBits
  have hr : ∀ (r : ℝ) (a : ℤ), r = a → |a| ≤ (W : ℤ) + 1 → IsBitRat Bits r := by
    intro r a hra ha
    refine ⟨a, 1, by norm_num, by omega, ?_, by simp [hra]⟩
    have : (0 : ℤ) ≤ W := by positivity
    simp
    omega
  obtain ⟨⟨b, hb, hb2⟩, hi, hp⟩ := hg
  refine ⟨hr _ b hb hb2, fun i => ?_, fun j _ => ?_⟩
  · obtain ⟨a, ha, ha2⟩ := hi i; exact hr _ a ha ha2
  · obtain ⟨a, ha, ha2⟩ := hp j; exact hr _ a ha ha2

theorem sw_bound (W : ℕ) (C : RealThresholdCircuit n) (hok : ∀ m i, Okay W (gateAt C m i))
    (m p c : ℕ) : |sw C m p c| ≤ (W : ℤ) + 1 := by
  have hW : (0 : ℤ) ≤ W := by positivity
  unfold sw
  split_ifs
  · by_cases h : c = p <;> simp [h] <;> omega
  · obtain ⟨_, hi, hp⟩ := hok m (p - n - cnt C m)
    unfold wg
    split_ifs with h
    · have := abs_zr_le _ W (hi ⟨c, h⟩); omega
    · have := abs_zr_le _ W (hp (c - n)); omega
  · simp; omega

theorem st_bound (W : ℕ) (C : RealThresholdCircuit n) (hok : ∀ m i, Okay W (gateAt C m i))
    (m p : ℕ) : |st C m p| ≤ (W : ℤ) + 1 ∧ |1 - st C m p| ≤ (W : ℤ) + 1 := by
  have hW : (0 : ℤ) ≤ W := by positivity
  unfold st
  split_ifs
  · simp; omega
  · obtain ⟨⟨b, hb, hb2⟩, _, _⟩ := hok m (p - n - cnt C m)
    have := abs_zr_le _ W ⟨b, hb, hb2⟩
    rw [abs_le] at this ⊢
    rw [abs_le]
    constructor <;> [skip; skip] <;> omega
  · simp; omega

theorem aunit_good (W : ℕ) (C : RealThresholdCircuit n) (hok : ∀ m i, Okay W (gateAt C m i))
    (m p s : ℕ) : GoodG W (Aunit C m p s) := by
  have hW : (0 : ℤ) ≤ W := by positivity
  obtain ⟨h1, h2⟩ := st_bound W C hok m p
  refine ⟨⟨_, rfl, ?_⟩, fun i => ?_, fun j => ?_⟩
  · by_cases hs : s = 0
    · simp [hs, h2]
    · simp [hs]; exact h1
  · by_cases hm : m = 0
    · exact ⟨sw C m p i.val, by simp [Aunit, hm], sw_bound W C hok m p _⟩
    · exact ⟨0, by simp [Aunit, hm], by simp; omega⟩
  · by_cases hc : (m ≠ 0 ∧ 3 * TT C * (m - 1) + 2 * TT C ≤ j ∧ j < 3 * TT C * (m - 1) + 2 * TT C + TT C)
    · exact ⟨sw C m p (j - (3 * TT C * (m - 1) + 2 * TT C)), by simp [Aunit, hc], sw_bound W C hok m p _⟩
    · exact ⟨0, by simp [Aunit, hc], by simp; omega⟩

theorem bunit_good (W : ℕ) (C : RealThresholdCircuit n) (m p : ℕ) : GoodG W (Bunit C m p) := by
  have hW : (0 : ℤ) ≤ W := by positivity
  refine ⟨⟨0, by simp [Bunit], by simp <;> omega⟩, fun i => ⟨0, by simp [Bunit], by simp <;> omega⟩, fun j => ?_⟩
  by_cases h1 : j = 3 * TT C * m + 2 * p
  · exact ⟨1, by simp [Bunit, h1], by simp <;> omega⟩
  · by_cases h2 : j = 3 * TT C * m + 2 * p + 1
    · exact ⟨-1, by simp [Bunit, h1, h2], by simp <;> omega⟩
    · exact ⟨0, by simp [Bunit, h1, h2], by simp <;> omega⟩

theorem net_bits (W Bits : ℕ) (hBits : W + 2 < 2 ^ Bits) (C : RealThresholdCircuit n)
    (hok : ∀ m i, Okay W (gateAt C m i)) : HasBitWeights Bits (Net C) := by
  constructor
  · intro k hk g hg
    have hk' : k < (NL C).length := hk
    have hgk : g ∈ (NL C)[k] := hg
    apply bits_of_good W Bits hBits
    rcases NL_getElem C k hk' with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1] at hgk
      obtain ⟨j, hj⟩ : ∃ j : Fin (2 * TT C), Aunit C (k / 2) (j.val / 2) (j.val % 2) = g := by
        simpa [Alay, List.mem_ofFn] using hgk
      subst hj
      exact aunit_good W C hok _ _ _
    · rw [h1] at hgk
      obtain ⟨j, hj⟩ : ∃ j : Fin (TT C), Bunit C (k / 2) j.val = g := by
        simpa [Blay, List.mem_ofFn] using hgk
      subst hj
      exact bunit_good W C _ _
  · exact bits_of_good W Bits hBits _ (bunit_good W C _ _) _

theorem foldl_max_le {α : Type} (L : List (List α)) (B : ℕ) :
    ∀ w, w ≤ B → (∀ l ∈ L, l.length ≤ B) → L.foldl (fun w l => max w l.length) w ≤ B := by
  induction L with
  | nil => intro w hw _; simpa using hw
  | cons a L ih =>
    intro w hw hL
    simp only [List.foldl_cons]
    apply ih
    · exact max_le hw (hL a (by simp))
    · intro l hl; exact hL l (by simp [hl])

theorem net_width (C : RealThresholdCircuit n) : (Net C).width ≤ 2 * (n + C.size) + 2 := by
  unfold Network.width
  apply foldl_max_le _ _ _ (by omega)
  intro l hl
  obtain ⟨r, h | h⟩ := mem_NL C l hl
  · rw [h, Alay_length]; unfold TT; omega
  · rw [h, Blay_length]; unfold TT; omega

end Net

theorem compile {n : ℕ} (C : RealThresholdCircuit n) (W Bits : ℕ) (hBits : W + 2 < 2 ^ Bits)
    (hBits1 : 1 ≤ Bits)
    (hint : ∀ (g : ThresholdGate n), (g ∈ C.output :: C.layers.flatten) →
      (∃ b : ℤ, g.threshold = b ∧ |b| ≤ W) ∧
      (∀ i, ∃ a : ℤ, g.inputWeight i = a ∧ |a| ≤ W) ∧
      (∀ j, ∃ p : ℤ, g.previousWeight j = p ∧ |p| ≤ W)) :
    ∃ N : Network n, IsLayered N ∧ N.outputRelu = true ∧ N.depth = 2 * C.depth ∧
        N.width ≤ 2 * (n + C.size) + 2 ∧ HasBitWeights Bits N ∧
        ∀ x, (1 / 2 < N.eval x ↔ C.eval x = true) := by
  have hok : ∀ m i, Okay W (gateAt C m i) := okay_gateAt W C hint
  refine ⟨Net C, net_layered C, rfl, ?_, net_width C, net_bits W Bits hBits C hok, ?_⟩
  · unfold Network.depth RealThresholdCircuit.depth
    show (NL C).length + 1 = _
    rw [NL_length, LL_length]; omega
  · intro x
    rw [net_eval W C hok x]
    cases h : C.eval x <;> simp [ind] <;> norm_num

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.Compile
end

section
set_option autoImplicit false

noncomputable section
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.Int

open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement

def dat {n : ℕ} (g : ThresholdGate n) (m : ℕ) : (Fin n ⊕ Fin m → ℤ) × ℤ :=
  let h := ReLUBinaryDepth.Dev.Muroga.muroga (ι := Fin n ⊕ Fin m)
    (Sum.elim g.inputWeight (fun j => g.previousWeight j.val)) g.threshold
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

theorem dat_spec {n : ℕ} (g : ThresholdGate n) (m : ℕ) :
    (∀ j, |(dat g m).1 j| ≤ (((Fintype.card (Fin n ⊕ Fin m) + 1) ^ (Fintype.card (Fin n ⊕ Fin m) + 1) : ℕ) : ℤ)) ∧
    |(dat g m).2| ≤ (((Fintype.card (Fin n ⊕ Fin m) + 1) ^ (Fintype.card (Fin n ⊕ Fin m) + 1) : ℕ) : ℤ) ∧
    ∀ y : Fin n ⊕ Fin m → Bool,
      (g.threshold ≤ ∑ j, (Sum.elim g.inputWeight (fun j => g.previousWeight j.val)) j *
          (if y j then (1 : ℝ) else 0)) ↔
      ((dat g m).2 ≤ ∑ j, (dat g m).1 j * (if y j then (1 : ℤ) else 0)) := by
  have h := ReLUBinaryDepth.Dev.Muroga.muroga (ι := Fin n ⊕ Fin m)
    (Sum.elim g.inputWeight (fun j => g.previousWeight j.val)) g.threshold
  have hs := Classical.choose_spec (Classical.choose_spec h)
  exact hs

def tg {n : ℕ} (g : ThresholdGate n) (m : ℕ) : ThresholdGate n where
  threshold := ((dat g m).2 : ℝ)
  inputWeight := fun i => (((dat g m).1 (Sum.inl i) : ℤ) : ℝ)
  previousWeight := fun j => if h : j < m then (((dat g m).1 (Sum.inr ⟨j, h⟩) : ℤ) : ℝ) else 0

theorem tg_eval {n : ℕ} (g : ThresholdGate n) (x : Cube n) (v : List Bool) :
    (tg g v.length).eval x v = g.eval x v := by
  have hsp := (dat_spec g v.length).2.2 (Sum.elim x (fun j : Fin v.length => v[j]))
  unfold ThresholdGate.eval
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hsp
  have e1 : (((dat g v.length).2 : ℤ) : ℝ) ≤ (∑ i, (((dat g v.length).1 (Sum.inl i) : ℤ) : ℝ) * bit (x i)) +
      ∑ j : Fin v.length, (if h : j.val < v.length then (((dat g v.length).1 (Sum.inr ⟨j.val, h⟩) : ℤ) : ℝ) else 0) * bit v[j]
      ↔ (dat g v.length).2 ≤ (∑ i, (dat g v.length).1 (Sum.inl i) * (if x i then (1 : ℤ) else 0)) +
        ∑ j : Fin v.length, (dat g v.length).1 (Sum.inr j) * (if v[j] then (1 : ℤ) else 0) := by
    rw [← Int.cast_le (R := ℝ)]
    push_cast
    have a1 : ∀ i, ((((dat g v.length).1 (Sum.inl i) : ℤ) : ℝ)) * bit (x i) =
        ((dat g v.length).1 (Sum.inl i) : ℝ) * (if x i then (1 : ℝ) else 0) := by
      intro i; simp [bit]
    have a2 : ∀ j : Fin v.length, (if h : j.val < v.length then (((dat g v.length).1 (Sum.inr ⟨j.val, h⟩) : ℤ) : ℝ) else 0) * bit v[j] =
        ((dat g v.length).1 (Sum.inr j) : ℝ) * (if v[j] then (1 : ℝ) else 0) := by
      intro j; simp [bit, j.isLt]
    simp only [a1, a2]
  have e2 : (g.threshold ≤ (∑ i, g.inputWeight i * (if x i then (1 : ℝ) else 0)) +
      ∑ j : Fin v.length, g.previousWeight j.val * (if v[j] then (1 : ℝ) else 0)) ↔
      (dat g v.length).2 ≤ (∑ i, (dat g v.length).1 (Sum.inl i) * (if x i then (1 : ℤ) else 0)) +
        ∑ j : Fin v.length, (dat g v.length).1 (Sum.inr j) * (if v[j] then (1 : ℤ) else 0) := hsp
  have : ((tg g v.length).threshold ≤ (∑ i, (tg g v.length).inputWeight i * bit (x i)) +
      ∑ j : Fin v.length, (tg g v.length).previousWeight j.val * bit v[j]) ↔
      (g.threshold ≤ ∑ i, g.inputWeight i * bit (x i) + ∑ j : Fin v.length, g.previousWeight j.val * bit v[j]) := by
    simp only [tg]
    rw [e1]
    simp only [bit]
    exact e2.symm
  exact decide_eq_decide.2 this

def mapL {n : ℕ} : List (List (ThresholdGate n)) → ℕ → List (List (ThresholdGate n))
  | [], _ => []
  | l :: L, m => l.map (fun g => tg g m) :: mapL L (m + l.length)

def intC {n : ℕ} (C : RealThresholdCircuit n) : RealThresholdCircuit n where
  layers := mapL C.layers 0
  output := tg C.output (C.layers.map List.length).sum

theorem fold_eq {n : ℕ} (x : Cube n) : ∀ (L : List (List (ThresholdGate n))) (v : List Bool),
    (mapL L v.length).foldl (fun v layer => v ++ layer.map (fun g => g.eval x v)) v =
      L.foldl (fun v layer => v ++ layer.map (fun g => g.eval x v)) v := by
  intro L
  induction L with
  | nil => intro v; simp [mapL]
  | cons l L ih =>
    intro v
    simp only [mapL, List.foldl_cons]
    have h1 : (v ++ (l.map (fun g => tg g v.length)).map (fun g => g.eval x v)) =
        v ++ l.map (fun g => g.eval x v) := by
      simp [List.map_map, Function.comp_def, tg_eval]
    rw [h1]
    have hl : (v ++ l.map (fun g => g.eval x v)).length = v.length + l.length := by simp
    have := ih (v ++ l.map (fun g => g.eval x v))
    rw [hl] at this
    exact this

theorem fold_length {n : ℕ} (x : Cube n) : ∀ (L : List (List (ThresholdGate n))) (v : List Bool),
    (L.foldl (fun v layer => v ++ layer.map (fun g => g.eval x v)) v).length =
      v.length + (L.map List.length).sum := by
  intro L
  induction L with
  | nil => intro v; simp
  | cons l L ih => intro v; simp [ih]; ring

theorem intC_eval {n : ℕ} (C : RealThresholdCircuit n) (x : Cube n) :
    (intC C).eval x = C.eval x := by
  have hv : (intC C).values x = C.values x := by
    unfold RealThresholdCircuit.values intC
    exact fold_eq x C.layers []
  have hl : (C.values x).length = (C.layers.map List.length).sum := by
    unfold RealThresholdCircuit.values
    rw [fold_length]; simp
  unfold RealThresholdCircuit.eval
  rw [hv]
  show (tg C.output (C.layers.map List.length).sum).eval x (C.values x) = _
  rw [← hl]
  exact tg_eval _ _ _

theorem intC_depth {n : ℕ} (C : RealThresholdCircuit n) : (intC C).depth = C.depth := by
  have : ∀ (L : List (List (ThresholdGate n))) (m : ℕ), (mapL L m).length = L.length := by
    intro L; induction L with
    | nil => intro m; simp [mapL]
    | cons l L ih => intro m; simp [mapL, ih]
  simp [RealThresholdCircuit.depth, intC, this]

theorem intC_size {n : ℕ} (C : RealThresholdCircuit n) : (intC C).size = C.size := by
  have : ∀ (L : List (List (ThresholdGate n))) (m : ℕ),
      ((mapL L m).map List.length).sum = (L.map List.length).sum := by
    intro L; induction L with
    | nil => intro m; simp [mapL]
    | cons l L ih => intro m; simp [mapL, ih]
  simp [RealThresholdCircuit.size, intC, this]

theorem mem_mapL {n : ℕ} (g : ThresholdGate n) : ∀ (L : List (List (ThresholdGate n))) (m : ℕ),
    g ∈ (mapL L m).flatten → ∃ g0 m', m' ≤ m + (L.map List.length).sum ∧ g = tg g0 m' := by
  intro L
  induction L with
  | nil => intro m h; simp [mapL] at h
  | cons l L ih =>
    intro m h
    simp only [mapL, List.flatten_cons, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨g0, _, rfl⟩ := List.mem_map.1 h
      exact ⟨g0, m, by simp, rfl⟩
    · obtain ⟨g0, m', hm, hg⟩ := ih _ h
      exact ⟨g0, m', by simp; omega, hg⟩

theorem good_tg {n : ℕ} (g0 : ThresholdGate n) (m T : ℕ) (hT : n + m ≤ T) :
    (∃ b : ℤ, (tg g0 m).threshold = b ∧ |b| ≤ (((T + 1) ^ (T + 1) : ℕ) : ℤ)) ∧
    (∀ i, ∃ a : ℤ, (tg g0 m).inputWeight i = a ∧ |a| ≤ (((T + 1) ^ (T + 1) : ℕ) : ℤ)) ∧
    (∀ j, ∃ p : ℤ, (tg g0 m).previousWeight j = p ∧ |p| ≤ (((T + 1) ^ (T + 1) : ℕ) : ℤ)) := by
  obtain ⟨h1, h2, _⟩ := dat_spec g0 m
  have hc : Fintype.card (Fin n ⊕ Fin m) = n + m := by simp
  rw [hc] at h1 h2
  have hmono : (((n + m + 1) ^ (n + m + 1) : ℕ) : ℤ) ≤ (((T + 1) ^ (T + 1) : ℕ) : ℤ) := by
    exact_mod_cast (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  refine ⟨⟨_, rfl, (h2).trans hmono⟩, fun i => ⟨_, rfl, (h1 _).trans hmono⟩, fun j => ?_⟩
  by_cases hj : j < m
  · exact ⟨(dat g0 m).1 (Sum.inr ⟨j, hj⟩), by simp [tg, hj], (h1 _).trans hmono⟩
  · exact ⟨0, by simp [tg, hj], by positivity⟩

theorem intC_hint {n : ℕ} (C : RealThresholdCircuit n) (T : ℕ) (hT : n + C.size ≤ T) :
    ∀ g ∈ (intC C).output :: (intC C).layers.flatten,
      (∃ b : ℤ, g.threshold = b ∧ |b| ≤ (((T + 1) ^ (T + 1) : ℕ) : ℤ)) ∧
      (∀ i, ∃ a : ℤ, g.inputWeight i = a ∧ |a| ≤ (((T + 1) ^ (T + 1) : ℕ) : ℤ)) ∧
      (∀ j, ∃ p : ℤ, g.previousWeight j = p ∧ |p| ≤ (((T + 1) ^ (T + 1) : ℕ) : ℤ)) := by
  intro g hg
  simp only [List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact good_tg _ _ T (by simp [RealThresholdCircuit.size] at hT; omega)
  · obtain ⟨g0, m', hm, rfl⟩ := mem_mapL g C.layers 0 hg
    exact good_tg _ _ T (by simp [RealThresholdCircuit.size] at hT; omega)

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.Int
end
end

section
set_option autoImplicit false

namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T32

open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement Filter

theorem arith_bits (n c S : ℕ) (hS : S ≤ c * (n + 1) ^ c) :
    ((n + S + 1) ^ (n + S + 1) + 2 < 2 ^ (3 * (c + 1) ^ 2 * (n + 1) ^ (3 * (c + 1) ^ 2))) ∧
    2 * (n + S) + 2 ≤ 3 * (c + 1) ^ 2 * (n + 1) ^ (3 * (c + 1) ^ 2) := by
  set u := n + 1 with hu
  have hu1 : 1 ≤ u := by omega
  set T := n + S with hT
  have h1 : u ≤ u ^ (c + 1) := Nat.le_self_pow (by omega) u
  have h2 : u ^ c ≤ u ^ (c + 1) := Nat.pow_le_pow_right hu1 (by omega)
  have hT1 : T + 1 ≤ (c + 1) * u ^ (c + 1) := by
    have : c * u ^ c ≤ c * u ^ (c + 1) := Nat.mul_le_mul_left _ h2
    nlinarith
  have hsq : (T + 1) ^ 2 ≤ (c + 1) ^ 2 * u ^ (2 * c + 2) := by
    calc (T + 1) ^ 2 ≤ ((c + 1) * u ^ (c + 1)) ^ 2 := Nat.pow_le_pow_left hT1 2
      _ = (c + 1) ^ 2 * u ^ (2 * c + 2) := by rw [mul_pow, ← pow_mul]; ring_nf
  have hX : 1 ≤ (c + 1) ^ 2 * u ^ (2 * c + 2) :=
    Nat.mul_pos (by positivity) (by positivity)
  have hc' : 2 * c + 2 ≤ 3 * (c + 1) ^ 2 := by nlinarith
  have hR : 3 * (c + 1) ^ 2 * u ^ (2 * c + 2) ≤ 3 * (c + 1) ^ 2 * u ^ (3 * (c + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hu1 hc')
  have hR2 : (T + 1) ^ 2 + 2 ≤ 3 * (c + 1) ^ 2 * u ^ (3 * (c + 1) ^ 2) := by
    have : 3 * (c + 1) ^ 2 * u ^ (2 * c + 2) = 3 * ((c + 1) ^ 2 * u ^ (2 * c + 2)) := by ring
    omega
  refine ⟨?_, ?_⟩
  · have h3 : (T + 1) ^ (T + 1) ≤ 2 ^ ((T + 1) * (T + 1)) := by
      calc (T + 1) ^ (T + 1) ≤ (2 ^ (T + 1)) ^ (T + 1) :=
            Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
        _ = 2 ^ ((T + 1) * (T + 1)) := by rw [← pow_mul]
    have h4 : 2 ^ ((T + 1) * (T + 1)) + 2 < 2 ^ ((T + 1) * (T + 1) + 2) := by
      have : 1 ≤ 2 ^ ((T + 1) * (T + 1)) := Nat.one_le_two_pow
      rw [pow_add]; omega
    have h5 : 2 ^ ((T + 1) * (T + 1) + 2) ≤ 2 ^ (3 * (c + 1) ^ 2 * u ^ (3 * (c + 1) ^ 2)) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  · nlinarith

theorem sim {n c : ℕ} (C : RealThresholdCircuit n) (hsize : C.size ≤ c * (n + 1) ^ c) :
    ∃ N : Network n, IsLayered N ∧ N.outputRelu = true ∧ N.depth = 2 * C.depth ∧
      N.width ≤ 3 * (c + 1) ^ 2 * (n + 1) ^ (3 * (c + 1) ^ 2) ∧
      HasBitWeights (3 * (c + 1) ^ 2 * (n + 1) ^ (3 * (c + 1) ^ 2)) N ∧
      ∀ x, (1 / 2 < N.eval x ↔ C.eval x = true) := by
  have hS : C.size ≤ c * (n + 1) ^ c := hsize
  obtain ⟨hb, hw⟩ := arith_bits n c C.size hS
  have hint := Dev.Int.intC_hint C (n + C.size) le_rfl
  have hBits1 : 1 ≤ 3 * (c + 1) ^ 2 * (n + 1) ^ (3 * (c + 1) ^ 2) := by omega
  obtain ⟨N, h1, h2, h3, h4, h5, h6⟩ := Dev.Compile.compile (Dev.Int.intC C)
    ((n + C.size + 1) ^ (n + C.size + 1))
    (3 * (c + 1) ^ 2 * (n + 1) ^ (3 * (c + 1) ^ 2)) hb hBits1 hint
  rw [Dev.Int.intC_depth] at h3
  rw [Dev.Int.intC_size] at h4
  refine ⟨N, h1, h2, h3, by omega, h5, fun x => ?_⟩
  rw [h6 x, Dev.Int.intC_eval]

theorem core (f : (n : ℕ) → Cube n → Bool) (s : ℕ → ℝ)
    (H : ∀ c : ℕ, ∀ᶠ n in atTop, ∀ N : Network n, IsLayered N → N.outputRelu = true →
      (N.depth : ℝ) ≤ s n → N.width ≤ c * (n + 1) ^ c →
      HasBitWeights (c * (n + 1) ^ c) N → ¬ BoolComputes N (f n)) (c : ℕ) :
    ¬ ∀ᶠ n in atTop, ∃ C : RealThresholdCircuit n,
        2 * (C.depth : ℝ) ≤ s n ∧ C.size ≤ c * (n + 1) ^ c ∧ C.Computes (f n) := by
  intro hev
  obtain ⟨n, hn, hHn⟩ := (hev.and (H (3 * (c + 1) ^ 2))).exists
  obtain ⟨C, hd, hs, hc⟩ := hn
  obtain ⟨N, h1, h2, h3, h4, h5, h6⟩ := sim C hs
  refine hHn N h1 h2 ?_ h4 h5 ?_
  · rw [h3]; push_cast; exact hd
  · intro x
    rw [h6 x, hc x]

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T32

namespace ReLUBinaryDepth.ProductTradeoff.Supplement

open ReLUBinaryDepth.ProductTradeoff Filter
open ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T32 in
theorem chk_theorem_3_2 (f : (n : ℕ) → Cube n → Bool) (s : ℕ → ℝ) (hs : ∀ n, 1 ≤ s n)
    (H : ∀ c : ℕ, ∀ᶠ n in atTop, ∀ N : Network n, IsLayered N → N.outputRelu = true →
      (N.depth : ℝ) ≤ s n → N.width ≤ c * (n + 1) ^ c →
      HasBitWeights (c * (n + 1) ^ c) N → ¬ BoolComputes N (f n)) :
    (¬ ∃ c : ℕ, ∀ᶠ n in atTop, ∃ C : RealThresholdCircuit n,
        2 * (C.depth : ℝ) ≤ s n ∧ C.size ≤ c * (n + 1) ^ c ∧ C.Computes (f n)) ∧
    (Tendsto s atTop atTop →
      ¬ ∃ d c : ℕ, ∀ᶠ n in atTop, ∃ C : RealThresholdCircuit n,
        C.depth ≤ d ∧ C.size ≤ c * (n + 1) ^ c ∧ C.Computes (f n)) ∧
    (∀ d₀ : ℕ, (∀ᶠ n in atTop, 2 * (d₀ : ℝ) ≤ s n) →
      ¬ ∃ c : ℕ, ∀ᶠ n in atTop, ∃ C : RealThresholdCircuit n,
        C.depth ≤ d₀ ∧ C.size ≤ c * (n + 1) ^ c ∧ C.Computes (f n)) := by
  refine ⟨fun ⟨c, hc⟩ => core f s H c hc, ?_, ?_⟩
  · rintro ht ⟨d, c, hc⟩
    have h2 : ∀ᶠ n in atTop, 2 * (d : ℝ) ≤ s n := ht.eventually_ge_atTop _
    refine core f s H c ?_
    filter_upwards [hc, h2] with n ⟨C, hd, hsz, hcomp⟩ hsn
    refine ⟨C, ?_, hsz, hcomp⟩
    have : (C.depth : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  · rintro d₀ h2 ⟨c, hc⟩
    refine core f s H c ?_
    filter_upwards [hc, h2] with n ⟨C, hd, hsz, hcomp⟩ hsn
    refine ⟨C, ?_, hsz, hcomp⟩
    have : (C.depth : ℝ) ≤ d₀ := by exact_mod_cast hd
    linarith

end ReLUBinaryDepth.ProductTradeoff.Supplement
end

theorem solution : type_of% @ReLUBinaryDepth.ProductTradeoff.Supplement.chk_theorem_3_2 := @ReLUBinaryDepth.ProductTradeoff.Supplement.chk_theorem_3_2

-- Prove2me | solution 1 for QAOAE3Lin2.Typical.eq_49
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T13:16:13.873526+00:00
-- url     : https://prove2.me/submissions/48ee55d6-c0c7-4751-a700-8014b618e206

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting
import Theorems.Thm_QAOAE3Lin2_Typical_eq_47
import Theorems.Thm_QAOAE3Lin2_Typical_eq_48

open QAOAE3Lin2.Typical

/-- Independence under the uniform average over the right-hand sides: if `f` depends only on the
coordinates in `A` and `g` only on the coordinates outside `A`, then `E[f g] = E[f] E[g]`. -/
theorem qa_indep_avg {m : ℕ} (A : Finset (Fin m)) (f g : (Fin m → Bool) → ℝ)
    (hf : ∀ r r' : Fin m → Bool, (∀ j ∈ A, r j = r' j) → f r = f r')
    (hg : ∀ r r' : Fin m → Bool, (∀ j, j ∉ A → r j = r' j) → g r = g r') :
    avgD (fun r => f r * g r) = avgD f * avgD g := by
  classical
  let mix : (Fin m → Bool) → (Fin m → Bool) → (Fin m → Bool) :=
    fun r r' j => if j ∈ A then r j else r' j
  let φ : (Fin m → Bool) × (Fin m → Bool) → (Fin m → Bool) × (Fin m → Bool) :=
    fun p => (mix p.1 p.2, mix p.2 p.1)
  have hφ : Function.Involutive φ := by
    rintro ⟨a, b⟩
    apply Prod.ext
    · funext j
      by_cases h : j ∈ A <;> simp [φ, mix, h]
    · funext j
      by_cases h : j ∈ A <;> simp [φ, mix, h]
  have hswap : ∑ p : (Fin m → Bool) × (Fin m → Bool), f p.1 * g p.2 =
      ∑ p : (Fin m → Bool) × (Fin m → Bool), f p.1 * g p.1 := by
    calc ∑ p : (Fin m → Bool) × (Fin m → Bool), f p.1 * g p.2
        = ∑ p : (Fin m → Bool) × (Fin m → Bool), f (φ p).1 * g (φ p).1 := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          have h1 : f (φ p).1 = f p.1 := hf _ _ (fun j hj => by simp [φ, mix, hj])
          have h2 : g (φ p).1 = g p.2 := hg _ _ (fun j hj => by simp [φ, mix, hj])
          rw [h1, h2]
      _ = ∑ p : (Fin m → Bool) × (Fin m → Bool), f p.1 * g p.1 :=
          hφ.bijective.sum_comp (fun p => f p.1 * g p.1)
  have hcard : (Fintype.card (Fin m → Bool) : ℝ) = (2 : ℝ) ^ m := by
    simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hL : ∑ p : (Fin m → Bool) × (Fin m → Bool), f p.1 * g p.2 = (∑ r, f r) * (∑ r, g r) := by
    rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum]
  have hR : ∑ p : (Fin m → Bool) × (Fin m → Bool), f p.1 * g p.1 =
      (2 : ℝ) ^ m * ∑ r, f r * g r := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum, hcard]
  have key : (∑ r, f r) * (∑ r, g r) = (2 : ℝ) ^ m * ∑ r, f r * g r := by
    rw [← hL, hswap, hR]
  have h2 : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  simp only [avgD]
  calc ((2 : ℝ) ^ m)⁻¹ * ∑ r, f r * g r
      = ((2 : ℝ) ^ m)⁻¹ * (((2 : ℝ) ^ m)⁻¹ * ((2 : ℝ) ^ m * ∑ r, f r * g r)) := by
        rw [← mul_assoc ((2 : ℝ) ^ m)⁻¹ ((2 : ℝ) ^ m), inv_mul_cancel₀ h2, one_mul]
    _ = ((2 : ℝ) ^ m)⁻¹ * (((2 : ℝ) ^ m)⁻¹ * ((∑ r, f r) * (∑ r, g r))) := by rw [key]
    _ = ((2 : ℝ) ^ m)⁻¹ * (∑ r, f r) * (((2 : ℝ) ^ m)⁻¹ * ∑ r, g r) := by ring

/-- Averaging over the sign of one equation first. -/
theorem qa_avg_coord {m : ℕ} (i : Fin m) (h : (Fin m → Bool) → ℝ) :
    avgD h = avgD (fun r => (h (Function.update r i false) + h (Function.update r i true)) / 2) := by
  classical
  let flip : (Fin m → Bool) → (Fin m → Bool) := fun r => Function.update r i (!r i)
  have hflip : Function.Involutive flip := by
    intro r
    funext j
    by_cases hj : j = i
    · subst hj; simp [flip]
    · simp [flip, Function.update_of_ne hj]
  have hpt : ∀ r : Fin m → Bool,
      h (Function.update r i false) + h (Function.update r i true) = h r + h (flip r) := by
    intro r
    cases hri : r i with
    | false =>
      have e1 : Function.update r i false = r := by rw [← hri, Function.update_eq_self]
      have e2 : Function.update r i true = flip r := by simp [flip, hri]
      rw [e1, e2]
    | true =>
      have e1 : Function.update r i true = r := by rw [← hri, Function.update_eq_self]
      have e2 : Function.update r i false = flip r := by simp [flip, hri]
      rw [e1, e2, add_comm]
  have hsumflip : ∑ r, h (flip r) = ∑ r, h r := hflip.bijective.sum_comp h
  have hsum : ∑ r : Fin m → Bool,
      (h (Function.update r i false) + h (Function.update r i true)) / 2 = ∑ r, h r := by
    calc ∑ r : Fin m → Bool, (h (Function.update r i false) + h (Function.update r i true)) / 2
        = ∑ r : Fin m → Bool, (h r + h (flip r)) / 2 :=
          Finset.sum_congr rfl (fun r _ => by rw [hpt r])
      _ = (∑ r, h r + ∑ r, h (flip r)) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
      _ = ∑ r, h r := by rw [hsumflip]; ring
  simp only [avgD]
  rw [hsum]

/-- The polynomial `c_k` of equation `i` reads only the signs of the equations sharing exactly
the `k`-th bit of `i`. -/
theorem qa_cPoly_congr {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (i : Fin m) (k : Fin 3)
    (x : QAlgorithms.Qubits n) (r r' : Fin m → Bool)
    (h : ∀ j, QAOAE3Lin2.General.sharesOnly tri i j k → r j = r' j) :
    QAOAE3Lin2.General.cPoly tri r i k x = QAOAE3Lin2.General.cPoly tri r' i k x := by
  unfold QAOAE3Lin2.General.cPoly
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : QAOAE3Lin2.General.sharesOnly tri i j k
  · rw [if_pos hj, if_pos hj]
    have hs : QAOAE3Lin2.General.sgn r j = QAOAE3Lin2.General.sgn r' j := by
      unfold QAOAE3Lin2.General.sgn
      rw [h j hj]
    rw [hs]
  · rw [if_neg hj, if_neg hj]

/-- An equation cannot share exactly the `k`-th and exactly the `k'`-th bit of `i` for `k ≠ k'`. -/
theorem qa_shares_disjoint {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (i j : Fin m)
    (k k' : Fin 3) (hkk : k ≠ k') (h : QAOAE3Lin2.General.sharesOnly tri i j k)
    (h' : QAOAE3Lin2.General.sharesOnly tri i j k') : False :=
  h.2.2 k' (Ne.symm hkk) h'.2.1

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (D : ℕ) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (hocc : QAOAE3Lin2.General.BoundedOccurrence tri D) (i : Fin m) (γ : ℝ) :
    avgD (fun rhs => clauseTerm tri rhs i γ) =
        (1 / 2) * Real.sin γ *
          Real.cos γ ^ (QAOAE3Lin2.General.termCount tri i 0 + QAOAE3Lin2.General.termCount tri i 1 + QAOAE3Lin2.General.termCount tri i 2) ∧
      QAOAE3Lin2.General.termCount tri i 0 + QAOAE3Lin2.General.termCount tri i 1 + QAOAE3Lin2.General.termCount tri i 2 ≤ 3 * D := by
  constructor
  · -- the three cosine factors, as functions of the signs, for a fixed string `x`
    let f : Fin 3 → QAlgorithms.Qubits n → (Fin m → Bool) → ℝ :=
      fun k x r => Real.cos (γ * QAOAE3Lin2.General.cPoly tri r i k x)
    have hfdep : ∀ (k : Fin 3) (x : QAlgorithms.Qubits n) (r r' : Fin m → Bool),
        (∀ j, QAOAE3Lin2.General.sharesOnly tri i j k → r j = r' j) → f k x r = f k x r' := by
      intro k x r r' h
      show Real.cos (γ * QAOAE3Lin2.General.cPoly tri r i k x) =
        Real.cos (γ * QAOAE3Lin2.General.cPoly tri r' i k x)
      rw [qa_cPoly_congr tri i k x r r' h]
    -- for fixed `x`, the average of the product is the product of the averages, by (48)
    have hx : ∀ x : QAlgorithms.Qubits n,
        avgD (fun r => f 0 x r * f 1 x r * f 2 x r) =
          Real.cos γ ^ (QAOAE3Lin2.General.termCount tri i 0 + QAOAE3Lin2.General.termCount tri i 1 +
            QAOAE3Lin2.General.termCount tri i 2) := by
      intro x
      classical
      let S : Fin 3 → Finset (Fin m) := fun k =>
        Finset.univ.filter fun j => QAOAE3Lin2.General.sharesOnly tri i j k
      have hmem : ∀ k j, j ∈ S k ↔ QAOAE3Lin2.General.sharesOnly tri i j k := by
        intro k j; simp [S]
      have hassoc : (fun r => f 0 x r * f 1 x r * f 2 x r) =
          fun r => f 0 x r * (f 1 x r * f 2 x r) := by
        funext r; ring
      have h01 : avgD (fun r => f 0 x r * (f 1 x r * f 2 x r)) =
          avgD (f 0 x) * avgD (fun r => f 1 x r * f 2 x r) := by
        refine qa_indep_avg (S 0) (f 0 x) (fun r => f 1 x r * f 2 x r) ?_ ?_
        · intro r r' h
          exact hfdep 0 x r r' (fun j hj => h j ((hmem 0 j).mpr hj))
        · intro r r' h
          have e1 : f 1 x r = f 1 x r' := hfdep 1 x r r' (fun j hj =>
            h j (fun hj0 => qa_shares_disjoint tri i j 0 1 (by decide) ((hmem 0 j).mp hj0) hj))
          have e2 : f 2 x r = f 2 x r' := hfdep 2 x r r' (fun j hj =>
            h j (fun hj0 => qa_shares_disjoint tri i j 0 2 (by decide) ((hmem 0 j).mp hj0) hj))
          show f 1 x r * f 2 x r = f 1 x r' * f 2 x r'
          rw [e1, e2]
      have h12 : avgD (fun r => f 1 x r * f 2 x r) = avgD (f 1 x) * avgD (f 2 x) := by
        refine qa_indep_avg (S 1) (f 1 x) (f 2 x) ?_ ?_
        · intro r r' h
          exact hfdep 1 x r r' (fun j hj => h j ((hmem 1 j).mpr hj))
        · intro r r' h
          exact hfdep 2 x r r' (fun j hj =>
            h j (fun hj1 => qa_shares_disjoint tri i j 1 2 (by decide) ((hmem 1 j).mp hj1) hj))
      have h48 : ∀ k : Fin 3, avgD (f k x) = Real.cos γ ^ QAOAE3Lin2.General.termCount tri i k :=
        fun k => eq_48 tri i k γ x
      rw [hassoc, h01, h12, h48 0, h48 1, h48 2, pow_add, pow_add]
      ring
    -- average over the sign of equation `i` first, then use (47)
    rw [qa_avg_coord i (fun rhs => clauseTerm tri rhs i γ)]
    have h47 : (fun r : Fin m → Bool =>
          (clauseTerm tri (Function.update r i false) i γ +
            clauseTerm tri (Function.update r i true) i γ) / 2) =
        fun r => (1 / 2) * Real.sin γ *
          QAOAE3Lin2.General.avgZ (fun x => f 0 x r * f 1 x r * f 2 x r) := by
      funext r
      exact eq_47 tri htri r i γ
    rw [h47]
    -- exchange the two finite averages
    have hswap : avgD (fun r => (1 / 2) * Real.sin γ *
          QAOAE3Lin2.General.avgZ (fun x => f 0 x r * f 1 x r * f 2 x r)) =
        (1 / 2) * Real.sin γ *
          QAOAE3Lin2.General.avgZ (fun x => avgD (fun r => f 0 x r * f 1 x r * f 2 x r)) := by
      simp only [avgD, QAOAE3Lin2.General.avgZ, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun r _ => by ring))
    rw [hswap]
    have hconst : (fun x => avgD (fun r => f 0 x r * f 1 x r * f 2 x r)) =
        fun _ => Real.cos γ ^ (QAOAE3Lin2.General.termCount tri i 0 +
          QAOAE3Lin2.General.termCount tri i 1 + QAOAE3Lin2.General.termCount tri i 2) :=
      funext hx
    rw [hconst]
    have hQ : (Fintype.card (QAlgorithms.Qubits n) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [QAOAE3Lin2.General.avgZ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc (Fintype.card (QAlgorithms.Qubits n) : ℝ)⁻¹, inv_mul_cancel₀ hQ, one_mul]
  · -- each `c_k` has at most `D` terms
    have hD : ∀ k : Fin 3, QAOAE3Lin2.General.termCount tri i k ≤ D := by
      intro k
      unfold QAOAE3Lin2.General.termCount
      have hsub : (Finset.univ.filter fun j => QAOAE3Lin2.General.sharesOnly tri i j k) ⊆
          (Finset.univ.filter fun j =>
            QAOAE3Lin2.General.onTriple (tri j) (QAOAE3Lin2.General.roleBit (tri i) k)).erase i := by
        intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_erase, Finset.mem_filter]
        exact ⟨hj.2.1, Finset.mem_univ j, hj.2.2.1⟩
      have hi : i ∈ Finset.univ.filter fun j =>
          QAOAE3Lin2.General.onTriple (tri j) (QAOAE3Lin2.General.roleBit (tri i) k) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ i, ?_⟩
        fin_cases k <;> simp [QAOAE3Lin2.General.onTriple, QAOAE3Lin2.General.roleBit]
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hi] at hcard
      have hb := hocc (QAOAE3Lin2.General.roleBit (tri i) k)
      omega
    have h0 := hD 0
    have h1 := hD 1
    have h2 := hD 2
    omega

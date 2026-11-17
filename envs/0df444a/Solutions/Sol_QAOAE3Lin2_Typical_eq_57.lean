-- Prove2me | solution 1 for QAOAE3Lin2.Typical.eq_57
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T13:13:01.389073+00:00
-- url     : https://prove2.me/submissions/8d3cb624-c314-4746-92a3-8a92558bb6ec

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting
import Theorems.Thm_QAOAE3Lin2_Typical_eq_25

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

/-- By (25), the clause term of equation `i` depends only on the signs of the equations in
`deps tri i`. -/
theorem qa_clauseTerm_congr {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n)
    (htri : QAOAE3Lin2.General.IsTripleFamily tri) (i : Fin m) (γ : ℝ) (r r' : Fin m → Bool)
    (h : ∀ j ∈ deps tri i, r j = r' j) :
    clauseTerm tri r i γ = clauseTerm tri r' i γ := by
  have hsgn : QAOAE3Lin2.General.sgn r i = QAOAE3Lin2.General.sgn r' i := by
    unfold QAOAE3Lin2.General.sgn
    rw [h i (by simp [deps])]
  have hc : ∀ (k : Fin 3) (x : QAlgorithms.Qubits n),
      QAOAE3Lin2.General.cPoly tri r i k x = QAOAE3Lin2.General.cPoly tri r' i k x := by
    intro k x
    unfold QAOAE3Lin2.General.cPoly
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : QAOAE3Lin2.General.sharesOnly tri i j k
    · rw [if_pos hj, if_pos hj]
      have hmem : j ∈ deps tri i := by
        simp only [deps, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨k, hj⟩
      have hs : QAOAE3Lin2.General.sgn r j = QAOAE3Lin2.General.sgn r' j := by
        unfold QAOAE3Lin2.General.sgn
        rw [h j hmem]
      rw [hs]
    · rw [if_neg hj, if_neg hj]
  rw [eq_25 tri htri r i γ, eq_25 tri htri r' i γ]
  unfold QAOAE3Lin2.General.clauseSin
  simp only [hsgn, hc]

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (i i' : Fin m) (hdis : Disjoint (deps tri i) (deps tri i')) (γ : ℝ) :
    avgD (fun rhs => clauseTerm tri rhs i γ * clauseTerm tri rhs i' γ) =
      avgD (fun rhs => clauseTerm tri rhs i γ) *
        avgD (fun rhs => clauseTerm tri rhs i' γ) := by
  refine qa_indep_avg (deps tri i) (fun rhs => clauseTerm tri rhs i γ)
    (fun rhs => clauseTerm tri rhs i' γ) ?_ ?_
  · intro r r' h
    exact qa_clauseTerm_congr tri htri i γ r r' h
  · intro r r' h
    exact qa_clauseTerm_congr tri htri i' γ r r'
      (fun j hj => h j (fun hjA => Finset.disjoint_left.mp hdis hjA hj))

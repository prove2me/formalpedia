-- Prove2me | solution 1 for RiemannMasullo.summable_lattice_product_majorant
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:14:41.814628+00:00
-- url     : https://prove2.me/submissions/86ded1bb-5a34-42d3-9ecd-465cbfed5ef6

-- New supporting result for the lattice-sequence identification in Masullo Appendix D.
import Mathlib

theorem solution (r : ℕ) :
    let b := fun k : ℤ => 1/(1+(k:ℝ)^2)
    Summable (fun a : Fin r → ℤ => ∏ i, b (a i)) ∧
      (∑' a : Fin r → ℤ, ∏ i, b (a i)) = (∑' k : ℤ, b k)^r := by
  classical
  let b := fun k : ℤ => 1/(1+(k:ℝ)^2)
  have hb : Summable b := by
    have h0 := (hasSum_ite_eq (0:ℤ) (1:ℝ)).summable
    have h2 := Real.summable_one_div_int_pow.mpr (by decide : 1 < 2)
    apply (h0.add h2).of_nonneg_of_le (fun k => by dsimp [b]; positivity)
    intro k
    by_cases hk : k = 0
    · subst k; simp [b]
    · simp only [Pi.add_apply, if_neg hk, zero_add]
      exact one_div_le_one_div_of_le (by positivity : 0 < (k:ℝ)^2) (by linarith)
  change Summable (fun a : Fin r → ℤ => ∏ i, b (a i)) ∧ _
  induction r with
  | zero =>
    constructor
    · exact (hasSum_fintype _).summable
    · simp
  | succ r ih =>
    let q := fun a : Fin r → ℤ => ∏ i, b (a i)
    let g := fun x : ℤ × (Fin r → ℤ) => b x.1 * q x.2
    let e := Fin.consEquiv (fun _ : Fin (r+1) => ℤ)
    have hg : Summable g := by
      apply (summable_prod_of_nonneg (f:=g) (fun x => by dsimp [g,q,b]; positivity)).mpr
      constructor
      · intro k; exact ih.1.mul_left (b k)
      · simpa only [g,tsum_mul_left] using hb.mul_right (∑' a,q a)
    have he (x : ℤ × (Fin r → ℤ)) : (∏ i, b (e x i)) = g x := by
      rw [Fin.prod_univ_succ]
      rfl
    constructor
    · apply e.summable_iff.mp
      exact hg.congr (fun x => (he x).symm)
    · rw [←e.tsum_eq (fun a => ∏ i,b (a i))]
      simp_rw [he]
      rw [hg.tsum_prod]
      simp only [g,tsum_mul_left,tsum_mul_right]
      change _ * (∑' a : Fin r → ℤ, ∏ i,b (a i)) = _
      rw [ih.2,pow_succ]
      ring

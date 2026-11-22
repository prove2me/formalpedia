-- Prove2me | solution 1 for ShiShallow.quadratic_form_majority_le_of_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T23:28:50.259178+00:00
-- url     : https://prove2.me/submissions/4c4f1260-6690-4a23-b67f-41ae0fe156f0

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow

/-! ### Scalar helpers -/

/-- `conj z * z` is the real number `‖z‖ ^ 2`. -/
private lemma shiFin4_conj_mul_self (z : ℂ) :
    (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- Complex conjugation is involutive (routed through `star_star`). -/
private lemma shiFin4_conj_involutive (z : ℂ) :
    (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := by
  rw [starRingEnd_apply, starRingEnd_apply, star_star]

/-! ### Real majority-polynomial helpers -/

private theorem shiFin4_maj_step (a a' b d : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (h : a ≤ a') :
    a * b + b * d + d * a - 2 * (a * b * d)
      ≤ a' * b + b * d + d * a' - 2 * (a' * b * d) := by
  have hnn : 0 ≤ b * (1 - d) + d * (1 - b) :=
    add_nonneg (mul_nonneg hb0 (by linarith)) (mul_nonneg hd0 (by linarith))
  have hprod : 0 ≤ (a' - a) * (b * (1 - d) + d * (1 - b)) :=
    mul_nonneg (by linarith) hnn
  first
    | (linarith [hprod]; done)
    | (nlinarith [hprod]; done)

private theorem shiFin4_sym_le_maj_of_le_upper (p1 p2 p3 s : ℝ)
    (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (hp3 : 0 ≤ p3)
    (k1 : p1 ≤ s) (k2 : p2 ≤ s) (k3 : p3 ≤ s) (hs : s ≤ 1) :
    p1 * p2 + p2 * p3 + p3 * p1 - 2 * (p1 * p2 * p3) ≤ 3 * s ^ 2 - 2 * s ^ 3 := by
  have hs0 : 0 ≤ s := le_trans hp1 k1
  have hp21 : p2 ≤ 1 := le_trans k2 hs
  have hp31 : p3 ≤ 1 := le_trans k3 hs
  have m1 := shiFin4_maj_step p1 s p2 p3 hp2 hp21 hp3 hp31 k1
  have m2 := shiFin4_maj_step p2 s s p3 hs0 hs hp3 hp31 k2
  have m3 := shiFin4_maj_step p3 s s s hs0 hs hs0 hs k3
  first
    | (linarith [m1, m2, m3]; done)
    | (nlinarith [m1, m2, m3]; done)

private theorem shiFin4_weighted_majority_bound
    {ι : Type*} [Fintype ι] (s : ℝ) (α1 α2 α3 w : ι → ℝ) (hs : s ≤ 1)
    (h1 : ∀ j, 0 ≤ α1 j) (h2 : ∀ j, 0 ≤ α2 j) (h3 : ∀ j, 0 ≤ α3 j)
    (b1 : ∀ j, α1 j ≤ s) (b2 : ∀ j, α2 j ≤ s) (b3 : ∀ j, α3 j ≤ s)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) :
    ∑ j, (α1 j * α2 j + α2 j * α3 j + α3 j * α1 j
          - 2 * (α1 j * α2 j * α3 j)) * w j
      ≤ 3 * s ^ 2 - 2 * s ^ 3 := by
  have hpt : ∀ j : ι,
      (α1 j * α2 j + α2 j * α3 j + α3 j * α1 j - 2 * (α1 j * α2 j * α3 j)) * w j
        ≤ (3 * s ^ 2 - 2 * s ^ 3) * w j := fun j =>
    mul_le_mul_of_nonneg_right
      (shiFin4_sym_le_maj_of_le_upper (α1 j) (α2 j) (α3 j) s
        (h1 j) (h2 j) (h3 j) (b1 j) (b2 j) (b3 j) hs) (hw j)
  calc ∑ j, (α1 j * α2 j + α2 j * α3 j + α3 j * α1 j
              - 2 * (α1 j * α2 j * α3 j)) * w j
      ≤ ∑ j, (3 * s ^ 2 - 2 * s ^ 3) * w j :=
        Finset.sum_le_sum (fun j _ => hpt j)
    _ = (3 * s ^ 2 - 2 * s ^ 3) * ∑ j, w j := by
        first
          | (rw [← Finset.mul_sum]; done)
          | (rw [Finset.mul_sum]; done)
          | (simp [Finset.mul_sum]; done)
    _ = 3 * s ^ 2 - 2 * s ^ 3 := by rw [hsum, mul_one]

/-! ### The registered statement -/

theorem solution {N : ℕ}
    (M : Matrix (Bits N) (Bits N) ℂ) (s : ℝ) (hs : s ≤ 1)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → (Bits N → ℂ)) (α1 α2 α3 : ι → ℝ)
    (h1 : ∀ i, 0 ≤ α1 i) (h2 : ∀ i, 0 ≤ α2 i) (h3 : ∀ i, 0 ≤ α3 i)
    (b1 : ∀ i, α1 i ≤ s) (b2 : ∀ i, α2 i ≤ s) (b3 : ∀ i, α3 i ≤ s)
    (horth : ∀ i j, (∑ y : Bits N, (starRingEnd ℂ) (v i y) * v j y)
      = if i = j then 1 else 0)
    (hpars : ∀ z : Bits N → ℂ,
      (∑ i : ι, ‖∑ y : Bits N, (starRingEnd ℂ) (z y) * v i y‖ ^ 2)
        = ∑ y : Bits N, ‖z y‖ ^ 2)
    (heig : ∀ i, Matrix.mulVec M (v i)
      = fun y => ((α1 i * α2 i + α2 i * α3 i + α3 i * α1 i
            - 2 * (α1 i * α2 i * α3 i) : ℝ) : ℂ) * v i y)
    (Φ : Bits N → ℂ) (hΦ : ∑ y : Bits N, ‖Φ y‖ ^ 2 = 1) :
    (∑ y : Bits N, (starRingEnd ℂ) (Φ y) * Matrix.mulVec M Φ y).re
      ≤ 3 * s ^ 2 - 2 * s ^ 3 := by
  -- Abbreviate the majority polynomial.
  obtain ⟨lam, hlam⟩ : ∃ lam : ι → ℝ, ∀ i, lam i
      = α1 i * α2 i + α2 i * α3 i + α3 i * α1 i - 2 * (α1 i * α2 i * α3 i) :=
    ⟨_, fun _ => rfl⟩
  have heigL : ∀ i, Matrix.mulVec M (v i) = fun y => ((lam i : ℝ) : ℂ) * v i y := by
    intro i
    rw [hlam i]
    exact heig i
  -- Expansion coefficients `c i = ⟪v i, Φ⟫`.
  obtain ⟨c, hcj⟩ : ∃ c : ι → ℂ, ∀ i,
      c i = ∑ y : Bits N, (starRingEnd ℂ) (v i y) * Φ y := ⟨_, fun _ => rfl⟩
  -- The opposite-order inner product is the conjugate coefficient.
  have hcc : ∀ i : ι, (∑ y : Bits N, (starRingEnd ℂ) (Φ y) * v i y)
      = (starRingEnd ℂ) (c i) := by
    intro i
    have hstep : (starRingEnd ℂ) (c i)
        = ∑ y : Bits N, (starRingEnd ℂ) ((starRingEnd ℂ) (v i y) * Φ y) := by
      rw [hcj i]
      first
        | (exact map_sum (starRingEnd ℂ) _ Finset.univ; done)
        | (rw [map_sum]; done)
        | (simp only [map_sum]; done)
    rw [hstep]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [map_mul, shiFin4_conj_involutive]
    ring
  -- The Parseval weights sum to one.
  have hw1 : (∑ i : ι, ‖c i‖ ^ 2) = 1 := by
    have hP := hpars Φ
    rw [hΦ] at hP
    have hcongr : (∑ i : ι, ‖∑ y : Bits N, (starRingEnd ℂ) (Φ y) * v i y‖ ^ 2)
        = ∑ i : ι, ‖c i‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hcc i]
      first
        | (rw [RCLike.norm_conj]; done)
        | (rw [starRingEnd_apply, norm_star]; done)
        | (simp; done)
    rw [← hcongr]
    exact hP
  -- The residual of the eigenbasis expansion.
  obtain ⟨r, hr⟩ : ∃ r : Bits N → ℂ, ∀ y, r y = Φ y - ∑ i : ι, c i * v i y :=
    ⟨_, fun _ => rfl⟩
  have horthr : ∀ j : ι, (∑ y : Bits N, (starRingEnd ℂ) (v j y) * r y) = 0 := by
    intro j
    have hterm : ∀ y : Bits N, (starRingEnd ℂ) (v j y) * r y
        = (starRingEnd ℂ) (v j y) * Φ y
          - ∑ i : ι, c i * ((starRingEnd ℂ) (v j y) * v i y) := by
      intro y
      have hpull : (∑ i : ι, c i * ((starRingEnd ℂ) (v j y) * v i y))
          = (starRingEnd ℂ) (v j y) * ∑ i : ι, c i * v i y := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      rw [hr y, hpull, mul_sub]
    have hrw : (∑ y : Bits N, (starRingEnd ℂ) (v j y) * r y)
        = ∑ y : Bits N, ((starRingEnd ℂ) (v j y) * Φ y
            - ∑ i : ι, c i * ((starRingEnd ℂ) (v j y) * v i y)) :=
      Finset.sum_congr rfl (fun y _ => hterm y)
    have hswap : (∑ y : Bits N, ∑ i : ι, c i * ((starRingEnd ℂ) (v j y) * v i y))
        = ∑ i : ι, c i * ∑ y : Bits N, (starRingEnd ℂ) (v j y) * v i y := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
    have hdel : (∑ i : ι, c i * ∑ y : Bits N, (starRingEnd ℂ) (v j y) * v i y)
        = c j := by
      have hpt : ∀ i : ι, c i * (∑ y : Bits N, (starRingEnd ℂ) (v j y) * v i y)
          = if j = i then c i else 0 := by
        intro i
        rw [horth j i]
        by_cases hji : j = i
        · rw [if_pos hji, if_pos hji, mul_one]
        · rw [if_neg hji, if_neg hji, mul_zero]
      have hsc : (∑ i : ι, c i * ∑ y : Bits N, (starRingEnd ℂ) (v j y) * v i y)
          = ∑ i : ι, if j = i then c i else 0 :=
        Finset.sum_congr rfl (fun i _ => hpt i)
      rw [hsc, Finset.sum_ite_eq_of_mem Finset.univ j c (Finset.mem_univ j)]
    rw [hrw, Finset.sum_sub_distrib, hswap, hdel, ← hcj j, sub_self]
  -- Parseval forces the residual to vanish.
  have hr0 : ∀ y : Bits N, r y = 0 := by
    have hz : ∀ i : ι, (∑ y : Bits N, (starRingEnd ℂ) (r y) * v i y) = 0 := by
      intro i
      have hst : (∑ y : Bits N, (starRingEnd ℂ) (r y) * v i y)
          = (starRingEnd ℂ) (∑ y : Bits N, (starRingEnd ℂ) (v i y) * r y) := by
        have hmap : (starRingEnd ℂ) (∑ y : Bits N, (starRingEnd ℂ) (v i y) * r y)
            = ∑ y : Bits N, (starRingEnd ℂ) ((starRingEnd ℂ) (v i y) * r y) := by
          first
            | (exact map_sum (starRingEnd ℂ) _ Finset.univ; done)
            | (rw [map_sum]; done)
            | (simp only [map_sum]; done)
        rw [hmap]
        refine Finset.sum_congr rfl ?_
        intro y _
        rw [map_mul, shiFin4_conj_involutive]
        ring
      rw [hst, horthr i, map_zero]
    have hsum0 : (∑ y : Bits N, ‖r y‖ ^ 2) = 0 := by
      rw [← hpars r]
      refine Finset.sum_eq_zero ?_
      intro i _
      first
        | (rw [hz i, norm_zero]; norm_num; done)
        | (rw [hz i]; simp; done)
    intro y
    have hy : ‖r y‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => sq_nonneg ‖r w‖)).mp hsum0 y
        (Finset.mem_univ y)
    have hy2 : ‖r y‖ = 0 := by
      first
        | (exact pow_eq_zero_iff two_ne_zero |>.mp hy; done)
        | (exact sq_eq_zero_iff.mp hy; done)
        | (nlinarith [norm_nonneg (r y), hy]; done)
    exact norm_eq_zero.mp hy2
  have hexp : ∀ y : Bits N, Φ y = ∑ i : ι, c i * v i y := by
    intro y
    have hzy := hr0 y
    rw [hr y] at hzy
    first
      | (exact sub_eq_zero.mp hzy; done)
      | (exact sub_eq_zero_iff_eq.mp hzy; done)
      | (linear_combination hzy)
  -- Apply `M` termwise.
  have hMPhi : ∀ y : Bits N, Matrix.mulVec M Φ y
      = ∑ i : ι, c i * (((lam i : ℝ) : ℂ) * v i y) := by
    intro y
    have p0 : Matrix.mulVec M Φ y = ∑ z : Bits N, M y z * Φ z :=
      Matrix.mulVec_apply_eq_sum M Φ y
    have p1 : (∑ z : Bits N, M y z * Φ z)
        = ∑ z : Bits N, ∑ i : ι, c i * (M y z * v i z) := by
      refine Finset.sum_congr rfl ?_
      intro z _
      rw [hexp z, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have p2 : (∑ z : Bits N, ∑ i : ι, c i * (M y z * v i z))
        = ∑ i : ι, c i * ∑ z : Bits N, M y z * v i z := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
    have p3 : ∀ i : ι, (∑ z : Bits N, M y z * v i z)
        = ((lam i : ℝ) : ℂ) * v i y := by
      intro i
      have hv : Matrix.mulVec M (v i) y = ((lam i : ℝ) : ℂ) * v i y := by
        rw [heigL i]
      rw [← hv]
      exact (Matrix.mulVec_apply_eq_sum M (v i) y).symm
    have p4 : (∑ i : ι, c i * ∑ z : Bits N, M y z * v i z)
        = ∑ i : ι, c i * (((lam i : ℝ) : ℂ) * v i y) :=
      Finset.sum_congr rfl (fun i _ => by rw [p3 i])
    rw [p0, p1, p2, p4]
  -- Expand the quadratic form in the eigenbasis.
  have hquad : (∑ y : Bits N, (starRingEnd ℂ) (Φ y) * Matrix.mulVec M Φ y)
      = ∑ i : ι, ((lam i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    have q1 : (∑ y : Bits N, (starRingEnd ℂ) (Φ y) * Matrix.mulVec M Φ y)
        = ∑ y : Bits N, ∑ i : ι,
            (c i * ((lam i : ℝ) : ℂ)) * ((starRingEnd ℂ) (Φ y) * v i y) := by
      refine Finset.sum_congr rfl ?_
      intro y _
      rw [hMPhi y, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have q2 : (∑ y : Bits N, ∑ i : ι,
          (c i * ((lam i : ℝ) : ℂ)) * ((starRingEnd ℂ) (Φ y) * v i y))
        = ∑ i : ι, (c i * ((lam i : ℝ) : ℂ))
            * ∑ y : Bits N, (starRingEnd ℂ) (Φ y) * v i y := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
    have q3 : ∀ i : ι, (c i * ((lam i : ℝ) : ℂ))
          * (∑ y : Bits N, (starRingEnd ℂ) (Φ y) * v i y)
        = ((lam i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [hcc i]
      have hm : (starRingEnd ℂ) (c i) * c i = ((‖c i‖ ^ 2 : ℝ) : ℂ) :=
        shiFin4_conj_mul_self (c i)
      calc (c i * ((lam i : ℝ) : ℂ)) * (starRingEnd ℂ) (c i)
          = ((starRingEnd ℂ) (c i) * c i) * ((lam i : ℝ) : ℂ) := by ring
        _ = ((‖c i‖ ^ 2 : ℝ) : ℂ) * ((lam i : ℝ) : ℂ) := by rw [hm]
        _ = ((lam i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
              first
                | (push_cast; ring; done)
                | (rw [Complex.ofReal_mul]; ring; done)
                | (rw [Complex.ofReal_mul, mul_comm]; done)
    have q4 : (∑ i : ι, (c i * ((lam i : ℝ) : ℂ))
            * ∑ y : Bits N, (starRingEnd ℂ) (Φ y) * v i y)
        = ∑ i : ι, ((lam i * ‖c i‖ ^ 2 : ℝ) : ℂ) :=
      Finset.sum_congr rfl (fun i _ => q3 i)
    rw [q1, q2, q4]
  -- Take real parts and apply the weighted majority bound.
  rw [hquad, Complex.re_sum]
  have hre : (∑ i : ι, (((lam i * ‖c i‖ ^ 2 : ℝ) : ℂ)).re)
      = ∑ i : ι, lam i * ‖c i‖ ^ 2 :=
    Finset.sum_congr rfl (fun i _ => Complex.ofReal_re _)
  have hfin : (∑ i : ι, lam i * ‖c i‖ ^ 2)
      = ∑ i : ι, (α1 i * α2 i + α2 i * α3 i + α3 i * α1 i
          - 2 * (α1 i * α2 i * α3 i)) * ‖c i‖ ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [hlam i])
  rw [hre, hfin]
  exact shiFin4_weighted_majority_bound s α1 α2 α3 (fun i => ‖c i‖ ^ 2) hs
    h1 h2 h3 b1 b2 b3 (fun i => sq_nonneg _) hw1

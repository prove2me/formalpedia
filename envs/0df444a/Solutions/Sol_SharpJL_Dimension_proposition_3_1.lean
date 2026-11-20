-- Prove2me | solution 1 for SharpJL.Dimension.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:12:09.713499+00:00
-- url     : https://prove2.me/submissions/81587906-751d-4c40-a1cb-d7905db5ebe7

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
/-!
Blueprint for `SharpJL.Dimension.proposition_3_1` (Jain, STOC 2027 #707, Prop. 3.1).

Route: a deterministic potential-function walk (Levy–Ramadas–Rothvoss style) replacing the
paper's Brownian Lovett–Meka walk. State: a symmetric contraction `Q`. Potential
`pot λ w Q = ∑ₗ cosh (λ · wₗᵀ Q wₗ)`. Each step moves `Q ↦ Q + t H` with `H` symmetric,
Frobenius norm 1, Frobenius-orthogonal to `Q`, killing `ker (1 - Q)` and `ker (1 + Q)`,
annihilating the frozen forms (`|wₗᵀ Q wₗ| ≥ b`), orthogonal to the gradient of the potential,
and chosen by averaging over an orthonormal basis so the second-order term is ≤ pot / d₀.
The step size `t ≤ δ` is maximal subject to staying a contraction: either `t = δ`
(Frobenius² grows by δ²) or a new eigenvalue ±1 appears (`edim` grows).
-/
abbrev Mat (k : ℕ) := Matrix (Fin k) (Fin k) ℝ

/-- the quadratic form `wᵀ Q w` -/
def qf {k : ℕ} (Q : Mat k) (w : Fin k → ℝ) : ℝ := ∑ i, ∑ j, w i * Q i j * w j

/-- squared Frobenius norm -/
def frob {k : ℕ} (Q : Mat k) : ℝ := ∑ i, ∑ j, Q i j ^ 2

/-- Frobenius inner product -/
def fip {k : ℕ} (A B : Mat k) : ℝ := ∑ i, ∑ j, A i j * B i j

/-- number of eigenvalues equal to `1` or `-1` (with multiplicity) -/
noncomputable def edim {k : ℕ} (Q : Mat k) : ℕ :=
  Module.finrank ℝ (LinearMap.ker (1 - Q).mulVecLin) +
    Module.finrank ℝ (LinearMap.ker (1 + Q).mulVecLin)

/-- the potential -/
noncomputable def pot {k m : ℕ} (lam : ℝ) (w : Fin m → Fin k → ℝ) (Q : Mat k) : ℝ :=
  ∑ ℓ, Real.cosh (lam * qf Q (w ℓ))

/-- the frozen forms -/
noncomputable def frozen {k m : ℕ} (b : ℝ) (w : Fin m → Fin k → ℝ) (Q : Mat k) :
    Finset (Fin m) :=
  Finset.univ.filter (fun ℓ => b ≤ |qf Q (w ℓ)|)

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartB
open SharpJL.Dimension.Dev.P31
theorem qf_add_smul {k : ℕ} (Q H : Mat k) (t : ℝ) (w : Fin k → ℝ) :
    qf (Q + t • H) w = qf Q w + t * qf H w := by
  simp only [qf, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end SharpJL.Dimension.Dev.P31.PartB
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
/-! ### Elementary facts -/
alias qf_add_smul := SharpJL.Dimension.Dev.P31.PartB.qf_add_smul

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartB
open SharpJL.Dimension.Dev.P31
theorem qf_zero {k : ℕ} (w : Fin k → ℝ) : qf (0 : Mat k) w = 0 := by
  simp [qf]

end SharpJL.Dimension.Dev.P31.PartB
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
alias qf_zero := SharpJL.Dimension.Dev.P31.PartB.qf_zero

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartB
open SharpJL.Dimension.Dev.P31
theorem qf_abs_le {k : ℕ} (H : Mat k) (w : Fin k → ℝ) (hw : ∑ i, w i ^ 2 = 1)
    (hH : frob H = 1) : |qf H w| ≤ 1 := by
  have h1 : qf H w = ∑ p : Fin k × Fin k, (w p.1 * w p.2) * H p.1 p.2 := by
    rw [Fintype.sum_prod_type]; simp only [qf]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ p : Fin k × Fin k, (w p.1 * w p.2) ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, hw, one_mul]
  have h3 : ∑ p : Fin k × Fin k, (H p.1 p.2) ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]; exact hH
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun p : Fin k × Fin k => w p.1 * w p.2)
    (fun p => H p.1 p.2)
  rw [h2, h3, ← h1, one_mul] at this
  exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)

end SharpJL.Dimension.Dev.P31.PartB
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
alias qf_abs_le := SharpJL.Dimension.Dev.P31.PartB.qf_abs_le

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartB
open SharpJL.Dimension.Dev.P31
theorem frob_add_smul {k : ℕ} (Q H : Mat k) (t : ℝ) (h : fip Q H = 0) :
    frob (Q + t • H) = frob Q + t ^ 2 * frob H := by
  have e : frob (Q + t • H) = frob Q + 2 * t * fip Q H + t ^ 2 * frob H := by
    simp only [frob, fip, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e, h]; ring

end SharpJL.Dimension.Dev.P31.PartB
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
alias frob_add_smul := SharpJL.Dimension.Dev.P31.PartB.frob_add_smul

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartB
open SharpJL.Dimension.Dev.P31
theorem frob_zero {k : ℕ} : frob (0 : Mat k) = 0 := by
  simp [frob]

end SharpJL.Dimension.Dev.P31.PartB
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
alias frob_zero := SharpJL.Dimension.Dev.P31.PartB.frob_zero

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartA
open SharpJL.Dimension.Dev.P31
theorem inner_self_euc {k : ℕ} (e : EuclideanSpace ℝ (Fin k)) :
    inner ℝ e e = (WithLp.ofLp e) ⬝ᵥ (WithLp.ofLp e) := by
  have := inner_toEuclideanCLM (n := Fin k) (1 : Mat k) e e
  simpa using this

theorem norm_le_one_iff {k : ℕ} (A : Mat k) (hA : A.IsSymm) :
    ‖A‖ ≤ 1 ↔ ∀ x : Fin k → ℝ, |x ⬝ᵥ A *ᵥ x| ≤ x ⬝ᵥ x := by
  set T := toEuclideanCLM (n := Fin k) (𝕜 := ℝ) A with hT
  have hTs : (T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)).IsSymmetric := by
    rw [hT, coe_toEuclideanCLM_eq_toEuclideanLin]
    exact isSymmetric_toEuclideanLin_iff.mpr (isHermitian_iff_isSymm.mpr hA)
  have hnorm : ‖A‖ = ‖T‖ := rfl
  constructor
  · intro h x
    set e : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 x
    have h1 : x ⬝ᵥ A *ᵥ x = inner ℝ e (T e) := (inner_toEuclideanCLM A e e).symm
    have h2 : x ⬝ᵥ x = ‖e‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_self_euc]
    rw [h1, h2]
    calc |inner ℝ e (T e)| ≤ ‖e‖ * ‖T e‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖e‖ * (‖T‖ * ‖e‖) := by gcongr; exact T.le_opNorm e
      _ ≤ ‖e‖ * (1 * ‖e‖) := by gcongr; rw [← hnorm]; exact h
      _ = ‖e‖ ^ 2 := by ring
  · intro h
    rw [hnorm, T.norm_eq_iSup_rayleighQuotient hTs]
    refine ciSup_le fun e => ?_
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖e‖ ^ 2)]
    apply div_le_one_of_le₀ _ (by positivity)
    have := h (WithLp.ofLp e)
    rw [← inner_toEuclideanCLM, ← inner_self_euc, real_inner_self_eq_norm_sq] at this
    simpa [real_inner_comm] using this

theorem dot_self_nonneg {k : ℕ} (x : Fin k → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem frob_le_of_contraction {k : ℕ} (Q : Mat k) (hQ : SpencerEight.IsSymmContraction Q) :
    frob Q ≤ k := by
  have hcol : ∀ j, ∑ i, Q i j ^ 2 ≤ 1 := by
    intro j
    set e : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single j 1
    have h := Q.l2_opNorm_mulVec e
    have he : ‖e‖ = 1 := by simp [e]
    rw [he, mul_one] at h
    set v := Q *ᵥ WithLp.ofLp e
    have hv : v = fun i => Q i j := by
      ext i; simp [v, e]
    have h2 : ‖(EuclideanSpace.equiv (Fin k) ℝ).symm v‖ ^ 2 ≤ 1 := by
      have := norm_nonneg ((EuclideanSpace.equiv (Fin k) ℝ).symm v)
      nlinarith [hQ.2]
    rw [← real_inner_self_eq_norm_sq, inner_self_euc] at h2
    simpa [hv, dotProduct, sq] using h2
  unfold frob
  rw [Finset.sum_comm]
  calc ∑ j, ∑ i, Q i j ^ 2 ≤ ∑ _j : Fin k, (1 : ℝ) := Finset.sum_le_sum fun j _ => hcol j
    _ = k := by simp

end SharpJL.Dimension.Dev.P31.PartA
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
alias frob_le_of_contraction := SharpJL.Dimension.Dev.P31.PartA.frob_le_of_contraction

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartA
open SharpJL.Dimension.Dev.P31
theorem isSymmContraction_zero {k : ℕ} : SpencerEight.IsSymmContraction (0 : Mat k) :=
  ⟨isSymm_zero, by simp⟩

end SharpJL.Dimension.Dev.P31.PartA
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartA
open SharpJL.Dimension.Dev.P31
theorem isSymmContraction_one {k : ℕ} : SpencerEight.IsSymmContraction (1 : Mat k) := by
  refine ⟨isSymm_one, (norm_le_one_iff _ isSymm_one).2 fun x => ?_⟩
  rw [one_mulVec, abs_of_nonneg (dot_self_nonneg x)]

end SharpJL.Dimension.Dev.P31.PartA
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
alias isSymmContraction_one := SharpJL.Dimension.Dev.P31.PartA.isSymmContraction_one

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartA
open SharpJL.Dimension.Dev.P31
theorem edim_le {k : ℕ} (Q : Mat k) : edim Q ≤ k := by
  unfold edim
  set K1 := LinearMap.ker (1 - Q).mulVecLin
  set K2 := LinearMap.ker (1 + Q).mulVecLin
  have hinf : K1 ⊓ K2 = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨h1, h2⟩ := hv
    simp only [K1, K2, LinearMap.mem_ker, mulVecLin_apply, sub_mulVec, add_mulVec,
      one_mulVec] at h1 h2
    rw [Submodule.mem_bot]
    have : (2 : ℝ) • v = 0 := by
      rw [two_smul]; have e := sub_eq_zero.mp h1
      calc v + v = v + Q *ᵥ v := by rw [← e]
        _ = 0 := h2
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  have := Submodule.finrank_sup_add_finrank_inf_eq K1 K2
  rw [hinf, finrank_bot, add_zero] at this
  have h3 := Submodule.finrank_le (K1 ⊔ K2)
  simp only [Module.finrank_fin_fun] at h3
  omega

end SharpJL.Dimension.Dev.P31.PartA
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartA
open SharpJL.Dimension.Dev.P31
theorem edim_one {k : ℕ} : edim (1 : Mat k) = k := by
  unfold edim
  have h1 : LinearMap.ker ((1 : Mat k) - 1).mulVecLin = ⊤ := by
    rw [sub_self]; ext v; simp
  have h2 : LinearMap.ker ((1 : Mat k) + 1).mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    simp only [LinearMap.mem_ker, mulVecLin_apply, add_mulVec, one_mulVec] at hv
    rw [Submodule.mem_bot]
    rw [← two_smul ℝ v] at hv
    exact (smul_eq_zero.mp hv).resolve_left two_ne_zero
  rw [h1, h2, finrank_top, finrank_bot, Module.finrank_fin_fun]
  rfl

end SharpJL.Dimension.Dev.P31.PartA
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
alias edim_one := SharpJL.Dimension.Dev.P31.PartA.edim_one

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartB
open SharpJL.Dimension.Dev.P31
theorem pot_zero {k m : ℕ} (lam : ℝ) (w : Fin m → Fin k → ℝ) : pot lam w (0 : Mat k) = m := by
  simp [pot, qf_zero]

end SharpJL.Dimension.Dev.P31.PartB
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
alias pot_zero := SharpJL.Dimension.Dev.P31.PartB.pot_zero

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartB
open SharpJL.Dimension.Dev.P31
theorem card_frozen_le {k m : ℕ} (lam b : ℝ) (hlam : 0 ≤ lam) (w : Fin m → Fin k → ℝ)
    (Q : Mat k) :
    ((frozen b w Q).card : ℝ) * Real.exp (lam * b) ≤ 2 * pot lam w Q := by
  have hle : ∀ ℓ ∈ frozen b w Q, Real.exp (lam * b) ≤ 2 * Real.cosh (lam * qf Q (w ℓ)) := by
    intro ℓ hℓ
    simp only [frozen, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    have e1 : Real.exp (lam * b) ≤ Real.exp |lam * qf Q (w ℓ)| := by
      rw [abs_mul, abs_of_nonneg hlam]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hℓ hlam)
    have e2 := Real.exp_abs_le (lam * qf Q (w ℓ))
    rw [Real.cosh_eq]; linarith
  calc ((frozen b w Q).card : ℝ) * Real.exp (lam * b)
      = ∑ ℓ ∈ frozen b w Q, Real.exp (lam * b) := by simp
    _ ≤ ∑ ℓ ∈ frozen b w Q, 2 * Real.cosh (lam * qf Q (w ℓ)) := Finset.sum_le_sum hle
    _ ≤ ∑ ℓ, 2 * Real.cosh (lam * qf Q (w ℓ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun ℓ _ _ => by positivity)
    _ = 2 * pot lam w Q := by rw [pot, Finset.mul_sum]

end SharpJL.Dimension.Dev.P31.PartB
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartB
open SharpJL.Dimension.Dev.P31
lemma cosh_le_quad (y : ℝ) (hy : |y| ≤ 1) : Real.cosh y ≤ 1 + y ^ 2 := by
  have h1 := Real.abs_exp_sub_one_sub_id_le hy
  have h2 := Real.abs_exp_sub_one_sub_id_le (x := -y) (by rwa [abs_neg])
  rw [Real.cosh_eq]
  have := (abs_le.mp h1).2; have := (abs_le.mp h2).2
  nlinarith

lemma sinh_sub_le (y : ℝ) (hy : |y| ≤ 1) : |Real.sinh y - y| ≤ y ^ 2 := by
  have h1 := Real.abs_exp_sub_one_sub_id_le hy
  have h2 := Real.abs_exp_sub_one_sub_id_le (x := -y) (by rwa [abs_neg])
  rw [Real.sinh_eq]
  obtain ⟨a1, a2⟩ := abs_le.mp h1; obtain ⟨b1, b2⟩ := abs_le.mp h2
  rw [abs_le]; constructor <;> nlinarith

lemma abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  rw [Real.abs_sinh, ← Real.cosh_abs]; exact (Real.sinh_lt_cosh _).le

lemma cosh_add_le (x y : ℝ) (hy : |y| ≤ 1) :
    Real.cosh (x + y) ≤ Real.cosh x + y * Real.sinh x + 2 * y ^ 2 * Real.cosh x := by
  rw [Real.cosh_add]
  have hc := cosh_le_quad y hy
  have hs := sinh_sub_le y hy
  have hx := abs_sinh_le_cosh x
  have hcx := Real.cosh_pos x
  have e1 : Real.cosh x * Real.cosh y ≤ Real.cosh x * (1 + y ^ 2) :=
    mul_le_mul_of_nonneg_left hc hcx.le
  have e2 : Real.sinh x * (Real.sinh y - y) ≤ Real.cosh x * y ^ 2 := by
    calc Real.sinh x * (Real.sinh y - y) ≤ |Real.sinh x * (Real.sinh y - y)| := le_abs_self _
      _ = |Real.sinh x| * |Real.sinh y - y| := abs_mul _ _
      _ ≤ Real.cosh x * y ^ 2 := mul_le_mul hx hs (abs_nonneg _) hcx.le
  nlinarith

theorem pot_step {k m : ℕ} (lam d t : ℝ) (hlam : 0 ≤ lam) (hd : 0 < d) (ht : 0 ≤ t)
    (hlt : lam * t ≤ 1) (w : Fin m → Fin k → ℝ) (hw : ∀ ℓ, ∑ i, w ℓ i ^ 2 = 1) (Q H : Mat k)
    (hH : frob H = 1)
    (hs : ∑ ℓ, Real.sinh (lam * qf Q (w ℓ)) * qf H (w ℓ) = 0)
    (hc : ∑ ℓ, Real.cosh (lam * qf Q (w ℓ)) * qf H (w ℓ) ^ 2 ≤ pot lam w Q / d) :
    pot lam w (Q + t • H) ≤ pot lam w Q * (1 + 2 * lam ^ 2 * t ^ 2 / d) := by
  have key : ∀ ℓ, Real.cosh (lam * qf (Q + t • H) (w ℓ)) ≤
      Real.cosh (lam * qf Q (w ℓ)) + (lam * t) * (Real.sinh (lam * qf Q (w ℓ)) * qf H (w ℓ))
        + 2 * (lam * t) ^ 2 * (Real.cosh (lam * qf Q (w ℓ)) * qf H (w ℓ) ^ 2) := by
    intro ℓ
    have hh := qf_abs_le H (w ℓ) (hw ℓ) hH
    have hy : |lam * t * qf H (w ℓ)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hlam ht)]
      calc lam * t * |qf H (w ℓ)| ≤ 1 * 1 :=
            mul_le_mul hlt hh (abs_nonneg _) zero_le_one
        _ = 1 := by ring
    have := cosh_add_le (lam * qf Q (w ℓ)) (lam * t * qf H (w ℓ)) hy
    rw [qf_add_smul, mul_add, ← mul_assoc lam t]
    linarith [show (lam * t * qf H (w ℓ)) ^ 2 * Real.cosh (lam * qf Q (w ℓ))
      = (lam * t) ^ 2 * (Real.cosh (lam * qf Q (w ℓ)) * qf H (w ℓ) ^ 2) by ring]
  have hpot : 0 ≤ pot lam w Q := Finset.sum_nonneg fun ℓ _ => (Real.cosh_pos _).le
  calc pot lam w (Q + t • H) ≤ ∑ ℓ, (Real.cosh (lam * qf Q (w ℓ))
        + (lam * t) * (Real.sinh (lam * qf Q (w ℓ)) * qf H (w ℓ))
        + 2 * (lam * t) ^ 2 * (Real.cosh (lam * qf Q (w ℓ)) * qf H (w ℓ) ^ 2)) :=
        Finset.sum_le_sum fun ℓ _ => key ℓ
    _ = pot lam w Q + (lam * t) * ∑ ℓ, Real.sinh (lam * qf Q (w ℓ)) * qf H (w ℓ)
        + 2 * (lam * t) ^ 2 * ∑ ℓ, Real.cosh (lam * qf Q (w ℓ)) * qf H (w ℓ) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          pot]
    _ ≤ pot lam w Q + (lam * t) * 0 + 2 * (lam * t) ^ 2 * (pot lam w Q / d) := by
        rw [hs]; gcongr
    _ = pot lam w Q * (1 + 2 * lam ^ 2 * t ^ 2 / d) := by
        field_simp; ring

/-! ### The direction -/
abbrev Xs (k : ℕ) := EuclideanSpace ℝ (Fin k × Fin k)

def toMat {k : ℕ} (x : Xs k) : Mat k := Matrix.of fun i j => x (i, j)

def toMatL (k : ℕ) : Xs k →ₗ[ℝ] Mat k where
  toFun := toMat
  map_add' x y := by ext i j; simp [toMat]
  map_smul' c x := by ext i j; simp [toMat]

def qfL {k : ℕ} (w : Fin k → ℝ) : Mat k →ₗ[ℝ] ℝ where
  toFun H := qf H w
  map_add' A B := by simpa using qf_add_smul A B 1 w
  map_smul' c B := by simpa [qf_zero] using qf_add_smul 0 B c w

def fipL {k : ℕ} (Q : Mat k) : Mat k →ₗ[ℝ] ℝ where
  toFun H := fip Q H
  map_add' A B := by
    simp only [fip, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c B := by
    simp only [fip, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

abbrev Up (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

def symL (k : ℕ) : Mat k →ₗ[ℝ] (Up k → ℝ) where
  toFun H := fun p => H p.1.1 p.1.2 - H p.1.2 p.1.1
  map_add' A B := by ext p; simp; ring
  map_smul' c B := by ext p; simp; ring

def kerL {k : ℕ} (K : Submodule ℝ (Fin k → ℝ)) : Mat k →ₗ[ℝ] (K →ₗ[ℝ] (Fin k → ℝ)) where
  toFun H := H.mulVecLin ∘ₗ K.subtype
  map_add' A B := by ext v; simp
  map_smul' c B := by ext v; simp

lemma card_up_le (k : ℕ) : 2 * Fintype.card (Up k) ≤ k * k := by
  have h1 := Fintype.card_subtype_compl (fun p : Fin k × Fin k => p.1 < p.2)
  have h2 : Fintype.card {p : Fin k × Fin k // p.2 < p.1} = Fintype.card (Up k) :=
    Fintype.card_congr (Equiv.subtypeEquiv (Equiv.prodComm _ _) (by simp))
  have h3 : Fintype.card {p : Fin k × Fin k // p.2 < p.1} ≤
      Fintype.card {p : Fin k × Fin k // ¬ p.1 < p.2} :=
    Fintype.card_le_of_injective (fun p => ⟨p.1, not_lt.mpr p.2.le⟩)
      (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
  have h4 : Fintype.card (Up k) ≤ Fintype.card (Fin k × Fin k) := Fintype.card_subtype_le _
  have h5 : Fintype.card {x : Fin k × Fin k // ¬ x.1 < x.2} =
      Fintype.card (Fin k × Fin k) - Fintype.card (Up k) := by
    rw [h1]
  simp only [Fintype.card_prod, Fintype.card_fin] at h5 h4
  omega

lemma frob_toMat {k : ℕ} (x : Xs k) : frob (toMat x) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fintype.sum_prod_type]
  simp [frob, toMat]

def Wv {k : ℕ} (w : Fin k → ℝ) : Xs k := WithLp.toLp 2 (fun p => w p.1 * w p.2)

lemma inner_Wv {k : ℕ} (x : Xs k) (w : Fin k → ℝ) : inner ℝ x (Wv w) = qf (toMat x) w := by
  simp only [PiLp.inner_apply, Wv, toMat, qf, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp; ring

lemma norm_Wv {k : ℕ} (w : Fin k → ℝ) (hw : ∑ i, w i ^ 2 = 1) : ‖Wv w‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fintype.sum_prod_type]
  simp only [Wv, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, mul_pow, ← Finset.mul_sum,
    ← Finset.sum_mul, hw, one_mul]

theorem exists_direction {k m : ℕ} (w : Fin m → Fin k → ℝ) (hw : ∀ ℓ, ∑ i, w ℓ i ^ 2 = 1)
    (Q : Mat k) (J : Finset (Fin m)) (c s : Fin m → ℝ) (hc : ∀ ℓ, 0 ≤ c ℓ) (d₀ : ℝ)
    (hd₀ : 0 < d₀)
    (hdim : (k : ℝ) ^ 2 / 2 + (edim Q : ℝ) * k + J.card + 2 + d₀ ≤ (k : ℝ) ^ 2) :
    ∃ H : Mat k, H.IsSymm ∧ frob H = 1 ∧ fip Q H = 0 ∧
      (∀ v, (1 - Q) *ᵥ v = 0 → H *ᵥ v = 0) ∧ (∀ v, (1 + Q) *ᵥ v = 0 → H *ᵥ v = 0) ∧
      (∀ ℓ ∈ J, qf H (w ℓ) = 0) ∧ ∑ ℓ, s ℓ * qf H (w ℓ) = 0 ∧
      ∑ ℓ, c ℓ * qf H (w ℓ) ^ 2 ≤ (∑ ℓ, c ℓ) / d₀ := by
  set K1 := LinearMap.ker (1 - Q).mulVecLin
  set K2 := LinearMap.ker (1 + Q).mulVecLin
  let qJ : Mat k →ₗ[ℝ] (J → ℝ) := LinearMap.pi fun ℓ : J => qfL (w ℓ)
  let sL : Mat k →ₗ[ℝ] ℝ := ∑ ℓ, s ℓ • qfL (w ℓ)
  let L : Mat k →ₗ[ℝ] _ :=
    (symL k).prod ((kerL K1).prod ((kerL K2).prod (qJ.prod ((fipL Q).prod sL))))
  let Lx := L ∘ₗ toMatL k
  -- dimension count
  have hrn := LinearMap.finrank_range_add_finrank_ker Lx
  have hrange := Submodule.finrank_le (LinearMap.range Lx)
  simp only [Module.finrank_prod, Module.finrank_linearMap, Module.finrank_fintype_fun_eq_card,
    Module.finrank_self, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe] at hrn hrange
  have hup := card_up_le k
  have hD : d₀ ≤ (Module.finrank ℝ (LinearMap.ker Lx) : ℝ) := by
    have e : (Module.finrank ℝ (LinearMap.ker Lx) : ℝ) + Module.finrank ℝ (LinearMap.range Lx) = k * k := by
      exact_mod_cast (by omega : Module.finrank ℝ (LinearMap.ker Lx) + Module.finrank ℝ (LinearMap.range Lx)
        = k * k)
    have hr : (Module.finrank ℝ (LinearMap.range Lx) : ℝ) ≤ Fintype.card (Up k) +
        (Module.finrank ℝ K1 * k + (Module.finrank ℝ K2 * k + (J.card + (1 + 1)))) := by
      exact_mod_cast hrange
    have hu : (2 * Fintype.card (Up k) : ℝ) ≤ k * k := by exact_mod_cast hup
    have he : (edim Q : ℝ) = Module.finrank ℝ K1 + Module.finrank ℝ K2 := by
      simp [edim, K1, K2]
    rw [he] at hdim
    nlinarith
  -- orthonormal basis and averaging
  set D := Module.finrank ℝ (LinearMap.ker Lx)
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le hd₀ hD
  let b := stdOrthonormalBasis ℝ (LinearMap.ker Lx)
  let v : Fin D → Xs k := fun i => (b i : Xs k)
  have hv : Orthonormal ℝ v := b.orthonormal.comp_linearIsometry (LinearMap.ker Lx).subtypeₗᵢ
  have bessel : ∀ ℓ, ∑ i, qf (toMat (v i)) (w ℓ) ^ 2 ≤ 1 := by
    intro ℓ
    have := hv.sum_inner_products_le (Wv (w ℓ)) (s := Finset.univ)
    rw [norm_Wv _ (hw ℓ)] at this
    simpa [inner_Wv, Real.norm_eq_abs, sq_abs] using this
  have hsumc : 0 ≤ ∑ ℓ, c ℓ := Finset.sum_nonneg fun ℓ _ => hc ℓ
  have htot : ∑ i, ∑ ℓ, c ℓ * qf (toMat (v i)) (w ℓ) ^ 2 ≤ ∑ i : Fin D, (∑ ℓ, c ℓ) / D := by
    rw [Finset.sum_comm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_div_cancel₀ _ hDpos.ne']
    refine Finset.sum_le_sum fun ℓ _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_of_le_one_right (hc ℓ) (bessel ℓ)
  have hne : (Finset.univ : Finset (Fin D)).Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ⟨⟨0, ?_⟩⟩
    exact_mod_cast hDpos
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hne htot
  have hmem : Lx (v i) = 0 := (b i).2
  have hmem' : ∀ y : Mat k, L y = 0 → (symL k y = 0 ∧ kerL K1 y = 0 ∧ kerL K2 y = 0 ∧
      qJ y = 0 ∧ fipL Q y = 0 ∧ sL y = 0) := by
    intro y hy
    simp only [L, LinearMap.prod_apply, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at hy
    exact hy
  replace hmem := hmem' _ hmem
  obtain ⟨hsym, hk1, hk2, hqJ, hfip, hs⟩ := hmem
  refine ⟨toMat (v i), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have key : ∀ a c : Fin k, a < c → toMat (v i) a c = toMat (v i) c a := by
      intro a c h
      have := congr_fun hsym ⟨(a, c), h⟩
      simp only [symL, toMatL, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      linarith
    refine Matrix.IsSymm.ext fun a c => ?_
    rcases lt_trichotomy a c with h | h | h
    · exact (key _ _ h).symm
    · subst h; rfl
    · exact key _ _ h
  · rw [frob_toMat]; simp [v, hv.1 i]
  · exact hfip
  · intro u hu
    have := LinearMap.congr_fun hk1 ⟨u, by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hu⟩
    simpa [kerL, toMatL] using this
  · intro u hu
    have := LinearMap.congr_fun hk2 ⟨u, by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hu⟩
    simpa [kerL, toMatL] using this
  · intro ℓ hℓ
    have := congr_fun hqJ ⟨ℓ, hℓ⟩
    simpa [qJ, qfL, toMatL] using this
  · simpa [sL, qfL, toMatL] using hs
  · exact hi.trans (div_le_div_of_nonneg_left hsumc hd₀ hD)

end SharpJL.Dimension.Dev.P31.PartB
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
/-! ### The direction (linear algebra and averaging) -/
alias exists_direction := SharpJL.Dimension.Dev.P31.PartB.exists_direction

/-! ### The potential step (Taylor bound for cosh) -/
alias pot_step := SharpJL.Dimension.Dev.P31.PartB.pot_step

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartA
open SharpJL.Dimension.Dev.P31
theorem dot_conj {k : ℕ} (U M : Mat k) (y : Fin k → ℝ) :
    (U *ᵥ y) ⬝ᵥ (M *ᵥ (U *ᵥ y)) = y ⬝ᵥ ((Uᵀ * M * U) *ᵥ y) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec y Uᵀ, vecMul_transpose]

theorem spectral_real {k : ℕ} (Q : Mat k) (hQ : Q.IsSymm) :
    ∃ (U : Mat k) (lam : Fin k → ℝ), Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ Uᵀ * Q * U = diagonal lam := by
  have hQh : Q.IsHermitian := isHermitian_iff_isSymm.mpr hQ
  have h1 : (hQh.eigenvectorUnitary : Mat k)ᵀ * hQh.eigenvectorUnitary = 1 := by
    have := Unitary.coe_star_mul_self hQh.eigenvectorUnitary
    simpa [star_eq_conjTranspose] using this
  have h2 : (hQh.eigenvectorUnitary : Mat k) * (hQh.eigenvectorUnitary : Mat k)ᵀ = 1 := by
    have := Unitary.coe_mul_star_self hQh.eigenvectorUnitary
    simpa [star_eq_conjTranspose] using this
  refine ⟨hQh.eigenvectorUnitary, hQh.eigenvalues, h1, h2, ?_⟩
  have hs := congrArg (fun M => (hQh.eigenvectorUnitary : Mat k)ᵀ * M *
    (hQh.eigenvectorUnitary : Mat k)) hQh.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial] at hs
  rw [hs]
  simp only [mul_assoc, h1, mul_one]
  rw [← mul_assoc, h1, one_mul]
  rfl

theorem exists_eps {k : ℕ} (Q H : Mat k) (hQ : SpencerEight.IsSymmContraction Q)
    (hH : H.IsSymm)
    (h1 : ∀ v, (1 - Q) *ᵥ v = 0 → H *ᵥ v = 0) (h2 : ∀ v, (1 + Q) *ᵥ v = 0 → H *ᵥ v = 0) :
    ∃ ε > 0, ∀ s : ℝ, 0 ≤ s → s ≤ ε → ∀ x : Fin k → ℝ,
      |x ⬝ᵥ Q *ᵥ x + s * (x ⬝ᵥ H *ᵥ x)| ≤ x ⬝ᵥ x := by
  obtain ⟨U, lam, hUU, hUU', hD⟩ := spectral_real Q hQ.1
  have hQq := (norm_le_one_iff Q hQ.1).1 hQ.2
  set H' := Uᵀ * H * U with hH'
  -- formulas in the new coordinates
  have fx : ∀ y, (U *ᵥ y) ⬝ᵥ (U *ᵥ y) = y ⬝ᵥ y := by
    intro y; have := dot_conj U 1 y; simpa [hUU] using this
  have fQ : ∀ y, (U *ᵥ y) ⬝ᵥ (Q *ᵥ (U *ᵥ y)) = ∑ i, lam i * y i ^ 2 := by
    intro y; rw [dot_conj, hD]
    simp [dotProduct, mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => by ring
  have fH : ∀ y, (U *ᵥ y) ⬝ᵥ (H *ᵥ (U *ᵥ y)) = ∑ i, ∑ j, y i * H' i j * y j := by
    intro y; rw [dot_conj]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  -- eigen-relations
  have hQU : Q * U = U * diagonal lam := by
    rw [← hD, ← mul_assoc, ← mul_assoc, hUU', one_mul]
  have heig : ∀ j, Q *ᵥ (U *ᵥ Pi.single j 1) = lam j • (U *ᵥ Pi.single j 1) := by
    intro j
    rw [mulVec_mulVec, hQU, ← mulVec_mulVec, mulVec_single_one, ← mulVec_smul]
    congr 1
    ext i
    by_cases h : i = j <;> simp [h, diagonal]
  have hbad : ∀ j, |lam j| = 1 → H *ᵥ (U *ᵥ Pi.single j 1) = 0 := by
    intro j hj
    rcases abs_eq (zero_le_one) |>.1 hj with h | h
    · apply h1; rw [sub_mulVec, one_mulVec, heig, h, one_smul, sub_self]
    · apply h2; rw [add_mulVec, one_mulVec, heig, h, neg_one_smul, add_neg_cancel]
  have hH'sym : H'ᵀ = H' := by
    rw [hH', transpose_mul, transpose_mul, transpose_transpose, hH.eq, mul_assoc]
  have hcol : ∀ i j, |lam j| = 1 → H' i j = 0 := by
    intro i j hj
    have : H' *ᵥ Pi.single j 1 = 0 := by
      rw [hH', ← mulVec_mulVec, ← mulVec_mulVec, hbad j hj, mulVec_zero]
    have := congrFun this i
    simpa [mulVec_single_one] using this
  have hrow : ∀ i j, |lam i| = 1 → H' i j = 0 := by
    intro i j hi
    rw [← hH'sym, transpose_apply]; exact hcol j i hi
  -- eigenvalue bounds
  have hlam : ∀ i, |lam i| ≤ 1 := by
    intro i
    have := hQq (U *ᵥ Pi.single i 1)
    rw [fQ, fx] at this
    simpa [Pi.single_apply] using this
  -- the gap γ
  obtain ⟨γ, hγ, hγle⟩ : ∃ γ > 0, ∀ i, |lam i| = 1 ∨ γ ≤ 1 - |lam i| := by
    rcases isEmpty_or_nonempty (Fin k) with hk | hk
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · set f : Fin k → ℝ := fun i => if |lam i| = 1 then 1 else 1 - |lam i|
      obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
      refine ⟨f i0, ?_, fun i => ?_⟩
      · simp only [f]; split_ifs with h
        · exact one_pos
        · have := hlam i0; have : |lam i0| < 1 := lt_of_le_of_ne this h; linarith
      · by_cases h : |lam i| = 1
        · exact Or.inl h
        · right; have := hi0 i (Finset.mem_univ _); simp only [f, h, if_false] at this
          exact this
  set B := ∑ i, ∑ j, |H' i j| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨γ / (B + 1), by positivity, fun s hs0 hsε x => ?_⟩
  set y := Uᵀ *ᵥ x
  have hx : x = U *ᵥ y := by rw [mulVec_mulVec, hUU', one_mulVec]
  rw [hx, fQ, fH, fx]
  set S := ∑ i, (1 - |lam i|) * y i ^ 2 with hS
  have hSterm : ∀ i, (1 - |lam i|) * y i ^ 2 ≤ S := fun i =>
    Finset.single_le_sum (f := fun i => (1 - |lam i|) * y i ^ 2)
      (fun i _ => mul_nonneg (by linarith [hlam i]) (sq_nonneg _)) (Finset.mem_univ i)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (by linarith [hlam i]) (sq_nonneg _)
  have hterm : ∀ i j, |y i * H' i j * y j| ≤ |H' i j| * (S / γ) := by
    intro i j
    rcases hγle i with hi | hi
    · rw [hrow i j hi]; simp only [mul_zero, zero_mul, abs_zero]; positivity
    rcases hγle j with hj | hj
    · rw [hcol i j hj]; simp only [mul_zero, zero_mul, abs_zero]; positivity
    rw [abs_mul, abs_mul, mul_comm |y i|, mul_assoc]
    gcongr
    rw [le_div_iff₀ hγ, ← abs_mul]
    have a1 := hSterm i; have a2 := hSterm j
    have a3 : γ * y i ^ 2 ≤ (1 - |lam i|) * y i ^ 2 := by gcongr
    have a4 : γ * y j ^ 2 ≤ (1 - |lam j|) * y j ^ 2 := by gcongr
    have a5 : 2 * |y i * y j| ≤ y i ^ 2 + y j ^ 2 := by
      rw [abs_mul]; nlinarith [sq_nonneg (|y i| - |y j|), sq_abs (y i), sq_abs (y j)]
    nlinarith
  have hHb : |∑ i, ∑ j, y i * H' i j * y j| ≤ B * (S / γ) := by
    calc |∑ i, ∑ j, y i * H' i j * y j| ≤ ∑ i, ∑ j, |y i * H' i j * y j| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |H' i j| * (S / γ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = B * (S / γ) := by rw [hB, Finset.sum_mul]; simp only [Finset.sum_mul]
  have hsB : s * B ≤ γ := by
    calc s * B ≤ γ / (B + 1) * B := by gcongr
      _ ≤ γ := by rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  have hQpart : |∑ i, lam i * y i ^ 2| ≤ ∑ i, |lam i| * y i ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg (y i))]
  have hyy : y ⬝ᵥ y = ∑ i, |lam i| * y i ^ 2 + S := by
    rw [hS, ← Finset.sum_add_distrib]; simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hyy]
  calc |∑ i, lam i * y i ^ 2 + s * ∑ i, ∑ j, y i * H' i j * y j|
      ≤ |∑ i, lam i * y i ^ 2| + |s * ∑ i, ∑ j, y i * H' i j * y j| := abs_add_le _ _
    _ ≤ ∑ i, |lam i| * y i ^ 2 + s * (B * (S / γ)) := by
        rw [abs_mul, abs_of_nonneg hs0]; gcongr
    _ ≤ ∑ i, |lam i| * y i ^ 2 + S := by
        have : s * (B * (S / γ)) = (s * B) * S / γ := by ring
        have h' : s * B * S / γ ≤ S := by rw [div_le_iff₀ hγ]; nlinarith
        linarith

theorem dot_add_smul {k : ℕ} (Q H : Mat k) (t : ℝ) (x : Fin k → ℝ) :
    x ⬝ᵥ (Q + t • H) *ᵥ x = x ⬝ᵥ Q *ᵥ x + t * (x ⬝ᵥ H *ᵥ x) := by
  rw [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]

theorem contraction_add_smul_iff {k : ℕ} (Q H : Mat k) (hQ : Q.IsSymm) (hH : H.IsSymm) (t : ℝ) :
    SpencerEight.IsSymmContraction (Q + t • H) ↔
      ∀ x : Fin k → ℝ, |x ⬝ᵥ Q *ᵥ x + t * (x ⬝ᵥ H *ᵥ x)| ≤ x ⬝ᵥ x := by
  have hs : (Q + t • H).IsSymm := hQ.add (hH.smul t)
  unfold SpencerEight.IsSymmContraction
  rw [norm_le_one_iff _ hs]
  simp only [hs, true_and, dot_add_smul]

theorem ker_sub_mono {k : ℕ} (Q H : Mat k) (t : ℝ)
    (h1 : ∀ v, (1 - Q) *ᵥ v = 0 → H *ᵥ v = 0) :
    LinearMap.ker (1 - Q).mulVecLin ≤ LinearMap.ker (1 - (Q + t • H)).mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  have := h1 v hv
  rw [sub_add_eq_sub_sub, sub_mulVec, hv, smul_mulVec, this, smul_zero, sub_zero]

theorem ker_add_mono {k : ℕ} (Q H : Mat k) (t : ℝ)
    (h2 : ∀ v, (1 + Q) *ᵥ v = 0 → H *ᵥ v = 0) :
    LinearMap.ker (1 + Q).mulVecLin ≤ LinearMap.ker (1 + (Q + t • H)).mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  have := h2 v hv
  rw [← add_assoc, add_mulVec, hv, smul_mulVec, this, smul_zero, add_zero]

theorem max_step {k : ℕ} (Q H : Mat k) (hQ : SpencerEight.IsSymmContraction Q) (hH : H.IsSymm)
    (h1 : ∀ v, (1 - Q) *ᵥ v = 0 → H *ᵥ v = 0) (h2 : ∀ v, (1 + Q) *ᵥ v = 0 → H *ᵥ v = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ t, 0 ≤ t ∧ t ≤ δ ∧ SpencerEight.IsSymmContraction (Q + t • H) ∧
      edim Q ≤ edim (Q + t • H) ∧ (t = δ ∨ edim Q < edim (Q + t • H)) := by
  have hmono : ∀ t, edim Q ≤ edim (Q + t • H) := fun t =>
    Nat.add_le_add (Submodule.finrank_mono (ker_sub_mono Q H t h1))
      (Submodule.finrank_mono (ker_add_mono Q H t h2))
  set S : Set ℝ := Set.Icc 0 δ ∩
    ⋂ x : Fin k → ℝ, {t : ℝ | |x ⬝ᵥ Q *ᵥ x + t * (x ⬝ᵥ H *ᵥ x)| ≤ x ⬝ᵥ x} with hS
  have hmem : ∀ t, t ∈ S ↔ 0 ≤ t ∧ t ≤ δ ∧ SpencerEight.IsSymmContraction (Q + t • H) := by
    intro t
    rw [contraction_add_smul_iff Q H hQ.1 hH]
    simp [hS, Set.mem_iInter, and_assoc]
  have hclosed : IsClosed S :=
    isClosed_Icc.inter (isClosed_iInter fun x => isClosed_le (by fun_prop) continuous_const)
  have hne : S.Nonempty := ⟨0, (hmem 0).2 ⟨le_rfl, hδ.le, by simpa using hQ⟩⟩
  have hbdd : BddAbove S := ⟨δ, fun t ht => ((hmem t).1 ht).2.1⟩
  set ts := sSup S with hts
  have htsS : ts ∈ S := hclosed.csSup_mem hne hbdd
  obtain ⟨hts0, htsδ, htsC⟩ := (hmem ts).1 htsS
  refine ⟨ts, hts0, htsδ, htsC, hmono ts, ?_⟩
  by_cases heq : ts = δ
  · exact Or.inl heq
  right
  by_contra hlt
  have hle := hmono ts
  have hEq : edim (Q + ts • H) = edim Q := by omega
  have hk1 := Submodule.finrank_mono (ker_sub_mono Q H ts h1)
  have hk2 := Submodule.finrank_mono (ker_add_mono Q H ts h2)
  unfold edim at hEq
  have e1 := Submodule.eq_of_le_of_finrank_eq (ker_sub_mono Q H ts h1) (by omega)
  have e2 := Submodule.eq_of_le_of_finrank_eq (ker_add_mono Q H ts h2) (by omega)
  have h1' : ∀ v, (1 - (Q + ts • H)) *ᵥ v = 0 → H *ᵥ v = 0 := by
    intro v hv
    have : v ∈ LinearMap.ker (1 - (Q + ts • H)).mulVecLin := hv
    rw [← e1] at this
    exact h1 v this
  have h2' : ∀ v, (1 + (Q + ts • H)) *ᵥ v = 0 → H *ᵥ v = 0 := by
    intro v hv
    have : v ∈ LinearMap.ker (1 + (Q + ts • H)).mulVecLin := hv
    rw [← e2] at this
    exact h2 v this
  obtain ⟨ε, hε, hεs⟩ := exists_eps (Q + ts • H) H htsC hH h1' h2'
  have hδts : 0 < δ - ts := sub_pos.2 (lt_of_le_of_ne htsδ heq)
  set s := min ε (δ - ts)
  have hs0 : 0 < s := lt_min hε hδts
  have hmem' : ts + s ∈ S := by
    refine (hmem _).2 ⟨by linarith, by linarith [min_le_right ε (δ - ts)], ?_⟩
    rw [contraction_add_smul_iff Q H hQ.1 hH]
    intro x
    have := hεs s hs0.le (min_le_left _ _) x
    rw [dot_add_smul] at this
    calc _ = |x ⬝ᵥ Q *ᵥ x + ts * (x ⬝ᵥ H *ᵥ x) + s * (x ⬝ᵥ H *ᵥ x)| := by ring_nf
      _ ≤ _ := this
  have := le_csSup hbdd hmem'
  linarith

end SharpJL.Dimension.Dev.P31.PartA
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
/-! ### The spectral step -/

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartA
open SharpJL.Dimension.Dev.P31
theorem walk {k m : ℕ} (w : Fin m → Fin k → ℝ) (hw : ∀ ℓ, ∑ i, w ℓ i ^ 2 = 1)
    (lam b δ d₀ : ℝ) (hlam : 0 < lam) (hb : 0 ≤ b) (hδ : 0 < δ) (hδl : lam * δ ≤ 1)
    (hd₀ : 0 < d₀)
    (hbudget : ∀ Q : Mat k, SpencerEight.IsSymmContraction Q → edim Q < ⌈(k : ℝ) / 4⌉₊ →
      pot lam w Q ≤ m * Real.exp (2 * lam ^ 2 * frob Q / d₀) →
      (k : ℝ) ^ 2 / 2 + (edim Q : ℝ) * k + (frozen b w Q).card + 2 + d₀ ≤ (k : ℝ) ^ 2) :
    ∃ Q : Mat k, SpencerEight.IsSymmContraction Q ∧ ⌈(k : ℝ) / 4⌉₊ ≤ edim Q ∧
      ∀ ℓ, |qf Q (w ℓ)| ≤ b + δ := by
  set G : Mat k → Prop := fun Q => SpencerEight.IsSymmContraction Q ∧
    (∀ ℓ, |qf Q (w ℓ)| ≤ b + δ) ∧ pot lam w Q ≤ m * Real.exp (2 * lam ^ 2 * frob Q / d₀)
    with hG
  set μ : Mat k → ℕ := fun Q => (k - edim Q) + ⌈((k : ℝ) - frob Q) / δ ^ 2⌉₊ with hμ
  have hk4 : ⌈(k : ℝ) / 4⌉₊ ≤ k := Nat.ceil_le.2 (by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith)
  have main : ∀ n : ℕ, ∀ Q : Mat k, G Q → μ Q = n →
      ∃ Q : Mat k, SpencerEight.IsSymmContraction Q ∧ ⌈(k : ℝ) / 4⌉₊ ≤ edim Q ∧
        ∀ ℓ, |qf Q (w ℓ)| ≤ b + δ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro Q hQG hμQ
    obtain ⟨hQC, hQf, hQp⟩ := hQG
    by_cases hdone : ⌈(k : ℝ) / 4⌉₊ ≤ edim Q
    · exact ⟨Q, hQC, hdone, hQf⟩
    rw [not_le] at hdone
    have hdim := hbudget Q hQC hdone hQp
    set J := frozen b w Q with hJdef
    obtain ⟨H, hHs, hHf, hfip, hk1, hk2, hJ, hss, hcc⟩ := exists_direction w hw Q J
      (fun ℓ => Real.cosh (lam * qf Q (w ℓ))) (fun ℓ => Real.sinh (lam * qf Q (w ℓ)))
      (fun ℓ => (Real.cosh_pos _).le) d₀ hd₀ hdim
    obtain ⟨t, ht0, htδ, hQ'C, hed, hcase⟩ := PartA.max_step Q H hQC hHs hk1 hk2 δ hδ
    set Q' := Q + t • H with hQ'
    have hfrob' : frob Q' = frob Q + t ^ 2 := by
      rw [hQ', frob_add_smul Q H t hfip, hHf, mul_one]
    have hpot := pot_step lam d₀ t hlam.le hd₀ ht0
      (by nlinarith) w hw Q H hHf hss hcc
    have hG' : G Q' := by
      refine ⟨hQ'C, fun ℓ => ?_, ?_⟩
      · rw [hQ', qf_add_smul]
        by_cases hℓ : ℓ ∈ J
        · rw [hJ ℓ hℓ, mul_zero, add_zero]; exact hQf ℓ
        · have hlt : |qf Q (w ℓ)| < b := by
            simpa [hJdef, frozen] using hℓ
          have h1 := qf_abs_le H (w ℓ) (hw ℓ) hHf
          calc |qf Q (w ℓ) + t * qf H (w ℓ)| ≤ |qf Q (w ℓ)| + |t * qf H (w ℓ)| := abs_add_le _ _
            _ ≤ b + δ := by
              rw [abs_mul, abs_of_nonneg ht0]
              nlinarith
      · rw [hfrob']
        have hx : 0 ≤ 2 * lam ^ 2 * t ^ 2 / d₀ := by positivity
        have he := Real.add_one_le_exp (2 * lam ^ 2 * t ^ 2 / d₀)
        have hm : 0 ≤ (m : ℝ) * Real.exp (2 * lam ^ 2 * frob Q / d₀) := by positivity
        calc pot lam w Q' ≤ pot lam w Q * (1 + 2 * lam ^ 2 * t ^ 2 / d₀) := hpot
          _ ≤ (m * Real.exp (2 * lam ^ 2 * frob Q / d₀)) * (1 + 2 * lam ^ 2 * t ^ 2 / d₀) := by
              gcongr
          _ ≤ (m * Real.exp (2 * lam ^ 2 * frob Q / d₀)) * Real.exp (2 * lam ^ 2 * t ^ 2 / d₀) := by
              gcongr; linarith
          _ = m * Real.exp (2 * lam ^ 2 * (frob Q + t ^ 2) / d₀) := by
              rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    have hfk : frob Q' ≤ k := PartA.frob_le_of_contraction Q' hQ'C
    have hek : edim Q' ≤ k := PartA.edim_le Q'
    have hdec : μ Q' < μ Q := by
      simp only [hμ]
      rcases hcase with htδ' | hlt
      · subst htδ'
        have ha : 0 ≤ ((k : ℝ) - frob Q') / t ^ 2 := div_nonneg (by linarith) (by positivity)
        have hceil : ⌈((k : ℝ) - frob Q) / t ^ 2⌉₊ = ⌈((k : ℝ) - frob Q') / t ^ 2⌉₊ + 1 := by
          rw [← Nat.ceil_add_one ha]
          congr 1
          rw [hfrob']; field_simp; ring
        rw [hceil]
        omega
      · have hc : ⌈((k : ℝ) - frob Q') / δ ^ 2⌉₊ ≤ ⌈((k : ℝ) - frob Q) / δ ^ 2⌉₊ := by
          apply Nat.ceil_mono
          gcongr
          rw [hfrob']; nlinarith
        omega
    exact ih (μ Q') (hμQ ▸ hdec) Q' hG' rfl
  refine main _ 0 ⟨PartA.isSymmContraction_zero, fun ℓ => ?_, ?_⟩ rfl
  · rw [qf_zero, abs_zero]; linarith
  · rw [pot_zero, frob_zero]; simp

end SharpJL.Dimension.Dev.P31.PartA
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
/-! ### The walk -/
alias walk := SharpJL.Dimension.Dev.P31.PartA.walk

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31.PartB
open SharpJL.Dimension.Dev.P31
/-! ### Proposition 3.1 -/
lemma qf_one {k : ℕ} (w : Fin k → ℝ) : qf (1 : Mat k) w = ∑ i, w i ^ 2 := by
  simp [qf, Matrix.one_apply, sq]

lemma frozen_card_small (k m : ℕ) (hk : 1 ≤ k) (F lam b Λ P : ℝ) (hF : 0 ≤ F)
    (hΛ : Real.exp Λ = 3 + (m : ℝ) / (k : ℝ) ^ 2) (hlb : lam * b = 32 * Λ)
    (hfr : F * Real.exp (lam * b) ≤ 2 * P) (hP : P ≤ m * Real.exp (16 * Λ)) :
    F ≤ (k : ℝ) ^ 2 / 1000 := by
  set x : ℝ := (m : ℝ) / (k : ℝ) ^ 2 with hx
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hm : (m : ℝ) = x * (k : ℝ) ^ 2 := by rw [hx]; field_simp
  have e16 : Real.exp (16 * Λ) = (3 + x) ^ 16 := by
    rw [show (16 : ℝ) * Λ = ((16 : ℕ) : ℝ) * Λ by norm_num, Real.exp_nat_mul, hΛ]
  have e32 : Real.exp (lam * b) = (3 + x) ^ 16 * (3 + x) ^ 16 := by
    rw [hlb, show (32 : ℝ) * Λ = ((32 : ℕ) : ℝ) * Λ by norm_num, Real.exp_nat_mul, hΛ]; ring
  rw [e32] at hfr
  rw [e16] at hP
  have hpos : 0 < (3 + x) ^ 16 := by positivity
  have h1 : F * (3 + x) ^ 16 ≤ 2 * x * (k : ℝ) ^ 2 := by
    have : F * (3 + x) ^ 16 * (3 + x) ^ 16 ≤ 2 * x * (k : ℝ) ^ 2 * (3 + x) ^ 16 := by
      nlinarith
    exact le_of_mul_le_mul_right this hpos
  have h2 : (3 : ℝ) ^ 15 * (3 + x) ≤ (3 + x) ^ 16 := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by linarith) 15)
      (by linarith)
  by_contra hcon
  rw [not_le] at hcon
  have : (k : ℝ) ^ 2 / 1000 * ((3 : ℝ) ^ 15 * (3 + x)) ≤ F * (3 + x) ^ 16 :=
    mul_le_mul hcon.le h2 (by positivity) hF
  nlinarith

theorem prop31 :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (k m : ℕ), 1 ≤ k → 1 ≤ m →
      ∀ (w : Fin m → EuclideanSpace ℝ (Fin k)),
        (∀ ℓ, ‖w ℓ‖ = 1) →
        ∃ Q : Matrix (Fin k) (Fin k) ℝ,
          SpencerEight.IsSymmContraction Q ∧
          ⌈(k : ℝ) / 4⌉₊ ≤
            Module.finrank ℝ (LinearMap.ker (1 - Q).mulVecLin) +
            Module.finrank ℝ (LinearMap.ker (1 + Q).mulVecLin) ∧
          ∀ ℓ : Fin m,
            |∑ i : Fin k, ∑ j : Fin k, w ℓ i * Q i j * w ℓ j| ≤
              C₁ * Real.sqrt (Real.log (3 + (m : ℝ) / (k : ℝ) ^ 2) / (k : ℝ)) := by
  refine ⟨64, by norm_num, ?_⟩
  intro k m hk hm w hw
  set w' : Fin m → Fin k → ℝ := fun ℓ i => w ℓ i with hw'def
  have hw' : ∀ ℓ, ∑ i, w' ℓ i ^ 2 = 1 := by
    intro ℓ
    have h := hw ℓ
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
    simpa [w', Real.norm_eq_abs, sq_abs] using h
  show ∃ Q : Mat k, SpencerEight.IsSymmContraction Q ∧ ⌈(k : ℝ) / 4⌉₊ ≤ edim Q ∧
    ∀ ℓ, |qf Q (w' ℓ)| ≤ 64 * Real.sqrt (Real.log (3 + (m : ℝ) / (k : ℝ) ^ 2) / (k : ℝ))
  set x : ℝ := (m : ℝ) / (k : ℝ) ^ 2 with hx
  set Λ := Real.log (3 + x) with hΛdef
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hx0 : 0 ≤ x := by positivity
  have hΛexp : Real.exp Λ = 3 + x := Real.exp_log (by linarith)
  have hΛ1 : 1 < Λ := by
    rw [hΛdef, Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  set b := 32 * Real.sqrt (Λ / k) with hbdef
  have hb0 : 0 ≤ b := by positivity
  by_cases hb1 : 1 ≤ b
  · refine ⟨1, isSymmContraction_one, ?_, ?_⟩
    · rw [edim_one, Nat.ceil_le]; linarith
    · intro ℓ
      rw [qf_one, hw' ℓ, abs_one]
      have : 0 ≤ Real.sqrt (Λ / k) := Real.sqrt_nonneg _
      linarith
  rw [not_le] at hb1
  have hΛk : 0 ≤ Λ / k := by positivity
  have hb2 : b ^ 2 = 1024 * (Λ / k) := by
    rw [hbdef, mul_pow, Real.sq_sqrt hΛk]; norm_num
  have hk1024 : 1024 * Λ < k := by
    have : b ^ 2 < 1 := by nlinarith
    rw [hb2] at this
    rw [mul_div_assoc'] at this
    rwa [div_lt_one hkpos] at this
  set lam := Real.sqrt (k * Λ) with hlamdef
  have hlampos : 0 < lam := Real.sqrt_pos.mpr (by positivity)
  have hlam2 : lam ^ 2 = k * Λ := Real.sq_sqrt (by positivity)
  have hlb : lam * b = 32 * Λ := by
    rw [hlamdef, hbdef, mul_left_comm, ← Real.sqrt_mul (by positivity),
      show (k : ℝ) * Λ * (Λ / k) = Λ ^ 2 by field_simp, Real.sqrt_sq (by linarith)]
  set δ := 1 / lam with hδdef
  have hδ : 0 < δ := by positivity
  have hδl : lam * δ ≤ 1 := by rw [hδdef, mul_one_div_cancel hlampos.ne']
  have hδb : δ ≤ b := by
    rw [hδdef, div_le_iff₀ hlampos]; nlinarith
  set d₀ : ℝ := (k : ℝ) ^ 2 / 8 with hd₀def
  have hd₀ : 0 < d₀ := by positivity
  obtain ⟨Q, hQ, hdim, hbd⟩ := walk w' hw' lam b δ d₀ hlampos hb0 hδ hδl hd₀ (by
    intro Q hQ hedim hpot
    have hfrob := frob_le_of_contraction Q hQ
    have hexp : 2 * lam ^ 2 * frob Q / d₀ ≤ 16 * Λ := by
      rw [hlam2, hd₀def, div_le_iff₀ (by positivity)]
      have : 0 ≤ Λ := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hfrob (by positivity : (0 : ℝ) ≤ 2 * (k * Λ))]
    have hP : pot lam w' Q ≤ m * Real.exp (16 * Λ) :=
      hpot.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))
    have hF := frozen_card_small k m hk ((frozen b w' Q).card) lam b Λ (pot lam w' Q)
      (by positivity) hΛexp hlb (card_frozen_le lam b hlampos.le w' Q) hP
    have he : (edim Q : ℝ) < k / 4 := Nat.lt_ceil.mp hedim
    have he' : (edim Q : ℝ) * k ≤ k / 4 * k := mul_le_mul_of_nonneg_right he.le hkpos.le
    have hk5 : (5 : ℝ) ≤ k := by linarith
    rw [hd₀def]
    nlinarith)
  refine ⟨Q, hQ, hdim, fun ℓ => (hbd ℓ).trans ?_⟩
  have : 0 ≤ Real.sqrt (Λ / k) := Real.sqrt_nonneg _
  linarith

end SharpJL.Dimension.Dev.P31.PartB
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension.Dev.P31
/-! ### Proposition 3.1 (parameters: C = 32, Λ = log (3 + m/k²), b = C √(Λ/k), λ = √(kΛ),
δ = 1/λ, d₀ = k²/8; case b ≥ 1 by `Q = 1`) -/
alias prop31 := SharpJL.Dimension.Dev.P31.PartB.prop31

end SharpJL.Dimension.Dev.P31
end

section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace SharpJL.Dimension
theorem chk_proposition_3_1 :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (k m : ℕ), 1 ≤ k → 1 ≤ m →
      ∀ (w : Fin m → EuclideanSpace ℝ (Fin k)),
        (∀ ℓ, ‖w ℓ‖ = 1) →
        ∃ Q : Matrix (Fin k) (Fin k) ℝ,
          SpencerEight.IsSymmContraction Q ∧
          ⌈(k : ℝ) / 4⌉₊ ≤
            Module.finrank ℝ (LinearMap.ker (1 - Q).mulVecLin) +
            Module.finrank ℝ (LinearMap.ker (1 + Q).mulVecLin) ∧
          ∀ ℓ : Fin m,
            |∑ i : Fin k, ∑ j : Fin k, w ℓ i * Q i j * w ℓ j| ≤
              C₁ * Real.sqrt (Real.log (3 + (m : ℝ) / (k : ℝ) ^ 2) / (k : ℝ)) := Dev.P31.prop31

end SharpJL.Dimension
end

theorem solution : type_of% @SharpJL.Dimension.chk_proposition_3_1 := @SharpJL.Dimension.chk_proposition_3_1

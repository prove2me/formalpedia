-- Prove2me | solution 1 for ShiTensor.quadratic_form_three_block_majority_le_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-15T20:46:04.157891+00:00
-- url     : https://prove2.me/submissions/85903a38-5d0f-462b-b0a5-e4bef06284f1

/-
SNDR-1: the FIRST NON-VACUOUS three-block majority soundness bound.

WHY.  `ShiTensor.majority_weight_three_copies_le_of_single_copy_bound` hypothesises that every
normalized state's single-copy acceptance weight is `≤ s`.  That weight is the quadratic form of
`A = star (circMatrix c) * projOut out * circMatrix c`, a PROJECTOR (idempotent since
`circMatrix c` is unitary), whose quadratic form attains `1` on unit vectors unless it is `0`.
So the hypothesis forces `A = 0` for `s < 1`: vacuous.  Ditto
`ShiShallow.acceptOperator_eigenvalues_in_zero_s`.

FIX: state the bound for an ARBITRARY HERMITIAN `A` on the witness space `Bits w`, not for an
acceptance projector.  A general Hermitian's quadratic form can genuinely lie in `[0, s]`,
`s < 1`.

SATISFIABILITY WITNESS (verified before fixing the statement).  For any `0 < s ≤ 1` take
`A = ((s : ℝ) : ℂ) • (1 : Op w)` and `A1 = A2 = A3 = ((s : ℝ) : ℂ) • (1 : Op (w + w + w))`.
`A` is Hermitian and NON-ZERO; at normalized `v` the quadratic form is
`∑ y, conj (v y) * (s * v y) = s`, real part `s ∈ [0, s]`, so `hqf` holds.  `hlift` holds:
`Matrix.mulVec A p = α • p` with `A = s • 1` gives `α • p = s • p`, so `α = s` unless `p = 0`,
and either way `Matrix.mulVec A1 (tensor (tensor p q) t) = α • tensor (tensor p q) t`.  Finally
`A1 * A2 + A2 * A3 + A3 * A1 - (2 : ℂ) • (A1 * A2 * A3) = (3 * s ^ 2 - 2 * s ^ 3) • 1`, so the
CONCLUSION holds with EQUALITY at every normalized `Θ`: tight, and the bounded quantity is
non-zero.  Generally any diagonal `A` with entries in `[0, s]`, with `A1, A2, A3` the block
liftings `A ⊗ 1 ⊗ 1`, `1 ⊗ A ⊗ 1`, `1 ⊗ 1 ⊗ A`, qualifies.  Nothing forces `A = 0`.

DESIGN.
* `A1 A2 A3` are EXPLICIT PARAMETERS constrained by `hlift`, whose shape is verbatim the
  conclusion shape of `ShiTensor.three_copy_conj_projOut_common_eigenvector`.  Constructing the
  liftings here would drag in `Fin.addCases`/`Fin.natAdd` reindexing irrelevant to the spectral
  argument and would hard-wire one lifting convention.
* The hypothesis bounds the QUADRATIC FORM over NORMALIZED vectors (the physically checkable
  form, and what a later compression step supplies), not the eigenvalues.  Homogenisation
  (`v ↦ v / ‖v‖`, `v = 0` separate) happens internally in `shiSnd_homog`, since the platform's
  eigenvalue theorems consume the homogeneous bound.
* `Θ` is an ARBITRARY normalized state of `Bits (w + w + w)`; NO product structure is assumed.
* The compression step (circuit acceptance operator ↔ `A`) is deliberately ABSENT.

Cited platform theorems (all Proved): `ShiShallow.exists_sum_form_eigenbasis`,
`ShiShallow.eigenvalues_nonneg_of_quadratic_form_nonneg`,
`ShiShallow.eigenvalues_le_of_quadratic_form_le`,
`ShiShallow.product_eigenbasis_sum_form_three`,
`ShiShallow.mulVec_majority_inclusion_exclusion_of_common_eigenvector`,
`ShiShallow.quadratic_form_majority_le_of_eigenbasis`.
Deliberately NOT cited: the two vacuous statements named above.

Built against Mathlib at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Matrix
import Definitions.Def_ShiTensor_Core
import Theorems.Thm_ShiShallow_exists_sum_form_eigenbasis
import Theorems.Thm_ShiShallow_eigenvalues_nonneg_of_quadratic_form_nonneg
import Theorems.Thm_ShiShallow_eigenvalues_le_of_quadratic_form_le
import Theorems.Thm_ShiShallow_product_eigenbasis_sum_form_three
import Theorems.Thm_ShiShallow_mulVec_majority_inclusion_exclusion_of_common_eigenvector
import Theorems.Thm_ShiShallow_quadratic_form_majority_le_of_eigenbasis

set_option autoImplicit false

open ShiShallow
open ShiTensor

/-- `Matrix.mulVec` as an explicit sum (definitional). -/
private lemma shiSnd_mulVec_sum {N : ℕ} (A : Op N) (v : Bits N → ℂ) (y : Bits N) :
    Matrix.mulVec A v y = ∑ z : Bits N, A y z * v z := by
  first
    | rfl
    | (simp only [Matrix.mulVec, dotProduct]; done)
    | (simp [Matrix.mulVec, dotProduct]; done)

/-- Pointwise scalar multiple of a vector, as a `•`. -/
private lemma shiSnd_smul_fun {N : ℕ} (k : ℂ) (v : Bits N → ℂ) :
    (fun y => k * v y) = k • v := by
  first
    | rfl
    | (funext y; rfl)
    | (funext y; simp)

/-- `Matrix.mulVec` is homogeneous in its vector argument. -/
private lemma shiSnd_mulVec_const {N : ℕ} (A : Op N) (k : ℂ) (v : Bits N → ℂ) (y : Bits N) :
    Matrix.mulVec A (fun x => k * v x) y = k * Matrix.mulVec A v y := by
  rw [shiSnd_mulVec_sum, shiSnd_mulVec_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by ring

/-- Real part of a real scalar times a complex number. -/
private lemma shiSnd_re_ofReal_mul (c : ℝ) (z : ℂ) : (((c : ℝ) : ℂ) * z).re = c * z.re := by
  first
    | (simp [Complex.mul_re]; done)
    | (simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring)

/-- The quadratic form is degree two homogeneous: scaling the vector by `k` scales it by
`conj k * k`. -/
private lemma shiSnd_qf_const {N : ℕ} (A : Op N) (k : ℂ) (v : Bits N → ℂ) :
    (∑ y : Bits N, (starRingEnd ℂ) (k * v y) * Matrix.mulVec A (fun x => k * v x) y)
      = (starRingEnd ℂ) k * k
          * ∑ y : Bits N, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [shiSnd_mulVec_const, map_mul]
  ring

/-- **Homogenisation.**  A two-sided bound on the quadratic form over NORMALIZED vectors
upgrades to the degree-two homogeneous bounds that the platform's eigenvalue theorems consume.
The zero vector is handled separately; otherwise `v` is rescaled to `v / ‖v‖`. -/
private lemma shiSnd_homog {N : ℕ} (A : Op N) (s : ℝ)
    (hqf : ∀ v : Bits N → ℂ, (∑ y : Bits N, ‖v y‖ ^ 2) = 1 →
      0 ≤ (∑ y : Bits N, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y).re
        ∧ (∑ y : Bits N, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y).re ≤ s)
    (v : Bits N → ℂ) :
    0 ≤ (∑ y : Bits N, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y).re
      ∧ (∑ y : Bits N, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y).re
          ≤ s * ∑ y : Bits N, ‖v y‖ ^ 2 := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = ∑ y : Bits N, ‖v y‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ,
      X = (∑ y : Bits N, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y).re := ⟨_, rfl⟩
  rw [← hn, ← hX]
  have hn0 : 0 ≤ n := by
    rw [hn]
    exact Finset.sum_nonneg fun y _ => by positivity
  rcases eq_or_lt_of_le hn0 with hzero | hpos
  · -- degenerate case: `v = 0`, both sides vanish
    have hv0 : ∀ a : Bits N, v a = 0 := by
      intro a
      have hsum : (∑ y : Bits N, ‖v y‖ ^ 2) = 0 := by rw [← hn, ← hzero]
      have hterm : ‖v a‖ ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun b _ => by positivity).mp hsum a (Finset.mem_univ a)
      have hz : ‖v a‖ = 0 := by nlinarith [norm_nonneg (v a)]
      simpa using hz
    have hQ0 : X = 0 := by
      rw [hX]
      have hvan : (∑ y : Bits N, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y) = 0 :=
        Finset.sum_eq_zero fun y _ => by rw [hv0 y]; simp
      rw [hvan]
      simp
    rw [hQ0, ← hzero, mul_zero]
    exact ⟨le_refl 0, le_refl 0⟩
  · -- generic case: rescale to a unit vector
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt n := ⟨_, rfl⟩
    have hr0 : 0 < r := by
      rw [hr]
      exact Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = n := by
      rw [hr]
      first
        | (exact Real.sq_sqrt (le_of_lt hpos); done)
        | (simpa using Real.sq_sqrt (le_of_lt hpos); done)
    have hk : ‖((r⁻¹ : ℝ) : ℂ)‖ = r⁻¹ := by
      first
        | (rw [Complex.norm_ofReal, abs_of_pos (inv_pos.mpr hr0)]; done)
        | (rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]; done)
        | (simp [abs_of_pos (inv_pos.mpr hr0)]; done)
    have hnorm1 : (∑ y : Bits N, ‖((r⁻¹ : ℝ) : ℂ) * v y‖ ^ 2) = 1 := by
      have hstep : ∀ y : Bits N, ‖((r⁻¹ : ℝ) : ℂ) * v y‖ ^ 2 = r⁻¹ ^ 2 * ‖v y‖ ^ 2 := by
        intro y
        rw [norm_mul, hk, mul_pow]
      rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hstep y, ← Finset.mul_sum, ← hn,
        ← hr2]
      field_simp
    obtain ⟨hlo, hhi⟩ := hqf (fun y => ((r⁻¹ : ℝ) : ℂ) * v y) hnorm1
    have hscale : (∑ y : Bits N, (starRingEnd ℂ) (((r⁻¹ : ℝ) : ℂ) * v y)
        * Matrix.mulVec A (fun x => ((r⁻¹ : ℝ) : ℂ) * v x) y).re = r⁻¹ ^ 2 * X := by
      have hcc : (starRingEnd ℂ) (((r⁻¹ : ℝ) : ℂ)) * (((r⁻¹ : ℝ) : ℂ))
          = (((r⁻¹ ^ 2 : ℝ)) : ℂ) := by
        first
          | (rw [Complex.conj_ofReal]; push_cast; ring; done)
          | (push_cast [Complex.conj_ofReal]; ring; done)
          | (simp [Complex.conj_ofReal]; ring; done)
      rw [shiSnd_qf_const, hcc, hX]
      exact shiSnd_re_ofReal_mul _ _
    have hlo' : 0 ≤ r⁻¹ ^ 2 * X := by
      rw [← hscale]
      exact hlo
    have hhi' : r⁻¹ ^ 2 * X ≤ s := by
      rw [← hscale]
      exact hhi
    have hid : X = r ^ 2 * (r⁻¹ ^ 2 * X) := by
      rw [← mul_assoc, show r ^ 2 * r⁻¹ ^ 2 = (1 : ℝ) from by field_simp, one_mul]
    have hsq : (0 : ℝ) ≤ r ^ 2 := by positivity
    refine ⟨by linarith [mul_nonneg hsq hlo'], ?_⟩
    have h1 : r ^ 2 * (r⁻¹ ^ 2 * X) ≤ r ^ 2 * s := mul_le_mul_of_nonneg_left hhi' hsq
    have h2 : s * n = r ^ 2 * s := by
      rw [← hr2]
      ring
    linarith

/-- **The three-block majority bound for an abstract Hermitian operator.**

`A` is an ARBITRARY Hermitian operator on `Bits w` -- not a projector, not built from a circuit
-- whose quadratic form lies in `[0, s]` on every NORMALIZED vector.  `A1, A2, A3` act on a
product of three `A`-eigenvectors as the first, second and third eigenvalue (`hlift`), so the
block liftings `A ⊗ 1 ⊗ 1`, `1 ⊗ A ⊗ 1`, `1 ⊗ 1 ⊗ A` are instances.  Then the
inclusion-exclusion majority polynomial has quadratic form `≤ 3 s ^ 2 - 2 s ^ 3` at an ARBITRARY
normalized `Θ`, with NO product structure assumed of `Θ`.  Satisfiable with equality -- see the
module docstring. -/
theorem solution {w : ℕ} (A : Op w) (hA : A.IsHermitian) (s : ℝ) (hs : s ≤ 1)
    (hqf : ∀ v : Bits w → ℂ, (∑ y : Bits w, ‖v y‖ ^ 2) = 1 →
      0 ≤ (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y).re
        ∧ (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y).re ≤ s)
    (A1 A2 A3 : Op (w + w + w))
    (hlift : ∀ (p q t : QState w) (α β γ : ℂ),
      Matrix.mulVec A p = α • p → Matrix.mulVec A q = β • q → Matrix.mulVec A t = γ • t →
        Matrix.mulVec A1 (tensor (tensor p q) t) = α • tensor (tensor p q) t
          ∧ Matrix.mulVec A2 (tensor (tensor p q) t) = β • tensor (tensor p q) t
          ∧ Matrix.mulVec A3 (tensor (tensor p q) t) = γ • tensor (tensor p q) t)
    (Θ : QState (w + w + w)) (hΘ : (∑ y : Bits (w + w + w), ‖Θ y‖ ^ 2) = 1) :
    (∑ y : Bits (w + w + w), (starRingEnd ℂ) (Θ y)
        * Matrix.mulVec (A1 * A2 + A2 * A3 + A3 * A1 - (2 : ℂ) • (A1 * A2 * A3)) Θ y).re
      ≤ 3 * s ^ 2 - 2 * s ^ 3 := by
  classical
  -- an orthonormal Parseval eigenbasis of the abstract Hermitian `A`
  obtain ⟨u, horth, _hpars, heigA⟩ := exists_sum_form_eigenbasis A hA
  have heigA' : ∀ i : Bits w,
      Matrix.mulVec A (u i) = ((hA.eigenvalues i : ℝ) : ℂ) • u i := fun i =>
    (heigA i).trans (shiSnd_smul_fun _ _)
  -- the eigenvalues of `A` lie in `[0, s]`, via homogenisation of `hqf`
  have hlo : ∀ v : Bits w → ℂ,
      0 ≤ (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y).re :=
    fun v => (shiSnd_homog A s hqf v).1
  have hhi : ∀ v : Bits w → ℂ,
      (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y).re
        ≤ s * ∑ y : Bits w, ‖v y‖ ^ 2 := fun v => (shiSnd_homog A s hqf v).2
  have hα0 : ∀ i : Bits w, 0 ≤ hA.eigenvalues i := fun i =>
    eigenvalues_nonneg_of_quadratic_form_nonneg A hA hlo i
  have hαs : ∀ i : Bits w, hA.eigenvalues i ≤ s := fun i =>
    eigenvalues_le_of_quadratic_form_le A hA s hhi i
  -- products of the eigenbasis form an orthonormal Parseval family on `Bits (w + w + w)`
  obtain ⟨porth, ppars⟩ := product_eigenbasis_sum_form_three u horth
  -- the finisher: arbitrary `Θ` is expanded in that product basis by Parseval
  refine quadratic_form_majority_le_of_eigenbasis _ s hs
    (fun i : (Bits w × Bits w) × Bits w => tensor (tensor (u i.1.1) (u i.1.2)) (u i.2))
    (fun i => hA.eigenvalues i.1.1) (fun i => hA.eigenvalues i.1.2) (fun i => hA.eigenvalues i.2)
    (fun i => hα0 _) (fun i => hα0 _) (fun i => hα0 _)
    (fun i => hαs _) (fun i => hαs _) (fun i => hαs _)
    porth ppars ?_ Θ hΘ
  -- each product basis vector is a common eigenvector of `A1, A2, A3`, hence an eigenvector of
  -- the majority polynomial with the majority polynomial of the three eigenvalues
  intro i
  obtain ⟨h1, h2, h3⟩ := hlift (u i.1.1) (u i.1.2) (u i.2)
    ((hA.eigenvalues i.1.1 : ℝ) : ℂ) ((hA.eigenvalues i.1.2 : ℝ) : ℂ)
    ((hA.eigenvalues i.2 : ℝ) : ℂ) (heigA' i.1.1) (heigA' i.1.2) (heigA' i.2)
  refine Eq.trans (mulVec_majority_inclusion_exclusion_of_common_eigenvector
    A1 A2 A3 (tensor (tensor (u i.1.1) (u i.1.2)) (u i.2)) _ _ _ h1 h2 h3) ?_
  funext y
  first
    | (simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring; done)
    | (push_cast [Pi.smul_apply, smul_eq_mul]; ring; done)
    | (push_cast [Pi.smul_apply, smul_eq_mul]; done)

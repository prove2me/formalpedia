-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P44.compact_positive_marginal_slices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:14:29.381517+00:00
-- url     : https://prove2.me/submissions/ced7282c-39f3-400e-b4bb-c986082a4965

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

open scoped Matrix ComplexOrder ComplexConjugate

namespace X7cs

theorem closed_psd {E : Type*} [Fintype E] :
    IsClosed {X : Matrix E E ℂ | X.PosSemidef} := by
  have e : {X : Matrix E E ℂ | X.PosSemidef} =
      {X | Xᴴ = X} ∩ ⋂ x : E → ℂ, {X | 0 ≤ (star x ⬝ᵥ (X *ᵥ x)).re ∧ (star x ⬝ᵥ (X *ᵥ x)).im = 0} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Matrix.posSemidef_iff_dotProduct_mulVec,
      Matrix.IsHermitian, Complex.nonneg_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun x => ⟨(h2 x).1, (h2 x).2.symm⟩⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun x => ⟨(h2 x).1, (h2 x).2.symm⟩⟩
  rw [e]
  refine IsClosed.inter (isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id) ?_
  refine isClosed_iInter fun x => ?_
  have hc : Continuous fun X : Matrix E E ℂ => star x ⬝ᵥ (X *ᵥ x) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  exact IsClosed.inter (isClosed_le continuous_const (Complex.continuous_re.comp hc))
    (isClosed_eq (Complex.continuous_im.comp hc) continuous_const)

theorem entry_bound {E : Type*} [Fintype E] [DecidableEq E] (X : Matrix E E ℂ) (hX : X.PosSemidef) (i j : E) :
    ‖X i j‖ ≤ X.trace.re := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  have hent : ∀ a b, X a b = ∑ k, v k a * conj (v k b) := by
    intro a b; rw [hv, Matrix.sum_apply]; simp [Matrix.vecMulVec_apply]
  have htr : X.trace.re = ∑ k, ∑ a, Complex.normSq (v k a) := by
    rw [Matrix.trace, Complex.re_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.diag, hent, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re]
  rw [hent, htr]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, Complex.norm_conj]
  have h1 : ‖v k i‖ * ‖v k j‖ ≤ (Complex.normSq (v k i) + Complex.normSq (v k j)) / 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖v k i‖ - ‖v k j‖)]
  by_cases hij : i = j
  · subst hij
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have := Finset.sum_nonneg (s := Finset.univ.erase i) fun a _ => Complex.normSq_nonneg (v k a)
    linarith
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
    have := Finset.sum_nonneg (s := (Finset.univ.erase i).erase j) fun a _ => Complex.normSq_nonneg (v k a)
    have h2 := Complex.normSq_nonneg (v k i)
    have h3 := Complex.normSq_nonneg (v k j)
    linarith

theorem main {E : Type*} [Fintype E] [DecidableEq E] (alpha : ℝ) (halpha : 0 ≤ alpha) :
    IsCompact {X : Matrix E E ℂ | X.PosSemidef ∧ X.trace.re ≤ alpha} ∧
      IsCompact {X : Matrix E E ℂ | X.PosSemidef ∧ X.trace.re = alpha} := by
  have hK : IsCompact (Set.univ.pi fun _ : E => Set.univ.pi fun _ : E => Metric.closedBall (0 : ℂ) alpha) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 alpha
  have htr : Continuous fun X : Matrix E E ℂ => X.trace.re := by
    simp only [Matrix.trace, Matrix.diag]; fun_prop
  have h1 : IsCompact {X : Matrix E E ℂ | X.PosSemidef ∧ X.trace.re ≤ alpha} := by
    refine hK.of_isClosed_subset ?_ ?_
    · exact IsClosed.inter closed_psd (isClosed_le htr continuous_const)
    · rintro X ⟨hX, ht⟩
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
      intro i j
      exact (entry_bound X hX i j).trans ht
  refine ⟨h1, h1.of_isClosed_subset ?_ ?_⟩
  · exact IsClosed.inter closed_psd (isClosed_eq htr continuous_const)
  · rintro X ⟨hX, ht⟩; exact ⟨hX, ht.le⟩

end X7cs

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

open scoped Matrix ComplexOrder

theorem X7cs_marg {E G : Type*} [Fintype E] [Fintype G] [DecidableEq E] [DecidableEq G]
    (sigma : Matrix G G ℂ) (hsigma : sigma.PosSemidef) :
    IsCompact {X : Matrix (E × G) (E × G) ℂ |
      X.PosSemidef ∧ (sigma - traceLeft X).PosSemidef} ∧
    IsCompact {X : Matrix (E × G) (E × G) ℂ |
      X.PosSemidef ∧ traceLeft X = sigma} := by
  have htrL : ∀ X : Matrix (E × G) (E × G) ℂ, (traceLeft X).trace = X.trace := by
    intro X
    simp only [traceLeft, Matrix.trace, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hcont : Continuous fun X : Matrix (E × G) (E × G) ℂ => traceLeft X := by
    refine continuous_pi fun b => continuous_pi fun b' => ?_
    simp only [traceLeft, Matrix.of_apply]
    fun_prop
  have hα : 0 ≤ sigma.trace.re := (Complex.nonneg_iff.mp hsigma.trace_nonneg).1
  have hK := (X7cs.main (E := E × G) sigma.trace.re hα).1
  constructor
  · refine hK.of_isClosed_subset ?_ ?_
    · refine IsClosed.inter X7cs.closed_psd ?_
      exact X7cs.closed_psd.preimage (continuous_const.sub hcont)
    · rintro X ⟨hX, hS⟩
      refine ⟨hX, ?_⟩
      have := (Complex.nonneg_iff.mp hS.trace_nonneg).1
      rw [Matrix.trace_sub, Complex.sub_re, htrL] at this
      linarith
  · refine hK.of_isClosed_subset ?_ ?_
    · exact IsClosed.inter X7cs.closed_psd (isClosed_eq hcont continuous_const)
    · rintro X ⟨hX, hS⟩
      refine ⟨hX, ?_⟩
      rw [← htrL, hS]

end QAlgorithms.Papers.Independent.Support50.P44

end

open QAlgorithms.Papers.Independent.Support50.P44 QAlgorithms in
open scoped Matrix ComplexOrder in
theorem solution {E G : Type*} [Fintype E] [Fintype G]
    [DecidableEq E] [DecidableEq G]
    (sigma : Matrix G G ℂ) (hsigma : sigma.PosSemidef) :
    IsCompact {X : Matrix (E × G) (E × G) ℂ |
      X.PosSemidef ∧ (sigma - traceLeft X).PosSemidef} ∧
    IsCompact {X : Matrix (E × G) (E × G) ℂ |
      X.PosSemidef ∧ traceLeft X = sigma} :=
  X7cs_marg sigma hsigma
